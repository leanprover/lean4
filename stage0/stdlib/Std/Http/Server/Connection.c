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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(uint8_t, lean_object*);
lean_object* l_Std_Http_Body_Stream_send(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Body_Stream_close(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object*);
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_date;
lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Http_Body_mkStream();
lean_object* l_Std_Http_Protocol_H1_Machine_canContinue(uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Async_Selector_sleep(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Functor_discard(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Channel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(lean_object* v_x_40_){
_start:
{
switch(lean_obj_tag(v_x_40_))
{
case 0:
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(0u);
return v___x_41_;
}
case 1:
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(1u);
return v___x_42_;
}
case 2:
{
lean_object* v___x_43_; 
v___x_43_ = lean_unsigned_to_nat(2u);
return v___x_43_;
}
case 3:
{
lean_object* v___x_44_; 
v___x_44_ = lean_unsigned_to_nat(3u);
return v___x_44_;
}
case 4:
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(4u);
return v___x_45_;
}
case 5:
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(5u);
return v___x_46_;
}
default: 
{
lean_object* v___x_47_; 
v___x_47_ = lean_unsigned_to_nat(6u);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg___boxed(lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(v_x_48_);
lean_dec(v_x_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx(lean_object* v_00_u03b2_50_, lean_object* v_x_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(v_x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___boxed(lean_object* v_00_u03b2_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx(v_00_u03b2_53_, v_x_54_);
lean_dec(v_x_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(lean_object* v_t_56_, lean_object* v_k_57_){
_start:
{
switch(lean_obj_tag(v_t_56_))
{
case 0:
{
lean_object* v_x_58_; lean_object* v___x_59_; 
v_x_58_ = lean_ctor_get(v_t_56_, 0);
lean_inc(v_x_58_);
lean_dec_ref_known(v_t_56_, 1);
v___x_59_ = lean_apply_1(v_k_57_, v_x_58_);
return v___x_59_;
}
case 1:
{
lean_object* v_x_60_; lean_object* v___x_61_; 
v_x_60_ = lean_ctor_get(v_t_56_, 0);
lean_inc(v_x_60_);
lean_dec_ref_known(v_t_56_, 1);
v___x_61_ = lean_apply_1(v_k_57_, v_x_60_);
return v___x_61_;
}
case 2:
{
uint8_t v_x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_x_62_ = lean_ctor_get_uint8(v_t_56_, 0);
lean_dec_ref_known(v_t_56_, 0);
v___x_63_ = lean_box(v_x_62_);
v___x_64_ = lean_apply_1(v_k_57_, v___x_63_);
return v___x_64_;
}
case 3:
{
lean_object* v_x_65_; lean_object* v___x_66_; 
v_x_65_ = lean_ctor_get(v_t_56_, 0);
lean_inc_ref(v_x_65_);
lean_dec_ref_known(v_t_56_, 1);
v___x_66_ = lean_apply_1(v_k_57_, v_x_65_);
return v___x_66_;
}
default: 
{
lean_dec(v_t_56_);
return v_k_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(lean_object* v_00_u03b2_67_, lean_object* v_motive_68_, lean_object* v_ctorIdx_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_k_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_70_, v_k_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___boxed(lean_object* v_00_u03b2_74_, lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(v_00_u03b2_74_, v_motive_75_, v_ctorIdx_76_, v_t_77_, v_h_78_, v_k_79_);
lean_dec(v_ctorIdx_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim___redArg(lean_object* v_t_81_, lean_object* v_bytes_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_81_, v_bytes_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim(lean_object* v_00_u03b2_84_, lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_bytes_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_86_, v_bytes_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim___redArg(lean_object* v_t_90_, lean_object* v_responseBody_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_90_, v_responseBody_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim(lean_object* v_00_u03b2_93_, lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_responseBody_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_95_, v_responseBody_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim___redArg(lean_object* v_t_99_, lean_object* v_bodyInterest_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_99_, v_bodyInterest_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim(lean_object* v_00_u03b2_102_, lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_bodyInterest_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_104_, v_bodyInterest_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim___redArg(lean_object* v_t_108_, lean_object* v_response_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_108_, v_response_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim(lean_object* v_00_u03b2_111_, lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_response_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_113_, v_response_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object* v_t_117_, lean_object* v_timeout_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_117_, v_timeout_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object* v_00_u03b2_120_, lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_timeout_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_122_, v_timeout_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object* v_t_126_, lean_object* v_shutdown_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_126_, v_shutdown_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object* v_00_u03b2_129_, lean_object* v_motive_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_shutdown_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_131_, v_shutdown_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object* v_t_135_, lean_object* v_close_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_135_, v_close_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object* v_00_u03b2_138_, lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_close_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_140_, v_close_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_a_156_ = lean_ctor_get(v_x_152_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v_x_152_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v_x_152_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_163_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
}
else
{
lean_object* v_a_165_; 
v_a_165_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v_x_152_, 1);
if (lean_obj_tag(v_a_165_) == 1)
{
lean_object* v_val_166_; 
v_val_166_ = lean_ctor_get(v_a_165_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v_a_165_, 1);
if (lean_obj_tag(v_val_166_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_167_;
}
else
{
lean_dec(v_val_166_);
goto v___jp_154_;
}
}
else
{
lean_dec(v_a_165_);
goto v___jp_154_;
}
}
v___jp_154_:
{
lean_object* v___x_155_; 
v___x_155_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1));
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_a_177_ = lean_ctor_get(v_x_175_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_175_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v_x_175_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v_x_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_184_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
else
{
lean_object* v___x_186_; 
lean_dec_ref_known(v_x_175_, 1);
v___x_186_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_190_, lean_object* v_handler_191_, lean_object* v___f_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v_a_195_; lean_object* v_onFailure_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; 
v_a_195_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v_x_193_, 1);
v_onFailure_196_ = lean_ctor_get(v_inst_190_, 2);
lean_inc_ref(v_onFailure_196_);
lean_dec_ref(v_inst_190_);
v___x_197_ = lean_apply_3(v_onFailure_196_, v_handler_191_, v_a_195_, lean_box(0));
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = 0;
v___x_200_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_198_, v___x_199_, v___x_197_, v___f_192_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; 
lean_dec_ref(v___f_192_);
lean_dec(v_handler_191_);
lean_dec_ref(v_inst_190_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v_x_193_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_202_, lean_object* v_handler_203_, lean_object* v___f_204_, lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_202_, v_handler_203_, v___f_204_, v_x_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v_x_208_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_218_, 0, v_x_216_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_x_3646__boxed_223_; lean_object* v_res_224_; 
v_x_3646__boxed_223_ = lean_unbox(v_x_221_);
v_res_224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3646__boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_225_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_x_225_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v_x_233_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v___f_247_, lean_object* v_response_248_, lean_object* v___x_249_, lean_object* v___f_250_, lean_object* v_requestBody_251_, lean_object* v___f_252_, lean_object* v_responseBody_253_, lean_object* v_inst_254_, lean_object* v___f_255_, lean_object* v_____r_256_, lean_object* v_selectables_257_){
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
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___x_261_ = l_Std_Async_Selectable_one___redArg(v_selectables_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = 0;
v___x_264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_262_, v___x_263_, v___x_261_, v___f_247_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v___f_282_, lean_object* v_response_283_, lean_object* v___x_284_, lean_object* v___f_285_, lean_object* v_requestBody_286_, lean_object* v___f_287_, lean_object* v_responseBody_288_, lean_object* v_inst_289_, lean_object* v___f_290_, lean_object* v_____r_291_, lean_object* v_selectables_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_282_, v_response_283_, v___x_284_, v___f_285_, v_requestBody_286_, v___f_287_, v_responseBody_288_, v_inst_289_, v___f_290_, v_____r_291_, v_selectables_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v_token_295_, lean_object* v___f_296_, lean_object* v_x_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; 
v___x_299_ = l_Std_CancellationToken_getCancellationReason(v_token_295_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = 0;
v___x_304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_302_, v___x_303_, v___x_301_, v___f_296_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v_token_305_, lean_object* v___f_306_, lean_object* v_x_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v_token_305_, v___f_306_, v_x_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v___f_310_, lean_object* v_selectables_311_, lean_object* v___f_312_, lean_object* v_x_313_){
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v___f_329_, lean_object* v_selectables_330_, lean_object* v___f_331_, lean_object* v_x_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v___f_329_, v_selectables_330_, v___f_331_, v_x_332_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1000000000u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1000u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1000000u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v_val_341_, lean_object* v___f_342_, lean_object* v_x_343_){
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
lean_object* v_a_354_; lean_object* v_second_355_; lean_object* v_nano_356_; lean_object* v_second_357_; lean_object* v_nano_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_second_368_; lean_object* v_nano_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_millis_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; 
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
v___x_361_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_362_ = lean_int_mul(v_second_357_, v___x_361_);
v___x_363_ = lean_int_add(v___x_362_, v_nano_358_);
lean_dec(v___x_362_);
v___x_364_ = lean_int_mul(v___x_359_, v___x_361_);
lean_dec(v___x_359_);
v___x_365_ = lean_int_add(v___x_364_, v___x_360_);
lean_dec(v___x_360_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_add(v___x_363_, v___x_365_);
lean_dec(v___x_365_);
lean_dec(v___x_363_);
v___x_367_ = l_Std_Time_Duration_ofNanoseconds(v___x_366_);
lean_dec(v___x_366_);
v_second_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_second_368_);
v_nano_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_nano_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1);
v___x_371_ = lean_int_mul(v_second_368_, v___x_370_);
lean_dec(v_second_368_);
v___x_372_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_373_ = lean_int_ediv(v_nano_369_, v___x_372_);
lean_dec(v_nano_369_);
v_millis_374_ = lean_int_add(v___x_371_, v___x_373_);
lean_dec(v___x_373_);
lean_dec(v___x_371_);
v___x_375_ = l_Std_Async_Selector_sleep(v_millis_374_);
lean_dec(v_millis_374_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = 0;
v___x_378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_376_, v___x_377_, v___x_375_, v___f_342_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v_val_379_, lean_object* v___f_380_, lean_object* v_x_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v_val_379_, v___f_380_, v_x_381_);
lean_dec_ref(v_val_379_);
return v_res_383_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_instInhabitedError;
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_config_396_, lean_object* v_handler_397_, lean_object* v_sources_398_){
_start:
{
lean_object* v___y_401_; lean_object* v_val_402_; lean_object* v_socket_407_; lean_object* v_expect_408_; lean_object* v_response_409_; lean_object* v_responseBody_410_; lean_object* v_requestBody_411_; lean_object* v_timeout_412_; lean_object* v_keepAliveTimeout_413_; lean_object* v_headerTimeout_414_; lean_object* v_connectionContext_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___f_425_; lean_object* v___y_427_; lean_object* v___y_472_; 
v_socket_407_ = lean_ctor_get(v_sources_398_, 0);
lean_inc(v_socket_407_);
v_expect_408_ = lean_ctor_get(v_sources_398_, 1);
lean_inc(v_expect_408_);
v_response_409_ = lean_ctor_get(v_sources_398_, 2);
lean_inc_n(v_response_409_, 2);
v_responseBody_410_ = lean_ctor_get(v_sources_398_, 3);
lean_inc_n(v_responseBody_410_, 2);
v_requestBody_411_ = lean_ctor_get(v_sources_398_, 4);
lean_inc_n(v_requestBody_411_, 2);
v_timeout_412_ = lean_ctor_get(v_sources_398_, 5);
lean_inc(v_timeout_412_);
v_keepAliveTimeout_413_ = lean_ctor_get(v_sources_398_, 6);
lean_inc(v_keepAliveTimeout_413_);
v_headerTimeout_414_ = lean_ctor_get(v_sources_398_, 7);
lean_inc(v_headerTimeout_414_);
v_connectionContext_415_ = lean_ctor_get(v_sources_398_, 8);
lean_inc_ref(v_connectionContext_415_);
lean_dec_ref(v_sources_398_);
v___f_416_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_417_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_418_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_418_, 0, v_inst_394_);
lean_closure_set(v___f_418_, 1, v_handler_397_);
lean_closure_set(v___f_418_, 2, v___f_417_);
v___f_419_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_420_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_421_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_422_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_423_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___x_424_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7);
lean_inc_ref(v_inst_395_);
lean_inc_ref(v___f_418_);
v___f_425_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed), 12, 9);
lean_closure_set(v___f_425_, 0, v___f_418_);
lean_closure_set(v___f_425_, 1, v_response_409_);
lean_closure_set(v___f_425_, 2, v___x_424_);
lean_closure_set(v___f_425_, 3, v___f_419_);
lean_closure_set(v___f_425_, 4, v_requestBody_411_);
lean_closure_set(v___f_425_, 5, v___f_420_);
lean_closure_set(v___f_425_, 6, v_responseBody_410_);
lean_closure_set(v___f_425_, 7, v_inst_395_);
lean_closure_set(v___f_425_, 8, v___f_421_);
if (lean_obj_tag(v_expect_408_) == 0)
{
lean_object* v_defaultPayloadBytes_475_; 
v_defaultPayloadBytes_475_ = lean_ctor_get(v_config_396_, 8);
lean_inc(v_defaultPayloadBytes_475_);
v___y_472_ = v_defaultPayloadBytes_475_;
goto v___jp_471_;
}
else
{
lean_object* v_val_476_; 
v_val_476_ = lean_ctor_get(v_expect_408_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_expect_408_, 1);
v___y_472_ = v_val_476_;
goto v___jp_471_;
}
v___jp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v_val_402_);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = 0;
v___x_406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_404_, v___x_405_, v___x_403_, v___y_401_);
return v___x_406_;
}
v___jp_426_:
{
lean_object* v_token_428_; lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_selectables_434_; 
v_token_428_ = lean_ctor_get(v_connectionContext_415_, 1);
lean_inc_ref_n(v_token_428_, 2);
lean_dec_ref(v_connectionContext_415_);
v___f_429_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 4, 2);
lean_closure_set(v___f_429_, 0, v_token_428_);
lean_closure_set(v___f_429_, 1, v___f_416_);
v___x_430_ = l_Std_CancellationToken_selector(v_token_428_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___f_429_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_mk_empty_array_with_capacity(v___x_432_);
v_selectables_434_ = lean_array_push(v___x_433_, v___x_431_);
if (lean_obj_tag(v_socket_407_) == 1)
{
lean_object* v_val_435_; lean_object* v_recvSelector_436_; uint64_t v_expectedBytes_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_selectables_441_; 
v_val_435_ = lean_ctor_get(v_socket_407_, 0);
lean_inc(v_val_435_);
lean_dec_ref_known(v_socket_407_, 1);
v_recvSelector_436_ = lean_ctor_get(v_inst_393_, 2);
lean_inc_ref(v_recvSelector_436_);
lean_dec_ref(v_inst_393_);
v_expectedBytes_437_ = lean_uint64_of_nat(v___y_427_);
lean_dec(v___y_427_);
v___x_438_ = lean_box_uint64(v_expectedBytes_437_);
v___x_439_ = lean_apply_2(v_recvSelector_436_, v_val_435_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___f_422_);
v_selectables_441_ = lean_array_push(v_selectables_434_, v___x_440_);
if (lean_obj_tag(v_keepAliveTimeout_413_) == 0)
{
lean_dec_ref(v___f_418_);
lean_dec(v_requestBody_411_);
lean_dec(v_responseBody_410_);
lean_dec(v_response_409_);
lean_dec_ref(v_inst_395_);
if (lean_obj_tag(v_headerTimeout_414_) == 1)
{
lean_object* v_val_442_; lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
lean_dec(v_timeout_412_);
v_val_442_ = lean_ctor_get(v_headerTimeout_414_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v_headerTimeout_414_, 1);
v___f_443_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_443_, 0, v___f_423_);
lean_closure_set(v___f_443_, 1, v_selectables_441_);
lean_closure_set(v___f_443_, 2, v___f_425_);
v___f_444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 4, 2);
lean_closure_set(v___f_444_, 0, v_val_442_);
lean_closure_set(v___f_444_, 1, v___f_443_);
v___x_445_ = lean_get_current_time();
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 1);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
v___y_401_ = v___f_444_;
v_val_402_ = v___x_451_;
goto v___jp_400_;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_445_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_445_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 0);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_401_ = v___f_444_;
v_val_402_ = v___x_459_;
goto v___jp_400_;
}
}
}
}
else
{
lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; 
lean_dec(v_headerTimeout_414_);
v___x_462_ = l_Std_Async_Selector_sleep(v_timeout_412_);
lean_dec(v_timeout_412_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_463_, 0, v___f_423_);
lean_closure_set(v___f_463_, 1, v_selectables_441_);
lean_closure_set(v___f_463_, 2, v___f_425_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = 0;
v___x_466_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_464_, v___x_465_, v___x_462_, v___f_463_);
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec_ref_known(v_keepAliveTimeout_413_, 1);
lean_dec_ref(v___f_425_);
lean_dec(v_headerTimeout_414_);
lean_dec(v_timeout_412_);
v___x_467_ = lean_box(0);
v___x_468_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_418_, v_response_409_, v___x_424_, v___f_419_, v_requestBody_411_, v___f_420_, v_responseBody_410_, v_inst_395_, v___f_421_, v___x_467_, v_selectables_441_);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v___y_427_);
lean_dec_ref(v___f_425_);
lean_dec(v_headerTimeout_414_);
lean_dec(v_keepAliveTimeout_413_);
lean_dec(v_timeout_412_);
lean_dec(v_socket_407_);
lean_dec_ref(v_inst_393_);
v___x_469_ = lean_box(0);
v___x_470_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_418_, v_response_409_, v___x_424_, v___f_419_, v_requestBody_411_, v___f_420_, v_responseBody_410_, v_inst_395_, v___f_421_, v___x_469_, v_selectables_434_);
return v___x_470_;
}
}
v___jp_471_:
{
lean_object* v_maximumRecvSize_473_; uint8_t v___x_474_; 
v_maximumRecvSize_473_ = lean_ctor_get(v_config_396_, 7);
lean_inc(v_maximumRecvSize_473_);
lean_dec_ref(v_config_396_);
v___x_474_ = lean_nat_dec_le(v___y_472_, v_maximumRecvSize_473_);
if (v___x_474_ == 0)
{
lean_dec(v___y_472_);
v___y_427_ = v_maximumRecvSize_473_;
goto v___jp_426_;
}
else
{
lean_dec(v_maximumRecvSize_473_);
v___y_427_ = v___y_472_;
goto v___jp_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_config_480_, lean_object* v_handler_481_, lean_object* v_sources_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_477_, v_inst_478_, v_inst_479_, v_config_480_, v_handler_481_, v_sources_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_485_, lean_object* v_00_u03c3_486_, lean_object* v_00_u03b2_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_config_491_, lean_object* v_handler_492_, lean_object* v_sources_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_config_491_, v_handler_492_, v_sources_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_496_, lean_object* v_00_u03c3_497_, lean_object* v_00_u03b2_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_config_502_, lean_object* v_handler_503_, lean_object* v_sources_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_496_, v_00_u03c3_497_, v_00_u03b2_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_config_502_, v_handler_503_, v_sources_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_507_, lean_object* v_x_508_){
_start:
{
lean_object* v___y_511_; uint8_t v___y_512_; 
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_machine_507_);
v_a_517_ = lean_ctor_get(v_x_508_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v_x_508_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v_x_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___y_528_; uint8_t v___x_534_; 
v_a_526_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v_x_508_, 1);
v___x_534_ = lean_unbox(v_a_526_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_box(40);
v___y_528_ = v___x_535_;
goto v___jp_527_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(0);
v___y_528_ = v___x_536_;
goto v___jp_527_;
}
v___jp_527_:
{
uint8_t v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_529_ = 0;
lean_inc(v___y_528_);
v___x_530_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_529_, v_machine_507_, v___y_528_);
v___x_531_ = lean_unbox(v_a_526_);
lean_dec(v_a_526_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
v___x_532_ = 1;
v___y_511_ = v___x_530_;
v___y_512_ = v___x_532_;
goto v___jp_510_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = 0;
v___y_511_ = v___x_530_;
v___y_512_ = v___x_533_;
goto v___jp_510_;
}
}
}
v___jp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_box(v___y_512_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___y_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_537_, lean_object* v_x_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_537_, v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_541_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_box(v___y_541_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___y_1411__boxed_548_; lean_object* v_res_549_; 
v___y_1411__boxed_548_ = lean_unbox(v___y_546_);
v_res_549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1411__boxed_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_550_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; 
v_a_551_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_x_550_, 1);
v___x_552_ = lean_task_pure(v_a_551_);
return v___x_552_;
}
else
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v_x_550_, 0);
lean_inc_ref(v_a_553_);
lean_dec_ref_known(v_x_550_, 1);
return v_a_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref_known(v_x_555_, 1);
v___x_557_ = 0;
v___x_558_ = lean_box(v___x_557_);
v___x_559_ = l_Std_Channel_send___redArg(v_a_554_, v___x_558_);
lean_dec_ref(v___x_559_);
v___x_560_ = lean_box(0);
return v___x_560_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_561_ = lean_ctor_get(v_x_555_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v_x_555_, 1);
v___x_562_ = l_Std_Channel_send___redArg(v_a_554_, v_a_561_);
lean_dec_ref(v___x_562_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_564_, lean_object* v_x_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_564_, v_x_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_box(v___x_568_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_574_, lean_object* v_x_575_, lean_object* v___y_576_){
_start:
{
uint8_t v___x_1455__boxed_577_; lean_object* v_res_578_; 
v___x_1455__boxed_577_ = lean_unbox(v___x_574_);
v_res_578_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1455__boxed_577_, v_x_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_579_, uint8_t v___x_580_, lean_object* v_a_581_, lean_object* v___f_582_, lean_object* v___f_583_, lean_object* v___x_584_, uint8_t v___x_585_, lean_object* v___f_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v___f_586_);
lean_dec(v___x_584_);
lean_dec_ref(v___f_583_);
lean_dec_ref(v___f_582_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_connectionContext_579_);
v_a_589_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v_x_587_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v_x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v_token_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_a_598_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v_x_587_, 1);
v_token_599_ = lean_ctor_get(v_connectionContext_579_, 1);
lean_inc_ref(v_token_599_);
lean_dec_ref(v_connectionContext_579_);
v___x_600_ = lean_box(v___x_580_);
v___x_601_ = l_Std_Channel_recvSelector___redArg(v___x_600_, v_a_581_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___f_582_);
v___x_603_ = l_Std_CancellationToken_selector(v_token_599_);
lean_inc_ref(v___f_583_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___f_583_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v_a_598_);
lean_ctor_set(v___x_605_, 1, v___f_583_);
v___x_606_ = lean_unsigned_to_nat(3u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_array_push(v___x_607_, v___x_602_);
v___x_609_ = lean_array_push(v___x_608_, v___x_604_);
v___x_610_ = lean_array_push(v___x_609_, v___x_605_);
v___x_611_ = l_Std_Async_Selectable_one___redArg(v___x_610_);
v___x_612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_584_, v___x_585_, v___x_611_, v___f_586_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_613_, lean_object* v___x_614_, lean_object* v_a_615_, lean_object* v___f_616_, lean_object* v___f_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___f_620_, lean_object* v_x_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_1470__boxed_623_; uint8_t v___x_1475__boxed_624_; lean_object* v_res_625_; 
v___x_1470__boxed_623_ = lean_unbox(v___x_614_);
v___x_1475__boxed_624_ = lean_unbox(v___x_619_);
v_res_625_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_613_, v___x_1470__boxed_623_, v_a_615_, v___f_616_, v___f_617_, v___x_618_, v___x_1475__boxed_624_, v___f_620_, v_x_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_626_, lean_object* v___x_627_, uint8_t v___x_628_, lean_object* v___f_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___f_629_);
lean_dec(v___x_627_);
v_a_632_ = lean_ctor_get(v_x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v_x_630_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v_x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
else
{
lean_object* v_lingeringTimeout_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref_known(v_x_630_, 1);
v_lingeringTimeout_641_ = lean_ctor_get(v_config_626_, 4);
v___x_642_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_641_);
v___x_643_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_627_, v___x_628_, v___x_642_, v___f_629_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___f_647_, lean_object* v_x_648_, lean_object* v___y_649_){
_start:
{
uint8_t v___x_1544__boxed_650_; lean_object* v_res_651_; 
v___x_1544__boxed_650_ = lean_unbox(v___x_646_);
v_res_651_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_644_, v___x_645_, v___x_1544__boxed_650_, v___f_647_, v_x_648_);
lean_dec_ref(v_config_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v___f_655_, lean_object* v___x_656_, lean_object* v_connectionContext_657_, uint8_t v___x_658_, lean_object* v_a_659_, lean_object* v___f_660_, lean_object* v___f_661_, lean_object* v_config_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_config_662_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v___f_660_);
lean_dec_ref(v_a_659_);
lean_dec_ref(v_connectionContext_657_);
lean_dec(v___x_656_);
lean_dec_ref(v___f_655_);
v_a_665_ = lean_ctor_get(v_x_663_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_673_ == 0)
{
v___x_667_ = v_x_663_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v_x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_672_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_691_; 
v_a_674_ = lean_ctor_get(v_x_663_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_691_ == 0)
{
v___x_676_ = v_x_663_;
v_isShared_677_ = v_isSharedCheck_691_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v_x_663_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_691_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___f_683_; lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_687_; 
v___x_678_ = 0;
lean_inc_n(v___x_656_, 3);
v___x_679_ = l_BaseIO_chainTask___redArg(v_a_674_, v___f_655_, v___x_656_, v___x_678_);
v___f_680_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_681_ = lean_box(v___x_658_);
v___x_682_ = lean_box(v___x_678_);
v___f_683_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_683_, 0, v_connectionContext_657_);
lean_closure_set(v___f_683_, 1, v___x_681_);
lean_closure_set(v___f_683_, 2, v_a_659_);
lean_closure_set(v___f_683_, 3, v___f_660_);
lean_closure_set(v___f_683_, 4, v___f_680_);
lean_closure_set(v___f_683_, 5, v___x_656_);
lean_closure_set(v___f_683_, 6, v___x_682_);
lean_closure_set(v___f_683_, 7, v___f_661_);
v___x_684_ = lean_box(v___x_678_);
v___f_685_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_685_, 0, v_config_662_);
lean_closure_set(v___f_685_, 1, v___x_656_);
lean_closure_set(v___f_685_, 2, v___x_684_);
lean_closure_set(v___f_685_, 3, v___f_683_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_679_);
v___x_687_ = v___x_676_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_679_);
v___x_687_ = v_reuseFailAlloc_690_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___x_689_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_656_, v___x_678_, v___x_688_, v___f_685_);
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v___f_692_, lean_object* v___x_693_, lean_object* v_connectionContext_694_, lean_object* v___x_695_, lean_object* v_a_696_, lean_object* v___f_697_, lean_object* v___f_698_, lean_object* v_config_699_, lean_object* v_x_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_1586__boxed_702_; lean_object* v_res_703_; 
v___x_1586__boxed_702_ = lean_unbox(v___x_695_);
v_res_703_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v___f_692_, v___x_693_, v_connectionContext_694_, v___x_1586__boxed_702_, v_a_696_, v___f_697_, v___f_698_, v_config_699_, v_x_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_704_, lean_object* v_handler_705_, lean_object* v_head_706_, lean_object* v_connectionContext_707_, uint8_t v___x_708_, lean_object* v___f_709_, lean_object* v___f_710_, lean_object* v_config_711_, lean_object* v___f_712_, lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___f_712_);
lean_dec_ref(v_config_711_);
lean_dec_ref(v___f_710_);
lean_dec_ref(v___f_709_);
lean_dec_ref(v_connectionContext_707_);
lean_dec_ref(v_head_706_);
lean_dec(v_handler_705_);
lean_dec_ref(v_inst_704_);
v_a_715_ = lean_ctor_get(v_x_713_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v_x_713_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v_x_713_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_744_; 
v_a_724_ = lean_ctor_get(v_x_713_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_744_ == 0)
{
v___x_726_ = v_x_713_;
v_isShared_727_ = v_isSharedCheck_744_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v_x_713_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_744_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_onContinue_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___f_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v_onContinue_728_ = lean_ctor_get(v_inst_704_, 3);
lean_inc_ref(v_onContinue_728_);
lean_dec_ref(v_inst_704_);
v___x_729_ = lean_apply_2(v_onContinue_728_, v_handler_705_, v_head_706_);
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_731_, 0, lean_box(0));
lean_closure_set(v___x_731_, 1, v___x_729_);
v___x_732_ = lean_io_as_task(v___x_731_, v___x_730_);
lean_inc(v_a_724_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v_a_724_);
v___x_734_ = lean_box(v___x_708_);
v___f_735_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_735_, 0, v___f_733_);
lean_closure_set(v___f_735_, 1, v___x_730_);
lean_closure_set(v___f_735_, 2, v_connectionContext_707_);
lean_closure_set(v___f_735_, 3, v___x_734_);
lean_closure_set(v___f_735_, 4, v_a_724_);
lean_closure_set(v___f_735_, 5, v___f_709_);
lean_closure_set(v___f_735_, 6, v___f_710_);
lean_closure_set(v___f_735_, 7, v_config_711_);
v___x_736_ = 1;
v___x_737_ = lean_task_bind(v___x_732_, v___f_712_, v___x_730_, v___x_736_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_737_);
v___x_739_ = v___x_726_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
v___x_741_ = 0;
v___x_742_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_730_, v___x_741_, v___x_740_, v___f_735_);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_745_, lean_object* v_handler_746_, lean_object* v_head_747_, lean_object* v_connectionContext_748_, lean_object* v___x_749_, lean_object* v___f_750_, lean_object* v___f_751_, lean_object* v_config_752_, lean_object* v___f_753_, lean_object* v_x_754_, lean_object* v___y_755_){
_start:
{
uint8_t v___x_1667__boxed_756_; lean_object* v_res_757_; 
v___x_1667__boxed_756_ = lean_unbox(v___x_749_);
v_res_757_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_745_, v_handler_746_, v_head_747_, v_connectionContext_748_, v___x_1667__boxed_756_, v___f_750_, v___f_751_, v_config_752_, v___f_753_, v_x_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_760_, lean_object* v_handler_761_, lean_object* v_machine_762_, lean_object* v_head_763_, lean_object* v_config_764_, lean_object* v_connectionContext_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_767_ = lean_box(0);
v___x_768_ = l_Std_CloseableChannel_new___redArg(v___x_767_);
v___f_769_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_769_, 0, v_machine_762_);
v___f_770_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_771_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_772_ = 0;
v___x_773_ = lean_box(v___x_772_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_774_, 0, v_inst_760_);
lean_closure_set(v___f_774_, 1, v_handler_761_);
lean_closure_set(v___f_774_, 2, v_head_763_);
lean_closure_set(v___f_774_, 3, v_connectionContext_765_);
lean_closure_set(v___f_774_, 4, v___x_773_);
lean_closure_set(v___f_774_, 5, v___f_770_);
lean_closure_set(v___f_774_, 6, v___f_769_);
lean_closure_set(v___f_774_, 7, v_config_764_);
lean_closure_set(v___f_774_, 8, v___f_771_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_768_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_777_, v___x_772_, v___x_776_, v___f_774_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_779_, lean_object* v_handler_780_, lean_object* v_machine_781_, lean_object* v_head_782_, lean_object* v_config_783_, lean_object* v_connectionContext_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_779_, v_handler_780_, v_machine_781_, v_head_782_, v_config_783_, v_connectionContext_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_787_, lean_object* v_inst_788_, lean_object* v_handler_789_, lean_object* v_machine_790_, lean_object* v_head_791_, lean_object* v_config_792_, lean_object* v_connectionContext_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_788_, v_handler_789_, v_machine_790_, v_head_791_, v_config_792_, v_connectionContext_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_796_, lean_object* v_inst_797_, lean_object* v_handler_798_, lean_object* v_machine_799_, lean_object* v_head_800_, lean_object* v_config_801_, lean_object* v_connectionContext_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_796_, v_inst_797_, v_handler_798_, v_machine_799_, v_head_800_, v_config_801_, v_connectionContext_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_i_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_mk_empty_array_with_capacity(v___x_807_);
v___x_809_ = lean_array_push(v___x_808_, v_i_805_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_val_811_ = lean_ctor_get(v_x_806_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_806_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v_x_806_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v_x_806_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_array_push(v_val_811_, v_i_805_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_m_820_, lean_object* v_query_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_zero_825_; uint8_t v_isZero_826_; 
v_zero_825_ = lean_unsigned_to_nat(0u);
v_isZero_826_ = lean_nat_dec_eq(v_x_823_, v_zero_825_);
if (v_isZero_826_ == 1)
{
lean_dec(v_x_824_);
lean_dec(v_x_823_);
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v___x_827_; 
v___x_827_ = lean_box(2);
return v___x_827_;
}
else
{
lean_object* v_val_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_val_828_ = lean_ctor_get(v_x_822_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v_x_822_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_val_828_);
lean_dec(v_x_822_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_keyArray_836_; lean_object* v_valueArray_837_; lean_object* v___x_838_; uint8_t v_isSome_839_; 
v_keyArray_836_ = lean_ctor_get(v_m_820_, 1);
v_valueArray_837_ = lean_ctor_get(v_m_820_, 2);
v___x_838_ = lean_array_fget_borrowed(v_keyArray_836_, v_x_824_);
v_isSome_839_ = lean_noption_is_some(v___x_838_);
if (v_isSome_839_ == 0)
{
lean_dec(v_x_823_);
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_x_824_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_x_824_);
v_val_841_ = lean_ctor_get(v_x_822_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v_x_822_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_val_841_);
lean_dec(v_x_822_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_val_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_one_849_; lean_object* v_n_850_; lean_object* v___y_852_; 
v_one_849_ = lean_unsigned_to_nat(1u);
v_n_850_ = lean_nat_sub(v_x_823_, v_one_849_);
lean_dec(v_x_823_);
if (v_isSome_839_ == 0)
{
goto v___jp_858_;
}
else
{
lean_object* v___x_860_; uint8_t v_isSome_861_; 
v___x_860_ = lean_array_fget_borrowed(v_valueArray_837_, v_x_824_);
v_isSome_861_ = lean_noption_is_some(v___x_860_);
if (v_isSome_861_ == 0)
{
goto v___jp_858_;
}
else
{
lean_object* v_val_862_; uint8_t v___x_863_; 
lean_inc(v___x_838_);
v_val_862_ = lean_noption_get(v___x_838_);
v___x_863_ = lean_string_dec_eq(v_val_862_, v_query_821_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
lean_dec(v_val_862_);
v___x_864_ = lean_array_get_size(v_keyArray_836_);
v___x_865_ = lean_nat_add(v_x_824_, v_one_849_);
lean_dec(v_x_824_);
v___x_866_ = lean_nat_dec_lt(v___x_865_, v___x_864_);
if (v___x_866_ == 0)
{
lean_dec(v___x_865_);
v_x_823_ = v_n_850_;
v_x_824_ = v_zero_825_;
goto _start;
}
else
{
v_x_823_ = v_n_850_;
v_x_824_ = v___x_865_;
goto _start;
}
}
else
{
lean_object* v_val_869_; lean_object* v___x_870_; 
lean_dec(v_n_850_);
lean_dec(v_x_822_);
lean_inc(v___x_860_);
v_val_869_ = lean_noption_get(v___x_860_);
v___x_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_870_, 0, v_x_824_);
lean_ctor_set(v___x_870_, 1, v_val_862_);
lean_ctor_set(v___x_870_, 2, v_val_869_);
return v___x_870_;
}
}
}
v___jp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_array_get_size(v_keyArray_836_);
v___x_854_ = lean_nat_add(v_x_824_, v_one_849_);
lean_dec(v_x_824_);
v___x_855_ = lean_nat_dec_lt(v___x_854_, v___x_853_);
if (v___x_855_ == 0)
{
lean_dec(v___x_854_);
v_x_822_ = v___y_852_;
v_x_823_ = v_n_850_;
v_x_824_ = v_zero_825_;
goto _start;
}
else
{
v_x_822_ = v___y_852_;
v_x_823_ = v_n_850_;
v_x_824_ = v___x_854_;
goto _start;
}
}
v___jp_858_:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v___x_859_; 
lean_inc(v_x_824_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v_x_824_);
v___y_852_ = v___x_859_;
goto v___jp_851_;
}
else
{
v___y_852_ = v_x_822_;
goto v___jp_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_m_871_, lean_object* v_query_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_m_871_, v_query_872_, v_x_873_, v_x_874_, v_x_875_);
lean_dec_ref(v_query_872_);
lean_dec_ref(v_m_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(lean_object* v_m_877_, lean_object* v_query_878_){
_start:
{
lean_object* v_keyArray_879_; lean_object* v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v___x_883_; uint64_t v_fold_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_keyArray_879_ = lean_ctor_get(v_m_877_, 1);
v___x_880_ = lean_array_get_size(v_keyArray_879_);
v___x_881_ = lean_string_hash(v_query_878_);
v___x_882_ = 32ULL;
v___x_883_ = lean_uint64_shift_right(v___x_881_, v___x_882_);
v_fold_884_ = lean_uint64_xor(v___x_881_, v___x_883_);
v___x_885_ = 16ULL;
v___x_886_ = lean_uint64_shift_right(v_fold_884_, v___x_885_);
v___x_887_ = lean_uint64_xor(v_fold_884_, v___x_886_);
v___x_888_ = lean_uint64_to_usize(v___x_887_);
v___x_889_ = lean_usize_of_nat(v___x_880_);
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_sub(v___x_889_, v___x_890_);
v___x_892_ = lean_usize_land(v___x_888_, v___x_891_);
v___x_893_ = lean_usize_to_nat(v___x_892_);
v___x_894_ = lean_box(0);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_m_877_, v_query_878_, v___x_894_, v___x_880_, v___x_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg___boxed(lean_object* v_m_896_, lean_object* v_query_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v_m_896_, v_query_897_);
lean_dec_ref(v_query_897_);
lean_dec_ref(v_m_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg(lean_object* v_b_899_, lean_object* v_acc_900_, lean_object* v_i_901_){
_start:
{
lean_object* v___y_903_; lean_object* v_keyArray_911_; lean_object* v_valueArray_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_keyArray_911_ = lean_ctor_get(v_b_899_, 1);
v_valueArray_912_ = lean_ctor_get(v_b_899_, 2);
v___x_913_ = lean_array_get_size(v_keyArray_911_);
v___x_914_ = lean_nat_dec_lt(v_i_901_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec(v_i_901_);
return v_acc_900_;
}
else
{
lean_object* v___x_915_; uint8_t v_isSome_916_; 
v___x_915_ = lean_array_fget_borrowed(v_keyArray_911_, v_i_901_);
v_isSome_916_ = lean_noption_is_some(v___x_915_);
if (v_isSome_916_ == 0)
{
goto v___jp_907_;
}
else
{
lean_object* v___x_917_; uint8_t v_isSome_918_; 
v___x_917_ = lean_array_fget_borrowed(v_valueArray_912_, v_i_901_);
v_isSome_918_ = lean_noption_is_some(v___x_917_);
if (v_isSome_918_ == 0)
{
goto v___jp_907_;
}
else
{
lean_object* v_val_919_; lean_object* v_val_920_; lean_object* v_i_922_; lean_object* v___x_927_; 
lean_inc(v___x_915_);
v_val_919_ = lean_noption_get(v___x_915_);
lean_inc(v___x_917_);
v_val_920_ = lean_noption_get(v___x_917_);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v_acc_900_, v_val_919_);
switch(lean_obj_tag(v___x_927_))
{
case 0:
{
lean_object* v_index_928_; lean_object* v_size_929_; lean_object* v___x_930_; 
v_index_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_index_928_);
lean_dec_ref_known(v___x_927_, 3);
v_size_929_ = lean_ctor_get(v_acc_900_, 0);
lean_inc(v_size_929_);
v___x_930_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_900_, v_size_929_, v_index_928_, v_val_919_, v_val_920_);
lean_dec(v_index_928_);
v___y_903_ = v___x_930_;
goto v___jp_902_;
}
case 1:
{
lean_object* v_index_931_; 
v_index_931_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_index_931_);
lean_dec_ref_known(v___x_927_, 1);
v_i_922_ = v_index_931_;
goto v___jp_921_;
}
default: 
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_900_, v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_index_934_; 
v_index_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_index_934_);
lean_dec_ref_known(v___x_933_, 1);
v_i_922_ = v_index_934_;
goto v___jp_921_;
}
else
{
lean_dec(v_val_920_);
lean_dec(v_val_919_);
v___y_903_ = v_acc_900_;
goto v___jp_902_;
}
}
}
v___jp_921_:
{
lean_object* v_size_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_size_923_ = lean_ctor_get(v_acc_900_, 0);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_add(v_size_923_, v___x_924_);
v___x_926_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_900_, v___x_925_, v_i_922_, v_val_919_, v_val_920_);
lean_dec(v_i_922_);
v___y_903_ = v___x_926_;
goto v___jp_902_;
}
}
}
}
v___jp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_add(v_i_901_, v___x_904_);
lean_dec(v_i_901_);
v_acc_900_ = v___y_903_;
v_i_901_ = v___x_905_;
goto _start;
}
v___jp_907_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_i_901_, v___x_908_);
lean_dec(v_i_901_);
v_i_901_ = v___x_909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_935_, lean_object* v_acc_936_, lean_object* v_i_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg(v_b_935_, v_acc_936_, v_i_937_);
lean_dec_ref(v_b_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg(lean_object* v_init_939_, lean_object* v_b_940_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg(v_b_940_, v_init_939_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg___boxed(lean_object* v_init_943_, lean_object* v_b_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg(v_init_943_, v_b_944_);
lean_dec_ref(v_b_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object* v_m_946_){
_start:
{
lean_object* v_keyArray_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_cellCount_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_target_954_; lean_object* v___x_955_; 
v_keyArray_947_ = lean_ctor_get(v_m_946_, 1);
v___x_948_ = lean_array_get_size(v_keyArray_947_);
v___x_949_ = lean_unsigned_to_nat(2u);
v_cellCount_950_ = lean_nat_mul(v___x_948_, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_950_);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_950_);
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_950_);
v_target_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_954_, 0, v___x_951_);
lean_ctor_set(v_target_954_, 1, v___x_952_);
lean_ctor_set(v_target_954_, 2, v___x_953_);
v___x_955_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg(v_target_954_, v_m_946_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object* v_m_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_956_);
lean_dec_ref(v_m_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_entries_958_, lean_object* v_status_959_, uint8_t v_version_960_, lean_object* v_indexes_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_indexes_961_);
lean_dec(v_status_959_);
lean_dec_ref(v_entries_958_);
v_a_964_ = lean_ctor_get(v_x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v_x_962_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v_x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1065_; 
v_a_973_ = lean_ctor_get(v_x_962_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_x_962_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_975_ = v_x_962_;
v_isShared_976_ = v_isSharedCheck_1065_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v_x_962_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1065_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_i_980_; lean_object* v___x_981_; lean_object* v_entries_982_; lean_object* v___y_984_; lean_object* v___x_991_; 
v___x_977_ = l_Std_Http_Header_Name_date;
v___x_978_ = l_Std_Time_DateTime_toRFC822String(v_a_973_);
v___x_979_ = l_Std_Http_Header_Value_ofString_x21(v___x_978_);
v_i_980_ = lean_array_get_size(v_entries_958_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_977_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
v_entries_982_ = lean_array_push(v_entries_958_, v___x_981_);
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v_indexes_961_, v___x_977_);
switch(lean_obj_tag(v___x_991_))
{
case 0:
{
lean_object* v_index_992_; lean_object* v_value_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_val_996_; lean_object* v_size_997_; lean_object* v___x_998_; 
v_index_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_index_992_);
v_value_993_ = lean_ctor_get(v___x_991_, 2);
lean_inc(v_value_993_);
lean_dec_ref_known(v___x_991_, 3);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_value_993_);
v___x_995_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_i_980_, v___x_994_);
v_val_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_val_996_);
lean_dec(v___x_995_);
v_size_997_ = lean_ctor_get(v_indexes_961_, 0);
lean_inc(v_size_997_);
v___x_998_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_961_, v_size_997_, v_index_992_, v___x_977_, v_val_996_);
lean_dec(v_index_992_);
v___y_984_ = v___x_998_;
goto v___jp_983_;
}
case 1:
{
lean_object* v_index_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_val_1002_; lean_object* v___y_1004_; lean_object* v_i_1005_; lean_object* v_size_1020_; lean_object* v_keyArray_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_index_999_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_index_999_);
lean_dec_ref_known(v___x_991_, 1);
v___x_1000_ = lean_box(0);
v___x_1001_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_i_980_, v___x_1000_);
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec(v___x_1001_);
v_size_1020_ = lean_ctor_get(v_indexes_961_, 0);
v_keyArray_1021_ = lean_ctor_get(v_indexes_961_, 1);
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_size_1020_, v___x_1022_);
v___x_1024_ = lean_array_get_size(v_keyArray_1021_);
v___x_1025_ = lean_nat_dec_lt(v___x_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v___x_1023_);
lean_dec(v_index_999_);
goto v___jp_1010_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1026_ = lean_unsigned_to_nat(4u);
v___x_1027_ = lean_nat_mul(v___x_1023_, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(3u);
v___x_1029_ = lean_nat_mul(v___x_1024_, v___x_1028_);
v___x_1030_ = lean_nat_dec_le(v___x_1027_, v___x_1029_);
lean_dec(v___x_1029_);
lean_dec(v___x_1027_);
if (v___x_1030_ == 0)
{
lean_dec(v___x_1023_);
lean_dec(v_index_999_);
goto v___jp_1010_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_961_, v___x_1023_, v_index_999_, v___x_977_, v_val_1002_);
lean_dec(v_index_999_);
v___y_984_ = v___x_1031_;
goto v___jp_983_;
}
}
v___jp_1003_:
{
lean_object* v_size_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_size_1006_ = lean_ctor_get(v___y_1004_, 0);
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_nat_add(v_size_1006_, v___x_1007_);
v___x_1009_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1004_, v___x_1008_, v_i_1005_, v___x_977_, v_val_1002_);
lean_dec(v_i_1005_);
v___y_984_ = v___x_1009_;
goto v___jp_983_;
}
v___jp_1010_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_961_);
lean_dec_ref(v_indexes_961_);
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v___x_1011_, v___x_977_);
switch(lean_obj_tag(v___x_1012_))
{
case 0:
{
lean_object* v_index_1013_; lean_object* v_size_1014_; lean_object* v___x_1015_; 
v_index_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_index_1013_);
lean_dec_ref_known(v___x_1012_, 3);
v_size_1014_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_size_1014_);
v___x_1015_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1011_, v_size_1014_, v_index_1013_, v___x_977_, v_val_1002_);
lean_dec(v_index_1013_);
v___y_984_ = v___x_1015_;
goto v___jp_983_;
}
case 1:
{
lean_object* v_index_1016_; 
v_index_1016_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_index_1016_);
lean_dec_ref_known(v___x_1012_, 1);
v___y_1004_ = v___x_1011_;
v_i_1005_ = v_index_1016_;
goto v___jp_1003_;
}
default: 
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1011_, v___x_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_index_1019_; 
v_index_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_index_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___y_1004_ = v___x_1011_;
v_i_1005_ = v_index_1019_;
goto v___jp_1003_;
}
else
{
lean_dec(v_val_1002_);
v___y_984_ = v___x_1011_;
goto v___jp_983_;
}
}
}
}
}
default: 
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_val_1034_; lean_object* v___y_1036_; lean_object* v_i_1037_; lean_object* v___y_1043_; lean_object* v_size_1052_; lean_object* v_keyArray_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_i_980_, v___x_1032_);
v_val_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_val_1034_);
lean_dec(v___x_1033_);
v_size_1052_ = lean_ctor_get(v_indexes_961_, 0);
v_keyArray_1053_ = lean_ctor_get(v_indexes_961_, 1);
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_add(v_size_1052_, v___x_1054_);
v___x_1056_ = lean_array_get_size(v_keyArray_1053_);
v___x_1057_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec(v___x_1055_);
v___x_1058_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_961_);
lean_dec_ref(v_indexes_961_);
v___y_1043_ = v___x_1058_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1059_ = lean_unsigned_to_nat(4u);
v___x_1060_ = lean_nat_mul(v___x_1055_, v___x_1059_);
lean_dec(v___x_1055_);
v___x_1061_ = lean_unsigned_to_nat(3u);
v___x_1062_ = lean_nat_mul(v___x_1056_, v___x_1061_);
v___x_1063_ = lean_nat_dec_le(v___x_1060_, v___x_1062_);
lean_dec(v___x_1062_);
lean_dec(v___x_1060_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_961_);
lean_dec_ref(v_indexes_961_);
v___y_1043_ = v___x_1064_;
goto v___jp_1042_;
}
else
{
v___y_1043_ = v_indexes_961_;
goto v___jp_1042_;
}
}
v___jp_1035_:
{
lean_object* v_size_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_size_1038_ = lean_ctor_get(v___y_1036_, 0);
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_size_1038_, v___x_1039_);
v___x_1041_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1036_, v___x_1040_, v_i_1037_, v___x_977_, v_val_1034_);
lean_dec(v_i_1037_);
v___y_984_ = v___x_1041_;
goto v___jp_983_;
}
v___jp_1042_:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v___y_1043_, v___x_977_);
switch(lean_obj_tag(v___x_1044_))
{
case 0:
{
lean_object* v_index_1045_; lean_object* v_size_1046_; lean_object* v___x_1047_; 
v_index_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_index_1045_);
lean_dec_ref_known(v___x_1044_, 3);
v_size_1046_ = lean_ctor_get(v___y_1043_, 0);
lean_inc(v_size_1046_);
v___x_1047_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1043_, v_size_1046_, v_index_1045_, v___x_977_, v_val_1034_);
lean_dec(v_index_1045_);
v___y_984_ = v___x_1047_;
goto v___jp_983_;
}
case 1:
{
lean_object* v_index_1048_; 
v_index_1048_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_index_1048_);
lean_dec_ref_known(v___x_1044_, 1);
v___y_1036_ = v___y_1043_;
v_i_1037_ = v_index_1048_;
goto v___jp_1035_;
}
default: 
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1043_, v___x_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_index_1051_; 
v_index_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_index_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___y_1036_ = v___y_1043_;
v_i_1037_ = v_index_1051_;
goto v___jp_1035_;
}
else
{
lean_dec(v_val_1034_);
v___y_984_ = v___y_1043_;
goto v___jp_983_;
}
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_entries_982_);
lean_ctor_set(v___x_985_, 1, v___y_984_);
v___x_986_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_986_, 0, v_status_959_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*2, v_version_960_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_986_);
v___x_988_ = v___x_975_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_990_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_entries_1066_, lean_object* v_status_1067_, lean_object* v_version_1068_, lean_object* v_indexes_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v_version_boxed_1072_; lean_object* v_res_1073_; 
v_version_boxed_1072_ = lean_unbox(v_version_1068_);
v_res_1073_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_entries_1066_, v_status_1067_, v_version_boxed_1072_, v_indexes_1069_, v_x_1070_);
return v_res_1073_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_nat_to_int(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2(lean_object* v_tz_1076_, lean_object* v_a_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v_offset_1079_; lean_object* v_second_1080_; lean_object* v_nano_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_offset_1079_ = lean_ctor_get(v_tz_1076_, 0);
v_second_1080_ = lean_ctor_get(v_a_1077_, 0);
v_nano_1081_ = lean_ctor_get(v_a_1077_, 1);
v___x_1082_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___closed__0);
v___x_1083_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_1084_ = lean_int_mul(v_second_1080_, v___x_1083_);
v___x_1085_ = lean_int_add(v___x_1084_, v_nano_1081_);
lean_dec(v___x_1084_);
v___x_1086_ = lean_int_mul(v_offset_1079_, v___x_1083_);
v___x_1087_ = lean_int_add(v___x_1086_, v___x_1082_);
lean_dec(v___x_1086_);
v___x_1088_ = lean_int_add(v___x_1085_, v___x_1087_);
lean_dec(v___x_1087_);
lean_dec(v___x_1085_);
v___x_1089_ = l_Std_Time_Duration_ofNanoseconds(v___x_1088_);
lean_dec(v___x_1088_);
v___x_1090_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___boxed(lean_object* v_tz_1091_, lean_object* v_a_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2(v_tz_1091_, v_a_1092_, v_x_1093_);
lean_dec_ref(v_a_1092_);
lean_dec_ref(v_tz_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg(lean_object* v_m_1095_, lean_object* v_query_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v_m_1095_, v_query_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_index_1098_; lean_object* v_key_1099_; lean_object* v_value_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_index_1098_ = lean_ctor_get(v___x_1097_, 0);
v_key_1099_ = lean_ctor_get(v___x_1097_, 1);
v_value_1100_ = lean_ctor_get(v___x_1097_, 2);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1097_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_value_1100_);
lean_inc(v_key_1099_);
lean_inc(v_index_1098_);
lean_dec(v___x_1097_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_index_1098_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_key_1099_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_value_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v___x_1108_; 
lean_dec(v___x_1097_);
v___x_1108_ = lean_box(1);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg___boxed(lean_object* v_m_1109_, lean_object* v_query_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg(v_m_1109_, v_query_1110_);
lean_dec_ref(v_query_1110_);
lean_dec_ref(v_m_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg(v_m_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
uint8_t v___x_1115_; 
lean_dec_ref_known(v___x_1114_, 3);
v___x_1115_ = 1;
return v___x_1115_;
}
else
{
uint8_t v___x_1116_; 
v___x_1116_ = 0;
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg___boxed(lean_object* v_m_1117_, lean_object* v_a_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_m_1117_, v_a_1118_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_m_1117_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1122_, lean_object* v_head_1123_){
_start:
{
uint8_t v_generateDate_1128_; 
v_generateDate_1128_ = lean_ctor_get_uint8(v_config_1122_, sizeof(void*)*24 + 1);
if (v_generateDate_1128_ == 0)
{
goto v___jp_1125_;
}
else
{
lean_object* v_headers_1129_; lean_object* v_status_1130_; uint8_t v_version_1131_; lean_object* v_entries_1132_; lean_object* v_indexes_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_headers_1129_ = lean_ctor_get(v_head_1123_, 1);
v_status_1130_ = lean_ctor_get(v_head_1123_, 0);
v_version_1131_ = lean_ctor_get_uint8(v_head_1123_, sizeof(void*)*2);
v_entries_1132_ = lean_ctor_get(v_headers_1129_, 0);
v_indexes_1133_ = lean_ctor_get(v_headers_1129_, 1);
v___x_1134_ = l_Std_Http_Header_Name_date;
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_indexes_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___f_1137_; lean_object* v_val_1139_; lean_object* v_a_1144_; lean_object* v___x_1146_; 
lean_inc_ref(v_indexes_1133_);
lean_inc_ref(v_entries_1132_);
lean_inc(v_status_1130_);
lean_dec_ref(v_head_1123_);
v___x_1136_ = lean_box(v_version_1131_);
v___f_1137_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1137_, 0, v_entries_1132_);
lean_closure_set(v___f_1137_, 1, v_status_1130_);
lean_closure_set(v___f_1137_, 2, v___x_1136_);
lean_closure_set(v___f_1137_, 3, v_indexes_1133_);
v___x_1146_ = lean_get_current_time();
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1149_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1148_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1161_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_tz_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_inc(v_a_1150_);
v_tz_1154_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1150_, v_a_1147_);
lean_inc(v_a_1147_);
lean_inc_ref(v_tz_1154_);
v___f_1155_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1155_, 0, v_tz_1154_);
lean_closure_set(v___f_1155_, 1, v_a_1147_);
v___x_1156_ = lean_mk_thunk(v___f_1155_);
v___x_1157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_a_1147_);
lean_ctor_set(v___x_1157_, 2, v_a_1150_);
lean_ctor_set(v___x_1157_, 3, v_tz_1154_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
lean_ctor_set(v___x_1152_, 0, v___x_1157_);
v___x_1159_ = v___x_1152_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
v_val_1139_ = v___x_1159_;
goto v___jp_1138_;
}
}
}
else
{
lean_object* v_a_1162_; 
lean_dec(v_a_1147_);
v_a_1162_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1149_, 1);
v_a_1144_ = v_a_1162_;
goto v___jp_1143_;
}
}
else
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1146_, 1);
v_a_1144_ = v_a_1163_;
goto v___jp_1143_;
}
v___jp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_val_1139_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1141_, v___x_1135_, v___x_1140_, v___f_1137_);
return v___x_1142_;
}
v___jp_1143_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1144_);
v_val_1139_ = v___x_1145_;
goto v___jp_1138_;
}
}
else
{
goto v___jp_1125_;
}
}
v___jp_1125_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_head_1123_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1164_, lean_object* v_head_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1164_, v_head_1165_);
lean_dec_ref(v_config_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_00_u03b2_1168_, lean_object* v_m_1169_, lean_object* v_query_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___redArg(v_m_1169_, v_query_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0___boxed(lean_object* v_00_u03b2_1172_, lean_object* v_m_1173_, lean_object* v_query_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_00_u03b2_1172_, v_m_1173_, v_query_1174_);
lean_dec_ref(v_query_1174_);
lean_dec_ref(v_m_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_00_u03b2_1176_, lean_object* v_m_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object* v_00_u03b2_1179_, lean_object* v_m_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(v_00_u03b2_1179_, v_m_1180_);
lean_dec_ref(v_m_1180_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__4(lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_nat_to_int(v_a_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_nat_to_int(v_a_1184_);
v___x_1186_ = l_Rat_ofInt(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_00_u03b2_1187_, lean_object* v_m_1188_, lean_object* v_a_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_m_1188_, v_a_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object* v_00_u03b2_1191_, lean_object* v_m_1192_, lean_object* v_a_1193_){
_start:
{
uint8_t v_res_1194_; lean_object* v_r_1195_; 
v_res_1194_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_00_u03b2_1191_, v_m_1192_, v_a_1193_);
lean_dec_ref(v_a_1193_);
lean_dec_ref(v_m_1192_);
v_r_1195_ = lean_box(v_res_1194_);
return v_r_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1196_, lean_object* v_m_1197_, lean_object* v_query_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_m_1197_, v_query_1198_, v_x_1199_, v_x_1200_, v_x_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1204_, lean_object* v_m_1205_, lean_object* v_query_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1204_, v_m_1205_, v_query_1206_, v_x_1207_, v_x_1208_, v_x_1209_, v_x_1210_);
lean_dec_ref(v_query_1206_);
lean_dec_ref(v_m_1205_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2(lean_object* v_00_u03b2_1212_, lean_object* v_init_1213_, lean_object* v_b_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___redArg(v_init_1213_, v_b_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1216_, lean_object* v_init_1217_, lean_object* v_b_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2(v_00_u03b2_1216_, v_init_1217_, v_b_1218_);
lean_dec_ref(v_b_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6(lean_object* v_00_u03b2_1220_, lean_object* v_m_1221_, lean_object* v_query_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___redArg(v_m_1221_, v_query_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1224_, lean_object* v_m_1225_, lean_object* v_query_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__6(v_00_u03b2_1224_, v_m_1225_, v_query_1226_);
lean_dec_ref(v_query_1226_);
lean_dec_ref(v_m_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1228_, lean_object* v_b_1229_, lean_object* v_acc_1230_, lean_object* v_i_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___redArg(v_b_1229_, v_acc_1230_, v_i_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1233_, lean_object* v_b_1234_, lean_object* v_acc_1235_, lean_object* v_i_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__2_spec__3(v_00_u03b2_1233_, v_b_1234_, v_acc_1235_, v_i_1236_);
lean_dec_ref(v_b_1234_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1238_, lean_object* v_____r_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1238_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1245_, lean_object* v_____r_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1245_, v_____r_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v___f_1249_);
v_a_1252_ = lean_ctor_get(v_x_1250_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1250_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1254_ = v_x_1250_;
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v_x_1250_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_ctor_get(v_x_1250_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v_x_1250_, 1);
v___x_1262_ = lean_apply_2(v___f_1249_, v_a_1261_, lean_box(0));
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1263_, v_x_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1267_, lean_object* v_body_1268_, lean_object* v___f_1269_, lean_object* v___f_1270_, lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___f_1270_);
lean_dec_ref(v___f_1269_);
lean_dec(v_body_1268_);
lean_dec_ref(v_close_1267_);
v_a_1273_ = lean_ctor_get(v_x_1271_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1271_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v_x_1271_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v_x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1282_; uint8_t v___x_1283_; 
v_a_1282_ = lean_ctor_get(v_x_1271_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v_x_1271_, 1);
v___x_1283_ = lean_unbox(v_a_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref(v___f_1270_);
v___x_1284_ = lean_apply_2(v_close_1267_, v_body_1268_, lean_box(0));
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
v___x_1287_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1285_, v___x_1286_, v___x_1284_, v___f_1269_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_a_1282_);
lean_dec_ref(v___f_1269_);
lean_dec(v_body_1268_);
lean_dec_ref(v_close_1267_);
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_apply_2(v___f_1270_, v___x_1288_, lean_box(0));
return v___x_1289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1290_, lean_object* v_body_1291_, lean_object* v___f_1292_, lean_object* v___f_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1290_, v_body_1291_, v___f_1292_, v___f_1293_, v_x_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1297_, uint8_t v___x_1298_, lean_object* v___f_1299_, lean_object* v___f_1300_, lean_object* v_x1_1301_, lean_object* v_x2_1302_){
_start:
{
lean_object* v_fst_1303_; uint8_t v___x_1304_; 
v_fst_1303_ = lean_ctor_get(v_x2_1302_, 0);
lean_inc(v_fst_1303_);
v___x_1304_ = lean_string_dec_eq(v___x_1297_, v_fst_1303_);
if (v___x_1304_ == 0)
{
if (v___x_1298_ == 0)
{
lean_dec(v_fst_1303_);
lean_dec_ref(v_x2_1302_);
lean_dec_ref(v___f_1300_);
lean_dec_ref(v___f_1299_);
return v_x1_1301_;
}
else
{
lean_object* v_entries_1305_; lean_object* v_indexes_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1400_; 
v_entries_1305_ = lean_ctor_get(v_x1_1301_, 0);
v_indexes_1306_ = lean_ctor_get(v_x1_1301_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x1_1301_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1308_ = v_x1_1301_;
v_isShared_1309_ = v_isSharedCheck_1400_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_indexes_1306_);
lean_inc(v_entries_1305_);
lean_dec(v_x1_1301_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1400_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_i_1310_; lean_object* v_entries_1311_; lean_object* v___x_1312_; 
v_i_1310_ = lean_array_get_size(v_entries_1305_);
v_entries_1311_ = lean_array_push(v_entries_1305_, v_x2_1302_);
lean_inc(v_fst_1303_);
lean_inc_ref(v___f_1300_);
lean_inc_ref(v___f_1299_);
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1299_, v___f_1300_, v_indexes_1306_, v_fst_1303_);
switch(lean_obj_tag(v___x_1312_))
{
case 0:
{
lean_object* v_index_1313_; lean_object* v_value_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_val_1317_; lean_object* v_size_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
lean_dec_ref(v___f_1300_);
lean_dec_ref(v___f_1299_);
v_index_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_index_1313_);
v_value_1314_ = lean_ctor_get(v___x_1312_, 2);
lean_inc(v_value_1314_);
lean_dec_ref_known(v___x_1312_, 3);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_value_1314_);
v___x_1316_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_i_1310_, v___x_1315_);
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec(v___x_1316_);
v_size_1318_ = lean_ctor_get(v_indexes_1306_, 0);
lean_inc(v_size_1318_);
v___x_1319_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1306_, v_size_1318_, v_index_1313_, v_fst_1303_, v_val_1317_);
lean_dec(v_index_1313_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1319_);
lean_ctor_set(v___x_1308_, 0, v_entries_1311_);
v___x_1321_ = v___x_1308_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_entries_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
case 1:
{
lean_object* v_index_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_val_1326_; lean_object* v___y_1328_; lean_object* v_i_1329_; lean_object* v_size_1349_; lean_object* v_keyArray_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_index_1323_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_index_1323_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1324_ = lean_box(0);
v___x_1325_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_i_1310_, v___x_1324_);
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1326_);
lean_dec(v___x_1325_);
v_size_1349_ = lean_ctor_get(v_indexes_1306_, 0);
v_keyArray_1350_ = lean_ctor_get(v_indexes_1306_, 1);
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_add(v_size_1349_, v___x_1351_);
v___x_1353_ = lean_array_get_size(v_keyArray_1350_);
v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec(v___x_1352_);
lean_dec(v_index_1323_);
goto v___jp_1337_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1355_ = lean_unsigned_to_nat(4u);
v___x_1356_ = lean_nat_mul(v___x_1352_, v___x_1355_);
v___x_1357_ = lean_unsigned_to_nat(3u);
v___x_1358_ = lean_nat_mul(v___x_1353_, v___x_1357_);
v___x_1359_ = lean_nat_dec_le(v___x_1356_, v___x_1358_);
lean_dec(v___x_1358_);
lean_dec(v___x_1356_);
if (v___x_1359_ == 0)
{
lean_dec(v___x_1352_);
lean_dec(v_index_1323_);
goto v___jp_1337_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1308_);
lean_dec_ref(v___f_1300_);
lean_dec_ref(v___f_1299_);
v___x_1360_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1306_, v___x_1352_, v_index_1323_, v_fst_1303_, v_val_1326_);
lean_dec(v_index_1323_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_entries_1311_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
return v___x_1361_;
}
}
v___jp_1327_:
{
lean_object* v_size_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v_size_1330_ = lean_ctor_get(v___y_1328_, 0);
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v_size_1330_, v___x_1331_);
v___x_1333_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1328_, v___x_1332_, v_i_1329_, v_fst_1303_, v_val_1326_);
lean_dec(v_i_1329_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1333_);
lean_ctor_set(v___x_1308_, 0, v_entries_1311_);
v___x_1335_ = v___x_1308_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_entries_1311_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
v___jp_1337_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_inc_ref(v___f_1300_);
lean_inc_ref(v___f_1299_);
v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1299_, v___f_1300_, v_indexes_1306_);
lean_inc(v_fst_1303_);
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1299_, v___f_1300_, v___x_1338_, v_fst_1303_);
switch(lean_obj_tag(v___x_1339_))
{
case 0:
{
lean_object* v_index_1340_; lean_object* v_size_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1308_);
v_index_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_index_1340_);
lean_dec_ref_known(v___x_1339_, 3);
v_size_1341_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_size_1341_);
v___x_1342_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1338_, v_size_1341_, v_index_1340_, v_fst_1303_, v_val_1326_);
lean_dec(v_index_1340_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_entries_1311_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
return v___x_1343_;
}
case 1:
{
lean_object* v_index_1344_; 
v_index_1344_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_index_1344_);
lean_dec_ref_known(v___x_1339_, 1);
v___y_1328_ = v___x_1338_;
v_i_1329_ = v_index_1344_;
goto v___jp_1327_;
}
default: 
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1338_, v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_index_1347_; 
v_index_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_index_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___y_1328_ = v___x_1338_;
v_i_1329_ = v_index_1347_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1348_; 
lean_dec(v_val_1326_);
lean_del_object(v___x_1308_);
lean_dec(v_fst_1303_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_entries_1311_);
lean_ctor_set(v___x_1348_, 1, v___x_1338_);
return v___x_1348_;
}
}
}
}
}
default: 
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_val_1364_; lean_object* v___y_1366_; lean_object* v_i_1367_; lean_object* v___y_1376_; lean_object* v_size_1387_; lean_object* v_keyArray_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_i_1310_, v___x_1362_);
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec(v___x_1363_);
v_size_1387_ = lean_ctor_get(v_indexes_1306_, 0);
v_keyArray_1388_ = lean_ctor_get(v_indexes_1306_, 1);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v_size_1387_, v___x_1389_);
v___x_1391_ = lean_array_get_size(v_keyArray_1388_);
v___x_1392_ = lean_nat_dec_lt(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_dec(v___x_1390_);
lean_inc_ref(v___f_1300_);
lean_inc_ref(v___f_1299_);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1299_, v___f_1300_, v_indexes_1306_);
v___y_1376_ = v___x_1393_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1394_ = lean_unsigned_to_nat(4u);
v___x_1395_ = lean_nat_mul(v___x_1390_, v___x_1394_);
lean_dec(v___x_1390_);
v___x_1396_ = lean_unsigned_to_nat(3u);
v___x_1397_ = lean_nat_mul(v___x_1391_, v___x_1396_);
v___x_1398_ = lean_nat_dec_le(v___x_1395_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v___x_1395_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_inc_ref(v___f_1300_);
lean_inc_ref(v___f_1299_);
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1299_, v___f_1300_, v_indexes_1306_);
v___y_1376_ = v___x_1399_;
goto v___jp_1375_;
}
else
{
v___y_1376_ = v_indexes_1306_;
goto v___jp_1375_;
}
}
v___jp_1365_:
{
lean_object* v_size_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_size_1368_ = lean_ctor_get(v___y_1366_, 0);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_size_1368_, v___x_1369_);
v___x_1371_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1366_, v___x_1370_, v_i_1367_, v_fst_1303_, v_val_1364_);
lean_dec(v_i_1367_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1371_);
lean_ctor_set(v___x_1308_, 0, v_entries_1311_);
v___x_1373_ = v___x_1308_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_entries_1311_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
v___jp_1375_:
{
lean_object* v___x_1377_; 
lean_inc(v_fst_1303_);
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1299_, v___f_1300_, v___y_1376_, v_fst_1303_);
switch(lean_obj_tag(v___x_1377_))
{
case 0:
{
lean_object* v_index_1378_; lean_object* v_size_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_del_object(v___x_1308_);
v_index_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_index_1378_);
lean_dec_ref_known(v___x_1377_, 3);
v_size_1379_ = lean_ctor_get(v___y_1376_, 0);
lean_inc(v_size_1379_);
v___x_1380_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1376_, v_size_1379_, v_index_1378_, v_fst_1303_, v_val_1364_);
lean_dec(v_index_1378_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_entries_1311_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
return v___x_1381_;
}
case 1:
{
lean_object* v_index_1382_; 
v_index_1382_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_index_1382_);
lean_dec_ref_known(v___x_1377_, 1);
v___y_1366_ = v___y_1376_;
v_i_1367_ = v_index_1382_;
goto v___jp_1365_;
}
default: 
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1376_, v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_index_1385_; 
v_index_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_index_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___y_1366_ = v___y_1376_;
v_i_1367_ = v_index_1385_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1386_; 
lean_dec(v_val_1364_);
lean_del_object(v___x_1308_);
lean_dec(v_fst_1303_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_entries_1311_);
lean_ctor_set(v___x_1386_, 1, v___y_1376_);
return v___x_1386_;
}
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
lean_dec(v_fst_1303_);
lean_dec_ref(v_x2_1302_);
lean_dec_ref(v___f_1300_);
lean_dec_ref(v___f_1299_);
return v_x1_1301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1401_, lean_object* v___x_1402_, lean_object* v___f_1403_, lean_object* v___f_1404_, lean_object* v_x1_1405_, lean_object* v_x2_1406_){
_start:
{
uint8_t v___x_3597__boxed_1407_; lean_object* v_res_1408_; 
v___x_3597__boxed_1407_ = lean_unbox(v___x_1402_);
v_res_1408_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1401_, v___x_3597__boxed_1407_, v___f_1403_, v___f_1404_, v_x1_1405_, v_x2_1406_);
lean_dec_ref(v___x_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1430_, lean_object* v_body_1431_, lean_object* v_isClosed_1432_, lean_object* v_close_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v___y_1437_; uint8_t v_omitBody_1438_; lean_object* v___y_1451_; uint8_t v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1488_; 
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_close_1433_);
lean_dec_ref(v_isClosed_1432_);
lean_dec(v_body_1431_);
lean_dec_ref(v___y_1430_);
v_a_1491_ = lean_ctor_get(v_x_1434_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1493_ = v_x_1434_;
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v_x_1434_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
}
else
{
lean_object* v_writer_1500_; lean_object* v_a_1501_; lean_object* v_reader_1502_; lean_object* v_config_1503_; lean_object* v_events_1504_; lean_object* v_error_1505_; lean_object* v_instant_1506_; uint8_t v_keepAlive_1507_; uint8_t v_forcedFlush_1508_; uint8_t v_pullBodyStalled_1509_; lean_object* v_userData_1510_; lean_object* v_outputData_1511_; lean_object* v_state_1512_; lean_object* v_knownSize_1513_; lean_object* v_messageHead_1514_; uint8_t v_sentMessage_1515_; uint8_t v_userClosedBody_1516_; uint8_t v_omitBody_1517_; lean_object* v_userDataBytes_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1634_; 
v_writer_1500_ = lean_ctor_get(v___y_1430_, 1);
lean_inc_ref(v_writer_1500_);
v_a_1501_ = lean_ctor_get(v_x_1434_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v_x_1434_, 1);
v_reader_1502_ = lean_ctor_get(v___y_1430_, 0);
v_config_1503_ = lean_ctor_get(v___y_1430_, 2);
v_events_1504_ = lean_ctor_get(v___y_1430_, 3);
v_error_1505_ = lean_ctor_get(v___y_1430_, 4);
v_instant_1506_ = lean_ctor_get(v___y_1430_, 5);
v_keepAlive_1507_ = lean_ctor_get_uint8(v___y_1430_, sizeof(void*)*6);
v_forcedFlush_1508_ = lean_ctor_get_uint8(v___y_1430_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1509_ = lean_ctor_get_uint8(v___y_1430_, sizeof(void*)*6 + 2);
v_userData_1510_ = lean_ctor_get(v_writer_1500_, 0);
v_outputData_1511_ = lean_ctor_get(v_writer_1500_, 1);
v_state_1512_ = lean_ctor_get(v_writer_1500_, 2);
v_knownSize_1513_ = lean_ctor_get(v_writer_1500_, 3);
v_messageHead_1514_ = lean_ctor_get(v_writer_1500_, 4);
v_sentMessage_1515_ = lean_ctor_get_uint8(v_writer_1500_, sizeof(void*)*6);
v_userClosedBody_1516_ = lean_ctor_get_uint8(v_writer_1500_, sizeof(void*)*6 + 1);
v_omitBody_1517_ = lean_ctor_get_uint8(v_writer_1500_, sizeof(void*)*6 + 2);
v_userDataBytes_1518_ = lean_ctor_get(v_writer_1500_, 5);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_writer_1500_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1520_ = v_writer_1500_;
v_isShared_1521_ = v_isSharedCheck_1634_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_userDataBytes_1518_);
lean_inc(v_messageHead_1514_);
lean_inc(v_knownSize_1513_);
lean_inc(v_state_1512_);
lean_inc(v_outputData_1511_);
lean_inc(v_userData_1510_);
lean_dec(v_writer_1500_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1634_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; uint8_t v___y_1552_; uint8_t v___y_1553_; uint8_t v___y_1554_; lean_object* v___y_1555_; uint8_t v___y_1563_; lean_object* v___y_1564_; uint8_t v___y_1565_; uint8_t v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; uint8_t v___x_1583_; uint8_t v___y_1585_; uint8_t v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; uint8_t v___y_1589_; uint8_t v___y_1590_; uint8_t v___y_1597_; uint8_t v___y_1598_; uint8_t v___y_1599_; uint8_t v___y_1612_; uint8_t v___y_1613_; uint8_t v___y_1616_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1583_ = 0;
v___x_1632_ = lean_box(1);
v___x_1633_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1512_, v___x_1632_);
if (v___x_1633_ == 0)
{
v___y_1616_ = v___x_1633_;
goto v___jp_1615_;
}
else
{
if (v_sentMessage_1515_ == 0)
{
v___y_1616_ = v___x_1633_;
goto v___jp_1615_;
}
else
{
lean_del_object(v___x_1520_);
lean_dec(v_userDataBytes_1518_);
lean_dec(v_messageHead_1514_);
lean_dec(v_knownSize_1513_);
lean_dec(v_state_1512_);
lean_dec_ref(v_outputData_1511_);
lean_dec_ref(v_userData_1510_);
lean_dec(v_a_1501_);
v___y_1437_ = v___y_1430_;
v_omitBody_1438_ = v_omitBody_1517_;
goto v___jp_1436_;
}
}
v___jp_1522_:
{
lean_object* v_message_1525_; lean_object* v___x_3373__overap_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v_message_1525_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1523_, v_a_1501_, v___y_1524_);
v___x_3373__overap_1526_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1523_);
v___x_1527_ = lean_apply_2(v___x_3373__overap_1526_, v_outputData_1511_, v_message_1525_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v___x_1527_);
v___x_1529_ = v___x_1520_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_userData_1510_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_state_1512_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_knownSize_1513_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_messageHead_1514_);
lean_ctor_set(v_reuseFailAlloc_1531_, 5, v_userDataBytes_1518_);
lean_ctor_set_uint8(v_reuseFailAlloc_1531_, sizeof(void*)*6, v_sentMessage_1515_);
lean_ctor_set_uint8(v_reuseFailAlloc_1531_, sizeof(void*)*6 + 1, v_userClosedBody_1516_);
lean_ctor_set_uint8(v_reuseFailAlloc_1531_, sizeof(void*)*6 + 2, v_omitBody_1517_);
v___x_1529_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1530_, 0, v_reader_1502_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
lean_ctor_set(v___x_1530_, 2, v_config_1503_);
lean_ctor_set(v___x_1530_, 3, v_events_1504_);
lean_ctor_set(v___x_1530_, 4, v_error_1505_);
lean_ctor_set(v___x_1530_, 5, v_instant_1506_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*6, v_keepAlive_1507_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*6 + 1, v_forcedFlush_1508_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*6 + 2, v_pullBodyStalled_1509_);
v___y_1437_ = v___x_1530_;
v_omitBody_1438_ = v_omitBody_1517_;
goto v___jp_1436_;
}
}
v___jp_1532_:
{
lean_object* v_entries_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_entries_1538_ = lean_ctor_get(v___y_1537_, 0);
lean_inc_ref(v_entries_1538_);
lean_dec_ref(v___y_1537_);
v___x_1539_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1535_, v___y_1536_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v___y_1535_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_array_get_size(v_entries_1538_);
v___x_1542_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_1543_ = lean_nat_dec_lt(v___x_1540_, v___x_1541_);
if (v___x_1543_ == 0)
{
lean_dec_ref(v_entries_1538_);
lean_dec_ref(v___y_1533_);
v___y_1523_ = v___y_1534_;
v___y_1524_ = v___x_1539_;
goto v___jp_1522_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_nat_dec_le(v___x_1541_, v___x_1541_);
if (v___x_1544_ == 0)
{
if (v___x_1543_ == 0)
{
lean_dec_ref(v_entries_1538_);
lean_dec_ref(v___y_1533_);
v___y_1523_ = v___y_1534_;
v___y_1524_ = v___x_1539_;
goto v___jp_1522_;
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1541_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1542_, v___y_1533_, v_entries_1538_, v___x_1545_, v___x_1546_, v___x_1539_);
v___y_1523_ = v___y_1534_;
v___y_1524_ = v___x_1547_;
goto v___jp_1522_;
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_of_nat(v___x_1541_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1542_, v___y_1533_, v_entries_1538_, v___x_1548_, v___x_1549_, v___x_1539_);
v___y_1523_ = v___y_1534_;
v___y_1524_ = v___x_1550_;
goto v___jp_1522_;
}
}
}
v___jp_1551_:
{
lean_object* v___x_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; uint8_t v___x_1561_; 
v___x_1556_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1557_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___f_1558_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___x_1559_ = lean_box(v___y_1552_);
v___f_1560_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1560_, 0, v___x_1556_);
lean_closure_set(v___f_1560_, 1, v___x_1559_);
lean_closure_set(v___f_1560_, 2, v___f_1557_);
lean_closure_set(v___f_1560_, 3, v___f_1558_);
v___x_1561_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1557_, v___f_1558_, v___x_1556_, v___y_1555_);
if (v___x_1561_ == 0)
{
if (v___y_1553_ == 0)
{
v___y_1533_ = v___f_1560_;
v___y_1534_ = v___y_1554_;
v___y_1535_ = v___f_1557_;
v___y_1536_ = v___f_1558_;
v___y_1537_ = v___y_1555_;
goto v___jp_1532_;
}
else
{
lean_dec_ref(v___f_1560_);
v___y_1523_ = v___y_1554_;
v___y_1524_ = v___y_1555_;
goto v___jp_1522_;
}
}
else
{
v___y_1533_ = v___f_1560_;
v___y_1534_ = v___y_1554_;
v___y_1535_ = v___f_1557_;
v___y_1536_ = v___f_1558_;
v___y_1537_ = v___y_1555_;
goto v___jp_1532_;
}
}
v___jp_1562_:
{
lean_object* v_entries_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_entries_1570_ = lean_ctor_get(v___y_1568_, 0);
lean_inc_ref(v_entries_1570_);
lean_dec_ref(v___y_1568_);
v___x_1571_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1569_, v___y_1567_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v___y_1569_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get_size(v_entries_1570_);
v___x_1574_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_1575_ = lean_nat_dec_lt(v___x_1572_, v___x_1573_);
if (v___x_1575_ == 0)
{
lean_dec_ref(v_entries_1570_);
lean_dec_ref(v___y_1564_);
v___y_1552_ = v___y_1563_;
v___y_1553_ = v___y_1565_;
v___y_1554_ = v___y_1566_;
v___y_1555_ = v___x_1571_;
goto v___jp_1551_;
}
else
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_nat_dec_le(v___x_1573_, v___x_1573_);
if (v___x_1576_ == 0)
{
if (v___x_1575_ == 0)
{
lean_dec_ref(v_entries_1570_);
lean_dec_ref(v___y_1564_);
v___y_1552_ = v___y_1563_;
v___y_1553_ = v___y_1565_;
v___y_1554_ = v___y_1566_;
v___y_1555_ = v___x_1571_;
goto v___jp_1551_;
}
else
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = lean_usize_of_nat(v___x_1573_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1574_, v___y_1564_, v_entries_1570_, v___x_1577_, v___x_1578_, v___x_1571_);
v___y_1552_ = v___y_1563_;
v___y_1553_ = v___y_1565_;
v___y_1554_ = v___y_1566_;
v___y_1555_ = v___x_1579_;
goto v___jp_1551_;
}
}
else
{
size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1573_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1574_, v___y_1564_, v_entries_1570_, v___x_1580_, v___x_1581_, v___x_1571_);
v___y_1552_ = v___y_1563_;
v___y_1553_ = v___y_1565_;
v___y_1554_ = v___y_1566_;
v___y_1555_ = v___x_1582_;
goto v___jp_1551_;
}
}
}
v___jp_1584_:
{
lean_object* v_headerSize_1591_; lean_object* v_machine_1592_; lean_object* v_machine_1593_; lean_object* v_reader_1594_; lean_object* v_state_1595_; 
v_headerSize_1591_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1586_, v_a_1501_, v___y_1587_);
v_machine_1592_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1583_, v___y_1588_, v_headerSize_1591_, v___y_1590_);
v_machine_1593_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1583_, v_machine_1592_, v_a_1501_);
lean_dec(v_a_1501_);
v_reader_1594_ = lean_ctor_get(v_machine_1593_, 0);
lean_inc_ref(v_reader_1594_);
v_state_1595_ = lean_ctor_get(v_reader_1594_, 0);
lean_inc(v_state_1595_);
lean_dec_ref(v_reader_1594_);
if (lean_obj_tag(v_state_1595_) == 7)
{
lean_dec_ref_known(v_state_1595_, 1);
v___y_1486_ = v___y_1585_;
v___y_1487_ = v_machine_1593_;
v___y_1488_ = v___y_1589_;
goto v___jp_1485_;
}
else
{
lean_dec(v_state_1595_);
v___y_1486_ = v___y_1585_;
v___y_1487_ = v_machine_1593_;
v___y_1488_ = v___y_1587_;
goto v___jp_1485_;
}
}
v___jp_1596_:
{
uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v_indexes_1602_; lean_object* v___x_1603_; lean_object* v_machine_1604_; lean_object* v___x_1605_; lean_object* v___f_1606_; lean_object* v___f_1607_; uint8_t v___x_1608_; 
v___x_1600_ = 1;
v___x_1601_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1600_, v_a_1501_);
v_indexes_1602_ = lean_ctor_get(v___x_1601_, 1);
lean_inc_ref(v_indexes_1602_);
lean_dec_ref(v___x_1601_);
lean_inc(v_a_1501_);
v___x_1603_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1603_, 0, v_userData_1510_);
lean_ctor_set(v___x_1603_, 1, v_outputData_1511_);
lean_ctor_set(v___x_1603_, 2, v_state_1512_);
lean_ctor_set(v___x_1603_, 3, v_knownSize_1513_);
lean_ctor_set(v___x_1603_, 4, v_a_1501_);
lean_ctor_set(v___x_1603_, 5, v_userDataBytes_1518_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*6, v___y_1598_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*6 + 1, v_userClosedBody_1516_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*6 + 2, v_omitBody_1517_);
v_machine_1604_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1604_, 0, v_reader_1502_);
lean_ctor_set(v_machine_1604_, 1, v___x_1603_);
lean_ctor_set(v_machine_1604_, 2, v_config_1503_);
lean_ctor_set(v_machine_1604_, 3, v_events_1504_);
lean_ctor_set(v_machine_1604_, 4, v_error_1505_);
lean_ctor_set(v_machine_1604_, 5, v_instant_1506_);
lean_ctor_set_uint8(v_machine_1604_, sizeof(void*)*6, v_keepAlive_1507_);
lean_ctor_set_uint8(v_machine_1604_, sizeof(void*)*6 + 1, v_forcedFlush_1508_);
lean_ctor_set_uint8(v_machine_1604_, sizeof(void*)*6 + 2, v_pullBodyStalled_1509_);
v___x_1605_ = l_Std_Http_Header_Name_contentLength;
v___f_1606_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___f_1607_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1606_, v___f_1607_, v_indexes_1602_, v___x_1605_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1606_, v___f_1607_, v_indexes_1602_, v___x_1609_);
lean_dec_ref(v_indexes_1602_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v___x_1600_;
v___y_1587_ = v___y_1597_;
v___y_1588_ = v_machine_1604_;
v___y_1589_ = v___y_1598_;
v___y_1590_ = v___x_1610_;
goto v___jp_1584_;
}
else
{
lean_dec_ref(v_indexes_1602_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v___x_1600_;
v___y_1587_ = v___y_1597_;
v___y_1588_ = v_machine_1604_;
v___y_1589_ = v___y_1598_;
v___y_1590_ = v___x_1608_;
goto v___jp_1584_;
}
}
v___jp_1611_:
{
lean_object* v_state_1614_; 
v_state_1614_ = lean_ctor_get(v_reader_1502_, 0);
if (lean_obj_tag(v_state_1614_) == 7)
{
v___y_1597_ = v___y_1613_;
v___y_1598_ = v___y_1612_;
v___y_1599_ = v___y_1612_;
goto v___jp_1596_;
}
else
{
v___y_1597_ = v___y_1613_;
v___y_1598_ = v___y_1612_;
v___y_1599_ = v___y_1613_;
goto v___jp_1596_;
}
}
v___jp_1615_:
{
if (v___y_1616_ == 0)
{
lean_del_object(v___x_1520_);
lean_dec(v_userDataBytes_1518_);
lean_dec(v_messageHead_1514_);
lean_dec(v_knownSize_1513_);
lean_dec(v_state_1512_);
lean_dec_ref(v_outputData_1511_);
lean_dec_ref(v_userData_1510_);
lean_dec(v_a_1501_);
v___y_1437_ = v___y_1430_;
v_omitBody_1438_ = v_omitBody_1517_;
goto v___jp_1436_;
}
else
{
lean_object* v_status_1617_; uint8_t v___x_1618_; uint16_t v___x_1619_; uint16_t v___x_1620_; uint8_t v___x_1621_; 
lean_inc(v_instant_1506_);
lean_inc(v_error_1505_);
lean_inc_ref(v_events_1504_);
lean_inc_ref(v_config_1503_);
lean_inc_ref(v_reader_1502_);
lean_dec_ref(v___y_1430_);
v_status_1617_ = lean_ctor_get(v_a_1501_, 0);
v___x_1618_ = 0;
v___x_1619_ = 100;
v___x_1620_ = l_Std_Http_Status_toCode(v_status_1617_);
v___x_1621_ = lean_uint16_dec_le(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_del_object(v___x_1520_);
lean_dec(v_messageHead_1514_);
v___y_1612_ = v___y_1616_;
v___y_1613_ = v___x_1618_;
goto v___jp_1611_;
}
else
{
uint16_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = 200;
v___x_1623_ = lean_uint16_dec_lt(v___x_1620_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_del_object(v___x_1520_);
lean_dec(v_messageHead_1514_);
v___y_1612_ = v___y_1616_;
v___y_1613_ = v___x_1618_;
goto v___jp_1611_;
}
else
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___f_1630_; uint8_t v___x_1631_; 
v___x_1624_ = 1;
v___x_1625_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1624_, v_a_1501_);
v___x_1626_ = l_Std_Http_Header_Name_contentLength;
v___f_1627_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___f_1628_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___x_1629_ = lean_box(v___x_1623_);
v___f_1630_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1630_, 0, v___x_1626_);
lean_closure_set(v___f_1630_, 1, v___x_1629_);
lean_closure_set(v___f_1630_, 2, v___f_1627_);
lean_closure_set(v___f_1630_, 3, v___f_1628_);
v___x_1631_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1627_, v___f_1628_, v___x_1626_, v___x_1625_);
if (v___x_1631_ == 0)
{
if (v___x_1623_ == 0)
{
v___y_1563_ = v___x_1623_;
v___y_1564_ = v___f_1630_;
v___y_1565_ = v___x_1623_;
v___y_1566_ = v___x_1624_;
v___y_1567_ = v___f_1628_;
v___y_1568_ = v___x_1625_;
v___y_1569_ = v___f_1627_;
goto v___jp_1562_;
}
else
{
lean_dec_ref(v___f_1630_);
v___y_1552_ = v___x_1623_;
v___y_1553_ = v___x_1623_;
v___y_1554_ = v___x_1624_;
v___y_1555_ = v___x_1625_;
goto v___jp_1551_;
}
}
else
{
v___y_1563_ = v___x_1623_;
v___y_1564_ = v___f_1630_;
v___y_1565_ = v___x_1623_;
v___y_1566_ = v___x_1624_;
v___y_1567_ = v___f_1628_;
v___y_1568_ = v___x_1625_;
v___y_1569_ = v___f_1627_;
goto v___jp_1562_;
}
}
}
}
}
}
}
v___jp_1436_:
{
if (v_omitBody_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v_close_1433_);
lean_dec_ref(v_isClosed_1432_);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_body_1431_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1437_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
lean_inc(v_body_1431_);
v___x_1443_ = lean_apply_2(v_isClosed_1432_, v_body_1431_, lean_box(0));
v___f_1444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1444_, 0, v___y_1437_);
lean_inc_ref(v___f_1444_);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1445_, 0, v___f_1444_);
v___f_1446_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1446_, 0, v_close_1433_);
lean_closure_set(v___f_1446_, 1, v_body_1431_);
lean_closure_set(v___f_1446_, 2, v___f_1445_);
lean_closure_set(v___f_1446_, 3, v___f_1444_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = 0;
v___x_1449_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1447_, v___x_1448_, v___x_1443_, v___f_1446_);
return v___x_1449_;
}
}
v___jp_1450_:
{
lean_object* v_writer_1452_; lean_object* v_reader_1453_; lean_object* v_config_1454_; lean_object* v_events_1455_; lean_object* v_error_1456_; lean_object* v_instant_1457_; uint8_t v_keepAlive_1458_; uint8_t v_forcedFlush_1459_; uint8_t v_pullBodyStalled_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1484_; 
v_writer_1452_ = lean_ctor_get(v___y_1451_, 1);
v_reader_1453_ = lean_ctor_get(v___y_1451_, 0);
v_config_1454_ = lean_ctor_get(v___y_1451_, 2);
v_events_1455_ = lean_ctor_get(v___y_1451_, 3);
v_error_1456_ = lean_ctor_get(v___y_1451_, 4);
v_instant_1457_ = lean_ctor_get(v___y_1451_, 5);
v_keepAlive_1458_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*6);
v_forcedFlush_1459_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1460_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*6 + 2);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___y_1451_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1462_ = v___y_1451_;
v_isShared_1463_ = v_isSharedCheck_1484_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_instant_1457_);
lean_inc(v_error_1456_);
lean_inc(v_events_1455_);
lean_inc(v_config_1454_);
lean_inc(v_writer_1452_);
lean_inc(v_reader_1453_);
lean_dec(v___y_1451_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1484_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_userData_1464_; lean_object* v_outputData_1465_; lean_object* v_knownSize_1466_; lean_object* v_messageHead_1467_; uint8_t v_sentMessage_1468_; uint8_t v_userClosedBody_1469_; uint8_t v_omitBody_1470_; lean_object* v_userDataBytes_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1482_; 
v_userData_1464_ = lean_ctor_get(v_writer_1452_, 0);
v_outputData_1465_ = lean_ctor_get(v_writer_1452_, 1);
v_knownSize_1466_ = lean_ctor_get(v_writer_1452_, 3);
v_messageHead_1467_ = lean_ctor_get(v_writer_1452_, 4);
v_sentMessage_1468_ = lean_ctor_get_uint8(v_writer_1452_, sizeof(void*)*6);
v_userClosedBody_1469_ = lean_ctor_get_uint8(v_writer_1452_, sizeof(void*)*6 + 1);
v_omitBody_1470_ = lean_ctor_get_uint8(v_writer_1452_, sizeof(void*)*6 + 2);
v_userDataBytes_1471_ = lean_ctor_get(v_writer_1452_, 5);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_writer_1452_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_writer_1452_, 2);
lean_dec(v_unused_1483_);
v___x_1473_ = v_writer_1452_;
v_isShared_1474_ = v_isSharedCheck_1482_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_userDataBytes_1471_);
lean_inc(v_messageHead_1467_);
lean_inc(v_knownSize_1466_);
lean_inc(v_outputData_1465_);
lean_inc(v_userData_1464_);
lean_dec(v_writer_1452_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1482_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_box(2);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 2, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_userData_1464_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_outputData_1465_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_knownSize_1466_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_messageHead_1467_);
lean_ctor_set(v_reuseFailAlloc_1481_, 5, v_userDataBytes_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1481_, sizeof(void*)*6, v_sentMessage_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1481_, sizeof(void*)*6 + 1, v_userClosedBody_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1481_, sizeof(void*)*6 + 2, v_omitBody_1470_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 1, v___x_1477_);
v___x_1479_ = v___x_1462_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_reader_1453_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_config_1454_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_events_1455_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_error_1456_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v_instant_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*6, v_keepAlive_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*6 + 1, v_forcedFlush_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*6 + 2, v_pullBodyStalled_1460_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v___y_1437_ = v___x_1479_;
v_omitBody_1438_ = v_omitBody_1470_;
goto v___jp_1436_;
}
}
}
}
}
v___jp_1485_:
{
if (v___y_1488_ == 0)
{
v___y_1451_ = v___y_1487_;
goto v___jp_1450_;
}
else
{
if (v___y_1486_ == 0)
{
lean_object* v_writer_1489_; uint8_t v_omitBody_1490_; 
v_writer_1489_ = lean_ctor_get(v___y_1487_, 1);
v_omitBody_1490_ = lean_ctor_get_uint8(v_writer_1489_, sizeof(void*)*6 + 2);
v___y_1437_ = v___y_1487_;
v_omitBody_1438_ = v_omitBody_1490_;
goto v___jp_1436_;
}
else
{
v___y_1451_ = v___y_1487_;
goto v___jp_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1635_, lean_object* v_body_1636_, lean_object* v_isClosed_1637_, lean_object* v_close_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1635_, v_body_1636_, v_isClosed_1637_, v_close_1638_, v_x_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_config_1642_, lean_object* v_line_1643_, lean_object* v_body_1644_, lean_object* v_isClosed_1645_, lean_object* v_close_1646_, lean_object* v_machine_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___y_1651_; 
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_machine_1647_);
lean_dec_ref(v_close_1646_);
lean_dec_ref(v_isClosed_1645_);
lean_dec(v_body_1644_);
lean_dec_ref(v_line_1643_);
v_a_1657_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v_x_1648_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v_x_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; 
v_a_1666_ = lean_ctor_get(v_x_1648_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v_x_1648_, 1);
if (lean_obj_tag(v_a_1666_) == 1)
{
lean_object* v_writer_1667_; lean_object* v_reader_1668_; lean_object* v_config_1669_; lean_object* v_events_1670_; lean_object* v_error_1671_; lean_object* v_instant_1672_; uint8_t v_keepAlive_1673_; uint8_t v_forcedFlush_1674_; uint8_t v_pullBodyStalled_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1698_; 
v_writer_1667_ = lean_ctor_get(v_machine_1647_, 1);
v_reader_1668_ = lean_ctor_get(v_machine_1647_, 0);
v_config_1669_ = lean_ctor_get(v_machine_1647_, 2);
v_events_1670_ = lean_ctor_get(v_machine_1647_, 3);
v_error_1671_ = lean_ctor_get(v_machine_1647_, 4);
v_instant_1672_ = lean_ctor_get(v_machine_1647_, 5);
v_keepAlive_1673_ = lean_ctor_get_uint8(v_machine_1647_, sizeof(void*)*6);
v_forcedFlush_1674_ = lean_ctor_get_uint8(v_machine_1647_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1675_ = lean_ctor_get_uint8(v_machine_1647_, sizeof(void*)*6 + 2);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_machine_1647_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1677_ = v_machine_1647_;
v_isShared_1678_ = v_isSharedCheck_1698_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_instant_1672_);
lean_inc(v_error_1671_);
lean_inc(v_events_1670_);
lean_inc(v_config_1669_);
lean_inc(v_writer_1667_);
lean_inc(v_reader_1668_);
lean_dec(v_machine_1647_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1698_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_userData_1679_; lean_object* v_outputData_1680_; lean_object* v_state_1681_; lean_object* v_messageHead_1682_; uint8_t v_sentMessage_1683_; uint8_t v_userClosedBody_1684_; uint8_t v_omitBody_1685_; lean_object* v_userDataBytes_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1696_; 
v_userData_1679_ = lean_ctor_get(v_writer_1667_, 0);
v_outputData_1680_ = lean_ctor_get(v_writer_1667_, 1);
v_state_1681_ = lean_ctor_get(v_writer_1667_, 2);
v_messageHead_1682_ = lean_ctor_get(v_writer_1667_, 4);
v_sentMessage_1683_ = lean_ctor_get_uint8(v_writer_1667_, sizeof(void*)*6);
v_userClosedBody_1684_ = lean_ctor_get_uint8(v_writer_1667_, sizeof(void*)*6 + 1);
v_omitBody_1685_ = lean_ctor_get_uint8(v_writer_1667_, sizeof(void*)*6 + 2);
v_userDataBytes_1686_ = lean_ctor_get(v_writer_1667_, 5);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_writer_1667_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_writer_1667_, 3);
lean_dec(v_unused_1697_);
v___x_1688_ = v_writer_1667_;
v_isShared_1689_ = v_isSharedCheck_1696_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_userDataBytes_1686_);
lean_inc(v_messageHead_1682_);
lean_inc(v_state_1681_);
lean_inc(v_outputData_1680_);
lean_inc(v_userData_1679_);
lean_dec(v_writer_1667_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1696_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 3, v_a_1666_);
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_userData_1679_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_outputData_1680_);
lean_ctor_set(v_reuseFailAlloc_1695_, 2, v_state_1681_);
lean_ctor_set(v_reuseFailAlloc_1695_, 3, v_a_1666_);
lean_ctor_set(v_reuseFailAlloc_1695_, 4, v_messageHead_1682_);
lean_ctor_set(v_reuseFailAlloc_1695_, 5, v_userDataBytes_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, sizeof(void*)*6, v_sentMessage_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, sizeof(void*)*6 + 1, v_userClosedBody_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, sizeof(void*)*6 + 2, v_omitBody_1685_);
v___x_1691_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1691_);
v___x_1693_ = v___x_1677_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_reader_1668_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_config_1669_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_events_1670_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_error_1671_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v_instant_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*6, v_keepAlive_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*6 + 1, v_forcedFlush_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*6 + 2, v_pullBodyStalled_1675_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v___y_1651_ = v___x_1693_;
goto v___jp_1650_;
}
}
}
}
}
else
{
lean_dec(v_a_1666_);
v___y_1651_ = v_machine_1647_;
goto v___jp_1650_;
}
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1652_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1642_, v_line_1643_);
v___f_1653_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1653_, 0, v___y_1651_);
lean_closure_set(v___f_1653_, 1, v_body_1644_);
lean_closure_set(v___f_1653_, 2, v_isClosed_1645_);
lean_closure_set(v___f_1653_, 3, v_close_1646_);
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = 0;
v___x_1656_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1654_, v___x_1655_, v___x_1652_, v___f_1653_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_config_1699_, lean_object* v_line_1700_, lean_object* v_body_1701_, lean_object* v_isClosed_1702_, lean_object* v_close_1703_, lean_object* v_machine_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_config_1699_, v_line_1700_, v_body_1701_, v_isClosed_1702_, v_close_1703_, v_machine_1704_, v_x_1705_);
lean_dec_ref(v_config_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1708_, lean_object* v_config_1709_, lean_object* v_machine_1710_, lean_object* v_res_1711_){
_start:
{
lean_object* v_close_1713_; lean_object* v_isClosed_1714_; lean_object* v_getKnownSize_1715_; lean_object* v_line_1716_; lean_object* v_body_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v_close_1713_ = lean_ctor_get(v_inst_1708_, 1);
lean_inc_ref(v_close_1713_);
v_isClosed_1714_ = lean_ctor_get(v_inst_1708_, 2);
lean_inc_ref(v_isClosed_1714_);
v_getKnownSize_1715_ = lean_ctor_get(v_inst_1708_, 5);
lean_inc_ref(v_getKnownSize_1715_);
lean_dec_ref(v_inst_1708_);
v_line_1716_ = lean_ctor_get(v_res_1711_, 0);
lean_inc_ref(v_line_1716_);
v_body_1717_ = lean_ctor_get(v_res_1711_, 1);
lean_inc_n(v_body_1717_, 2);
lean_dec_ref(v_res_1711_);
v___x_1718_ = lean_apply_2(v_getKnownSize_1715_, v_body_1717_, lean_box(0));
v___f_1719_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1719_, 0, v_config_1709_);
lean_closure_set(v___f_1719_, 1, v_line_1716_);
lean_closure_set(v___f_1719_, 2, v_body_1717_);
lean_closure_set(v___f_1719_, 3, v_isClosed_1714_);
lean_closure_set(v___f_1719_, 4, v_close_1713_);
lean_closure_set(v___f_1719_, 5, v_machine_1710_);
v___x_1720_ = lean_unsigned_to_nat(0u);
v___x_1721_ = 0;
v___x_1722_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1720_, v___x_1721_, v___x_1718_, v___f_1719_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1723_, lean_object* v_config_1724_, lean_object* v_machine_1725_, lean_object* v_res_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1723_, v_config_1724_, v_machine_1725_, v_res_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1729_, lean_object* v_inst_1730_, lean_object* v_config_1731_, lean_object* v_machine_1732_, lean_object* v_res_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1730_, v_config_1731_, v_machine_1732_, v_res_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1736_, lean_object* v_inst_1737_, lean_object* v_config_1738_, lean_object* v_machine_1739_, lean_object* v_res_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1736_, v_inst_1737_, v_config_1738_, v_machine_1739_, v_res_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_closed_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_closed_1746_ = lean_ctor_get_uint8(v_____do__lift_1743_, sizeof(void*)*6);
v___x_1747_ = lean_box(v_closed_1746_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v_____do__lift_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; lean_object* v_pendingProducer_1762_; lean_object* v_pendingConsumer_1763_; lean_object* v_interestWaiter_1764_; uint8_t v_closed_1765_; lean_object* v_pendingIncompleteChunk_1766_; lean_object* v_closeError_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1776_; 
v___x_1761_ = lean_st_ref_take(v___y_1759_);
v_pendingProducer_1762_ = lean_ctor_get(v___x_1761_, 0);
v_pendingConsumer_1763_ = lean_ctor_get(v___x_1761_, 1);
v_interestWaiter_1764_ = lean_ctor_get(v___x_1761_, 2);
v_closed_1765_ = lean_ctor_get_uint8(v___x_1761_, sizeof(void*)*6);
v_pendingIncompleteChunk_1766_ = lean_ctor_get(v___x_1761_, 4);
v_closeError_1767_ = lean_ctor_get(v___x_1761_, 5);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1761_, 3);
lean_dec(v_unused_1777_);
v___x_1769_ = v___x_1761_;
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_closeError_1767_);
lean_inc(v_pendingIncompleteChunk_1766_);
lean_inc(v_interestWaiter_1764_);
lean_inc(v_pendingConsumer_1763_);
lean_inc(v_pendingProducer_1762_);
lean_dec(v___x_1761_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 3, v___x_1758_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_pendingProducer_1762_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_pendingConsumer_1763_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_interestWaiter_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_pendingIncompleteChunk_1766_);
lean_ctor_set(v_reuseFailAlloc_1775_, 5, v_closeError_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1775_, sizeof(void*)*6, v_closed_1765_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_st_ref_put(v___y_1759_, v___x_1772_);
v___x_1774_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1778_, v___y_1779_);
lean_dec(v___y_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1783_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___x_1782_);
v_a_1785_ = lean_ctor_get(v_x_1783_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_x_1783_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1787_ = v_x_1783_;
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v_x_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
}
}
else
{
lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1802_; 
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1783_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_x_1783_, 0);
lean_dec(v_unused_1803_);
v___x_1795_ = v_x_1783_;
v_isShared_1796_ = v_isSharedCheck_1802_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v_x_1783_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1802_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1782_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1797_);
v___x_1799_ = v___x_1795_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1804_, v_x_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1808_, lean_object* v_requestStream_1809_, lean_object* v_keepAliveTimeout_1810_, lean_object* v_currentTimeout_1811_, lean_object* v_headerTimeout_1812_, lean_object* v_response_1813_, lean_object* v_respStream_1814_, lean_object* v_expectData_1815_, uint8_t v_handlerDispatched_1816_, lean_object* v_____r_1817_){
_start:
{
uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = 0;
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1821_, 0, v_machine_1808_);
lean_ctor_set(v___x_1821_, 1, v_requestStream_1809_);
lean_ctor_set(v___x_1821_, 2, v_keepAliveTimeout_1810_);
lean_ctor_set(v___x_1821_, 3, v_currentTimeout_1811_);
lean_ctor_set(v___x_1821_, 4, v_headerTimeout_1812_);
lean_ctor_set(v___x_1821_, 5, v_response_1813_);
lean_ctor_set(v___x_1821_, 6, v_respStream_1814_);
lean_ctor_set(v___x_1821_, 7, v_expectData_1815_);
lean_ctor_set(v___x_1821_, 8, v___x_1820_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*9, v___x_1819_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*9 + 1, v_handlerDispatched_1816_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1825_, lean_object* v_requestStream_1826_, lean_object* v_keepAliveTimeout_1827_, lean_object* v_currentTimeout_1828_, lean_object* v_headerTimeout_1829_, lean_object* v_response_1830_, lean_object* v_respStream_1831_, lean_object* v_expectData_1832_, lean_object* v_handlerDispatched_1833_, lean_object* v_____r_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v_handlerDispatched_boxed_1836_; lean_object* v_res_1837_; 
v_handlerDispatched_boxed_1836_ = lean_unbox(v_handlerDispatched_1833_);
v_res_1837_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1825_, v_requestStream_1826_, v_keepAliveTimeout_1827_, v_currentTimeout_1828_, v_headerTimeout_1829_, v_response_1830_, v_respStream_1831_, v_expectData_1832_, v_handlerDispatched_boxed_1836_, v_____r_1834_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v___f_1838_);
v_a_1841_ = lean_ctor_get(v_x_1839_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1843_ = v_x_1839_;
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v_x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1841_);
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
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1851_; 
v_a_1850_ = lean_ctor_get(v_x_1839_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v_x_1839_, 1);
v___x_1851_ = lean_apply_2(v___f_1838_, v_a_1850_, lean_box(0));
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1852_, lean_object* v_x_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1852_, v_x_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1856_, lean_object* v___f_1857_, lean_object* v___f_1858_, lean_object* v_x_1859_){
_start:
{
if (lean_obj_tag(v_x_1859_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___f_1857_);
lean_dec_ref(v_requestStream_1856_);
v_a_1861_ = lean_ctor_get(v_x_1859_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_x_1859_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v_x_1859_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v_x_1859_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; uint8_t v___x_1871_; 
v_a_1870_ = lean_ctor_get(v_x_1859_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v_x_1859_, 1);
v___x_1871_ = lean_unbox(v_a_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v___f_1858_);
v___x_1872_ = l_Std_Http_Body_Stream_close(v_requestStream_1856_);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_unbox(v_a_1870_);
lean_dec(v_a_1870_);
v___x_1875_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1873_, v___x_1874_, v___x_1872_, v___f_1857_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec(v_a_1870_);
lean_dec_ref(v___f_1857_);
lean_dec_ref(v_requestStream_1856_);
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_apply_2(v___f_1858_, v___x_1876_, lean_box(0));
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1878_, lean_object* v___f_1879_, lean_object* v___f_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1878_, v___f_1879_, v___f_1880_, v_x_1881_);
return v_res_1883_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1884_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1885_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___f_1893_; 
v___x_1891_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1892_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1893_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1893_, 0, v___f_1892_);
lean_closure_set(v___f_1893_, 1, v___x_1891_);
return v___f_1893_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___f_1904_; 
v___x_1902_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1903_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1904_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1904_, 0, v___f_1903_);
lean_closure_set(v___f_1904_, 1, v___x_1902_);
return v___f_1904_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; 
v___f_1905_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1906_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1906_, 0, lean_box(0));
lean_closure_set(v___x_1906_, 1, lean_box(0));
lean_closure_set(v___x_1906_, 2, lean_box(0));
lean_closure_set(v___x_1906_, 3, v___f_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1907_, lean_object* v___f_1908_, lean_object* v_x_1909_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v___f_1908_);
lean_dec_ref(v___y_1907_);
v_a_1911_ = lean_ctor_get(v_x_1909_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_x_1909_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1913_ = v_x_1909_;
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v_x_1909_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
}
}
else
{
lean_object* v_machine_1920_; lean_object* v_requestStream_1921_; lean_object* v_keepAliveTimeout_1922_; lean_object* v_currentTimeout_1923_; lean_object* v_headerTimeout_1924_; lean_object* v_response_1925_; lean_object* v_respStream_1926_; lean_object* v_expectData_1927_; uint8_t v_handlerDispatched_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_4933__overap_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; lean_object* v___f_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
lean_dec_ref_known(v_x_1909_, 1);
v_machine_1920_ = lean_ctor_get(v___y_1907_, 0);
lean_inc_ref(v_machine_1920_);
v_requestStream_1921_ = lean_ctor_get(v___y_1907_, 1);
lean_inc_ref_n(v_requestStream_1921_, 3);
v_keepAliveTimeout_1922_ = lean_ctor_get(v___y_1907_, 2);
lean_inc(v_keepAliveTimeout_1922_);
v_currentTimeout_1923_ = lean_ctor_get(v___y_1907_, 3);
lean_inc(v_currentTimeout_1923_);
v_headerTimeout_1924_ = lean_ctor_get(v___y_1907_, 4);
lean_inc(v_headerTimeout_1924_);
v_response_1925_ = lean_ctor_get(v___y_1907_, 5);
lean_inc_ref(v_response_1925_);
v_respStream_1926_ = lean_ctor_get(v___y_1907_, 6);
lean_inc(v_respStream_1926_);
v_expectData_1927_ = lean_ctor_get(v___y_1907_, 7);
lean_inc(v_expectData_1927_);
v_handlerDispatched_1928_ = lean_ctor_get_uint8(v___y_1907_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1907_);
v___x_1929_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1930_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1931_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1932_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1933_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1933_, 0, lean_box(0));
lean_closure_set(v___x_1933_, 1, lean_box(0));
lean_closure_set(v___x_1933_, 2, v___x_1929_);
lean_closure_set(v___x_1933_, 3, lean_box(0));
lean_closure_set(v___x_1933_, 4, lean_box(0));
lean_closure_set(v___x_1933_, 5, v___x_1932_);
lean_closure_set(v___x_1933_, 6, v___f_1908_);
v___x_4933__overap_1934_ = l_Std_Mutex_atomically___redArg(v___x_1929_, v___f_1930_, v___f_1931_, v_requestStream_1921_, v___x_1933_);
v___x_1935_ = lean_apply_1(v___x_4933__overap_1934_, lean_box(0));
v___x_1936_ = lean_box(v_handlerDispatched_1928_);
v___f_1937_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1937_, 0, v_machine_1920_);
lean_closure_set(v___f_1937_, 1, v_requestStream_1921_);
lean_closure_set(v___f_1937_, 2, v_keepAliveTimeout_1922_);
lean_closure_set(v___f_1937_, 3, v_currentTimeout_1923_);
lean_closure_set(v___f_1937_, 4, v_headerTimeout_1924_);
lean_closure_set(v___f_1937_, 5, v_response_1925_);
lean_closure_set(v___f_1937_, 6, v_respStream_1926_);
lean_closure_set(v___f_1937_, 7, v_expectData_1927_);
lean_closure_set(v___f_1937_, 8, v___x_1936_);
lean_inc_ref(v___f_1937_);
v___f_1938_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1938_, 0, v___f_1937_);
v___f_1939_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1939_, 0, v_requestStream_1921_);
lean_closure_set(v___f_1939_, 1, v___f_1938_);
lean_closure_set(v___f_1939_, 2, v___f_1937_);
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = 0;
v___x_1942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1940_, v___x_1941_, v___x_1935_, v___f_1939_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1943_, lean_object* v___f_1944_, lean_object* v_x_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1943_, v___f_1944_, v_x_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1948_, lean_object* v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___y_1948_);
v_a_1951_ = lean_ctor_get(v_x_1949_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v_x_1949_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v_x_1949_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
}
}
else
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1968_; 
v_isSharedCheck_1968_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v_x_1949_, 0);
lean_dec(v_unused_1969_);
v___x_1961_ = v_x_1949_;
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v_x_1949_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___y_1948_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1963_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1970_, lean_object* v_x_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1970_, v_x_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1974_, lean_object* v___f_1975_, lean_object* v___y_1976_, lean_object* v_x_1977_){
_start:
{
if (lean_obj_tag(v_x_1977_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___y_1976_);
lean_dec_ref(v___f_1975_);
lean_dec_ref(v_requestStream_1974_);
v_a_1979_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1981_ = v_x_1977_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v_x_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2002_; 
v_a_1988_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1990_ = v_x_1977_;
v_isShared_1991_ = v_isSharedCheck_2002_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v_x_1977_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2002_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_unbox(v_a_1988_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; 
lean_del_object(v___x_1990_);
lean_dec_ref(v___y_1976_);
v___x_1993_ = l_Std_Http_Body_Stream_close(v_requestStream_1974_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
v___x_1996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1994_, v___x_1995_, v___x_1993_, v___f_1975_);
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_dec(v_a_1988_);
lean_dec_ref(v___f_1975_);
lean_dec_ref(v_requestStream_1974_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___y_1976_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1997_);
v___x_1999_ = v___x_1990_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_2003_, lean_object* v___f_2004_, lean_object* v___y_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_2003_, v___f_2004_, v___y_2005_, v_x_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_2009_, lean_object* v_machine_2010_, lean_object* v_a_2011_, uint8_t v_requiresData_2012_, lean_object* v_expectData_2013_, lean_object* v_pendingHead_2014_, lean_object* v_x_2015_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_pendingHead_2014_);
lean_dec(v_expectData_2013_);
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_machine_2010_);
v_a_2017_ = lean_ctor_get(v_x_2015_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v_x_2015_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v_x_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2040_; 
v_a_2026_ = lean_ctor_get(v_x_2015_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2028_ = v_x_2015_;
v_isShared_2029_ = v_isSharedCheck_2040_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v_x_2015_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2040_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_keepAliveTimeout_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v_keepAliveTimeout_2030_ = lean_ctor_get(v_config_2009_, 5);
lean_inc_n(v_keepAliveTimeout_2030_, 2);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_keepAliveTimeout_2030_);
v___x_2032_ = lean_box(0);
v___x_2033_ = 0;
v___x_2034_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2034_, 0, v_machine_2010_);
lean_ctor_set(v___x_2034_, 1, v_a_2011_);
lean_ctor_set(v___x_2034_, 2, v___x_2031_);
lean_ctor_set(v___x_2034_, 3, v_keepAliveTimeout_2030_);
lean_ctor_set(v___x_2034_, 4, v___x_2032_);
lean_ctor_set(v___x_2034_, 5, v_a_2026_);
lean_ctor_set(v___x_2034_, 6, v___x_2032_);
lean_ctor_set(v___x_2034_, 7, v_expectData_2013_);
lean_ctor_set(v___x_2034_, 8, v_pendingHead_2014_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*9, v_requiresData_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*9 + 1, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2035_);
v___x_2037_ = v___x_2028_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_2041_, lean_object* v_machine_2042_, lean_object* v_a_2043_, lean_object* v_requiresData_2044_, lean_object* v_expectData_2045_, lean_object* v_pendingHead_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v_requiresData_boxed_2049_; lean_object* v_res_2050_; 
v_requiresData_boxed_2049_ = lean_unbox(v_requiresData_2044_);
v_res_2050_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_2041_, v_machine_2042_, v_a_2043_, v_requiresData_boxed_2049_, v_expectData_2045_, v_pendingHead_2046_, v_x_2047_);
lean_dec_ref(v_config_2041_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_2051_, lean_object* v_machine_2052_, uint8_t v_requiresData_2053_, lean_object* v_expectData_2054_, lean_object* v_pendingHead_2055_, lean_object* v_x_2056_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_pendingHead_2055_);
lean_dec(v_expectData_2054_);
lean_dec_ref(v_machine_2052_);
lean_dec_ref(v_config_2051_);
v_a_2058_ = lean_ctor_get(v_x_2056_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2060_ = v_x_2056_;
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v_x_2056_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2082_; 
v_a_2067_ = lean_ctor_get(v_x_2056_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2069_ = v_x_2056_;
v_isShared_2070_ = v_isSharedCheck_2082_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v_x_2056_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2082_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___x_2076_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = l_Std_CloseableChannel_new___redArg(v___x_2071_);
v___x_2073_ = lean_box(v_requiresData_2053_);
v___f_2074_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2074_, 0, v_config_2051_);
lean_closure_set(v___f_2074_, 1, v_machine_2052_);
lean_closure_set(v___f_2074_, 2, v_a_2067_);
lean_closure_set(v___f_2074_, 3, v___x_2073_);
lean_closure_set(v___f_2074_, 4, v_expectData_2054_);
lean_closure_set(v___f_2074_, 5, v_pendingHead_2055_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2072_);
v___x_2076_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = 0;
v___x_2080_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2078_, v___x_2079_, v___x_2077_, v___f_2074_);
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_2083_, lean_object* v_machine_2084_, lean_object* v_requiresData_2085_, lean_object* v_expectData_2086_, lean_object* v_pendingHead_2087_, lean_object* v_x_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v_requiresData_boxed_2090_; lean_object* v_res_2091_; 
v_requiresData_boxed_2090_ = lean_unbox(v_requiresData_2085_);
v_res_2091_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_2083_, v_machine_2084_, v_requiresData_boxed_2090_, v_expectData_2086_, v_pendingHead_2087_, v_x_2088_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_2092_, lean_object* v_____r_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2095_ = l_Std_Http_Body_mkStream();
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = 0;
v___x_2098_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2096_, v___x_2097_, v___x_2095_, v___f_2092_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_2099_, lean_object* v_____r_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_2099_, v_____r_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_2103_, lean_object* v_val_2104_, lean_object* v___f_2105_, lean_object* v___f_2106_, lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2107_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v___f_2106_);
lean_dec_ref(v___f_2105_);
lean_dec(v_val_2104_);
lean_dec_ref(v_close_2103_);
v_a_2109_ = lean_ctor_get(v_x_2107_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2107_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2111_ = v_x_2107_;
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v_x_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
}
else
{
lean_object* v_a_2118_; uint8_t v___x_2119_; 
v_a_2118_ = lean_ctor_get(v_x_2107_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v_x_2107_, 1);
v___x_2119_ = lean_unbox(v_a_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v___f_2106_);
v___x_2120_ = lean_apply_2(v_close_2103_, v_val_2104_, lean_box(0));
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = lean_unbox(v_a_2118_);
lean_dec(v_a_2118_);
v___x_2123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2121_, v___x_2122_, v___x_2120_, v___f_2105_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_a_2118_);
lean_dec_ref(v___f_2105_);
lean_dec(v_val_2104_);
lean_dec_ref(v_close_2103_);
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_apply_2(v___f_2106_, v___x_2124_, lean_box(0));
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_2126_, lean_object* v_val_2127_, lean_object* v___f_2128_, lean_object* v___f_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_2126_, v_val_2127_, v___f_2128_, v___f_2129_, v_x_2130_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_2133_, lean_object* v_inst_2134_, lean_object* v___f_2135_, lean_object* v___f_2136_, lean_object* v_____r_2137_){
_start:
{
if (lean_obj_tag(v_respStream_2133_) == 1)
{
lean_object* v_val_2139_; lean_object* v_close_2140_; lean_object* v_isClosed_2141_; lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; 
v_val_2139_ = lean_ctor_get(v_respStream_2133_, 0);
lean_inc_n(v_val_2139_, 2);
lean_dec_ref_known(v_respStream_2133_, 1);
v_close_2140_ = lean_ctor_get(v_inst_2134_, 1);
lean_inc_ref(v_close_2140_);
v_isClosed_2141_ = lean_ctor_get(v_inst_2134_, 2);
lean_inc_ref(v_isClosed_2141_);
lean_dec_ref(v_inst_2134_);
v___x_2142_ = lean_apply_2(v_isClosed_2141_, v_val_2139_, lean_box(0));
v___f_2143_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_2143_, 0, v_close_2140_);
lean_closure_set(v___f_2143_, 1, v_val_2139_);
lean_closure_set(v___f_2143_, 2, v___f_2135_);
lean_closure_set(v___f_2143_, 3, v___f_2136_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = 0;
v___x_2146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2144_, v___x_2145_, v___x_2142_, v___f_2143_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v___f_2135_);
lean_dec_ref(v_inst_2134_);
lean_dec(v_respStream_2133_);
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_apply_2(v___f_2136_, v___x_2147_, lean_box(0));
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_2149_, lean_object* v_inst_2150_, lean_object* v___f_2151_, lean_object* v___f_2152_, lean_object* v_____r_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_2149_, v_inst_2150_, v___f_2151_, v___f_2152_, v_____r_2153_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2156_, lean_object* v_keepAliveTimeout_2157_, lean_object* v_currentTimeout_2158_, lean_object* v_headerTimeout_2159_, lean_object* v_response_2160_, lean_object* v_respStream_2161_, uint8_t v_requiresData_2162_, lean_object* v_expectData_2163_, uint8_t v_handlerDispatched_2164_, lean_object* v_pendingHead_2165_, lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_pendingHead_2165_);
lean_dec(v_expectData_2163_);
lean_dec(v_respStream_2161_);
lean_dec_ref(v_response_2160_);
lean_dec(v_headerTimeout_2159_);
lean_dec(v_currentTimeout_2158_);
lean_dec(v_keepAliveTimeout_2157_);
lean_dec_ref(v_requestStream_2156_);
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
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2198_; 
v_a_2177_ = lean_ctor_get(v_x_2166_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2179_ = v_x_2166_;
v_isShared_2180_ = v_isSharedCheck_2198_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v_x_2166_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2198_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_snd_2181_; uint8_t v___x_2182_; 
v_snd_2181_ = lean_ctor_get(v_a_2177_, 1);
v___x_2182_ = lean_unbox(v_snd_2181_);
if (v___x_2182_ == 0)
{
lean_object* v_fst_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v_fst_2183_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_fst_2183_);
lean_dec(v_a_2177_);
v___x_2184_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2184_, 0, v_fst_2183_);
lean_ctor_set(v___x_2184_, 1, v_requestStream_2156_);
lean_ctor_set(v___x_2184_, 2, v_keepAliveTimeout_2157_);
lean_ctor_set(v___x_2184_, 3, v_currentTimeout_2158_);
lean_ctor_set(v___x_2184_, 4, v_headerTimeout_2159_);
lean_ctor_set(v___x_2184_, 5, v_response_2160_);
lean_ctor_set(v___x_2184_, 6, v_respStream_2161_);
lean_ctor_set(v___x_2184_, 7, v_expectData_2163_);
lean_ctor_set(v___x_2184_, 8, v_pendingHead_2165_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*9, v_requiresData_2162_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*9 + 1, v_handlerDispatched_2164_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2185_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
}
else
{
lean_object* v_fst_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec(v_pendingHead_2165_);
v_fst_2190_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_fst_2190_);
lean_dec(v_a_2177_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2192_, 0, v_fst_2190_);
lean_ctor_set(v___x_2192_, 1, v_requestStream_2156_);
lean_ctor_set(v___x_2192_, 2, v_keepAliveTimeout_2157_);
lean_ctor_set(v___x_2192_, 3, v_currentTimeout_2158_);
lean_ctor_set(v___x_2192_, 4, v_headerTimeout_2159_);
lean_ctor_set(v___x_2192_, 5, v_response_2160_);
lean_ctor_set(v___x_2192_, 6, v_respStream_2161_);
lean_ctor_set(v___x_2192_, 7, v_expectData_2163_);
lean_ctor_set(v___x_2192_, 8, v___x_2191_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*9, v_requiresData_2162_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*9 + 1, v_handlerDispatched_2164_);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2193_);
v___x_2195_ = v___x_2179_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2199_, lean_object* v_keepAliveTimeout_2200_, lean_object* v_currentTimeout_2201_, lean_object* v_headerTimeout_2202_, lean_object* v_response_2203_, lean_object* v_respStream_2204_, lean_object* v_requiresData_2205_, lean_object* v_expectData_2206_, lean_object* v_handlerDispatched_2207_, lean_object* v_pendingHead_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v_requiresData_boxed_2211_; uint8_t v_handlerDispatched_boxed_2212_; lean_object* v_res_2213_; 
v_requiresData_boxed_2211_ = lean_unbox(v_requiresData_2205_);
v_handlerDispatched_boxed_2212_ = lean_unbox(v_handlerDispatched_2207_);
v_res_2213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2199_, v_keepAliveTimeout_2200_, v_currentTimeout_2201_, v_headerTimeout_2202_, v_response_2203_, v_respStream_2204_, v_requiresData_boxed_2211_, v_expectData_2206_, v_handlerDispatched_boxed_2212_, v_pendingHead_2208_, v_x_2209_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2226_, lean_object* v_inst_2227_, lean_object* v___f_2228_, lean_object* v_handler_2229_, lean_object* v___f_2230_, lean_object* v___f_2231_, lean_object* v_inst_2232_, lean_object* v_connectionContext_2233_, lean_object* v_a_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_){
_start:
{
switch(lean_obj_tag(v_a_2234_))
{
case 0:
{
lean_object* v_head_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_connectionContext_2233_);
lean_dec_ref(v_inst_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
lean_dec(v_handler_2229_);
lean_dec_ref(v___f_2228_);
lean_dec_ref(v_inst_2227_);
v_head_2238_ = lean_ctor_get(v_a_2234_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2240_ = v_a_2234_;
v_isShared_2241_ = v_isSharedCheck_2281_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_head_2238_);
lean_dec(v_a_2234_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2281_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_machine_2242_; lean_object* v_requestStream_2243_; lean_object* v_response_2244_; lean_object* v_respStream_2245_; uint8_t v_requiresData_2246_; lean_object* v_expectData_2247_; uint8_t v_handlerDispatched_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2276_; 
v_machine_2242_ = lean_ctor_get(v___y_2236_, 0);
v_requestStream_2243_ = lean_ctor_get(v___y_2236_, 1);
v_response_2244_ = lean_ctor_get(v___y_2236_, 5);
v_respStream_2245_ = lean_ctor_get(v___y_2236_, 6);
v_requiresData_2246_ = lean_ctor_get_uint8(v___y_2236_, sizeof(void*)*9);
v_expectData_2247_ = lean_ctor_get(v___y_2236_, 7);
v_handlerDispatched_2248_ = lean_ctor_get_uint8(v___y_2236_, sizeof(void*)*9 + 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___y_2236_);
if (v_isSharedCheck_2276_ == 0)
{
lean_object* v_unused_2277_; lean_object* v_unused_2278_; lean_object* v_unused_2279_; lean_object* v_unused_2280_; 
v_unused_2277_ = lean_ctor_get(v___y_2236_, 8);
lean_dec(v_unused_2277_);
v_unused_2278_ = lean_ctor_get(v___y_2236_, 4);
lean_dec(v_unused_2278_);
v_unused_2279_ = lean_ctor_get(v___y_2236_, 3);
lean_dec(v_unused_2279_);
v_unused_2280_ = lean_ctor_get(v___y_2236_, 2);
lean_dec(v_unused_2280_);
v___x_2250_ = v___y_2236_;
v_isShared_2251_ = v_isSharedCheck_2276_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_expectData_2247_);
lean_inc(v_respStream_2245_);
lean_inc(v_response_2244_);
lean_inc(v_requestStream_2243_);
lean_inc(v_machine_2242_);
lean_dec(v___y_2236_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2276_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_lingeringTimeout_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v_lingeringTimeout_2252_ = lean_ctor_get(v_config_2226_, 4);
lean_inc(v_lingeringTimeout_2252_);
lean_dec_ref(v_config_2226_);
v___x_2253_ = lean_box(0);
lean_inc(v_head_2238_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set_tag(v___x_2240_, 1);
v___x_2255_ = v___x_2240_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_head_2238_);
v___x_2255_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2257_; 
lean_inc_ref(v_requestStream_2243_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 8, v___x_2255_);
lean_ctor_set(v___x_2250_, 4, v___x_2253_);
lean_ctor_set(v___x_2250_, 3, v_lingeringTimeout_2252_);
lean_ctor_set(v___x_2250_, 2, v___x_2253_);
v___x_2257_ = v___x_2250_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_machine_2242_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_requestStream_2243_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_lingeringTimeout_2252_);
lean_ctor_set(v_reuseFailAlloc_2274_, 4, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2274_, 5, v_response_2244_);
lean_ctor_set(v_reuseFailAlloc_2274_, 6, v_respStream_2245_);
lean_ctor_set(v_reuseFailAlloc_2274_, 7, v_expectData_2247_);
lean_ctor_set(v_reuseFailAlloc_2274_, 8, v___x_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, sizeof(void*)*9, v_requiresData_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2274_, sizeof(void*)*9 + 1, v_handlerDispatched_2248_);
v___x_2257_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
uint8_t v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = 0;
v___x_2259_ = 1;
v___x_2260_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2258_, v_head_2238_, v___x_2259_);
lean_dec(v_head_2238_);
if (lean_obj_tag(v___x_2260_) == 1)
{
lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_5126__overap_2265_; lean_object* v___x_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; 
v___f_2261_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2261_, 0, v___x_2260_);
v___x_2262_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2263_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2264_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5126__overap_2265_ = l_Std_Mutex_atomically___redArg(v___x_2262_, v___f_2263_, v___f_2264_, v_requestStream_2243_, v___f_2261_);
v___x_2266_ = lean_apply_1(v___x_5126__overap_2265_, lean_box(0));
v___f_2267_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2267_, 0, v___x_2257_);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = 0;
v___x_2270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2268_, v___x_2269_, v___x_2266_, v___f_2267_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v___x_2260_);
lean_dec_ref(v_requestStream_2243_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2257_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_connectionContext_2233_);
lean_dec_ref(v_inst_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
lean_dec(v_handler_2229_);
lean_dec_ref(v___f_2228_);
lean_dec_ref(v_inst_2227_);
lean_dec_ref(v_config_2226_);
v_size_2282_ = lean_ctor_get(v_a_2234_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2284_ = v_a_2234_;
v_isShared_2285_ = v_isSharedCheck_2309_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_size_2282_);
lean_dec(v_a_2234_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2309_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_machine_2286_; lean_object* v_requestStream_2287_; lean_object* v_keepAliveTimeout_2288_; lean_object* v_currentTimeout_2289_; lean_object* v_headerTimeout_2290_; lean_object* v_response_2291_; lean_object* v_respStream_2292_; uint8_t v_handlerDispatched_2293_; lean_object* v_pendingHead_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2307_; 
v_machine_2286_ = lean_ctor_get(v___y_2236_, 0);
v_requestStream_2287_ = lean_ctor_get(v___y_2236_, 1);
v_keepAliveTimeout_2288_ = lean_ctor_get(v___y_2236_, 2);
v_currentTimeout_2289_ = lean_ctor_get(v___y_2236_, 3);
v_headerTimeout_2290_ = lean_ctor_get(v___y_2236_, 4);
v_response_2291_ = lean_ctor_get(v___y_2236_, 5);
v_respStream_2292_ = lean_ctor_get(v___y_2236_, 6);
v_handlerDispatched_2293_ = lean_ctor_get_uint8(v___y_2236_, sizeof(void*)*9 + 1);
v_pendingHead_2294_ = lean_ctor_get(v___y_2236_, 8);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___y_2236_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; 
v_unused_2308_ = lean_ctor_get(v___y_2236_, 7);
lean_dec(v_unused_2308_);
v___x_2296_ = v___y_2236_;
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_pendingHead_2294_);
lean_inc(v_respStream_2292_);
lean_inc(v_response_2291_);
lean_inc(v_headerTimeout_2290_);
lean_inc(v_currentTimeout_2289_);
lean_inc(v_keepAliveTimeout_2288_);
lean_inc(v_requestStream_2287_);
lean_inc(v_machine_2286_);
lean_dec(v___y_2236_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
uint8_t v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = 1;
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 7, v_size_2282_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_machine_2286_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_requestStream_2287_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_keepAliveTimeout_2288_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v_currentTimeout_2289_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_headerTimeout_2290_);
lean_ctor_set(v_reuseFailAlloc_2306_, 5, v_response_2291_);
lean_ctor_set(v_reuseFailAlloc_2306_, 6, v_respStream_2292_);
lean_ctor_set(v_reuseFailAlloc_2306_, 7, v_size_2282_);
lean_ctor_set(v_reuseFailAlloc_2306_, 8, v_pendingHead_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2306_, sizeof(void*)*9 + 1, v_handlerDispatched_2293_);
v___x_2300_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*9, v___x_2298_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2300_);
v___x_2302_ = v___x_2284_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2310_; lean_object* v_onFailure_2311_; lean_object* v___f_2312_; lean_object* v___y_2314_; 
lean_dec_ref(v_connectionContext_2233_);
lean_dec_ref(v_inst_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
lean_dec_ref(v_config_2226_);
v_err_2310_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_err_2310_);
lean_dec_ref_known(v_a_2234_, 1);
v_onFailure_2311_ = lean_ctor_get(v_inst_2227_, 2);
lean_inc_ref(v_onFailure_2311_);
lean_dec_ref(v_inst_2227_);
v___f_2312_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2312_, 0, v___y_2236_);
lean_closure_set(v___f_2312_, 1, v___f_2228_);
switch(lean_obj_tag(v_err_2310_))
{
case 0:
{
lean_object* v___x_2320_; 
v___x_2320_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2314_ = v___x_2320_;
goto v___jp_2313_;
}
case 1:
{
lean_object* v___x_2321_; 
v___x_2321_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2314_ = v___x_2321_;
goto v___jp_2313_;
}
case 2:
{
lean_object* v___x_2322_; 
v___x_2322_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2314_ = v___x_2322_;
goto v___jp_2313_;
}
case 3:
{
lean_object* v___x_2323_; 
v___x_2323_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2314_ = v___x_2323_;
goto v___jp_2313_;
}
case 4:
{
lean_object* v___x_2324_; 
v___x_2324_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2314_ = v___x_2324_;
goto v___jp_2313_;
}
case 5:
{
lean_object* v___x_2325_; 
v___x_2325_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2314_ = v___x_2325_;
goto v___jp_2313_;
}
case 6:
{
lean_object* v___x_2326_; 
v___x_2326_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2314_ = v___x_2326_;
goto v___jp_2313_;
}
case 7:
{
lean_object* v___x_2327_; 
v___x_2327_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2314_ = v___x_2327_;
goto v___jp_2313_;
}
case 8:
{
lean_object* v___x_2328_; 
v___x_2328_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2314_ = v___x_2328_;
goto v___jp_2313_;
}
case 9:
{
lean_object* v___x_2329_; 
v___x_2329_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2314_ = v___x_2329_;
goto v___jp_2313_;
}
case 10:
{
lean_object* v___x_2330_; 
v___x_2330_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2314_ = v___x_2330_;
goto v___jp_2313_;
}
default: 
{
lean_object* v_message_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_message_2331_ = lean_ctor_get(v_err_2310_, 0);
lean_inc_ref(v_message_2331_);
lean_dec_ref_known(v_err_2310_, 1);
v___x_2332_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2333_ = lean_string_append(v___x_2332_, v_message_2331_);
lean_dec_ref(v_message_2331_);
v___y_2314_ = v___x_2333_;
goto v___jp_2313_;
}
}
v___jp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = lean_mk_io_user_error(v___y_2314_);
v___x_2316_ = lean_apply_3(v_onFailure_2311_, v_handler_2229_, v___x_2315_, lean_box(0));
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = 0;
v___x_2319_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2317_, v___x_2318_, v___x_2316_, v___f_2312_);
return v___x_2319_;
}
}
case 4:
{
lean_object* v_requestStream_2334_; lean_object* v___x_2335_; lean_object* v___f_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_5182__overap_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; 
lean_dec_ref(v_connectionContext_2233_);
lean_dec_ref(v_inst_2232_);
lean_dec_ref(v___f_2231_);
lean_dec(v_handler_2229_);
lean_dec_ref(v___f_2228_);
lean_dec_ref(v_inst_2227_);
lean_dec_ref(v_config_2226_);
v_requestStream_2334_ = lean_ctor_get(v___y_2236_, 1);
lean_inc_ref_n(v_requestStream_2334_, 2);
v___x_2335_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2336_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2337_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2338_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2339_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2339_, 0, lean_box(0));
lean_closure_set(v___x_2339_, 1, lean_box(0));
lean_closure_set(v___x_2339_, 2, v___x_2335_);
lean_closure_set(v___x_2339_, 3, lean_box(0));
lean_closure_set(v___x_2339_, 4, lean_box(0));
lean_closure_set(v___x_2339_, 5, v___x_2338_);
lean_closure_set(v___x_2339_, 6, v___f_2230_);
v___x_5182__overap_2340_ = l_Std_Mutex_atomically___redArg(v___x_2335_, v___f_2336_, v___f_2337_, v_requestStream_2334_, v___x_2339_);
v___x_2341_ = lean_apply_1(v___x_5182__overap_2340_, lean_box(0));
lean_inc_ref(v___y_2236_);
v___f_2342_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2342_, 0, v___y_2236_);
v___f_2343_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2343_, 0, v_requestStream_2334_);
lean_closure_set(v___f_2343_, 1, v___f_2342_);
lean_closure_set(v___f_2343_, 2, v___y_2236_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = 0;
v___x_2346_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2344_, v___x_2345_, v___x_2341_, v___f_2343_);
return v___x_2346_;
}
case 6:
{
lean_object* v_machine_2347_; lean_object* v_requestStream_2348_; lean_object* v_respStream_2349_; uint8_t v_requiresData_2350_; lean_object* v_expectData_2351_; lean_object* v_pendingHead_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_5203__overap_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___f_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v_connectionContext_2233_);
lean_dec_ref(v___f_2230_);
lean_dec(v_handler_2229_);
lean_dec_ref(v___f_2228_);
lean_dec_ref(v_inst_2227_);
v_machine_2347_ = lean_ctor_get(v___y_2236_, 0);
lean_inc_ref(v_machine_2347_);
v_requestStream_2348_ = lean_ctor_get(v___y_2236_, 1);
lean_inc_ref_n(v_requestStream_2348_, 2);
v_respStream_2349_ = lean_ctor_get(v___y_2236_, 6);
lean_inc(v_respStream_2349_);
v_requiresData_2350_ = lean_ctor_get_uint8(v___y_2236_, sizeof(void*)*9);
v_expectData_2351_ = lean_ctor_get(v___y_2236_, 7);
lean_inc(v_expectData_2351_);
v_pendingHead_2352_ = lean_ctor_get(v___y_2236_, 8);
lean_inc(v_pendingHead_2352_);
lean_dec_ref(v___y_2236_);
v___x_2353_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2354_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2355_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2356_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2357_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2357_, 0, lean_box(0));
lean_closure_set(v___x_2357_, 1, lean_box(0));
lean_closure_set(v___x_2357_, 2, v___x_2353_);
lean_closure_set(v___x_2357_, 3, lean_box(0));
lean_closure_set(v___x_2357_, 4, lean_box(0));
lean_closure_set(v___x_2357_, 5, v___x_2356_);
lean_closure_set(v___x_2357_, 6, v___f_2231_);
v___x_5203__overap_2358_ = l_Std_Mutex_atomically___redArg(v___x_2353_, v___f_2354_, v___f_2355_, v_requestStream_2348_, v___x_2357_);
v___x_2359_ = lean_apply_1(v___x_5203__overap_2358_, lean_box(0));
v___x_2360_ = lean_box(v_requiresData_2350_);
v___f_2361_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2361_, 0, v_config_2226_);
lean_closure_set(v___f_2361_, 1, v_machine_2347_);
lean_closure_set(v___f_2361_, 2, v___x_2360_);
lean_closure_set(v___f_2361_, 3, v_expectData_2351_);
lean_closure_set(v___f_2361_, 4, v_pendingHead_2352_);
v___f_2362_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2362_, 0, v___f_2361_);
lean_inc_ref(v___f_2362_);
v___f_2363_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2363_, 0, v___f_2362_);
v___f_2364_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2364_, 0, v_respStream_2349_);
lean_closure_set(v___f_2364_, 1, v_inst_2232_);
lean_closure_set(v___f_2364_, 2, v___f_2363_);
lean_closure_set(v___f_2364_, 3, v___f_2362_);
lean_inc_ref(v___f_2364_);
v___f_2365_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2365_, 0, v___f_2364_);
v___f_2366_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2366_, 0, v_requestStream_2348_);
lean_closure_set(v___f_2366_, 1, v___f_2365_);
lean_closure_set(v___f_2366_, 2, v___f_2364_);
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = 0;
v___x_2369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2367_, v___x_2368_, v___x_2359_, v___f_2366_);
return v___x_2369_;
}
case 7:
{
lean_object* v_pendingHead_2370_; 
lean_dec_ref(v_inst_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
lean_dec_ref(v___f_2228_);
v_pendingHead_2370_ = lean_ctor_get(v___y_2236_, 8);
if (lean_obj_tag(v_pendingHead_2370_) == 1)
{
lean_object* v_machine_2371_; lean_object* v_requestStream_2372_; lean_object* v_keepAliveTimeout_2373_; lean_object* v_currentTimeout_2374_; lean_object* v_headerTimeout_2375_; lean_object* v_response_2376_; lean_object* v_respStream_2377_; uint8_t v_requiresData_2378_; lean_object* v_expectData_2379_; uint8_t v_handlerDispatched_2380_; lean_object* v_val_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
lean_inc_ref(v_pendingHead_2370_);
v_machine_2371_ = lean_ctor_get(v___y_2236_, 0);
lean_inc_ref(v_machine_2371_);
v_requestStream_2372_ = lean_ctor_get(v___y_2236_, 1);
lean_inc_ref(v_requestStream_2372_);
v_keepAliveTimeout_2373_ = lean_ctor_get(v___y_2236_, 2);
lean_inc(v_keepAliveTimeout_2373_);
v_currentTimeout_2374_ = lean_ctor_get(v___y_2236_, 3);
lean_inc(v_currentTimeout_2374_);
v_headerTimeout_2375_ = lean_ctor_get(v___y_2236_, 4);
lean_inc(v_headerTimeout_2375_);
v_response_2376_ = lean_ctor_get(v___y_2236_, 5);
lean_inc_ref(v_response_2376_);
v_respStream_2377_ = lean_ctor_get(v___y_2236_, 6);
lean_inc(v_respStream_2377_);
v_requiresData_2378_ = lean_ctor_get_uint8(v___y_2236_, sizeof(void*)*9);
v_expectData_2379_ = lean_ctor_get(v___y_2236_, 7);
lean_inc(v_expectData_2379_);
v_handlerDispatched_2380_ = lean_ctor_get_uint8(v___y_2236_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2236_);
v_val_2381_ = lean_ctor_get(v_pendingHead_2370_, 0);
lean_inc(v_val_2381_);
v___x_2382_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2227_, v_handler_2229_, v_machine_2371_, v_val_2381_, v_config_2226_, v_connectionContext_2233_);
v___x_2383_ = lean_box(v_requiresData_2378_);
v___x_2384_ = lean_box(v_handlerDispatched_2380_);
v___f_2385_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2385_, 0, v_requestStream_2372_);
lean_closure_set(v___f_2385_, 1, v_keepAliveTimeout_2373_);
lean_closure_set(v___f_2385_, 2, v_currentTimeout_2374_);
lean_closure_set(v___f_2385_, 3, v_headerTimeout_2375_);
lean_closure_set(v___f_2385_, 4, v_response_2376_);
lean_closure_set(v___f_2385_, 5, v_respStream_2377_);
lean_closure_set(v___f_2385_, 6, v___x_2383_);
lean_closure_set(v___f_2385_, 7, v_expectData_2379_);
lean_closure_set(v___f_2385_, 8, v___x_2384_);
lean_closure_set(v___f_2385_, 9, v_pendingHead_2370_);
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = 0;
v___x_2388_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2386_, v___x_2387_, v___x_2382_, v___f_2385_);
return v___x_2388_;
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref(v_connectionContext_2233_);
lean_dec(v_handler_2229_);
lean_dec_ref(v_inst_2227_);
lean_dec_ref(v_config_2226_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___y_2236_);
v___x_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
default: 
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_connectionContext_2233_);
lean_dec_ref(v_inst_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
lean_dec(v_handler_2229_);
lean_dec_ref(v___f_2228_);
lean_dec_ref(v_inst_2227_);
lean_dec_ref(v_config_2226_);
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___y_2236_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2395_, lean_object* v_inst_2396_, lean_object* v___f_2397_, lean_object* v_handler_2398_, lean_object* v___f_2399_, lean_object* v___f_2400_, lean_object* v_inst_2401_, lean_object* v_connectionContext_2402_, lean_object* v_a_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2395_, v_inst_2396_, v___f_2397_, v_handler_2398_, v___f_2399_, v___f_2400_, v_inst_2401_, v_connectionContext_2402_, v_a_2403_, v_x_2404_, v___y_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_x_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_handler_2418_, lean_object* v_config_2419_, lean_object* v_connectionContext_2420_, lean_object* v_events_2421_, lean_object* v_state_2422_){
_start:
{
lean_object* v___f_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; size_t v_sz_2427_; size_t v___x_2428_; lean_object* v___x_4114__overap_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; 
v___f_2424_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2425_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2425_, 0, v_config_2419_);
lean_closure_set(v___f_2425_, 1, v_inst_2416_);
lean_closure_set(v___f_2425_, 2, v___f_2424_);
lean_closure_set(v___f_2425_, 3, v_handler_2418_);
lean_closure_set(v___f_2425_, 4, v___f_2424_);
lean_closure_set(v___f_2425_, 5, v___f_2424_);
lean_closure_set(v___f_2425_, 6, v_inst_2417_);
lean_closure_set(v___f_2425_, 7, v_connectionContext_2420_);
v___x_2426_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2427_ = lean_array_size(v_events_2421_);
v___x_2428_ = ((size_t)0ULL);
v___x_4114__overap_2429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2426_, v_events_2421_, v___f_2425_, v_sz_2427_, v___x_2428_, v_state_2422_);
v___x_2430_ = lean_apply_1(v___x_4114__overap_2429_, lean_box(0));
v___f_2431_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = 0;
v___x_2434_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2432_, v___x_2433_, v___x_2430_, v___f_2431_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_handler_2437_, lean_object* v_config_2438_, lean_object* v_connectionContext_2439_, lean_object* v_events_2440_, lean_object* v_state_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2435_, v_inst_2436_, v_handler_2437_, v_config_2438_, v_connectionContext_2439_, v_events_2440_, v_state_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_handler_2448_, lean_object* v_config_2449_, lean_object* v_connectionContext_2450_, lean_object* v_events_2451_, lean_object* v_state_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2446_, v_inst_2447_, v_handler_2448_, v_config_2449_, v_connectionContext_2450_, v_events_2451_, v_state_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2455_, lean_object* v_00_u03b2_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_handler_2459_, lean_object* v_config_2460_, lean_object* v_connectionContext_2461_, lean_object* v_events_2462_, lean_object* v_state_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2455_, v_00_u03b2_2456_, v_inst_2457_, v_inst_2458_, v_handler_2459_, v_config_2460_, v_connectionContext_2461_, v_events_2462_, v_state_2463_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2466_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v_x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v_x_2466_, 1);
v___x_2468_ = lean_task_pure(v_a_2467_);
return v___x_2468_;
}
else
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v_x_2466_, 0);
lean_inc_ref(v_a_2469_);
lean_dec_ref_known(v_x_2466_, 1);
return v_a_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2470_, lean_object* v_requestStream_2471_, lean_object* v_keepAliveTimeout_2472_, lean_object* v_currentTimeout_2473_, lean_object* v_headerTimeout_2474_, lean_object* v_response_2475_, lean_object* v_respStream_2476_, uint8_t v_requiresData_2477_, lean_object* v_expectData_2478_, lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_expectData_2478_);
lean_dec(v_respStream_2476_);
lean_dec_ref(v_response_2475_);
lean_dec(v_headerTimeout_2474_);
lean_dec(v_currentTimeout_2473_);
lean_dec(v_keepAliveTimeout_2472_);
lean_dec_ref(v_requestStream_2471_);
lean_dec_ref(v_machine_2470_);
v_a_2481_ = lean_ctor_get(v_x_2479_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_x_2479_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2483_ = v_x_2479_;
v_isShared_2484_ = v_isSharedCheck_2489_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v_x_2479_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2489_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
}
else
{
lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2500_; 
v_isSharedCheck_2500_ = !lean_is_exclusive(v_x_2479_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_x_2479_, 0);
lean_dec(v_unused_2501_);
v___x_2491_ = v_x_2479_;
v_isShared_2492_ = v_isSharedCheck_2500_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v_x_2479_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2500_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2493_ = 1;
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2495_, 0, v_machine_2470_);
lean_ctor_set(v___x_2495_, 1, v_requestStream_2471_);
lean_ctor_set(v___x_2495_, 2, v_keepAliveTimeout_2472_);
lean_ctor_set(v___x_2495_, 3, v_currentTimeout_2473_);
lean_ctor_set(v___x_2495_, 4, v_headerTimeout_2474_);
lean_ctor_set(v___x_2495_, 5, v_response_2475_);
lean_ctor_set(v___x_2495_, 6, v_respStream_2476_);
lean_ctor_set(v___x_2495_, 7, v_expectData_2478_);
lean_ctor_set(v___x_2495_, 8, v___x_2494_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*9, v_requiresData_2477_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*9 + 1, v___x_2493_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2495_);
v___x_2497_ = v___x_2491_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
return v___x_2498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2502_, lean_object* v_requestStream_2503_, lean_object* v_keepAliveTimeout_2504_, lean_object* v_currentTimeout_2505_, lean_object* v_headerTimeout_2506_, lean_object* v_response_2507_, lean_object* v_respStream_2508_, lean_object* v_requiresData_2509_, lean_object* v_expectData_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v_requiresData_boxed_2513_; lean_object* v_res_2514_; 
v_requiresData_boxed_2513_ = lean_unbox(v_requiresData_2509_);
v_res_2514_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2502_, v_requestStream_2503_, v_keepAliveTimeout_2504_, v_currentTimeout_2505_, v_headerTimeout_2506_, v_response_2507_, v_respStream_2508_, v_requiresData_boxed_2513_, v_expectData_2510_, v_x_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2515_, lean_object* v_response_2516_, lean_object* v___x_2517_, lean_object* v___f_2518_, lean_object* v_x_2519_){
_start:
{
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v___f_2518_);
lean_dec(v___x_2517_);
lean_dec_ref(v_response_2516_);
lean_dec_ref(v_toFunctor_2515_);
v_a_2521_ = lean_ctor_get(v_x_2519_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_x_2519_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2523_ = v_x_2519_;
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v_x_2519_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2544_; 
v_a_2530_ = lean_ctor_get(v_x_2519_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_x_2519_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2532_ = v_x_2519_;
v_isShared_2533_ = v_isSharedCheck_2544_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v_x_2519_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2544_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2534_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2534_, 0, lean_box(0));
lean_closure_set(v___x_2534_, 1, lean_box(0));
lean_closure_set(v___x_2534_, 2, v_toFunctor_2515_);
v___x_2535_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2535_, 0, lean_box(0));
lean_closure_set(v___x_2535_, 1, v_response_2516_);
v___x_2536_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2536_, 0, lean_box(0));
lean_closure_set(v___x_2536_, 1, lean_box(0));
lean_closure_set(v___x_2536_, 2, lean_box(0));
lean_closure_set(v___x_2536_, 3, v___x_2534_);
lean_closure_set(v___x_2536_, 4, v___x_2535_);
v___x_2537_ = 0;
lean_inc(v___x_2517_);
v___x_2538_ = l_BaseIO_chainTask___redArg(v_a_2530_, v___x_2536_, v___x_2517_, v___x_2537_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2538_);
v___x_2540_ = v___x_2532_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2517_, v___x_2537_, v___x_2541_, v___f_2518_);
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2545_, lean_object* v_response_2546_, lean_object* v___x_2547_, lean_object* v___f_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2545_, v_response_2546_, v___x_2547_, v___f_2548_, v_x_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2553_, lean_object* v_handler_2554_, lean_object* v_extensions_2555_, lean_object* v_connectionContext_2556_, lean_object* v_state_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v_toApplicative_2560_; lean_object* v_pendingHead_2561_; 
v___x_2559_ = l_instMonadBaseIO;
v_toApplicative_2560_ = lean_ctor_get(v___x_2559_, 0);
v_pendingHead_2561_ = lean_ctor_get(v_state_2557_, 8);
lean_inc(v_pendingHead_2561_);
if (lean_obj_tag(v_pendingHead_2561_) == 1)
{
lean_object* v_toFunctor_2562_; lean_object* v_machine_2563_; lean_object* v_requestStream_2564_; lean_object* v_keepAliveTimeout_2565_; lean_object* v_currentTimeout_2566_; lean_object* v_headerTimeout_2567_; lean_object* v_response_2568_; lean_object* v_respStream_2569_; uint8_t v_requiresData_2570_; lean_object* v_expectData_2571_; lean_object* v_val_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2594_; 
v_toFunctor_2562_ = lean_ctor_get(v_toApplicative_2560_, 0);
v_machine_2563_ = lean_ctor_get(v_state_2557_, 0);
lean_inc_ref(v_machine_2563_);
v_requestStream_2564_ = lean_ctor_get(v_state_2557_, 1);
lean_inc_ref(v_requestStream_2564_);
v_keepAliveTimeout_2565_ = lean_ctor_get(v_state_2557_, 2);
lean_inc(v_keepAliveTimeout_2565_);
v_currentTimeout_2566_ = lean_ctor_get(v_state_2557_, 3);
lean_inc(v_currentTimeout_2566_);
v_headerTimeout_2567_ = lean_ctor_get(v_state_2557_, 4);
lean_inc(v_headerTimeout_2567_);
v_response_2568_ = lean_ctor_get(v_state_2557_, 5);
lean_inc_ref(v_response_2568_);
v_respStream_2569_ = lean_ctor_get(v_state_2557_, 6);
lean_inc(v_respStream_2569_);
v_requiresData_2570_ = lean_ctor_get_uint8(v_state_2557_, sizeof(void*)*9);
v_expectData_2571_ = lean_ctor_get(v_state_2557_, 7);
lean_inc(v_expectData_2571_);
lean_dec_ref(v_state_2557_);
v_val_2572_ = lean_ctor_get(v_pendingHead_2561_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_pendingHead_2561_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2574_ = v_pendingHead_2561_;
v_isShared_2575_ = v_isSharedCheck_2594_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_val_2572_);
lean_dec(v_pendingHead_2561_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2594_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_onRequest_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___f_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v_onRequest_2576_ = lean_ctor_get(v_inst_2553_, 1);
lean_inc_ref(v_onRequest_2576_);
lean_dec_ref(v_inst_2553_);
lean_inc_ref(v_requestStream_2564_);
v___x_2577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2577_, 0, v_val_2572_);
lean_ctor_set(v___x_2577_, 1, v_requestStream_2564_);
lean_ctor_set(v___x_2577_, 2, v_extensions_2555_);
v___x_2578_ = lean_apply_3(v_onRequest_2576_, v_handler_2554_, v___x_2577_, v_connectionContext_2556_);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2580_, 0, lean_box(0));
lean_closure_set(v___x_2580_, 1, v___x_2578_);
v___x_2581_ = lean_io_as_task(v___x_2580_, v___x_2579_);
v___f_2582_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2583_ = lean_box(v_requiresData_2570_);
lean_inc_ref(v_response_2568_);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2584_, 0, v_machine_2563_);
lean_closure_set(v___f_2584_, 1, v_requestStream_2564_);
lean_closure_set(v___f_2584_, 2, v_keepAliveTimeout_2565_);
lean_closure_set(v___f_2584_, 3, v_currentTimeout_2566_);
lean_closure_set(v___f_2584_, 4, v_headerTimeout_2567_);
lean_closure_set(v___f_2584_, 5, v_response_2568_);
lean_closure_set(v___f_2584_, 6, v_respStream_2569_);
lean_closure_set(v___f_2584_, 7, v___x_2583_);
lean_closure_set(v___f_2584_, 8, v_expectData_2571_);
lean_inc_ref(v_toFunctor_2562_);
v___f_2585_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2585_, 0, v_toFunctor_2562_);
lean_closure_set(v___f_2585_, 1, v_response_2568_);
lean_closure_set(v___f_2585_, 2, v___x_2579_);
lean_closure_set(v___f_2585_, 3, v___f_2584_);
v___x_2586_ = 1;
v___x_2587_ = lean_task_bind(v___x_2581_, v___f_2582_, v___x_2579_, v___x_2586_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2587_);
v___x_2589_ = v___x_2574_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = 0;
v___x_2592_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2579_, v___x_2591_, v___x_2590_, v___f_2585_);
return v___x_2592_;
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec(v_pendingHead_2561_);
lean_dec_ref(v_connectionContext_2556_);
lean_dec(v_extensions_2555_);
lean_dec(v_handler_2554_);
lean_dec_ref(v_inst_2553_);
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_state_2557_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2597_, lean_object* v_handler_2598_, lean_object* v_extensions_2599_, lean_object* v_connectionContext_2600_, lean_object* v_state_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2597_, v_handler_2598_, v_extensions_2599_, v_connectionContext_2600_, v_state_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2604_, lean_object* v_inst_2605_, lean_object* v_handler_2606_, lean_object* v_extensions_2607_, lean_object* v_connectionContext_2608_, lean_object* v_state_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2605_, v_handler_2606_, v_extensions_2607_, v_connectionContext_2608_, v_state_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2612_, lean_object* v_inst_2613_, lean_object* v_handler_2614_, lean_object* v_extensions_2615_, lean_object* v_connectionContext_2616_, lean_object* v_state_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2612_, v_inst_2613_, v_handler_2614_, v_extensions_2615_, v_connectionContext_2616_, v_state_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2620_, lean_object* v_____r_2621_){
_start:
{
lean_object* v_writer_2623_; lean_object* v_reader_2624_; lean_object* v_config_2625_; lean_object* v_events_2626_; lean_object* v_error_2627_; lean_object* v_instant_2628_; uint8_t v_keepAlive_2629_; uint8_t v_forcedFlush_2630_; uint8_t v_pullBodyStalled_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2658_; 
v_writer_2623_ = lean_ctor_get(v_machine_2620_, 1);
v_reader_2624_ = lean_ctor_get(v_machine_2620_, 0);
v_config_2625_ = lean_ctor_get(v_machine_2620_, 2);
v_events_2626_ = lean_ctor_get(v_machine_2620_, 3);
v_error_2627_ = lean_ctor_get(v_machine_2620_, 4);
v_instant_2628_ = lean_ctor_get(v_machine_2620_, 5);
v_keepAlive_2629_ = lean_ctor_get_uint8(v_machine_2620_, sizeof(void*)*6);
v_forcedFlush_2630_ = lean_ctor_get_uint8(v_machine_2620_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2631_ = lean_ctor_get_uint8(v_machine_2620_, sizeof(void*)*6 + 2);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_machine_2620_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2633_ = v_machine_2620_;
v_isShared_2634_ = v_isSharedCheck_2658_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_instant_2628_);
lean_inc(v_error_2627_);
lean_inc(v_events_2626_);
lean_inc(v_config_2625_);
lean_inc(v_writer_2623_);
lean_inc(v_reader_2624_);
lean_dec(v_machine_2620_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2658_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_userData_2635_; lean_object* v_outputData_2636_; lean_object* v_state_2637_; lean_object* v_knownSize_2638_; lean_object* v_messageHead_2639_; uint8_t v_sentMessage_2640_; uint8_t v_omitBody_2641_; lean_object* v_userDataBytes_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2657_; 
v_userData_2635_ = lean_ctor_get(v_writer_2623_, 0);
v_outputData_2636_ = lean_ctor_get(v_writer_2623_, 1);
v_state_2637_ = lean_ctor_get(v_writer_2623_, 2);
v_knownSize_2638_ = lean_ctor_get(v_writer_2623_, 3);
v_messageHead_2639_ = lean_ctor_get(v_writer_2623_, 4);
v_sentMessage_2640_ = lean_ctor_get_uint8(v_writer_2623_, sizeof(void*)*6);
v_omitBody_2641_ = lean_ctor_get_uint8(v_writer_2623_, sizeof(void*)*6 + 2);
v_userDataBytes_2642_ = lean_ctor_get(v_writer_2623_, 5);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_writer_2623_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2644_ = v_writer_2623_;
v_isShared_2645_ = v_isSharedCheck_2657_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_userDataBytes_2642_);
lean_inc(v_messageHead_2639_);
lean_inc(v_knownSize_2638_);
lean_inc(v_state_2637_);
lean_inc(v_outputData_2636_);
lean_inc(v_userData_2635_);
lean_dec(v_writer_2623_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2657_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = 1;
if (v_isShared_2645_ == 0)
{
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_userData_2635_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_outputData_2636_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_state_2637_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_knownSize_2638_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_messageHead_2639_);
lean_ctor_set(v_reuseFailAlloc_2656_, 5, v_userDataBytes_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2656_, sizeof(void*)*6, v_sentMessage_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2656_, sizeof(void*)*6 + 2, v_omitBody_2641_);
v___x_2648_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2650_; 
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*6 + 1, v___x_2646_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 1, v___x_2648_);
v___x_2650_ = v___x_2633_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_reader_2624_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_config_2625_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_events_2626_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_error_2627_);
lean_ctor_set(v_reuseFailAlloc_2655_, 5, v_instant_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, sizeof(void*)*6, v_keepAlive_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, sizeof(void*)*6 + 1, v_forcedFlush_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, sizeof(void*)*6 + 2, v_pullBodyStalled_2631_);
v___x_2650_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2659_, lean_object* v_____r_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2659_, v_____r_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2663_, lean_object* v_x2_2664_){
_start:
{
lean_object* v_data_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_data_2665_ = lean_ctor_get(v_x2_2664_, 0);
v___x_2666_ = lean_byte_array_size(v_data_2665_);
v___x_2667_ = lean_nat_add(v_x1_2663_, v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2668_, lean_object* v_x2_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2668_, v_x2_2669_);
lean_dec_ref(v_x2_2669_);
lean_dec(v_x1_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2671_, lean_object* v_machine_2672_, lean_object* v_isClosed_2673_, lean_object* v___f_2674_, lean_object* v___f_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v___y_2679_; 
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v___f_2675_);
lean_dec_ref(v___f_2674_);
lean_dec_ref(v_isClosed_2673_);
lean_dec_ref(v_machine_2672_);
lean_dec(v_body_2671_);
v_a_2684_ = lean_ctor_get(v_x_2676_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_x_2676_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2686_ = v_x_2676_;
v_isShared_2687_ = v_isSharedCheck_2692_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v_x_2676_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2692_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2760_; 
v_a_2693_ = lean_ctor_get(v_x_2676_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_x_2676_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2695_ = v_x_2676_;
v_isShared_2696_ = v_isSharedCheck_2760_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v_x_2676_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2760_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
if (lean_obj_tag(v_a_2693_) == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec_ref(v___f_2675_);
lean_dec_ref(v___f_2674_);
lean_dec_ref(v_isClosed_2673_);
v___x_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_body_2671_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_machine_2672_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2698_);
v___x_2700_ = v___x_2695_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
else
{
lean_object* v_val_2703_; 
lean_del_object(v___x_2695_);
v_val_2703_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_val_2703_);
lean_dec_ref_known(v_a_2693_, 1);
if (lean_obj_tag(v_val_2703_) == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref(v___f_2675_);
lean_dec_ref(v_machine_2672_);
v___x_2704_ = lean_apply_2(v_isClosed_2673_, v_body_2671_, lean_box(0));
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = 0;
v___x_2707_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2705_, v___x_2706_, v___x_2704_, v___f_2674_);
return v___x_2707_;
}
else
{
lean_object* v_val_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
lean_dec_ref(v___f_2674_);
lean_dec_ref(v_isClosed_2673_);
v_val_2708_ = lean_ctor_get(v_val_2703_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_val_2703_, 1);
v___x_2709_ = lean_unsigned_to_nat(1u);
v___x_2710_ = lean_mk_empty_array_with_capacity(v___x_2709_);
v___x_2711_ = lean_array_push(v___x_2710_, v_val_2708_);
v___x_2712_ = lean_array_get_size(v___x_2711_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_nat_dec_eq(v___x_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v_reader_2715_; lean_object* v_writer_2716_; lean_object* v_config_2717_; lean_object* v_events_2718_; lean_object* v_error_2719_; lean_object* v_instant_2720_; uint8_t v_keepAlive_2721_; uint8_t v_forcedFlush_2722_; uint8_t v_pullBodyStalled_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2759_; 
v_reader_2715_ = lean_ctor_get(v_machine_2672_, 0);
v_writer_2716_ = lean_ctor_get(v_machine_2672_, 1);
v_config_2717_ = lean_ctor_get(v_machine_2672_, 2);
v_events_2718_ = lean_ctor_get(v_machine_2672_, 3);
v_error_2719_ = lean_ctor_get(v_machine_2672_, 4);
v_instant_2720_ = lean_ctor_get(v_machine_2672_, 5);
v_keepAlive_2721_ = lean_ctor_get_uint8(v_machine_2672_, sizeof(void*)*6);
v_forcedFlush_2722_ = lean_ctor_get_uint8(v_machine_2672_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2723_ = lean_ctor_get_uint8(v_machine_2672_, sizeof(void*)*6 + 2);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_machine_2672_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2725_ = v_machine_2672_;
v_isShared_2726_ = v_isSharedCheck_2759_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_instant_2720_);
lean_inc(v_error_2719_);
lean_inc(v_events_2718_);
lean_inc(v_config_2717_);
lean_inc(v_writer_2716_);
lean_inc(v_reader_2715_);
lean_dec(v_machine_2672_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2759_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___y_2728_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_2751_ = lean_nat_dec_lt(v___x_2713_, v___x_2712_);
if (v___x_2751_ == 0)
{
lean_dec_ref(v___f_2675_);
v___y_2728_ = v___x_2713_;
goto v___jp_2727_;
}
else
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_nat_dec_le(v___x_2712_, v___x_2712_);
if (v___x_2752_ == 0)
{
if (v___x_2751_ == 0)
{
lean_dec_ref(v___f_2675_);
v___y_2728_ = v___x_2713_;
goto v___jp_2727_;
}
else
{
size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = lean_usize_of_nat(v___x_2712_);
lean_inc_ref(v___x_2711_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2750_, v___f_2675_, v___x_2711_, v___x_2753_, v___x_2754_, v___x_2713_);
v___y_2728_ = v___x_2755_;
goto v___jp_2727_;
}
}
else
{
size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = lean_usize_of_nat(v___x_2712_);
lean_inc_ref(v___x_2711_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2750_, v___f_2675_, v___x_2711_, v___x_2756_, v___x_2757_, v___x_2713_);
v___y_2728_ = v___x_2758_;
goto v___jp_2727_;
}
}
v___jp_2727_:
{
lean_object* v_userData_2729_; lean_object* v_outputData_2730_; lean_object* v_state_2731_; lean_object* v_knownSize_2732_; lean_object* v_messageHead_2733_; uint8_t v_sentMessage_2734_; uint8_t v_userClosedBody_2735_; uint8_t v_omitBody_2736_; lean_object* v_userDataBytes_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2749_; 
v_userData_2729_ = lean_ctor_get(v_writer_2716_, 0);
v_outputData_2730_ = lean_ctor_get(v_writer_2716_, 1);
v_state_2731_ = lean_ctor_get(v_writer_2716_, 2);
v_knownSize_2732_ = lean_ctor_get(v_writer_2716_, 3);
v_messageHead_2733_ = lean_ctor_get(v_writer_2716_, 4);
v_sentMessage_2734_ = lean_ctor_get_uint8(v_writer_2716_, sizeof(void*)*6);
v_userClosedBody_2735_ = lean_ctor_get_uint8(v_writer_2716_, sizeof(void*)*6 + 1);
v_omitBody_2736_ = lean_ctor_get_uint8(v_writer_2716_, sizeof(void*)*6 + 2);
v_userDataBytes_2737_ = lean_ctor_get(v_writer_2716_, 5);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_writer_2716_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2739_ = v_writer_2716_;
v_isShared_2740_ = v_isSharedCheck_2749_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_userDataBytes_2737_);
lean_inc(v_messageHead_2733_);
lean_inc(v_knownSize_2732_);
lean_inc(v_state_2731_);
lean_inc(v_outputData_2730_);
lean_inc(v_userData_2729_);
lean_dec(v_writer_2716_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2749_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2741_ = l_Array_append___redArg(v_userData_2729_, v___x_2711_);
lean_dec_ref(v___x_2711_);
v___x_2742_ = lean_nat_add(v_userDataBytes_2737_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec(v_userDataBytes_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 5, v___x_2742_);
lean_ctor_set(v___x_2739_, 0, v___x_2741_);
v___x_2744_ = v___x_2739_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_outputData_2730_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_state_2731_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_knownSize_2732_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_messageHead_2733_);
lean_ctor_set(v_reuseFailAlloc_2748_, 5, v___x_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*6, v_sentMessage_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*6 + 1, v_userClosedBody_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*6 + 2, v_omitBody_2736_);
v___x_2744_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2746_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2744_);
v___x_2746_ = v___x_2725_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_reader_2715_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_config_2717_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_events_2718_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_error_2719_);
lean_ctor_set(v_reuseFailAlloc_2747_, 5, v_instant_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6, v_keepAlive_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6 + 1, v_forcedFlush_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6 + 2, v_pullBodyStalled_2723_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
v___y_2679_ = v___x_2746_;
goto v___jp_2678_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2711_);
lean_dec_ref(v___f_2675_);
v___y_2679_ = v_machine_2672_;
goto v___jp_2678_;
}
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_body_2671_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___y_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2761_, lean_object* v_machine_2762_, lean_object* v_isClosed_2763_, lean_object* v___f_2764_, lean_object* v___f_2765_, lean_object* v_x_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2761_, v_machine_2762_, v_isClosed_2763_, v___f_2764_, v___f_2765_, v_x_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2770_, lean_object* v_machine_2771_, lean_object* v_body_2772_){
_start:
{
lean_object* v_close_2774_; lean_object* v_isClosed_2775_; lean_object* v_tryRecv_2776_; lean_object* v___x_2777_; lean_object* v___f_2778_; lean_object* v___f_2779_; lean_object* v___f_2780_; lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; 
v_close_2774_ = lean_ctor_get(v_inst_2770_, 1);
lean_inc_ref(v_close_2774_);
v_isClosed_2775_ = lean_ctor_get(v_inst_2770_, 2);
lean_inc_ref(v_isClosed_2775_);
v_tryRecv_2776_ = lean_ctor_get(v_inst_2770_, 4);
lean_inc_ref(v_tryRecv_2776_);
lean_dec_ref(v_inst_2770_);
lean_inc_n(v_body_2772_, 2);
v___x_2777_ = lean_apply_2(v_tryRecv_2776_, v_body_2772_, lean_box(0));
lean_inc_ref(v_machine_2771_);
v___f_2778_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2778_, 0, v_machine_2771_);
lean_inc_ref(v___f_2778_);
v___f_2779_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2779_, 0, v___f_2778_);
v___f_2780_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2780_, 0, v_close_2774_);
lean_closure_set(v___f_2780_, 1, v_body_2772_);
lean_closure_set(v___f_2780_, 2, v___f_2779_);
lean_closure_set(v___f_2780_, 3, v___f_2778_);
v___f_2781_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2782_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2782_, 0, v_body_2772_);
lean_closure_set(v___f_2782_, 1, v_machine_2771_);
lean_closure_set(v___f_2782_, 2, v_isClosed_2775_);
lean_closure_set(v___f_2782_, 3, v___f_2780_);
lean_closure_set(v___f_2782_, 4, v___f_2781_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = 0;
v___x_2785_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2783_, v___x_2784_, v___x_2777_, v___f_2782_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2786_, lean_object* v_machine_2787_, lean_object* v_body_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2786_, v_machine_2787_, v_body_2788_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2791_, lean_object* v_inst_2792_, lean_object* v_machine_2793_, lean_object* v_body_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2792_, v_machine_2793_, v_body_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2797_, lean_object* v_inst_2798_, lean_object* v_machine_2799_, lean_object* v_body_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2797_, v_inst_2798_, v_machine_2799_, v_body_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2809_, lean_object* v_____r_2810_, lean_object* v_st_2811_){
_start:
{
lean_object* v_machine_2813_; lean_object* v_requestStream_2814_; lean_object* v_keepAliveTimeout_2815_; lean_object* v_currentTimeout_2816_; lean_object* v_headerTimeout_2817_; lean_object* v_response_2818_; lean_object* v_respStream_2819_; uint8_t v_requiresData_2820_; lean_object* v_expectData_2821_; uint8_t v_handlerDispatched_2822_; lean_object* v_pendingHead_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2905_; 
v_machine_2813_ = lean_ctor_get(v_st_2811_, 0);
v_requestStream_2814_ = lean_ctor_get(v_st_2811_, 1);
v_keepAliveTimeout_2815_ = lean_ctor_get(v_st_2811_, 2);
v_currentTimeout_2816_ = lean_ctor_get(v_st_2811_, 3);
v_headerTimeout_2817_ = lean_ctor_get(v_st_2811_, 4);
v_response_2818_ = lean_ctor_get(v_st_2811_, 5);
v_respStream_2819_ = lean_ctor_get(v_st_2811_, 6);
v_requiresData_2820_ = lean_ctor_get_uint8(v_st_2811_, sizeof(void*)*9);
v_expectData_2821_ = lean_ctor_get(v_st_2811_, 7);
v_handlerDispatched_2822_ = lean_ctor_get_uint8(v_st_2811_, sizeof(void*)*9 + 1);
v_pendingHead_2823_ = lean_ctor_get(v_st_2811_, 8);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_st_2811_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2825_ = v_st_2811_;
v_isShared_2826_ = v_isSharedCheck_2905_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_pendingHead_2823_);
lean_inc(v_expectData_2821_);
lean_inc(v_respStream_2819_);
lean_inc(v_response_2818_);
lean_inc(v_headerTimeout_2817_);
lean_inc(v_currentTimeout_2816_);
lean_inc(v_keepAliveTimeout_2815_);
lean_inc(v_requestStream_2814_);
lean_inc(v_machine_2813_);
lean_dec(v_st_2811_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2905_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___y_2828_; lean_object* v_reader_2837_; lean_object* v_state_2838_; 
v_reader_2837_ = lean_ctor_get(v_machine_2813_, 0);
lean_inc_ref(v_reader_2837_);
v_state_2838_ = lean_ctor_get(v_reader_2837_, 0);
lean_inc(v_state_2838_);
if (lean_obj_tag(v_state_2838_) == 6)
{
lean_dec_ref(v_reader_2837_);
lean_dec_ref(v_val_2809_);
v___y_2828_ = v_machine_2813_;
goto v___jp_2827_;
}
else
{
if (lean_obj_tag(v_state_2838_) == 7)
{
lean_dec_ref_known(v_state_2838_, 1);
lean_dec_ref(v_reader_2837_);
lean_dec_ref(v_val_2809_);
v___y_2828_ = v_machine_2813_;
goto v___jp_2827_;
}
else
{
lean_object* v_input_2839_; lean_object* v_writer_2840_; lean_object* v_config_2841_; lean_object* v_events_2842_; lean_object* v_error_2843_; lean_object* v_instant_2844_; uint8_t v_keepAlive_2845_; uint8_t v_forcedFlush_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2903_; 
v_input_2839_ = lean_ctor_get(v_reader_2837_, 1);
lean_inc_ref(v_input_2839_);
v_writer_2840_ = lean_ctor_get(v_machine_2813_, 1);
v_config_2841_ = lean_ctor_get(v_machine_2813_, 2);
v_events_2842_ = lean_ctor_get(v_machine_2813_, 3);
v_error_2843_ = lean_ctor_get(v_machine_2813_, 4);
v_instant_2844_ = lean_ctor_get(v_machine_2813_, 5);
v_keepAlive_2845_ = lean_ctor_get_uint8(v_machine_2813_, sizeof(void*)*6);
v_forcedFlush_2846_ = lean_ctor_get_uint8(v_machine_2813_, sizeof(void*)*6 + 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_machine_2813_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v_machine_2813_, 0);
lean_dec(v_unused_2904_);
v___x_2848_ = v_machine_2813_;
v_isShared_2849_ = v_isSharedCheck_2903_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_instant_2844_);
lean_inc(v_error_2843_);
lean_inc(v_events_2842_);
lean_inc(v_config_2841_);
lean_inc(v_writer_2840_);
lean_dec(v_machine_2813_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2903_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v_messageHead_2850_; lean_object* v_messageCount_2851_; lean_object* v_bodyBytesRead_2852_; lean_object* v_headerBytesRead_2853_; uint8_t v_noMoreInput_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2900_; 
v_messageHead_2850_ = lean_ctor_get(v_reader_2837_, 2);
v_messageCount_2851_ = lean_ctor_get(v_reader_2837_, 3);
v_bodyBytesRead_2852_ = lean_ctor_get(v_reader_2837_, 4);
v_headerBytesRead_2853_ = lean_ctor_get(v_reader_2837_, 5);
v_noMoreInput_2854_ = lean_ctor_get_uint8(v_reader_2837_, sizeof(void*)*6);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_reader_2837_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; lean_object* v_unused_2902_; 
v_unused_2901_ = lean_ctor_get(v_reader_2837_, 1);
lean_dec(v_unused_2901_);
v_unused_2902_ = lean_ctor_get(v_reader_2837_, 0);
lean_dec(v_unused_2902_);
v___x_2856_ = v_reader_2837_;
v_isShared_2857_ = v_isSharedCheck_2900_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_headerBytesRead_2853_);
lean_inc(v_bodyBytesRead_2852_);
lean_inc(v_messageCount_2851_);
lean_inc(v_messageHead_2850_);
lean_dec(v_reader_2837_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2900_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_array_2858_; lean_object* v_idx_2859_; uint8_t v___x_2860_; lean_object* v___y_2862_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_array_2858_ = lean_ctor_get(v_input_2839_, 0);
lean_inc_ref(v_array_2858_);
v_idx_2859_ = lean_ctor_get(v_input_2839_, 1);
lean_inc(v_idx_2859_);
lean_dec_ref(v_input_2839_);
v___x_2860_ = 0;
v___x_2891_ = lean_byte_array_size(v_array_2858_);
v___x_2892_ = lean_nat_dec_le(v___x_2891_, v_idx_2859_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2893_ = l_ByteArray_extract(v_array_2858_, v_idx_2859_, v___x_2891_);
lean_dec_ref(v_array_2858_);
v___x_2894_ = lean_unsigned_to_nat(0u);
v___x_2895_ = lean_byte_array_size(v___x_2893_);
v___x_2896_ = lean_byte_array_size(v_val_2809_);
v___x_2897_ = lean_byte_array_copy_slice(v_val_2809_, v___x_2894_, v___x_2893_, v___x_2895_, v___x_2896_, v___x_2892_);
lean_dec_ref(v_val_2809_);
v___x_2898_ = l_ByteArray_mkIterator(v___x_2897_);
v___y_2862_ = v___x_2898_;
goto v___jp_2861_;
}
else
{
lean_object* v___x_2899_; 
lean_dec(v_idx_2859_);
lean_dec_ref(v_array_2858_);
v___x_2899_ = l_ByteArray_mkIterator(v_val_2809_);
v___y_2862_ = v___x_2899_;
goto v___jp_2861_;
}
v___jp_2861_:
{
lean_object* v_maxHeaderBytes_2863_; lean_object* v_maxStartLineLength_2864_; lean_object* v_maxChunkLineLength_2865_; lean_object* v_maxBodySize_2866_; lean_object* v_array_2867_; lean_object* v_idx_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_maxHeaderBytes_2863_ = lean_ctor_get(v_config_2841_, 2);
v_maxStartLineLength_2864_ = lean_ctor_get(v_config_2841_, 5);
v_maxChunkLineLength_2865_ = lean_ctor_get(v_config_2841_, 13);
v_maxBodySize_2866_ = lean_ctor_get(v_config_2841_, 15);
v_array_2867_ = lean_ctor_get(v___y_2862_, 0);
v_idx_2868_ = lean_ctor_get(v___y_2862_, 1);
v___x_2869_ = lean_nat_add(v_maxBodySize_2866_, v_maxHeaderBytes_2863_);
v___x_2870_ = lean_nat_add(v___x_2869_, v_maxStartLineLength_2864_);
lean_dec(v___x_2869_);
v___x_2871_ = lean_nat_add(v___x_2870_, v_maxChunkLineLength_2865_);
lean_dec(v___x_2870_);
v___x_2872_ = lean_byte_array_size(v_array_2867_);
v___x_2873_ = lean_nat_sub(v___x_2872_, v_idx_2868_);
v___x_2874_ = lean_nat_dec_lt(v___x_2871_, v___x_2873_);
lean_dec(v___x_2873_);
lean_dec(v___x_2871_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2876_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___y_2862_);
v___x_2876_ = v___x_2856_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_state_2838_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___y_2862_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_messageHead_2850_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_messageCount_2851_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_bodyBytesRead_2852_);
lean_ctor_set(v_reuseFailAlloc_2880_, 5, v_headerBytesRead_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*6, v_noMoreInput_2854_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v_machine_2878_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2876_);
v_machine_2878_ = v___x_2848_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_writer_2840_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_config_2841_);
lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_events_2842_);
lean_ctor_set(v_reuseFailAlloc_2879_, 4, v_error_2843_);
lean_ctor_set(v_reuseFailAlloc_2879_, 5, v_instant_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2879_, sizeof(void*)*6, v_keepAlive_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2879_, sizeof(void*)*6 + 1, v_forcedFlush_2846_);
v_machine_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_ctor_set_uint8(v_machine_2878_, sizeof(void*)*6 + 2, v___x_2860_);
v___y_2828_ = v_machine_2878_;
goto v___jp_2827_;
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec(v_error_2843_);
lean_dec(v_state_2838_);
v___x_2881_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2882_ = lean_array_push(v_events_2842_, v___x_2881_);
v___x_2883_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___y_2862_);
lean_ctor_set(v___x_2856_, 0, v___x_2883_);
v___x_2885_ = v___x_2856_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___y_2862_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_messageHead_2850_);
lean_ctor_set(v_reuseFailAlloc_2890_, 3, v_messageCount_2851_);
lean_ctor_set(v_reuseFailAlloc_2890_, 4, v_bodyBytesRead_2852_);
lean_ctor_set(v_reuseFailAlloc_2890_, 5, v_headerBytesRead_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2890_, sizeof(void*)*6, v_noMoreInput_2854_);
v___x_2885_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2886_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 4, v___x_2886_);
lean_ctor_set(v___x_2848_, 3, v___x_2882_);
lean_ctor_set(v___x_2848_, 0, v___x_2885_);
v___x_2888_ = v___x_2848_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_writer_2840_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_config_2841_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2889_, 4, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2889_, 5, v_instant_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2889_, sizeof(void*)*6, v_keepAlive_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2889_, sizeof(void*)*6 + 1, v_forcedFlush_2846_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*6 + 2, v___x_2860_);
v___y_2828_ = v___x_2888_;
goto v___jp_2827_;
}
}
}
}
}
}
}
}
v___jp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___y_2828_);
v___x_2830_ = v___x_2825_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___y_2828_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_requestStream_2814_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_keepAliveTimeout_2815_);
lean_ctor_set(v_reuseFailAlloc_2836_, 3, v_currentTimeout_2816_);
lean_ctor_set(v_reuseFailAlloc_2836_, 4, v_headerTimeout_2817_);
lean_ctor_set(v_reuseFailAlloc_2836_, 5, v_response_2818_);
lean_ctor_set(v_reuseFailAlloc_2836_, 6, v_respStream_2819_);
lean_ctor_set(v_reuseFailAlloc_2836_, 7, v_expectData_2821_);
lean_ctor_set(v_reuseFailAlloc_2836_, 8, v_pendingHead_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*9, v_requiresData_2820_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*9 + 1, v_handlerDispatched_2822_);
v___x_2830_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2831_ = 0;
v___x_2832_ = lean_box(v___x_2831_);
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2830_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2906_, lean_object* v_____r_2907_, lean_object* v_st_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2906_, v_____r_2907_, v_st_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2911_, lean_object* v_machine_2912_, lean_object* v_requestStream_2913_, lean_object* v_currentTimeout_2914_, lean_object* v_response_2915_, lean_object* v_respStream_2916_, uint8_t v_requiresData_2917_, lean_object* v_expectData_2918_, uint8_t v_handlerDispatched_2919_, lean_object* v_pendingHead_2920_, lean_object* v___f_2921_, lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v___f_2921_);
lean_dec(v_pendingHead_2920_);
lean_dec(v_expectData_2918_);
lean_dec(v_respStream_2916_);
lean_dec_ref(v_response_2915_);
lean_dec(v_currentTimeout_2914_);
lean_dec_ref(v_requestStream_2913_);
lean_dec_ref(v_machine_2912_);
v_a_2924_ = lean_ctor_get(v_x_2922_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v_x_2922_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v_x_2922_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v_headerTimeout_2934_; lean_object* v_second_2935_; lean_object* v_nano_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_second_2940_; lean_object* v_nano_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_a_2933_ = lean_ctor_get(v_x_2922_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v_x_2922_, 1);
v_headerTimeout_2934_ = lean_ctor_get(v_config_2911_, 6);
v_second_2935_ = lean_ctor_get(v_a_2933_, 0);
lean_inc(v_second_2935_);
v_nano_2936_ = lean_ctor_get(v_a_2933_, 1);
lean_inc(v_nano_2936_);
lean_dec(v_a_2933_);
v___x_2937_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2938_ = lean_int_mul(v_headerTimeout_2934_, v___x_2937_);
v___x_2939_ = l_Std_Time_Duration_ofNanoseconds(v___x_2938_);
lean_dec(v___x_2938_);
v_second_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_second_2940_);
v_nano_2941_ = lean_ctor_get(v___x_2939_, 1);
lean_inc(v_nano_2941_);
lean_dec_ref(v___x_2939_);
v___x_2942_ = lean_box(0);
v___x_2943_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2944_ = lean_int_mul(v_second_2935_, v___x_2943_);
lean_dec(v_second_2935_);
v___x_2945_ = lean_int_add(v___x_2944_, v_nano_2936_);
lean_dec(v_nano_2936_);
lean_dec(v___x_2944_);
v___x_2946_ = lean_int_mul(v_second_2940_, v___x_2943_);
lean_dec(v_second_2940_);
v___x_2947_ = lean_int_add(v___x_2946_, v_nano_2941_);
lean_dec(v_nano_2941_);
lean_dec(v___x_2946_);
v___x_2948_ = lean_int_add(v___x_2945_, v___x_2947_);
lean_dec(v___x_2947_);
lean_dec(v___x_2945_);
v___x_2949_ = l_Std_Time_Duration_ofNanoseconds(v___x_2948_);
lean_dec(v___x_2948_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2951_, 0, v_machine_2912_);
lean_ctor_set(v___x_2951_, 1, v_requestStream_2913_);
lean_ctor_set(v___x_2951_, 2, v___x_2942_);
lean_ctor_set(v___x_2951_, 3, v_currentTimeout_2914_);
lean_ctor_set(v___x_2951_, 4, v___x_2950_);
lean_ctor_set(v___x_2951_, 5, v_response_2915_);
lean_ctor_set(v___x_2951_, 6, v_respStream_2916_);
lean_ctor_set(v___x_2951_, 7, v_expectData_2918_);
lean_ctor_set(v___x_2951_, 8, v_pendingHead_2920_);
lean_ctor_set_uint8(v___x_2951_, sizeof(void*)*9, v_requiresData_2917_);
lean_ctor_set_uint8(v___x_2951_, sizeof(void*)*9 + 1, v_handlerDispatched_2919_);
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_apply_3(v___f_2921_, v___x_2952_, v___x_2951_, lean_box(0));
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2954_, lean_object* v_machine_2955_, lean_object* v_requestStream_2956_, lean_object* v_currentTimeout_2957_, lean_object* v_response_2958_, lean_object* v_respStream_2959_, lean_object* v_requiresData_2960_, lean_object* v_expectData_2961_, lean_object* v_handlerDispatched_2962_, lean_object* v_pendingHead_2963_, lean_object* v___f_2964_, lean_object* v_x_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v_requiresData_boxed_2967_; uint8_t v_handlerDispatched_boxed_2968_; lean_object* v_res_2969_; 
v_requiresData_boxed_2967_ = lean_unbox(v_requiresData_2960_);
v_handlerDispatched_boxed_2968_ = lean_unbox(v_handlerDispatched_2962_);
v_res_2969_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2954_, v_machine_2955_, v_requestStream_2956_, v_currentTimeout_2957_, v_response_2958_, v_respStream_2959_, v_requiresData_boxed_2967_, v_expectData_2961_, v_handlerDispatched_boxed_2968_, v_pendingHead_2963_, v___f_2964_, v_x_2965_);
lean_dec_ref(v_config_2954_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2970_, lean_object* v_requestStream_2971_, lean_object* v_keepAliveTimeout_2972_, lean_object* v_currentTimeout_2973_, lean_object* v_headerTimeout_2974_, lean_object* v_response_2975_, uint8_t v_requiresData_2976_, lean_object* v_expectData_2977_, uint8_t v_handlerDispatched_2978_, lean_object* v_pendingHead_2979_, lean_object* v_____r_2980_){
_start:
{
lean_object* v_writer_2982_; lean_object* v_reader_2983_; lean_object* v_config_2984_; lean_object* v_events_2985_; lean_object* v_error_2986_; lean_object* v_instant_2987_; uint8_t v_keepAlive_2988_; uint8_t v_forcedFlush_2989_; uint8_t v_pullBodyStalled_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3020_; 
v_writer_2982_ = lean_ctor_get(v_machine_2970_, 1);
v_reader_2983_ = lean_ctor_get(v_machine_2970_, 0);
v_config_2984_ = lean_ctor_get(v_machine_2970_, 2);
v_events_2985_ = lean_ctor_get(v_machine_2970_, 3);
v_error_2986_ = lean_ctor_get(v_machine_2970_, 4);
v_instant_2987_ = lean_ctor_get(v_machine_2970_, 5);
v_keepAlive_2988_ = lean_ctor_get_uint8(v_machine_2970_, sizeof(void*)*6);
v_forcedFlush_2989_ = lean_ctor_get_uint8(v_machine_2970_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2990_ = lean_ctor_get_uint8(v_machine_2970_, sizeof(void*)*6 + 2);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_machine_2970_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2992_ = v_machine_2970_;
v_isShared_2993_ = v_isSharedCheck_3020_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_instant_2987_);
lean_inc(v_error_2986_);
lean_inc(v_events_2985_);
lean_inc(v_config_2984_);
lean_inc(v_writer_2982_);
lean_inc(v_reader_2983_);
lean_dec(v_machine_2970_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3020_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_userData_2994_; lean_object* v_outputData_2995_; lean_object* v_state_2996_; lean_object* v_knownSize_2997_; lean_object* v_messageHead_2998_; uint8_t v_sentMessage_2999_; uint8_t v_omitBody_3000_; lean_object* v_userDataBytes_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3019_; 
v_userData_2994_ = lean_ctor_get(v_writer_2982_, 0);
v_outputData_2995_ = lean_ctor_get(v_writer_2982_, 1);
v_state_2996_ = lean_ctor_get(v_writer_2982_, 2);
v_knownSize_2997_ = lean_ctor_get(v_writer_2982_, 3);
v_messageHead_2998_ = lean_ctor_get(v_writer_2982_, 4);
v_sentMessage_2999_ = lean_ctor_get_uint8(v_writer_2982_, sizeof(void*)*6);
v_omitBody_3000_ = lean_ctor_get_uint8(v_writer_2982_, sizeof(void*)*6 + 2);
v_userDataBytes_3001_ = lean_ctor_get(v_writer_2982_, 5);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_writer_2982_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3003_ = v_writer_2982_;
v_isShared_3004_ = v_isSharedCheck_3019_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_userDataBytes_3001_);
lean_inc(v_messageHead_2998_);
lean_inc(v_knownSize_2997_);
lean_inc(v_state_2996_);
lean_inc(v_outputData_2995_);
lean_inc(v_userData_2994_);
lean_dec(v_writer_2982_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3019_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
uint8_t v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = 1;
if (v_isShared_3004_ == 0)
{
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_userData_2994_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_outputData_2995_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_state_2996_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_knownSize_2997_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_messageHead_2998_);
lean_ctor_set(v_reuseFailAlloc_3018_, 5, v_userDataBytes_3001_);
lean_ctor_set_uint8(v_reuseFailAlloc_3018_, sizeof(void*)*6, v_sentMessage_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3018_, sizeof(void*)*6 + 2, v_omitBody_3000_);
v___x_3007_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3009_; 
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*6 + 1, v___x_3005_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3007_);
v___x_3009_ = v___x_2992_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_reader_2983_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v_config_2984_);
lean_ctor_set(v_reuseFailAlloc_3017_, 3, v_events_2985_);
lean_ctor_set(v_reuseFailAlloc_3017_, 4, v_error_2986_);
lean_ctor_set(v_reuseFailAlloc_3017_, 5, v_instant_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3017_, sizeof(void*)*6, v_keepAlive_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_3017_, sizeof(void*)*6 + 1, v_forcedFlush_2989_);
lean_ctor_set_uint8(v_reuseFailAlloc_3017_, sizeof(void*)*6 + 2, v_pullBodyStalled_2990_);
v___x_3009_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v_requestStream_2971_);
lean_ctor_set(v___x_3011_, 2, v_keepAliveTimeout_2972_);
lean_ctor_set(v___x_3011_, 3, v_currentTimeout_2973_);
lean_ctor_set(v___x_3011_, 4, v_headerTimeout_2974_);
lean_ctor_set(v___x_3011_, 5, v_response_2975_);
lean_ctor_set(v___x_3011_, 6, v___x_3010_);
lean_ctor_set(v___x_3011_, 7, v_expectData_2977_);
lean_ctor_set(v___x_3011_, 8, v_pendingHead_2979_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*9, v_requiresData_2976_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*9 + 1, v_handlerDispatched_2978_);
v___x_3012_ = 0;
v___x_3013_ = lean_box(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3011_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_3021_, lean_object* v_requestStream_3022_, lean_object* v_keepAliveTimeout_3023_, lean_object* v_currentTimeout_3024_, lean_object* v_headerTimeout_3025_, lean_object* v_response_3026_, lean_object* v_requiresData_3027_, lean_object* v_expectData_3028_, lean_object* v_handlerDispatched_3029_, lean_object* v_pendingHead_3030_, lean_object* v_____r_3031_, lean_object* v___y_3032_){
_start:
{
uint8_t v_requiresData_boxed_3033_; uint8_t v_handlerDispatched_boxed_3034_; lean_object* v_res_3035_; 
v_requiresData_boxed_3033_ = lean_unbox(v_requiresData_3027_);
v_handlerDispatched_boxed_3034_ = lean_unbox(v_handlerDispatched_3029_);
v_res_3035_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3021_, v_requestStream_3022_, v_keepAliveTimeout_3023_, v_currentTimeout_3024_, v_headerTimeout_3025_, v_response_3026_, v_requiresData_boxed_3033_, v_expectData_3028_, v_handlerDispatched_boxed_3034_, v_pendingHead_3030_, v_____r_3031_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_3036_, lean_object* v_x_3037_){
_start:
{
if (lean_obj_tag(v_x_3037_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___f_3036_);
v_a_3039_ = lean_ctor_get(v_x_3037_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_x_3037_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3041_ = v_x_3037_;
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v_x_3037_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v_x_3037_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v_x_3037_, 1);
v___x_3049_ = lean_apply_2(v___f_3036_, v_a_3048_, lean_box(0));
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_3050_, lean_object* v_x_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_3050_, v_x_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_3054_, lean_object* v_val_3055_, lean_object* v___f_3056_, lean_object* v___f_3057_, lean_object* v_x_3058_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___f_3057_);
lean_dec_ref(v___f_3056_);
lean_dec(v_val_3055_);
lean_dec_ref(v_close_3054_);
v_a_3060_ = lean_ctor_get(v_x_3058_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_x_3058_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3062_ = v_x_3058_;
v_isShared_3063_ = v_isSharedCheck_3068_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v_x_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3068_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
}
else
{
lean_object* v_a_3069_; uint8_t v___x_3070_; 
v_a_3069_ = lean_ctor_get(v_x_3058_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v_x_3058_, 1);
v___x_3070_ = lean_unbox(v_a_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; 
lean_dec_ref(v___f_3057_);
v___x_3071_ = lean_apply_2(v_close_3054_, v_val_3055_, lean_box(0));
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = lean_unbox(v_a_3069_);
lean_dec(v_a_3069_);
v___x_3074_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3072_, v___x_3073_, v___x_3071_, v___f_3056_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec(v_a_3069_);
lean_dec_ref(v___f_3056_);
lean_dec(v_val_3055_);
lean_dec_ref(v_close_3054_);
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_apply_2(v___f_3057_, v___x_3075_, lean_box(0));
return v___x_3076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_3077_, lean_object* v_val_3078_, lean_object* v___f_3079_, lean_object* v___f_3080_, lean_object* v_x_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_3077_, v_val_3078_, v___f_3079_, v___f_3080_, v_x_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_3084_, lean_object* v_handler_3085_, lean_object* v_x_3086_){
_start:
{
if (lean_obj_tag(v_x_3086_) == 0)
{
lean_object* v_a_3088_; lean_object* v_onFailure_3089_; lean_object* v___x_3090_; 
v_a_3088_ = lean_ctor_get(v_x_3086_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v_x_3086_, 1);
v_onFailure_3089_ = lean_ctor_get(v_inst_3084_, 2);
lean_inc_ref(v_onFailure_3089_);
lean_dec_ref(v_inst_3084_);
v___x_3090_ = lean_apply_3(v_onFailure_3089_, v_handler_3085_, v_a_3088_, lean_box(0));
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; 
lean_dec(v_handler_3085_);
lean_dec_ref(v_inst_3084_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_x_3086_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_3092_, lean_object* v_handler_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_3092_, v_handler_3093_, v_x_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_3097_, lean_object* v_____r_3098_){
_start:
{
uint8_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3100_ = 0;
v___x_3101_ = lean_box(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_st_3097_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_3105_, lean_object* v_____r_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3105_, v_____r_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_3109_, lean_object* v___f_3110_, lean_object* v___f_3111_, lean_object* v_x_3112_){
_start:
{
if (lean_obj_tag(v_x_3112_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v___f_3111_);
lean_dec_ref(v___f_3110_);
lean_dec_ref(v_requestStream_3109_);
v_a_3114_ = lean_ctor_get(v_x_3112_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_x_3112_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3116_ = v_x_3112_;
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v_x_3112_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3123_; uint8_t v___x_3124_; 
v_a_3123_ = lean_ctor_get(v_x_3112_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v_x_3112_, 1);
v___x_3124_ = lean_unbox(v_a_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v___f_3111_);
v___x_3125_ = l_Std_Http_Body_Stream_close(v_requestStream_3109_);
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = lean_unbox(v_a_3123_);
lean_dec(v_a_3123_);
v___x_3128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3126_, v___x_3127_, v___x_3125_, v___f_3110_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec(v_a_3123_);
lean_dec_ref(v___f_3110_);
lean_dec_ref(v_requestStream_3109_);
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_apply_2(v___f_3111_, v___x_3129_, lean_box(0));
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_3131_, lean_object* v___f_3132_, lean_object* v___f_3133_, lean_object* v_x_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_3131_, v___f_3132_, v___f_3133_, v_x_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_3137_, lean_object* v___f_3138_, lean_object* v___f_3139_, lean_object* v_requestStream_3140_, lean_object* v___f_3141_, lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3142_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___f_3141_);
lean_dec_ref(v_requestStream_3140_);
lean_dec_ref(v___f_3139_);
lean_dec_ref(v___f_3138_);
v_a_3144_ = lean_ctor_get(v_x_3142_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_x_3142_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3146_ = v_x_3142_;
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v_x_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
}
else
{
lean_dec_ref_known(v_x_3142_, 1);
if (v_final_3137_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v___f_3141_);
lean_dec_ref(v_requestStream_3140_);
lean_dec_ref(v___f_3139_);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_apply_2(v___f_3138_, v___x_3153_, lean_box(0));
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_7913__overap_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; 
lean_dec_ref(v___f_3138_);
v___x_3155_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3156_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3157_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3158_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3159_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3159_, 0, lean_box(0));
lean_closure_set(v___x_3159_, 1, lean_box(0));
lean_closure_set(v___x_3159_, 2, v___x_3155_);
lean_closure_set(v___x_3159_, 3, lean_box(0));
lean_closure_set(v___x_3159_, 4, lean_box(0));
lean_closure_set(v___x_3159_, 5, v___x_3158_);
lean_closure_set(v___x_3159_, 6, v___f_3139_);
v___x_7913__overap_3160_ = l_Std_Mutex_atomically___redArg(v___x_3155_, v___f_3156_, v___f_3157_, v_requestStream_3140_, v___x_3159_);
v___x_3161_ = lean_apply_1(v___x_7913__overap_3160_, lean_box(0));
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = 0;
v___x_3164_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3162_, v___x_3163_, v___x_3161_, v___f_3141_);
return v___x_3164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3165_, lean_object* v___f_3166_, lean_object* v___f_3167_, lean_object* v_requestStream_3168_, lean_object* v___f_3169_, lean_object* v_x_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v_final_boxed_3172_; lean_object* v_res_3173_; 
v_final_boxed_3172_ = lean_unbox(v_final_3165_);
v_res_3173_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3172_, v___f_3166_, v___f_3167_, v_requestStream_3168_, v___f_3169_, v_x_3170_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3174_, lean_object* v_x_3175_){
_start:
{
if (lean_obj_tag(v_x_3175_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v_state_3174_);
v_a_3177_ = lean_ctor_get(v_x_3175_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3179_ = v_x_3175_;
v_isShared_3180_ = v_isSharedCheck_3185_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v_x_3175_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3185_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
else
{
lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3215_; 
v_isSharedCheck_3215_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v_x_3175_, 0);
lean_dec(v_unused_3216_);
v___x_3187_ = v_x_3175_;
v_isShared_3188_ = v_isSharedCheck_3215_;
goto v_resetjp_3186_;
}
else
{
lean_dec(v_x_3175_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3215_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_machine_3189_; lean_object* v_requestStream_3190_; lean_object* v_keepAliveTimeout_3191_; lean_object* v_currentTimeout_3192_; lean_object* v_headerTimeout_3193_; lean_object* v_response_3194_; lean_object* v_respStream_3195_; uint8_t v_requiresData_3196_; lean_object* v_expectData_3197_; lean_object* v_pendingHead_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3214_; 
v_machine_3189_ = lean_ctor_get(v_state_3174_, 0);
v_requestStream_3190_ = lean_ctor_get(v_state_3174_, 1);
v_keepAliveTimeout_3191_ = lean_ctor_get(v_state_3174_, 2);
v_currentTimeout_3192_ = lean_ctor_get(v_state_3174_, 3);
v_headerTimeout_3193_ = lean_ctor_get(v_state_3174_, 4);
v_response_3194_ = lean_ctor_get(v_state_3174_, 5);
v_respStream_3195_ = lean_ctor_get(v_state_3174_, 6);
v_requiresData_3196_ = lean_ctor_get_uint8(v_state_3174_, sizeof(void*)*9);
v_expectData_3197_ = lean_ctor_get(v_state_3174_, 7);
v_pendingHead_3198_ = lean_ctor_get(v_state_3174_, 8);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_state_3174_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3200_ = v_state_3174_;
v_isShared_3201_ = v_isSharedCheck_3214_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_pendingHead_3198_);
lean_inc(v_expectData_3197_);
lean_inc(v_respStream_3195_);
lean_inc(v_response_3194_);
lean_inc(v_headerTimeout_3193_);
lean_inc(v_currentTimeout_3192_);
lean_inc(v_keepAliveTimeout_3191_);
lean_inc(v_requestStream_3190_);
lean_inc(v_machine_3189_);
lean_dec(v_state_3174_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3214_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; lean_object* v___x_3206_; 
v___x_3202_ = lean_box(52);
v___x_3203_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3189_, v___x_3202_);
v___x_3204_ = 0;
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3203_);
v___x_3206_ = v___x_3200_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_requestStream_3190_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_keepAliveTimeout_3191_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v_currentTimeout_3192_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v_headerTimeout_3193_);
lean_ctor_set(v_reuseFailAlloc_3213_, 5, v_response_3194_);
lean_ctor_set(v_reuseFailAlloc_3213_, 6, v_respStream_3195_);
lean_ctor_set(v_reuseFailAlloc_3213_, 7, v_expectData_3197_);
lean_ctor_set(v_reuseFailAlloc_3213_, 8, v_pendingHead_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3213_, sizeof(void*)*9, v_requiresData_3196_);
v___x_3206_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
lean_ctor_set_uint8(v___x_3206_, sizeof(void*)*9 + 1, v___x_3204_);
v___x_3207_ = lean_box(v___x_3204_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3208_);
v___x_3210_ = v___x_3187_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3217_, lean_object* v_x_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3217_, v_x_3218_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3221_, lean_object* v_requestStream_3222_, lean_object* v_keepAliveTimeout_3223_, lean_object* v_currentTimeout_3224_, lean_object* v_headerTimeout_3225_, lean_object* v_response_3226_, lean_object* v_respStream_3227_, uint8_t v_requiresData_3228_, lean_object* v_expectData_3229_, lean_object* v_pendingHead_3230_, lean_object* v_____r_3231_){
_start:
{
uint8_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3233_ = 0;
v___x_3234_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3234_, 0, v_machine_3221_);
lean_ctor_set(v___x_3234_, 1, v_requestStream_3222_);
lean_ctor_set(v___x_3234_, 2, v_keepAliveTimeout_3223_);
lean_ctor_set(v___x_3234_, 3, v_currentTimeout_3224_);
lean_ctor_set(v___x_3234_, 4, v_headerTimeout_3225_);
lean_ctor_set(v___x_3234_, 5, v_response_3226_);
lean_ctor_set(v___x_3234_, 6, v_respStream_3227_);
lean_ctor_set(v___x_3234_, 7, v_expectData_3229_);
lean_ctor_set(v___x_3234_, 8, v_pendingHead_3230_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*9, v_requiresData_3228_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*9 + 1, v___x_3233_);
v___x_3235_ = lean_box(v___x_3233_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3239_, lean_object* v_requestStream_3240_, lean_object* v_keepAliveTimeout_3241_, lean_object* v_currentTimeout_3242_, lean_object* v_headerTimeout_3243_, lean_object* v_response_3244_, lean_object* v_respStream_3245_, lean_object* v_requiresData_3246_, lean_object* v_expectData_3247_, lean_object* v_pendingHead_3248_, lean_object* v_____r_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_requiresData_boxed_3251_; lean_object* v_res_3252_; 
v_requiresData_boxed_3251_ = lean_unbox(v_requiresData_3246_);
v_res_3252_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3239_, v_requestStream_3240_, v_keepAliveTimeout_3241_, v_currentTimeout_3242_, v_headerTimeout_3243_, v_response_3244_, v_respStream_3245_, v_requiresData_boxed_3251_, v_expectData_3247_, v_pendingHead_3248_, v_____r_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3253_, lean_object* v_body_3254_, lean_object* v___f_3255_, lean_object* v___f_3256_, lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v___f_3256_);
lean_dec_ref(v___f_3255_);
lean_dec(v_body_3254_);
lean_dec_ref(v_close_3253_);
v_a_3259_ = lean_ctor_get(v_x_3257_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_x_3257_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3261_ = v_x_3257_;
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v_x_3257_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
return v___x_3265_;
}
}
}
else
{
lean_object* v_a_3268_; uint8_t v___x_3269_; 
v_a_3268_ = lean_ctor_get(v_x_3257_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v_x_3257_, 1);
v___x_3269_ = lean_unbox(v_a_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; 
lean_dec_ref(v___f_3256_);
v___x_3270_ = lean_apply_2(v_close_3253_, v_body_3254_, lean_box(0));
v___x_3271_ = lean_unsigned_to_nat(0u);
v___x_3272_ = lean_unbox(v_a_3268_);
lean_dec(v_a_3268_);
v___x_3273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3271_, v___x_3272_, v___x_3270_, v___f_3255_);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v_a_3268_);
lean_dec_ref(v___f_3255_);
lean_dec(v_body_3254_);
lean_dec_ref(v_close_3253_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_apply_2(v___f_3256_, v___x_3274_, lean_box(0));
return v___x_3275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3276_, lean_object* v_body_3277_, lean_object* v___f_3278_, lean_object* v___f_3279_, lean_object* v_x_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3276_, v_body_3277_, v___f_3278_, v___f_3279_, v_x_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3283_, lean_object* v_keepAliveTimeout_3284_, lean_object* v_currentTimeout_3285_, lean_object* v_headerTimeout_3286_, lean_object* v_response_3287_, uint8_t v_requiresData_3288_, lean_object* v_expectData_3289_, uint8_t v___x_3290_, lean_object* v_pendingHead_3291_, lean_object* v_____x_3292_){
_start:
{
lean_object* v_snd_3294_; lean_object* v_fst_3295_; lean_object* v_fst_3296_; lean_object* v_snd_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3307_; 
v_snd_3294_ = lean_ctor_get(v_____x_3292_, 1);
lean_inc(v_snd_3294_);
v_fst_3295_ = lean_ctor_get(v_____x_3292_, 0);
lean_inc(v_fst_3295_);
lean_dec_ref(v_____x_3292_);
v_fst_3296_ = lean_ctor_get(v_snd_3294_, 0);
v_snd_3297_ = lean_ctor_get(v_snd_3294_, 1);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_snd_3294_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3299_ = v_snd_3294_;
v_isShared_3300_ = v_isSharedCheck_3307_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_snd_3297_);
lean_inc(v_fst_3296_);
lean_dec(v_snd_3294_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3307_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3301_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3301_, 0, v_fst_3295_);
lean_ctor_set(v___x_3301_, 1, v_requestStream_3283_);
lean_ctor_set(v___x_3301_, 2, v_keepAliveTimeout_3284_);
lean_ctor_set(v___x_3301_, 3, v_currentTimeout_3285_);
lean_ctor_set(v___x_3301_, 4, v_headerTimeout_3286_);
lean_ctor_set(v___x_3301_, 5, v_response_3287_);
lean_ctor_set(v___x_3301_, 6, v_fst_3296_);
lean_ctor_set(v___x_3301_, 7, v_expectData_3289_);
lean_ctor_set(v___x_3301_, 8, v_pendingHead_3291_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*9, v_requiresData_3288_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*9 + 1, v___x_3290_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3301_);
v___x_3303_ = v___x_3299_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_snd_3297_);
v___x_3303_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3308_, lean_object* v_keepAliveTimeout_3309_, lean_object* v_currentTimeout_3310_, lean_object* v_headerTimeout_3311_, lean_object* v_response_3312_, lean_object* v_requiresData_3313_, lean_object* v_expectData_3314_, lean_object* v___x_3315_, lean_object* v_pendingHead_3316_, lean_object* v_____x_3317_, lean_object* v___y_3318_){
_start:
{
uint8_t v_requiresData_boxed_3319_; uint8_t v___x_8729__boxed_3320_; lean_object* v_res_3321_; 
v_requiresData_boxed_3319_ = lean_unbox(v_requiresData_3313_);
v___x_8729__boxed_3320_ = lean_unbox(v___x_3315_);
v_res_3321_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3308_, v_keepAliveTimeout_3309_, v_currentTimeout_3310_, v_headerTimeout_3311_, v_response_3312_, v_requiresData_boxed_3319_, v_expectData_3314_, v___x_8729__boxed_3320_, v_pendingHead_3316_, v_____x_3317_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3322_, lean_object* v_x_3323_){
_start:
{
if (lean_obj_tag(v_x_3323_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v___f_3322_);
v_a_3325_ = lean_ctor_get(v_x_3323_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_x_3323_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3327_ = v_x_3323_;
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v_x_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3335_; 
v_a_3334_ = lean_ctor_get(v_x_3323_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v_x_3323_, 1);
v___x_3335_ = lean_apply_2(v___f_3322_, v_a_3334_, lean_box(0));
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3336_, lean_object* v_x_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3336_, v_x_3337_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3340_, lean_object* v_x_3341_){
_start:
{
if (lean_obj_tag(v_x_3341_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3351_; 
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
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3371_; 
v_a_3352_ = lean_ctor_get(v_x_3341_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_x_3341_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3354_ = v_x_3341_;
v_isShared_3355_ = v_isSharedCheck_3371_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v_x_3341_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3371_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3370_; 
v_fst_3356_ = lean_ctor_get(v_a_3352_, 0);
v_snd_3357_ = lean_ctor_get(v_a_3352_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_a_3352_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3359_ = v_a_3352_;
v_isShared_3360_ = v_isSharedCheck_3370_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_inc(v_fst_3356_);
lean_dec(v_a_3352_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3370_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = lean_box(v___x_3340_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3361_);
lean_ctor_set(v___x_3359_, 0, v_snd_3357_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_snd_3357_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_fst_3356_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3364_);
v___x_3366_ = v___x_3354_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
return v___x_3367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_){
_start:
{
uint8_t v___x_8797__boxed_3375_; lean_object* v_res_3376_; 
v___x_8797__boxed_3375_ = lean_unbox(v___x_3372_);
v_res_3376_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_8797__boxed_3375_, v_x_3373_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3377_, uint8_t v___x_3378_, lean_object* v_fst_3379_, lean_object* v_x_3380_){
_start:
{
if (lean_obj_tag(v_x_3380_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v_fst_3379_);
lean_dec(v_snd_3377_);
v_a_3382_ = lean_ctor_get(v_x_3380_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_x_3380_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3384_ = v_x_3380_;
v_isShared_3385_ = v_isSharedCheck_3390_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v_x_3380_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3390_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
}
else
{
lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3401_; 
v_isSharedCheck_3401_ = !lean_is_exclusive(v_x_3380_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v_x_3380_, 0);
lean_dec(v_unused_3402_);
v___x_3392_ = v_x_3380_;
v_isShared_3393_ = v_isSharedCheck_3401_;
goto v_resetjp_3391_;
}
else
{
lean_dec(v_x_3380_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3401_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3394_ = lean_box(v___x_3378_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_snd_3377_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v_fst_3379_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3396_);
v___x_3398_ = v___x_3392_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3403_, lean_object* v___x_3404_, lean_object* v_fst_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_){
_start:
{
uint8_t v___x_8865__boxed_3408_; lean_object* v_res_3409_; 
v___x_8865__boxed_3408_ = lean_unbox(v___x_3404_);
v_res_3409_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3403_, v___x_8865__boxed_3408_, v_fst_3405_, v_x_3406_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3410_, lean_object* v_handler_3411_, uint8_t v___x_3412_, lean_object* v___f_3413_, lean_object* v_x_3414_){
_start:
{
if (lean_obj_tag(v_x_3414_) == 0)
{
lean_object* v_a_3416_; lean_object* v_onFailure_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3416_ = lean_ctor_get(v_x_3414_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v_x_3414_, 1);
v_onFailure_3417_ = lean_ctor_get(v_inst_3410_, 2);
lean_inc_ref(v_onFailure_3417_);
lean_dec_ref(v_inst_3410_);
v___x_3418_ = lean_apply_3(v_onFailure_3417_, v_handler_3411_, v_a_3416_, lean_box(0));
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3419_, v___x_3412_, v___x_3418_, v___f_3413_);
return v___x_3420_;
}
else
{
lean_object* v___x_3421_; 
lean_dec_ref(v___f_3413_);
lean_dec(v_handler_3411_);
lean_dec_ref(v_inst_3410_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_x_3414_);
return v___x_3421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3422_, lean_object* v_handler_3423_, lean_object* v___x_3424_, lean_object* v___f_3425_, lean_object* v_x_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v___x_8923__boxed_3428_; lean_object* v_res_3429_; 
v___x_8923__boxed_3428_ = lean_unbox(v___x_3424_);
v_res_3429_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3422_, v_handler_3423_, v___x_8923__boxed_3428_, v___f_3425_, v_x_3426_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3430_, lean_object* v___f_3431_, lean_object* v_inst_3432_, lean_object* v___f_3433_, uint8_t v___x_3434_, lean_object* v_inst_3435_, lean_object* v_handler_3436_, lean_object* v___f_3437_, lean_object* v_x_3438_){
_start:
{
if (lean_obj_tag(v_x_3438_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v___f_3437_);
lean_dec(v_handler_3436_);
lean_dec_ref(v_inst_3435_);
lean_dec_ref(v___f_3433_);
lean_dec_ref(v_inst_3432_);
lean_dec_ref(v___f_3431_);
v_a_3440_ = lean_ctor_get(v_x_3438_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_x_3438_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3442_ = v_x_3438_;
v_isShared_3443_ = v_isSharedCheck_3448_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v_x_3438_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3448_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3482_; 
v_a_3449_ = lean_ctor_get(v_x_3438_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_x_3438_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3451_ = v_x_3438_;
v_isShared_3452_ = v_isSharedCheck_3482_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v_x_3438_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3482_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_snd_3453_; 
v_snd_3453_ = lean_ctor_get(v_a_3449_, 1);
lean_inc(v_snd_3453_);
if (lean_obj_tag(v_snd_3453_) == 0)
{
lean_object* v_fst_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v___f_3437_);
lean_dec(v_handler_3436_);
lean_dec_ref(v_inst_3435_);
lean_dec_ref(v___f_3433_);
lean_dec_ref(v_inst_3432_);
v_fst_3454_ = lean_ctor_get(v_a_3449_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_a_3449_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v_a_3449_, 1);
lean_dec(v_unused_3470_);
v___x_3456_ = v_a_3449_;
v_isShared_3457_ = v_isSharedCheck_3469_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_fst_3454_);
lean_dec(v_a_3449_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3469_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3458_ = lean_box(v___x_3430_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___x_3458_);
lean_ctor_set(v___x_3456_, 0, v_snd_3453_);
v___x_3460_ = v___x_3456_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_snd_3453_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v_fst_3454_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3461_);
v___x_3463_ = v___x_3451_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
v___x_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3465_, v___x_3430_, v___x_3464_, v___f_3431_);
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_fst_3471_; lean_object* v_val_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; lean_object* v___f_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_del_object(v___x_3451_);
lean_dec_ref(v___f_3431_);
v_fst_3471_ = lean_ctor_get(v_a_3449_, 0);
lean_inc_n(v_fst_3471_, 2);
lean_dec(v_a_3449_);
v_val_3472_ = lean_ctor_get(v_snd_3453_, 0);
lean_inc(v_val_3472_);
v___x_3473_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3432_, v_fst_3471_, v_val_3472_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v___x_3475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3474_, v___x_3430_, v___x_3473_, v___f_3433_);
v___x_3476_ = lean_box(v___x_3434_);
v___f_3477_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3477_, 0, v_snd_3453_);
lean_closure_set(v___f_3477_, 1, v___x_3476_);
lean_closure_set(v___f_3477_, 2, v_fst_3471_);
v___x_3478_ = lean_box(v___x_3430_);
v___f_3479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3479_, 0, v_inst_3435_);
lean_closure_set(v___f_3479_, 1, v_handler_3436_);
lean_closure_set(v___f_3479_, 2, v___x_3478_);
lean_closure_set(v___f_3479_, 3, v___f_3477_);
v___x_3480_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3474_, v___x_3430_, v___x_3475_, v___f_3479_);
v___x_3481_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3474_, v___x_3430_, v___x_3480_, v___f_3437_);
return v___x_3481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3483_, lean_object* v___f_3484_, lean_object* v_inst_3485_, lean_object* v___f_3486_, lean_object* v___x_3487_, lean_object* v_inst_3488_, lean_object* v_handler_3489_, lean_object* v___f_3490_, lean_object* v_x_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v___x_8948__boxed_3493_; uint8_t v___x_8952__boxed_3494_; lean_object* v_res_3495_; 
v___x_8948__boxed_3493_ = lean_unbox(v___x_3483_);
v___x_8952__boxed_3494_ = lean_unbox(v___x_3487_);
v_res_3495_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8948__boxed_3493_, v___f_3484_, v_inst_3485_, v___f_3486_, v___x_8952__boxed_3494_, v_inst_3488_, v_handler_3489_, v___f_3490_, v_x_3491_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3496_, lean_object* v_x_3497_){
_start:
{
if (lean_obj_tag(v_x_3497_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v_state_3496_);
v_a_3499_ = lean_ctor_get(v_x_3497_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_x_3497_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3501_ = v_x_3497_;
v_isShared_3502_ = v_isSharedCheck_3507_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v_x_3497_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3507_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
}
else
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3537_; 
v_isSharedCheck_3537_ = !lean_is_exclusive(v_x_3497_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; 
v_unused_3538_ = lean_ctor_get(v_x_3497_, 0);
lean_dec(v_unused_3538_);
v___x_3509_ = v_x_3497_;
v_isShared_3510_ = v_isSharedCheck_3537_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v_x_3497_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3537_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v_machine_3511_; lean_object* v_requestStream_3512_; lean_object* v_keepAliveTimeout_3513_; lean_object* v_currentTimeout_3514_; lean_object* v_headerTimeout_3515_; lean_object* v_response_3516_; lean_object* v_respStream_3517_; uint8_t v_requiresData_3518_; lean_object* v_expectData_3519_; lean_object* v_pendingHead_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3536_; 
v_machine_3511_ = lean_ctor_get(v_state_3496_, 0);
v_requestStream_3512_ = lean_ctor_get(v_state_3496_, 1);
v_keepAliveTimeout_3513_ = lean_ctor_get(v_state_3496_, 2);
v_currentTimeout_3514_ = lean_ctor_get(v_state_3496_, 3);
v_headerTimeout_3515_ = lean_ctor_get(v_state_3496_, 4);
v_response_3516_ = lean_ctor_get(v_state_3496_, 5);
v_respStream_3517_ = lean_ctor_get(v_state_3496_, 6);
v_requiresData_3518_ = lean_ctor_get_uint8(v_state_3496_, sizeof(void*)*9);
v_expectData_3519_ = lean_ctor_get(v_state_3496_, 7);
v_pendingHead_3520_ = lean_ctor_get(v_state_3496_, 8);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_state_3496_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3522_ = v_state_3496_;
v_isShared_3523_ = v_isSharedCheck_3536_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_pendingHead_3520_);
lean_inc(v_expectData_3519_);
lean_inc(v_respStream_3517_);
lean_inc(v_response_3516_);
lean_inc(v_headerTimeout_3515_);
lean_inc(v_currentTimeout_3514_);
lean_inc(v_keepAliveTimeout_3513_);
lean_inc(v_requestStream_3512_);
lean_inc(v_machine_3511_);
lean_dec(v_state_3496_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3536_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; lean_object* v___x_3528_; 
v___x_3524_ = lean_box(31);
v___x_3525_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3511_, v___x_3524_);
v___x_3526_ = 0;
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3528_ = v___x_3522_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_requestStream_3512_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_keepAliveTimeout_3513_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_currentTimeout_3514_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_headerTimeout_3515_);
lean_ctor_set(v_reuseFailAlloc_3535_, 5, v_response_3516_);
lean_ctor_set(v_reuseFailAlloc_3535_, 6, v_respStream_3517_);
lean_ctor_set(v_reuseFailAlloc_3535_, 7, v_expectData_3519_);
lean_ctor_set(v_reuseFailAlloc_3535_, 8, v_pendingHead_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3535_, sizeof(void*)*9, v_requiresData_3518_);
v___x_3528_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*9 + 1, v___x_3526_);
v___x_3529_ = lean_box(v___x_3526_);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3530_);
v___x_3532_ = v___x_3509_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3530_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3539_, lean_object* v_x_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3539_, v_x_3540_);
return v_res_3542_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3548_ = lean_mk_io_user_error(v___x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_handler_3551_, lean_object* v_config_3552_, lean_object* v_event_3553_, lean_object* v_state_3554_){
_start:
{
switch(lean_obj_tag(v_event_3553_))
{
case 0:
{
lean_object* v_x_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_handler_3551_);
lean_dec_ref(v_inst_3550_);
lean_dec_ref(v_inst_3549_);
v_x_3556_ = lean_ctor_get(v_event_3553_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_event_3553_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3558_ = v_event_3553_;
v_isShared_3559_ = v_isSharedCheck_3663_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_x_3556_);
lean_dec(v_event_3553_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3663_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
if (lean_obj_tag(v_x_3556_) == 0)
{
lean_object* v_machine_3560_; lean_object* v_reader_3561_; lean_object* v_requestStream_3562_; lean_object* v_keepAliveTimeout_3563_; lean_object* v_currentTimeout_3564_; lean_object* v_headerTimeout_3565_; lean_object* v_response_3566_; lean_object* v_respStream_3567_; uint8_t v_requiresData_3568_; lean_object* v_expectData_3569_; uint8_t v_handlerDispatched_3570_; lean_object* v_pendingHead_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v_config_3552_);
v_machine_3560_ = lean_ctor_get(v_state_3554_, 0);
lean_inc_ref(v_machine_3560_);
v_reader_3561_ = lean_ctor_get(v_machine_3560_, 0);
lean_inc_ref(v_reader_3561_);
v_requestStream_3562_ = lean_ctor_get(v_state_3554_, 1);
v_keepAliveTimeout_3563_ = lean_ctor_get(v_state_3554_, 2);
v_currentTimeout_3564_ = lean_ctor_get(v_state_3554_, 3);
v_headerTimeout_3565_ = lean_ctor_get(v_state_3554_, 4);
v_response_3566_ = lean_ctor_get(v_state_3554_, 5);
v_respStream_3567_ = lean_ctor_get(v_state_3554_, 6);
v_requiresData_3568_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3569_ = lean_ctor_get(v_state_3554_, 7);
v_handlerDispatched_3570_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9 + 1);
v_pendingHead_3571_ = lean_ctor_get(v_state_3554_, 8);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_state_3554_);
if (v_isSharedCheck_3614_ == 0)
{
lean_object* v_unused_3615_; 
v_unused_3615_ = lean_ctor_get(v_state_3554_, 0);
lean_dec(v_unused_3615_);
v___x_3573_ = v_state_3554_;
v_isShared_3574_ = v_isSharedCheck_3614_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_pendingHead_3571_);
lean_inc(v_expectData_3569_);
lean_inc(v_respStream_3567_);
lean_inc(v_response_3566_);
lean_inc(v_headerTimeout_3565_);
lean_inc(v_currentTimeout_3564_);
lean_inc(v_keepAliveTimeout_3563_);
lean_inc(v_requestStream_3562_);
lean_dec(v_state_3554_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3614_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_writer_3575_; lean_object* v_config_3576_; lean_object* v_events_3577_; lean_object* v_error_3578_; lean_object* v_instant_3579_; uint8_t v_keepAlive_3580_; uint8_t v_forcedFlush_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3612_; 
v_writer_3575_ = lean_ctor_get(v_machine_3560_, 1);
v_config_3576_ = lean_ctor_get(v_machine_3560_, 2);
v_events_3577_ = lean_ctor_get(v_machine_3560_, 3);
v_error_3578_ = lean_ctor_get(v_machine_3560_, 4);
v_instant_3579_ = lean_ctor_get(v_machine_3560_, 5);
v_keepAlive_3580_ = lean_ctor_get_uint8(v_machine_3560_, sizeof(void*)*6);
v_forcedFlush_3581_ = lean_ctor_get_uint8(v_machine_3560_, sizeof(void*)*6 + 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_machine_3560_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v_machine_3560_, 0);
lean_dec(v_unused_3613_);
v___x_3583_ = v_machine_3560_;
v_isShared_3584_ = v_isSharedCheck_3612_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_instant_3579_);
lean_inc(v_error_3578_);
lean_inc(v_events_3577_);
lean_inc(v_config_3576_);
lean_inc(v_writer_3575_);
lean_dec(v_machine_3560_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3612_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v_state_3585_; lean_object* v_input_3586_; lean_object* v_messageHead_3587_; lean_object* v_messageCount_3588_; lean_object* v_bodyBytesRead_3589_; lean_object* v_headerBytesRead_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3611_; 
v_state_3585_ = lean_ctor_get(v_reader_3561_, 0);
v_input_3586_ = lean_ctor_get(v_reader_3561_, 1);
v_messageHead_3587_ = lean_ctor_get(v_reader_3561_, 2);
v_messageCount_3588_ = lean_ctor_get(v_reader_3561_, 3);
v_bodyBytesRead_3589_ = lean_ctor_get(v_reader_3561_, 4);
v_headerBytesRead_3590_ = lean_ctor_get(v_reader_3561_, 5);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_reader_3561_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3592_ = v_reader_3561_;
v_isShared_3593_ = v_isSharedCheck_3611_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_headerBytesRead_3590_);
lean_inc(v_bodyBytesRead_3589_);
lean_inc(v_messageCount_3588_);
lean_inc(v_messageHead_3587_);
lean_inc(v_input_3586_);
lean_inc(v_state_3585_);
lean_dec(v_reader_3561_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3611_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
uint8_t v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = 1;
if (v_isShared_3593_ == 0)
{
v___x_3596_ = v___x_3592_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_state_3585_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_input_3586_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_messageHead_3587_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_messageCount_3588_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_bodyBytesRead_3589_);
lean_ctor_set(v_reuseFailAlloc_3610_, 5, v_headerBytesRead_3590_);
v___x_3596_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
uint8_t v___x_3597_; lean_object* v___x_3599_; 
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*6, v___x_3594_);
v___x_3597_ = 0;
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3596_);
v___x_3599_ = v___x_3583_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_writer_3575_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_config_3576_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_events_3577_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v_error_3578_);
lean_ctor_set(v_reuseFailAlloc_3609_, 5, v_instant_3579_);
lean_ctor_set_uint8(v_reuseFailAlloc_3609_, sizeof(void*)*6, v_keepAlive_3580_);
lean_ctor_set_uint8(v_reuseFailAlloc_3609_, sizeof(void*)*6 + 1, v_forcedFlush_3581_);
v___x_3599_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*6 + 2, v___x_3597_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3599_);
v___x_3601_ = v___x_3573_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_requestStream_3562_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v_keepAliveTimeout_3563_);
lean_ctor_set(v_reuseFailAlloc_3608_, 3, v_currentTimeout_3564_);
lean_ctor_set(v_reuseFailAlloc_3608_, 4, v_headerTimeout_3565_);
lean_ctor_set(v_reuseFailAlloc_3608_, 5, v_response_3566_);
lean_ctor_set(v_reuseFailAlloc_3608_, 6, v_respStream_3567_);
lean_ctor_set(v_reuseFailAlloc_3608_, 7, v_expectData_3569_);
lean_ctor_set(v_reuseFailAlloc_3608_, 8, v_pendingHead_3571_);
lean_ctor_set_uint8(v_reuseFailAlloc_3608_, sizeof(void*)*9, v_requiresData_3568_);
lean_ctor_set_uint8(v_reuseFailAlloc_3608_, sizeof(void*)*9 + 1, v_handlerDispatched_3570_);
v___x_3601_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = lean_box(v___x_3597_);
v___x_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 1);
lean_ctor_set(v___x_3558_, 0, v___x_3603_);
v___x_3605_ = v___x_3558_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
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
lean_object* v_val_3616_; lean_object* v_machine_3617_; lean_object* v_requestStream_3618_; lean_object* v_keepAliveTimeout_3619_; lean_object* v_currentTimeout_3620_; lean_object* v_response_3621_; lean_object* v_respStream_3622_; uint8_t v_requiresData_3623_; lean_object* v_expectData_3624_; uint8_t v_handlerDispatched_3625_; lean_object* v_pendingHead_3626_; lean_object* v___f_3627_; 
lean_del_object(v___x_3558_);
v_val_3616_ = lean_ctor_get(v_x_3556_, 0);
lean_inc_n(v_val_3616_, 2);
lean_dec_ref_known(v_x_3556_, 1);
v_machine_3617_ = lean_ctor_get(v_state_3554_, 0);
v_requestStream_3618_ = lean_ctor_get(v_state_3554_, 1);
v_keepAliveTimeout_3619_ = lean_ctor_get(v_state_3554_, 2);
lean_inc(v_keepAliveTimeout_3619_);
v_currentTimeout_3620_ = lean_ctor_get(v_state_3554_, 3);
v_response_3621_ = lean_ctor_get(v_state_3554_, 5);
v_respStream_3622_ = lean_ctor_get(v_state_3554_, 6);
v_requiresData_3623_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3624_ = lean_ctor_get(v_state_3554_, 7);
v_handlerDispatched_3625_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9 + 1);
v_pendingHead_3626_ = lean_ctor_get(v_state_3554_, 8);
v___f_3627_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3627_, 0, v_val_3616_);
if (lean_obj_tag(v_keepAliveTimeout_3619_) == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_dec_ref(v___f_3627_);
lean_dec_ref(v_config_3552_);
v___x_3628_ = lean_box(0);
v___x_3629_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3616_, v___x_3628_, v_state_3554_);
return v___x_3629_;
}
else
{
lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3661_; 
lean_inc(v_pendingHead_3626_);
lean_inc(v_expectData_3624_);
lean_inc(v_respStream_3622_);
lean_inc_ref(v_response_3621_);
lean_inc(v_currentTimeout_3620_);
lean_inc_ref(v_requestStream_3618_);
lean_inc_ref(v_machine_3617_);
lean_dec(v_val_3616_);
lean_dec_ref(v_state_3554_);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_keepAliveTimeout_3619_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; 
v_unused_3662_ = lean_ctor_get(v_keepAliveTimeout_3619_, 0);
lean_dec(v_unused_3662_);
v___x_3631_ = v_keepAliveTimeout_3619_;
v_isShared_3632_ = v_isSharedCheck_3661_;
goto v_resetjp_3630_;
}
else
{
lean_dec(v_keepAliveTimeout_3619_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3661_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___f_3635_; lean_object* v_val_3637_; lean_object* v___x_3644_; 
v___x_3633_ = lean_box(v_requiresData_3623_);
v___x_3634_ = lean_box(v_handlerDispatched_3625_);
v___f_3635_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3635_, 0, v_config_3552_);
lean_closure_set(v___f_3635_, 1, v_machine_3617_);
lean_closure_set(v___f_3635_, 2, v_requestStream_3618_);
lean_closure_set(v___f_3635_, 3, v_currentTimeout_3620_);
lean_closure_set(v___f_3635_, 4, v_response_3621_);
lean_closure_set(v___f_3635_, 5, v_respStream_3622_);
lean_closure_set(v___f_3635_, 6, v___x_3633_);
lean_closure_set(v___f_3635_, 7, v_expectData_3624_);
lean_closure_set(v___f_3635_, 8, v___x_3634_);
lean_closure_set(v___f_3635_, 9, v_pendingHead_3626_);
lean_closure_set(v___f_3635_, 10, v___f_3627_);
v___x_3644_ = lean_get_current_time();
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 1);
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
v_val_3637_ = v___x_3650_;
goto v___jp_3636_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3644_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3644_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 0);
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
v_val_3637_ = v___x_3658_;
goto v___jp_3636_;
}
}
}
v___jp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 0);
lean_ctor_set(v___x_3631_, 0, v_val_3637_);
v___x_3639_ = v___x_3631_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_val_3637_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3640_; uint8_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = 0;
v___x_3642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3640_, v___x_3641_, v___x_3639_, v___f_3635_);
return v___x_3642_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v_config_3552_);
lean_dec(v_handler_3551_);
lean_dec_ref(v_inst_3549_);
v_x_3664_ = lean_ctor_get(v_event_3553_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_event_3553_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3666_ = v_event_3553_;
v_isShared_3667_ = v_isSharedCheck_3779_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_x_3664_);
lean_dec(v_event_3553_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3779_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
if (lean_obj_tag(v_x_3664_) == 0)
{
lean_object* v_machine_3668_; lean_object* v_requestStream_3669_; lean_object* v_keepAliveTimeout_3670_; lean_object* v_currentTimeout_3671_; lean_object* v_headerTimeout_3672_; lean_object* v_response_3673_; lean_object* v_respStream_3674_; uint8_t v_requiresData_3675_; lean_object* v_expectData_3676_; uint8_t v_handlerDispatched_3677_; lean_object* v_pendingHead_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___f_3681_; 
lean_del_object(v___x_3666_);
v_machine_3668_ = lean_ctor_get(v_state_3554_, 0);
lean_inc_ref_n(v_machine_3668_, 2);
v_requestStream_3669_ = lean_ctor_get(v_state_3554_, 1);
lean_inc_ref_n(v_requestStream_3669_, 2);
v_keepAliveTimeout_3670_ = lean_ctor_get(v_state_3554_, 2);
lean_inc_n(v_keepAliveTimeout_3670_, 2);
v_currentTimeout_3671_ = lean_ctor_get(v_state_3554_, 3);
lean_inc_n(v_currentTimeout_3671_, 2);
v_headerTimeout_3672_ = lean_ctor_get(v_state_3554_, 4);
lean_inc_n(v_headerTimeout_3672_, 2);
v_response_3673_ = lean_ctor_get(v_state_3554_, 5);
lean_inc_ref_n(v_response_3673_, 2);
v_respStream_3674_ = lean_ctor_get(v_state_3554_, 6);
lean_inc(v_respStream_3674_);
v_requiresData_3675_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3676_ = lean_ctor_get(v_state_3554_, 7);
lean_inc_n(v_expectData_3676_, 2);
v_handlerDispatched_3677_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9 + 1);
v_pendingHead_3678_ = lean_ctor_get(v_state_3554_, 8);
lean_inc_n(v_pendingHead_3678_, 2);
lean_dec_ref(v_state_3554_);
v___x_3679_ = lean_box(v_requiresData_3675_);
v___x_3680_ = lean_box(v_handlerDispatched_3677_);
v___f_3681_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3681_, 0, v_machine_3668_);
lean_closure_set(v___f_3681_, 1, v_requestStream_3669_);
lean_closure_set(v___f_3681_, 2, v_keepAliveTimeout_3670_);
lean_closure_set(v___f_3681_, 3, v_currentTimeout_3671_);
lean_closure_set(v___f_3681_, 4, v_headerTimeout_3672_);
lean_closure_set(v___f_3681_, 5, v_response_3673_);
lean_closure_set(v___f_3681_, 6, v___x_3679_);
lean_closure_set(v___f_3681_, 7, v_expectData_3676_);
lean_closure_set(v___f_3681_, 8, v___x_3680_);
lean_closure_set(v___f_3681_, 9, v_pendingHead_3678_);
if (lean_obj_tag(v_respStream_3674_) == 1)
{
lean_object* v_val_3682_; lean_object* v_close_3683_; lean_object* v_isClosed_3684_; lean_object* v___x_3685_; lean_object* v___f_3686_; lean_object* v___f_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; lean_object* v___x_3690_; 
lean_dec(v_pendingHead_3678_);
lean_dec(v_expectData_3676_);
lean_dec_ref(v_response_3673_);
lean_dec(v_headerTimeout_3672_);
lean_dec(v_currentTimeout_3671_);
lean_dec(v_keepAliveTimeout_3670_);
lean_dec_ref(v_requestStream_3669_);
lean_dec_ref(v_machine_3668_);
v_val_3682_ = lean_ctor_get(v_respStream_3674_, 0);
lean_inc_n(v_val_3682_, 2);
lean_dec_ref_known(v_respStream_3674_, 1);
v_close_3683_ = lean_ctor_get(v_inst_3550_, 1);
lean_inc_ref(v_close_3683_);
v_isClosed_3684_ = lean_ctor_get(v_inst_3550_, 2);
lean_inc_ref(v_isClosed_3684_);
lean_dec_ref(v_inst_3550_);
v___x_3685_ = lean_apply_2(v_isClosed_3684_, v_val_3682_, lean_box(0));
lean_inc_ref(v___f_3681_);
v___f_3686_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3686_, 0, v___f_3681_);
v___f_3687_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3687_, 0, v_close_3683_);
lean_closure_set(v___f_3687_, 1, v_val_3682_);
lean_closure_set(v___f_3687_, 2, v___f_3686_);
lean_closure_set(v___f_3687_, 3, v___f_3681_);
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = 0;
v___x_3690_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3688_, v___x_3689_, v___x_3685_, v___f_3687_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
lean_dec_ref(v___f_3681_);
lean_dec(v_respStream_3674_);
lean_dec_ref(v_inst_3550_);
v___x_3691_ = lean_box(0);
v___x_3692_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3668_, v_requestStream_3669_, v_keepAliveTimeout_3670_, v_currentTimeout_3671_, v_headerTimeout_3672_, v_response_3673_, v_requiresData_3675_, v_expectData_3676_, v_handlerDispatched_3677_, v_pendingHead_3678_, v___x_3691_);
return v___x_3692_;
}
}
else
{
lean_object* v_val_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v_inst_3550_);
v_val_3693_ = lean_ctor_get(v_x_3664_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_x_3664_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3695_ = v_x_3664_;
v_isShared_3696_ = v_isSharedCheck_3778_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_val_3693_);
lean_dec(v_x_3664_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3778_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v_machine_3697_; lean_object* v_requestStream_3698_; lean_object* v_keepAliveTimeout_3699_; lean_object* v_currentTimeout_3700_; lean_object* v_headerTimeout_3701_; lean_object* v_response_3702_; lean_object* v_respStream_3703_; uint8_t v_requiresData_3704_; lean_object* v_expectData_3705_; uint8_t v_handlerDispatched_3706_; lean_object* v_pendingHead_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3777_; 
v_machine_3697_ = lean_ctor_get(v_state_3554_, 0);
v_requestStream_3698_ = lean_ctor_get(v_state_3554_, 1);
v_keepAliveTimeout_3699_ = lean_ctor_get(v_state_3554_, 2);
v_currentTimeout_3700_ = lean_ctor_get(v_state_3554_, 3);
v_headerTimeout_3701_ = lean_ctor_get(v_state_3554_, 4);
v_response_3702_ = lean_ctor_get(v_state_3554_, 5);
v_respStream_3703_ = lean_ctor_get(v_state_3554_, 6);
v_requiresData_3704_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3705_ = lean_ctor_get(v_state_3554_, 7);
v_handlerDispatched_3706_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9 + 1);
v_pendingHead_3707_ = lean_ctor_get(v_state_3554_, 8);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_state_3554_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3709_ = v_state_3554_;
v_isShared_3710_ = v_isSharedCheck_3777_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_pendingHead_3707_);
lean_inc(v_expectData_3705_);
lean_inc(v_respStream_3703_);
lean_inc(v_response_3702_);
lean_inc(v_headerTimeout_3701_);
lean_inc(v_currentTimeout_3700_);
lean_inc(v_keepAliveTimeout_3699_);
lean_inc(v_requestStream_3698_);
lean_inc(v_machine_3697_);
lean_dec(v_state_3554_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3777_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___y_3712_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3725_ = lean_unsigned_to_nat(1u);
v___x_3726_ = lean_mk_empty_array_with_capacity(v___x_3725_);
v___x_3727_ = lean_array_push(v___x_3726_, v_val_3693_);
v___x_3728_ = lean_array_get_size(v___x_3727_);
v___x_3729_ = lean_unsigned_to_nat(0u);
v___x_3730_ = lean_nat_dec_eq(v___x_3728_, v___x_3729_);
if (v___x_3730_ == 0)
{
lean_object* v_reader_3731_; lean_object* v_writer_3732_; lean_object* v_config_3733_; lean_object* v_events_3734_; lean_object* v_error_3735_; lean_object* v_instant_3736_; uint8_t v_keepAlive_3737_; uint8_t v_forcedFlush_3738_; uint8_t v_pullBodyStalled_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3776_; 
v_reader_3731_ = lean_ctor_get(v_machine_3697_, 0);
v_writer_3732_ = lean_ctor_get(v_machine_3697_, 1);
v_config_3733_ = lean_ctor_get(v_machine_3697_, 2);
v_events_3734_ = lean_ctor_get(v_machine_3697_, 3);
v_error_3735_ = lean_ctor_get(v_machine_3697_, 4);
v_instant_3736_ = lean_ctor_get(v_machine_3697_, 5);
v_keepAlive_3737_ = lean_ctor_get_uint8(v_machine_3697_, sizeof(void*)*6);
v_forcedFlush_3738_ = lean_ctor_get_uint8(v_machine_3697_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3739_ = lean_ctor_get_uint8(v_machine_3697_, sizeof(void*)*6 + 2);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_machine_3697_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3741_ = v_machine_3697_;
v_isShared_3742_ = v_isSharedCheck_3776_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_instant_3736_);
lean_inc(v_error_3735_);
lean_inc(v_events_3734_);
lean_inc(v_config_3733_);
lean_inc(v_writer_3732_);
lean_inc(v_reader_3731_);
lean_dec(v_machine_3697_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3776_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___y_3744_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v___x_3766_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_3767_ = lean_nat_dec_lt(v___x_3729_, v___x_3728_);
if (v___x_3767_ == 0)
{
v___y_3744_ = v___x_3729_;
goto v___jp_3743_;
}
else
{
lean_object* v___f_3768_; uint8_t v___x_3769_; 
v___f_3768_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3769_ = lean_nat_dec_le(v___x_3728_, v___x_3728_);
if (v___x_3769_ == 0)
{
if (v___x_3767_ == 0)
{
v___y_3744_ = v___x_3729_;
goto v___jp_3743_;
}
else
{
size_t v___x_3770_; size_t v___x_3771_; lean_object* v___x_3772_; 
v___x_3770_ = ((size_t)0ULL);
v___x_3771_ = lean_usize_of_nat(v___x_3728_);
lean_inc_ref(v___x_3727_);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3766_, v___f_3768_, v___x_3727_, v___x_3770_, v___x_3771_, v___x_3729_);
v___y_3744_ = v___x_3772_;
goto v___jp_3743_;
}
}
else
{
size_t v___x_3773_; size_t v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = ((size_t)0ULL);
v___x_3774_ = lean_usize_of_nat(v___x_3728_);
lean_inc_ref(v___x_3727_);
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3766_, v___f_3768_, v___x_3727_, v___x_3773_, v___x_3774_, v___x_3729_);
v___y_3744_ = v___x_3775_;
goto v___jp_3743_;
}
}
v___jp_3743_:
{
lean_object* v_userData_3745_; lean_object* v_outputData_3746_; lean_object* v_state_3747_; lean_object* v_knownSize_3748_; lean_object* v_messageHead_3749_; uint8_t v_sentMessage_3750_; uint8_t v_userClosedBody_3751_; uint8_t v_omitBody_3752_; lean_object* v_userDataBytes_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3765_; 
v_userData_3745_ = lean_ctor_get(v_writer_3732_, 0);
v_outputData_3746_ = lean_ctor_get(v_writer_3732_, 1);
v_state_3747_ = lean_ctor_get(v_writer_3732_, 2);
v_knownSize_3748_ = lean_ctor_get(v_writer_3732_, 3);
v_messageHead_3749_ = lean_ctor_get(v_writer_3732_, 4);
v_sentMessage_3750_ = lean_ctor_get_uint8(v_writer_3732_, sizeof(void*)*6);
v_userClosedBody_3751_ = lean_ctor_get_uint8(v_writer_3732_, sizeof(void*)*6 + 1);
v_omitBody_3752_ = lean_ctor_get_uint8(v_writer_3732_, sizeof(void*)*6 + 2);
v_userDataBytes_3753_ = lean_ctor_get(v_writer_3732_, 5);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_writer_3732_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3755_ = v_writer_3732_;
v_isShared_3756_ = v_isSharedCheck_3765_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_userDataBytes_3753_);
lean_inc(v_messageHead_3749_);
lean_inc(v_knownSize_3748_);
lean_inc(v_state_3747_);
lean_inc(v_outputData_3746_);
lean_inc(v_userData_3745_);
lean_dec(v_writer_3732_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3765_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3757_ = l_Array_append___redArg(v_userData_3745_, v___x_3727_);
lean_dec_ref(v___x_3727_);
v___x_3758_ = lean_nat_add(v_userDataBytes_3753_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec(v_userDataBytes_3753_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 5, v___x_3758_);
lean_ctor_set(v___x_3755_, 0, v___x_3757_);
v___x_3760_ = v___x_3755_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_outputData_3746_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_state_3747_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_knownSize_3748_);
lean_ctor_set(v_reuseFailAlloc_3764_, 4, v_messageHead_3749_);
lean_ctor_set(v_reuseFailAlloc_3764_, 5, v___x_3758_);
lean_ctor_set_uint8(v_reuseFailAlloc_3764_, sizeof(void*)*6, v_sentMessage_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3764_, sizeof(void*)*6 + 1, v_userClosedBody_3751_);
lean_ctor_set_uint8(v_reuseFailAlloc_3764_, sizeof(void*)*6 + 2, v_omitBody_3752_);
v___x_3760_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v___x_3760_);
v___x_3762_ = v___x_3741_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_reader_3731_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_config_3733_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_events_3734_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_error_3735_);
lean_ctor_set(v_reuseFailAlloc_3763_, 5, v_instant_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*6, v_keepAlive_3737_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*6 + 1, v_forcedFlush_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*6 + 2, v_pullBodyStalled_3739_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
v___y_3712_ = v___x_3762_;
goto v___jp_3711_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3727_);
v___y_3712_ = v_machine_3697_;
goto v___jp_3711_;
}
v___jp_3711_:
{
lean_object* v___x_3714_; 
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___y_3712_);
v___x_3714_ = v___x_3709_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___y_3712_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_requestStream_3698_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_keepAliveTimeout_3699_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_currentTimeout_3700_);
lean_ctor_set(v_reuseFailAlloc_3724_, 4, v_headerTimeout_3701_);
lean_ctor_set(v_reuseFailAlloc_3724_, 5, v_response_3702_);
lean_ctor_set(v_reuseFailAlloc_3724_, 6, v_respStream_3703_);
lean_ctor_set(v_reuseFailAlloc_3724_, 7, v_expectData_3705_);
lean_ctor_set(v_reuseFailAlloc_3724_, 8, v_pendingHead_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3724_, sizeof(void*)*9, v_requiresData_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3724_, sizeof(void*)*9 + 1, v_handlerDispatched_3706_);
v___x_3714_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
uint8_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3715_ = 0;
v___x_3716_ = lean_box(v___x_3715_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3714_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3717_);
v___x_3719_ = v___x_3695_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3717_);
v___x_3719_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3719_);
v___x_3721_ = v___x_3666_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
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
uint8_t v_x_3780_; 
lean_dec_ref(v_config_3552_);
lean_dec_ref(v_inst_3550_);
v_x_3780_ = lean_ctor_get_uint8(v_event_3553_, 0);
lean_dec_ref_known(v_event_3553_, 0);
if (v_x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec(v_handler_3551_);
lean_dec_ref(v_inst_3549_);
v___x_3781_ = lean_box(v_x_3780_);
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v_state_3554_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
else
{
lean_object* v_machine_3785_; lean_object* v_requestStream_3786_; lean_object* v_keepAliveTimeout_3787_; lean_object* v_currentTimeout_3788_; lean_object* v_headerTimeout_3789_; lean_object* v_response_3790_; lean_object* v_respStream_3791_; uint8_t v_requiresData_3792_; lean_object* v_expectData_3793_; uint8_t v_handlerDispatched_3794_; lean_object* v_pendingHead_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3845_; 
v_machine_3785_ = lean_ctor_get(v_state_3554_, 0);
v_requestStream_3786_ = lean_ctor_get(v_state_3554_, 1);
v_keepAliveTimeout_3787_ = lean_ctor_get(v_state_3554_, 2);
v_currentTimeout_3788_ = lean_ctor_get(v_state_3554_, 3);
v_headerTimeout_3789_ = lean_ctor_get(v_state_3554_, 4);
v_response_3790_ = lean_ctor_get(v_state_3554_, 5);
v_respStream_3791_ = lean_ctor_get(v_state_3554_, 6);
v_requiresData_3792_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3793_ = lean_ctor_get(v_state_3554_, 7);
v_handlerDispatched_3794_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9 + 1);
v_pendingHead_3795_ = lean_ctor_get(v_state_3554_, 8);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_state_3554_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3797_ = v_state_3554_;
v_isShared_3798_ = v_isSharedCheck_3845_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_pendingHead_3795_);
lean_inc(v_expectData_3793_);
lean_inc(v_respStream_3791_);
lean_inc(v_response_3790_);
lean_inc(v_headerTimeout_3789_);
lean_inc(v_currentTimeout_3788_);
lean_inc(v_keepAliveTimeout_3787_);
lean_inc(v_requestStream_3786_);
lean_inc(v_machine_3785_);
lean_dec(v_state_3554_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3845_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
uint8_t v___x_3799_; lean_object* v___x_3800_; lean_object* v_fst_3801_; lean_object* v_snd_3802_; lean_object* v_reader_3803_; lean_object* v_writer_3804_; lean_object* v_config_3805_; lean_object* v_events_3806_; lean_object* v_error_3807_; lean_object* v_instant_3808_; uint8_t v_keepAlive_3809_; uint8_t v_forcedFlush_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3844_; 
v___x_3799_ = 0;
v___x_3800_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3799_, v_machine_3785_);
v_fst_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_fst_3801_);
v_snd_3802_ = lean_ctor_get(v___x_3800_, 1);
lean_inc(v_snd_3802_);
lean_dec_ref(v___x_3800_);
v_reader_3803_ = lean_ctor_get(v_fst_3801_, 0);
v_writer_3804_ = lean_ctor_get(v_fst_3801_, 1);
v_config_3805_ = lean_ctor_get(v_fst_3801_, 2);
v_events_3806_ = lean_ctor_get(v_fst_3801_, 3);
v_error_3807_ = lean_ctor_get(v_fst_3801_, 4);
v_instant_3808_ = lean_ctor_get(v_fst_3801_, 5);
v_keepAlive_3809_ = lean_ctor_get_uint8(v_fst_3801_, sizeof(void*)*6);
v_forcedFlush_3810_ = lean_ctor_get_uint8(v_fst_3801_, sizeof(void*)*6 + 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_fst_3801_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3812_ = v_fst_3801_;
v_isShared_3813_ = v_isSharedCheck_3844_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_instant_3808_);
lean_inc(v_error_3807_);
lean_inc(v_events_3806_);
lean_inc(v_config_3805_);
lean_inc(v_writer_3804_);
lean_inc(v_reader_3803_);
lean_dec(v_fst_3801_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3844_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___f_3814_; lean_object* v___f_3815_; uint8_t v___y_3817_; 
v___f_3814_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3814_, 0, v_inst_3549_);
lean_closure_set(v___f_3814_, 1, v_handler_3551_);
v___f_3815_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3802_) == 0)
{
uint8_t v_sentMessage_3840_; 
v_sentMessage_3840_ = lean_ctor_get_uint8(v_writer_3804_, sizeof(void*)*6);
if (v_sentMessage_3840_ == 0)
{
lean_object* v_state_3841_; 
v_state_3841_ = lean_ctor_get(v_reader_3803_, 0);
if (lean_obj_tag(v_state_3841_) == 2)
{
v___y_3817_ = v_x_3780_;
goto v___jp_3816_;
}
else
{
v___y_3817_ = v_sentMessage_3840_;
goto v___jp_3816_;
}
}
else
{
uint8_t v___x_3842_; 
v___x_3842_ = 0;
v___y_3817_ = v___x_3842_;
goto v___jp_3816_;
}
}
else
{
uint8_t v___x_3843_; 
v___x_3843_ = 0;
v___y_3817_ = v___x_3843_;
goto v___jp_3816_;
}
v___jp_3816_:
{
lean_object* v___x_3819_; 
if (v_isShared_3813_ == 0)
{
v___x_3819_ = v___x_3812_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_reader_3803_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_writer_3804_);
lean_ctor_set(v_reuseFailAlloc_3839_, 2, v_config_3805_);
lean_ctor_set(v_reuseFailAlloc_3839_, 3, v_events_3806_);
lean_ctor_set(v_reuseFailAlloc_3839_, 4, v_error_3807_);
lean_ctor_set(v_reuseFailAlloc_3839_, 5, v_instant_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3839_, sizeof(void*)*6, v_keepAlive_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3839_, sizeof(void*)*6 + 1, v_forcedFlush_3810_);
v___x_3819_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v_st_3821_; 
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*6 + 2, v___y_3817_);
lean_inc_ref(v_requestStream_3786_);
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 0, v___x_3819_);
v_st_3821_ = v___x_3797_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_requestStream_3786_);
lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_keepAliveTimeout_3787_);
lean_ctor_set(v_reuseFailAlloc_3838_, 3, v_currentTimeout_3788_);
lean_ctor_set(v_reuseFailAlloc_3838_, 4, v_headerTimeout_3789_);
lean_ctor_set(v_reuseFailAlloc_3838_, 5, v_response_3790_);
lean_ctor_set(v_reuseFailAlloc_3838_, 6, v_respStream_3791_);
lean_ctor_set(v_reuseFailAlloc_3838_, 7, v_expectData_3793_);
lean_ctor_set(v_reuseFailAlloc_3838_, 8, v_pendingHead_3795_);
lean_ctor_set_uint8(v_reuseFailAlloc_3838_, sizeof(void*)*9, v_requiresData_3792_);
lean_ctor_set_uint8(v_reuseFailAlloc_3838_, sizeof(void*)*9 + 1, v_handlerDispatched_3794_);
v_st_3821_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___f_3822_; 
lean_inc_ref(v_st_3821_);
v___f_3822_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3822_, 0, v_st_3821_);
if (lean_obj_tag(v_snd_3802_) == 1)
{
lean_object* v_val_3823_; uint8_t v_final_3824_; uint8_t v_incomplete_3825_; lean_object* v_chunk_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; lean_object* v___x_3830_; lean_object* v___f_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; lean_object* v___f_3834_; lean_object* v___x_3835_; 
lean_dec_ref(v_st_3821_);
v_val_3823_ = lean_ctor_get(v_snd_3802_, 0);
lean_inc(v_val_3823_);
lean_dec_ref_known(v_snd_3802_, 1);
v_final_3824_ = lean_ctor_get_uint8(v_val_3823_, sizeof(void*)*1);
v_incomplete_3825_ = lean_ctor_get_uint8(v_val_3823_, sizeof(void*)*1 + 1);
v_chunk_3826_ = lean_ctor_get(v_val_3823_, 0);
lean_inc_ref(v_chunk_3826_);
lean_dec(v_val_3823_);
lean_inc_ref_n(v_requestStream_3786_, 2);
v___x_3827_ = l_Std_Http_Body_Stream_send(v_requestStream_3786_, v_chunk_3826_, v_incomplete_3825_);
v___x_3828_ = lean_unsigned_to_nat(0u);
v___x_3829_ = 0;
v___x_3830_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3828_, v___x_3829_, v___x_3827_, v___f_3814_);
lean_inc_ref_n(v___f_3822_, 2);
v___f_3831_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3831_, 0, v___f_3822_);
v___f_3832_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3832_, 0, v_requestStream_3786_);
lean_closure_set(v___f_3832_, 1, v___f_3831_);
lean_closure_set(v___f_3832_, 2, v___f_3822_);
v___x_3833_ = lean_box(v_final_3824_);
v___f_3834_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3834_, 0, v___x_3833_);
lean_closure_set(v___f_3834_, 1, v___f_3822_);
lean_closure_set(v___f_3834_, 2, v___f_3815_);
lean_closure_set(v___f_3834_, 3, v_requestStream_3786_);
lean_closure_set(v___f_3834_, 4, v___f_3832_);
v___x_3835_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3828_, v___x_3829_, v___x_3830_, v___f_3834_);
return v___x_3835_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_dec_ref(v___f_3822_);
lean_dec_ref(v___f_3814_);
lean_dec(v_snd_3802_);
lean_dec_ref(v_requestStream_3786_);
v___x_3836_ = lean_box(0);
v___x_3837_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3821_, v___x_3836_);
return v___x_3837_;
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
lean_object* v_x_3846_; 
v_x_3846_ = lean_ctor_get(v_event_3553_, 0);
lean_inc_ref(v_x_3846_);
lean_dec_ref_known(v_event_3553_, 1);
if (lean_obj_tag(v_x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v_onFailure_3848_; lean_object* v___x_3849_; lean_object* v___f_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; 
lean_dec_ref(v_config_3552_);
lean_dec_ref(v_inst_3550_);
v_a_3847_ = lean_ctor_get(v_x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v_x_3846_, 1);
v_onFailure_3848_ = lean_ctor_get(v_inst_3549_, 2);
lean_inc_ref(v_onFailure_3848_);
lean_dec_ref(v_inst_3549_);
v___x_3849_ = lean_apply_3(v_onFailure_3848_, v_handler_3551_, v_a_3847_, lean_box(0));
v___f_3850_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3850_, 0, v_state_3554_);
v___x_3851_ = lean_unsigned_to_nat(0u);
v___x_3852_ = 0;
v___x_3853_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3851_, v___x_3852_, v___x_3849_, v___f_3850_);
return v___x_3853_;
}
else
{
lean_object* v_machine_3854_; lean_object* v_reader_3855_; lean_object* v_state_3856_; 
v_machine_3854_ = lean_ctor_get(v_state_3554_, 0);
lean_inc_ref(v_machine_3854_);
v_reader_3855_ = lean_ctor_get(v_machine_3854_, 0);
v_state_3856_ = lean_ctor_get(v_reader_3855_, 0);
if (lean_obj_tag(v_state_3856_) == 7)
{
lean_object* v_a_3857_; lean_object* v_requestStream_3858_; lean_object* v_keepAliveTimeout_3859_; lean_object* v_currentTimeout_3860_; lean_object* v_headerTimeout_3861_; lean_object* v_response_3862_; lean_object* v_respStream_3863_; uint8_t v_requiresData_3864_; lean_object* v_expectData_3865_; lean_object* v_pendingHead_3866_; lean_object* v_close_3867_; lean_object* v_isClosed_3868_; lean_object* v_body_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___f_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; 
lean_dec_ref(v_config_3552_);
lean_dec(v_handler_3551_);
lean_dec_ref(v_inst_3549_);
v_a_3857_ = lean_ctor_get(v_x_3846_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v_x_3846_, 1);
v_requestStream_3858_ = lean_ctor_get(v_state_3554_, 1);
lean_inc_ref(v_requestStream_3858_);
v_keepAliveTimeout_3859_ = lean_ctor_get(v_state_3554_, 2);
lean_inc(v_keepAliveTimeout_3859_);
v_currentTimeout_3860_ = lean_ctor_get(v_state_3554_, 3);
lean_inc(v_currentTimeout_3860_);
v_headerTimeout_3861_ = lean_ctor_get(v_state_3554_, 4);
lean_inc(v_headerTimeout_3861_);
v_response_3862_ = lean_ctor_get(v_state_3554_, 5);
lean_inc_ref(v_response_3862_);
v_respStream_3863_ = lean_ctor_get(v_state_3554_, 6);
lean_inc(v_respStream_3863_);
v_requiresData_3864_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3865_ = lean_ctor_get(v_state_3554_, 7);
lean_inc(v_expectData_3865_);
v_pendingHead_3866_ = lean_ctor_get(v_state_3554_, 8);
lean_inc(v_pendingHead_3866_);
lean_dec_ref(v_state_3554_);
v_close_3867_ = lean_ctor_get(v_inst_3550_, 1);
lean_inc_ref(v_close_3867_);
v_isClosed_3868_ = lean_ctor_get(v_inst_3550_, 2);
lean_inc_ref(v_isClosed_3868_);
lean_dec_ref(v_inst_3550_);
v_body_3869_ = lean_ctor_get(v_a_3857_, 1);
lean_inc_n(v_body_3869_, 2);
lean_dec(v_a_3857_);
v___x_3870_ = lean_apply_2(v_isClosed_3868_, v_body_3869_, lean_box(0));
v___x_3871_ = lean_box(v_requiresData_3864_);
v___f_3872_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3872_, 0, v_machine_3854_);
lean_closure_set(v___f_3872_, 1, v_requestStream_3858_);
lean_closure_set(v___f_3872_, 2, v_keepAliveTimeout_3859_);
lean_closure_set(v___f_3872_, 3, v_currentTimeout_3860_);
lean_closure_set(v___f_3872_, 4, v_headerTimeout_3861_);
lean_closure_set(v___f_3872_, 5, v_response_3862_);
lean_closure_set(v___f_3872_, 6, v_respStream_3863_);
lean_closure_set(v___f_3872_, 7, v___x_3871_);
lean_closure_set(v___f_3872_, 8, v_expectData_3865_);
lean_closure_set(v___f_3872_, 9, v_pendingHead_3866_);
lean_inc_ref(v___f_3872_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3873_, 0, v___f_3872_);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3874_, 0, v_close_3867_);
lean_closure_set(v___f_3874_, 1, v_body_3869_);
lean_closure_set(v___f_3874_, 2, v___f_3873_);
lean_closure_set(v___f_3874_, 3, v___f_3872_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v___x_3876_ = 0;
v___x_3877_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3875_, v___x_3876_, v___x_3870_, v___f_3874_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v_requestStream_3879_; lean_object* v_keepAliveTimeout_3880_; lean_object* v_currentTimeout_3881_; lean_object* v_headerTimeout_3882_; lean_object* v_response_3883_; uint8_t v_requiresData_3884_; lean_object* v_expectData_3885_; lean_object* v_pendingHead_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___f_3891_; lean_object* v___f_3892_; lean_object* v___f_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___f_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_a_3878_ = lean_ctor_get(v_x_3846_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v_x_3846_, 1);
v_requestStream_3879_ = lean_ctor_get(v_state_3554_, 1);
lean_inc_ref(v_requestStream_3879_);
v_keepAliveTimeout_3880_ = lean_ctor_get(v_state_3554_, 2);
lean_inc(v_keepAliveTimeout_3880_);
v_currentTimeout_3881_ = lean_ctor_get(v_state_3554_, 3);
lean_inc(v_currentTimeout_3881_);
v_headerTimeout_3882_ = lean_ctor_get(v_state_3554_, 4);
lean_inc(v_headerTimeout_3882_);
v_response_3883_ = lean_ctor_get(v_state_3554_, 5);
lean_inc_ref(v_response_3883_);
v_requiresData_3884_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3885_ = lean_ctor_get(v_state_3554_, 7);
lean_inc(v_expectData_3885_);
v_pendingHead_3886_ = lean_ctor_get(v_state_3554_, 8);
lean_inc(v_pendingHead_3886_);
lean_dec_ref(v_state_3554_);
lean_inc_ref(v_inst_3550_);
v___x_3887_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3550_, v_config_3552_, v_machine_3854_, v_a_3878_);
v___x_3888_ = 0;
v___x_3889_ = lean_box(v_requiresData_3884_);
v___x_3890_ = lean_box(v___x_3888_);
v___f_3891_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3891_, 0, v_requestStream_3879_);
lean_closure_set(v___f_3891_, 1, v_keepAliveTimeout_3880_);
lean_closure_set(v___f_3891_, 2, v_currentTimeout_3881_);
lean_closure_set(v___f_3891_, 3, v_headerTimeout_3882_);
lean_closure_set(v___f_3891_, 4, v_response_3883_);
lean_closure_set(v___f_3891_, 5, v___x_3889_);
lean_closure_set(v___f_3891_, 6, v_expectData_3885_);
lean_closure_set(v___f_3891_, 7, v___x_3890_);
lean_closure_set(v___f_3891_, 8, v_pendingHead_3886_);
v___f_3892_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3892_, 0, v___f_3891_);
v___f_3893_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3894_ = 1;
v___x_3895_ = lean_box(v___x_3888_);
v___x_3896_ = lean_box(v___x_3894_);
lean_inc_ref(v___f_3892_);
v___f_3897_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3897_, 0, v___x_3895_);
lean_closure_set(v___f_3897_, 1, v___f_3892_);
lean_closure_set(v___f_3897_, 2, v_inst_3550_);
lean_closure_set(v___f_3897_, 3, v___f_3893_);
lean_closure_set(v___f_3897_, 4, v___x_3896_);
lean_closure_set(v___f_3897_, 5, v_inst_3549_);
lean_closure_set(v___f_3897_, 6, v_handler_3551_);
lean_closure_set(v___f_3897_, 7, v___f_3892_);
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3898_, v___x_3888_, v___x_3887_, v___f_3897_);
return v___x_3899_;
}
}
}
case 4:
{
lean_object* v_onFailure_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; 
lean_dec_ref(v_config_3552_);
lean_dec_ref(v_inst_3550_);
v_onFailure_3900_ = lean_ctor_get(v_inst_3549_, 2);
lean_inc_ref(v_onFailure_3900_);
lean_dec_ref(v_inst_3549_);
v___x_3901_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3902_ = lean_apply_3(v_onFailure_3900_, v_handler_3551_, v___x_3901_, lean_box(0));
v___f_3903_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3903_, 0, v_state_3554_);
v___x_3904_ = lean_unsigned_to_nat(0u);
v___x_3905_ = 0;
v___x_3906_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3904_, v___x_3905_, v___x_3902_, v___f_3903_);
return v___x_3906_;
}
case 5:
{
lean_object* v_machine_3907_; lean_object* v_requestStream_3908_; lean_object* v_keepAliveTimeout_3909_; lean_object* v_currentTimeout_3910_; lean_object* v_headerTimeout_3911_; lean_object* v_response_3912_; lean_object* v_respStream_3913_; uint8_t v_requiresData_3914_; lean_object* v_expectData_3915_; lean_object* v_pendingHead_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v_config_3552_);
lean_dec(v_handler_3551_);
lean_dec_ref(v_inst_3550_);
lean_dec_ref(v_inst_3549_);
v_machine_3907_ = lean_ctor_get(v_state_3554_, 0);
v_requestStream_3908_ = lean_ctor_get(v_state_3554_, 1);
v_keepAliveTimeout_3909_ = lean_ctor_get(v_state_3554_, 2);
v_currentTimeout_3910_ = lean_ctor_get(v_state_3554_, 3);
v_headerTimeout_3911_ = lean_ctor_get(v_state_3554_, 4);
v_response_3912_ = lean_ctor_get(v_state_3554_, 5);
v_respStream_3913_ = lean_ctor_get(v_state_3554_, 6);
v_requiresData_3914_ = lean_ctor_get_uint8(v_state_3554_, sizeof(void*)*9);
v_expectData_3915_ = lean_ctor_get(v_state_3554_, 7);
v_pendingHead_3916_ = lean_ctor_get(v_state_3554_, 8);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_state_3554_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3918_ = v_state_3554_;
v_isShared_3919_ = v_isSharedCheck_3930_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_pendingHead_3916_);
lean_inc(v_expectData_3915_);
lean_inc(v_respStream_3913_);
lean_inc(v_response_3912_);
lean_inc(v_headerTimeout_3911_);
lean_inc(v_currentTimeout_3910_);
lean_inc(v_keepAliveTimeout_3909_);
lean_inc(v_requestStream_3908_);
lean_inc(v_machine_3907_);
lean_dec(v_state_3554_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3930_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; lean_object* v___x_3924_; 
v___x_3920_ = lean_box(55);
v___x_3921_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3907_, v___x_3920_);
v___x_3922_ = 0;
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3921_);
v___x_3924_ = v___x_3918_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_requestStream_3908_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_keepAliveTimeout_3909_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_currentTimeout_3910_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v_headerTimeout_3911_);
lean_ctor_set(v_reuseFailAlloc_3929_, 5, v_response_3912_);
lean_ctor_set(v_reuseFailAlloc_3929_, 6, v_respStream_3913_);
lean_ctor_set(v_reuseFailAlloc_3929_, 7, v_expectData_3915_);
lean_ctor_set(v_reuseFailAlloc_3929_, 8, v_pendingHead_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3929_, sizeof(void*)*9, v_requiresData_3914_);
v___x_3924_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*9 + 1, v___x_3922_);
v___x_3925_ = lean_box(v___x_3922_);
v___x_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
}
}
default: 
{
uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec_ref(v_config_3552_);
lean_dec(v_handler_3551_);
lean_dec_ref(v_inst_3550_);
lean_dec_ref(v_inst_3549_);
v___x_3931_ = 1;
v___x_3932_ = lean_box(v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v_state_3554_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
return v___x_3935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3936_, lean_object* v_inst_3937_, lean_object* v_handler_3938_, lean_object* v_config_3939_, lean_object* v_event_3940_, lean_object* v_state_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3936_, v_inst_3937_, v_handler_3938_, v_config_3939_, v_event_3940_, v_state_3941_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3944_, lean_object* v_00_u03b2_3945_, lean_object* v_inst_3946_, lean_object* v_inst_3947_, lean_object* v_handler_3948_, lean_object* v_config_3949_, lean_object* v_event_3950_, lean_object* v_state_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3946_, v_inst_3947_, v_handler_3948_, v_config_3949_, v_event_3950_, v_state_3951_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3954_, lean_object* v_00_u03b2_3955_, lean_object* v_inst_3956_, lean_object* v_inst_3957_, lean_object* v_handler_3958_, lean_object* v_config_3959_, lean_object* v_event_3960_, lean_object* v_state_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3954_, v_00_u03b2_3955_, v_inst_3956_, v_inst_3957_, v_handler_3958_, v_config_3959_, v_event_3960_, v_state_3961_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3964_, uint8_t v_handlerDispatched_3965_, lean_object* v_keepAliveTimeout_3966_, lean_object* v_respStream_3967_, lean_object* v_headerTimeout_3968_, lean_object* v_expectData_3969_, lean_object* v_currentTimeout_3970_, lean_object* v_response_3971_, lean_object* v_socket_3972_, uint8_t v_requiresData_3973_, uint8_t v_sentMessage_3974_, lean_object* v_reader_3975_, uint8_t v_requestBodyInterested_3976_, lean_object* v_requestBody_3977_){
_start:
{
lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3991_; 
if (v_requiresData_3973_ == 0)
{
if (v_handlerDispatched_3965_ == 0)
{
goto v___jp_3994_;
}
else
{
if (lean_obj_tag(v_respStream_3967_) == 0)
{
if (v_sentMessage_3974_ == 0)
{
lean_object* v_state_3998_; 
v_state_3998_ = lean_ctor_get(v_reader_3975_, 0);
if (lean_obj_tag(v_state_3998_) == 2)
{
if (v_requestBodyInterested_3976_ == 0)
{
lean_dec(v_socket_3972_);
goto v___jp_3996_;
}
else
{
goto v___jp_3994_;
}
}
else
{
lean_dec(v_socket_3972_);
goto v___jp_3996_;
}
}
else
{
goto v___jp_3994_;
}
}
else
{
goto v___jp_3994_;
}
}
}
else
{
goto v___jp_3994_;
}
v___jp_3979_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3987_, 0, v___y_3984_);
lean_ctor_set(v___x_3987_, 1, v___y_3983_);
lean_ctor_set(v___x_3987_, 2, v___y_3986_);
lean_ctor_set(v___x_3987_, 3, v___y_3981_);
lean_ctor_set(v___x_3987_, 4, v_requestBody_3977_);
lean_ctor_set(v___x_3987_, 5, v___y_3985_);
lean_ctor_set(v___x_3987_, 6, v___y_3980_);
lean_ctor_set(v___x_3987_, 7, v___y_3982_);
lean_ctor_set(v___x_3987_, 8, v_connectionContext_3964_);
v___x_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
v___jp_3990_:
{
if (v_handlerDispatched_3965_ == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref(v_response_3971_);
v___x_3992_ = lean_box(0);
v___y_3980_ = v_keepAliveTimeout_3966_;
v___y_3981_ = v_respStream_3967_;
v___y_3982_ = v_headerTimeout_3968_;
v___y_3983_ = v_expectData_3969_;
v___y_3984_ = v___y_3991_;
v___y_3985_ = v_currentTimeout_3970_;
v___y_3986_ = v___x_3992_;
goto v___jp_3979_;
}
else
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3993_, 0, v_response_3971_);
v___y_3980_ = v_keepAliveTimeout_3966_;
v___y_3981_ = v_respStream_3967_;
v___y_3982_ = v_headerTimeout_3968_;
v___y_3983_ = v_expectData_3969_;
v___y_3984_ = v___y_3991_;
v___y_3985_ = v_currentTimeout_3970_;
v___y_3986_ = v___x_3993_;
goto v___jp_3979_;
}
}
v___jp_3994_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_socket_3972_);
v___y_3991_ = v___x_3995_;
goto v___jp_3990_;
}
v___jp_3996_:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_box(0);
v___y_3991_ = v___x_3997_;
goto v___jp_3990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3999_, lean_object* v_handlerDispatched_4000_, lean_object* v_keepAliveTimeout_4001_, lean_object* v_respStream_4002_, lean_object* v_headerTimeout_4003_, lean_object* v_expectData_4004_, lean_object* v_currentTimeout_4005_, lean_object* v_response_4006_, lean_object* v_socket_4007_, lean_object* v_requiresData_4008_, lean_object* v_sentMessage_4009_, lean_object* v_reader_4010_, lean_object* v_requestBodyInterested_4011_, lean_object* v_requestBody_4012_, lean_object* v___y_4013_){
_start:
{
uint8_t v_handlerDispatched_boxed_4014_; uint8_t v_requiresData_boxed_4015_; uint8_t v_sentMessage_boxed_4016_; uint8_t v_requestBodyInterested_boxed_4017_; lean_object* v_res_4018_; 
v_handlerDispatched_boxed_4014_ = lean_unbox(v_handlerDispatched_4000_);
v_requiresData_boxed_4015_ = lean_unbox(v_requiresData_4008_);
v_sentMessage_boxed_4016_ = lean_unbox(v_sentMessage_4009_);
v_requestBodyInterested_boxed_4017_ = lean_unbox(v_requestBodyInterested_4011_);
v_res_4018_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3999_, v_handlerDispatched_boxed_4014_, v_keepAliveTimeout_4001_, v_respStream_4002_, v_headerTimeout_4003_, v_expectData_4004_, v_currentTimeout_4005_, v_response_4006_, v_socket_4007_, v_requiresData_boxed_4015_, v_sentMessage_boxed_4016_, v_reader_4010_, v_requestBodyInterested_boxed_4017_, v_requestBody_4012_);
lean_dec_ref(v_reader_4010_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_4019_, lean_object* v_x_4020_){
_start:
{
if (lean_obj_tag(v_x_4020_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v___f_4019_);
v_a_4022_ = lean_ctor_get(v_x_4020_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_x_4020_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4024_ = v_x_4020_;
v_isShared_4025_ = v_isSharedCheck_4030_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v_x_4020_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4030_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; 
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
return v___x_4028_;
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4032_; 
v_a_4031_ = lean_ctor_get(v_x_4020_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v_x_4020_, 1);
v___x_4032_ = lean_apply_2(v___f_4019_, v_a_4031_, lean_box(0));
return v___x_4032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_4033_, lean_object* v_x_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_4033_, v_x_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_4041_, uint8_t v_handlerDispatched_4042_, lean_object* v_keepAliveTimeout_4043_, lean_object* v_respStream_4044_, lean_object* v_headerTimeout_4045_, lean_object* v_expectData_4046_, lean_object* v_currentTimeout_4047_, lean_object* v_response_4048_, lean_object* v_socket_4049_, uint8_t v_requiresData_4050_, uint8_t v_sentMessage_4051_, lean_object* v_reader_4052_, uint8_t v_pullBodyStalled_4053_, uint8_t v_requestBodyOpen_4054_, lean_object* v_requestStream_4055_, uint8_t v_requestBodyInterested_4056_){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___f_4062_; lean_object* v___f_4063_; 
v___x_4058_ = lean_box(v_handlerDispatched_4042_);
v___x_4059_ = lean_box(v_requiresData_4050_);
v___x_4060_ = lean_box(v_sentMessage_4051_);
v___x_4061_ = lean_box(v_requestBodyInterested_4056_);
lean_inc_ref(v_reader_4052_);
v___f_4062_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_4062_, 0, v_connectionContext_4041_);
lean_closure_set(v___f_4062_, 1, v___x_4058_);
lean_closure_set(v___f_4062_, 2, v_keepAliveTimeout_4043_);
lean_closure_set(v___f_4062_, 3, v_respStream_4044_);
lean_closure_set(v___f_4062_, 4, v_headerTimeout_4045_);
lean_closure_set(v___f_4062_, 5, v_expectData_4046_);
lean_closure_set(v___f_4062_, 6, v_currentTimeout_4047_);
lean_closure_set(v___f_4062_, 7, v_response_4048_);
lean_closure_set(v___f_4062_, 8, v_socket_4049_);
lean_closure_set(v___f_4062_, 9, v___x_4059_);
lean_closure_set(v___f_4062_, 10, v___x_4060_);
lean_closure_set(v___f_4062_, 11, v_reader_4052_);
lean_closure_set(v___f_4062_, 12, v___x_4061_);
v___f_4063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4063_, 0, v___f_4062_);
if (v_sentMessage_4051_ == 0)
{
lean_object* v_state_4069_; 
v_state_4069_ = lean_ctor_get(v_reader_4052_, 0);
lean_inc(v_state_4069_);
lean_dec_ref(v_reader_4052_);
if (lean_obj_tag(v_state_4069_) == 2)
{
lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4080_; 
v_isSharedCheck_4080_ = !lean_is_exclusive(v_state_4069_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v_state_4069_, 0);
lean_dec(v_unused_4081_);
v___x_4071_ = v_state_4069_;
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
else
{
lean_dec(v_state_4069_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
if (v_pullBodyStalled_4053_ == 0)
{
if (v_requestBodyOpen_4054_ == 0)
{
lean_del_object(v___x_4071_);
lean_dec_ref(v_requestStream_4055_);
goto v___jp_4064_;
}
else
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set_tag(v___x_4071_, 1);
lean_ctor_set(v___x_4071_, 0, v_requestStream_4055_);
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_requestStream_4055_);
v___x_4074_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
v___x_4077_ = lean_unsigned_to_nat(0u);
v___x_4078_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4077_, v_pullBodyStalled_4053_, v___x_4076_, v___f_4063_);
return v___x_4078_;
}
}
}
else
{
lean_del_object(v___x_4071_);
lean_dec_ref(v_requestStream_4055_);
goto v___jp_4064_;
}
}
}
else
{
lean_dec(v_state_4069_);
lean_dec_ref(v_requestStream_4055_);
goto v___jp_4064_;
}
}
else
{
lean_dec_ref(v_requestStream_4055_);
lean_dec_ref(v_reader_4052_);
goto v___jp_4064_;
}
v___jp_4064_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; lean_object* v___x_4068_; 
v___x_4065_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = 0;
v___x_4068_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4066_, v___x_4067_, v___x_4065_, v___f_4063_);
return v___x_4068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_4082_ = _args[0];
lean_object* v_handlerDispatched_4083_ = _args[1];
lean_object* v_keepAliveTimeout_4084_ = _args[2];
lean_object* v_respStream_4085_ = _args[3];
lean_object* v_headerTimeout_4086_ = _args[4];
lean_object* v_expectData_4087_ = _args[5];
lean_object* v_currentTimeout_4088_ = _args[6];
lean_object* v_response_4089_ = _args[7];
lean_object* v_socket_4090_ = _args[8];
lean_object* v_requiresData_4091_ = _args[9];
lean_object* v_sentMessage_4092_ = _args[10];
lean_object* v_reader_4093_ = _args[11];
lean_object* v_pullBodyStalled_4094_ = _args[12];
lean_object* v_requestBodyOpen_4095_ = _args[13];
lean_object* v_requestStream_4096_ = _args[14];
lean_object* v_requestBodyInterested_4097_ = _args[15];
lean_object* v___y_4098_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_4099_; uint8_t v_requiresData_boxed_4100_; uint8_t v_sentMessage_boxed_4101_; uint8_t v_pullBodyStalled_boxed_4102_; uint8_t v_requestBodyOpen_boxed_4103_; uint8_t v_requestBodyInterested_boxed_4104_; lean_object* v_res_4105_; 
v_handlerDispatched_boxed_4099_ = lean_unbox(v_handlerDispatched_4083_);
v_requiresData_boxed_4100_ = lean_unbox(v_requiresData_4091_);
v_sentMessage_boxed_4101_ = lean_unbox(v_sentMessage_4092_);
v_pullBodyStalled_boxed_4102_ = lean_unbox(v_pullBodyStalled_4094_);
v_requestBodyOpen_boxed_4103_ = lean_unbox(v_requestBodyOpen_4095_);
v_requestBodyInterested_boxed_4104_ = lean_unbox(v_requestBodyInterested_4097_);
v_res_4105_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_4082_, v_handlerDispatched_boxed_4099_, v_keepAliveTimeout_4084_, v_respStream_4085_, v_headerTimeout_4086_, v_expectData_4087_, v_currentTimeout_4088_, v_response_4089_, v_socket_4090_, v_requiresData_boxed_4100_, v_sentMessage_boxed_4101_, v_reader_4093_, v_pullBodyStalled_boxed_4102_, v_requestBodyOpen_boxed_4103_, v_requestStream_4096_, v_requestBodyInterested_boxed_4104_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_4106_, lean_object* v_x_4107_){
_start:
{
if (lean_obj_tag(v_x_4107_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4117_; 
lean_dec_ref(v___f_4106_);
v_a_4109_ = lean_ctor_get(v_x_4107_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4111_ = v_x_4107_;
v_isShared_4112_ = v_isSharedCheck_4117_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v_x_4107_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4117_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4119_; 
v_a_4118_ = lean_ctor_get(v_x_4107_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v_x_4107_, 1);
v___x_4119_ = lean_apply_2(v___f_4106_, v_a_4118_, lean_box(0));
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_4120_, v_x_4121_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_4129_, uint8_t v_handlerDispatched_4130_, lean_object* v_keepAliveTimeout_4131_, lean_object* v_respStream_4132_, lean_object* v_headerTimeout_4133_, lean_object* v_expectData_4134_, lean_object* v_currentTimeout_4135_, lean_object* v_response_4136_, lean_object* v_socket_4137_, uint8_t v_requiresData_4138_, uint8_t v_sentMessage_4139_, lean_object* v_reader_4140_, uint8_t v_pullBodyStalled_4141_, lean_object* v_requestStream_4142_, uint8_t v_requestBodyOpen_4143_){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___f_4150_; lean_object* v___f_4151_; 
v___x_4145_ = lean_box(v_handlerDispatched_4130_);
v___x_4146_ = lean_box(v_requiresData_4138_);
v___x_4147_ = lean_box(v_sentMessage_4139_);
v___x_4148_ = lean_box(v_pullBodyStalled_4141_);
v___x_4149_ = lean_box(v_requestBodyOpen_4143_);
lean_inc_ref(v_requestStream_4142_);
lean_inc_ref(v_reader_4140_);
v___f_4150_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_4150_, 0, v_connectionContext_4129_);
lean_closure_set(v___f_4150_, 1, v___x_4145_);
lean_closure_set(v___f_4150_, 2, v_keepAliveTimeout_4131_);
lean_closure_set(v___f_4150_, 3, v_respStream_4132_);
lean_closure_set(v___f_4150_, 4, v_headerTimeout_4133_);
lean_closure_set(v___f_4150_, 5, v_expectData_4134_);
lean_closure_set(v___f_4150_, 6, v_currentTimeout_4135_);
lean_closure_set(v___f_4150_, 7, v_response_4136_);
lean_closure_set(v___f_4150_, 8, v_socket_4137_);
lean_closure_set(v___f_4150_, 9, v___x_4146_);
lean_closure_set(v___f_4150_, 10, v___x_4147_);
lean_closure_set(v___f_4150_, 11, v_reader_4140_);
lean_closure_set(v___f_4150_, 12, v___x_4148_);
lean_closure_set(v___f_4150_, 13, v___x_4149_);
lean_closure_set(v___f_4150_, 14, v_requestStream_4142_);
v___f_4151_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4151_, 0, v___f_4150_);
if (v_sentMessage_4139_ == 0)
{
lean_object* v_state_4157_; 
v_state_4157_ = lean_ctor_get(v_reader_4140_, 0);
lean_inc(v_state_4157_);
lean_dec_ref(v_reader_4140_);
if (lean_obj_tag(v_state_4157_) == 2)
{
lean_dec_ref_known(v_state_4157_, 1);
if (v_requestBodyOpen_4143_ == 0)
{
lean_dec_ref(v_requestStream_4142_);
goto v___jp_4152_;
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4158_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_4142_);
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4159_, v_sentMessage_4139_, v___x_4158_, v___f_4151_);
return v___x_4160_;
}
}
else
{
lean_dec(v_state_4157_);
lean_dec_ref(v_requestStream_4142_);
goto v___jp_4152_;
}
}
else
{
lean_dec_ref(v_requestStream_4142_);
lean_dec_ref(v_reader_4140_);
goto v___jp_4152_;
}
v___jp_4152_:
{
uint8_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = 0;
v___x_4154_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4155_, v___x_4153_, v___x_4154_, v___f_4151_);
return v___x_4156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_4161_, lean_object* v_handlerDispatched_4162_, lean_object* v_keepAliveTimeout_4163_, lean_object* v_respStream_4164_, lean_object* v_headerTimeout_4165_, lean_object* v_expectData_4166_, lean_object* v_currentTimeout_4167_, lean_object* v_response_4168_, lean_object* v_socket_4169_, lean_object* v_requiresData_4170_, lean_object* v_sentMessage_4171_, lean_object* v_reader_4172_, lean_object* v_pullBodyStalled_4173_, lean_object* v_requestStream_4174_, lean_object* v_requestBodyOpen_4175_, lean_object* v___y_4176_){
_start:
{
uint8_t v_handlerDispatched_boxed_4177_; uint8_t v_requiresData_boxed_4178_; uint8_t v_sentMessage_boxed_4179_; uint8_t v_pullBodyStalled_boxed_4180_; uint8_t v_requestBodyOpen_boxed_4181_; lean_object* v_res_4182_; 
v_handlerDispatched_boxed_4177_ = lean_unbox(v_handlerDispatched_4162_);
v_requiresData_boxed_4178_ = lean_unbox(v_requiresData_4170_);
v_sentMessage_boxed_4179_ = lean_unbox(v_sentMessage_4171_);
v_pullBodyStalled_boxed_4180_ = lean_unbox(v_pullBodyStalled_4173_);
v_requestBodyOpen_boxed_4181_ = lean_unbox(v_requestBodyOpen_4175_);
v_res_4182_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_4161_, v_handlerDispatched_boxed_4177_, v_keepAliveTimeout_4163_, v_respStream_4164_, v_headerTimeout_4165_, v_expectData_4166_, v_currentTimeout_4167_, v_response_4168_, v_socket_4169_, v_requiresData_boxed_4178_, v_sentMessage_boxed_4179_, v_reader_4172_, v_pullBodyStalled_boxed_4180_, v_requestStream_4174_, v_requestBodyOpen_boxed_4181_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_4183_, lean_object* v___f_4184_, uint8_t v___x_4185_, lean_object* v_x_4186_){
_start:
{
uint8_t v___y_4189_; 
if (lean_obj_tag(v_x_4186_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4203_; 
lean_dec_ref(v___f_4184_);
v_a_4195_ = lean_ctor_get(v_x_4186_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_x_4186_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4197_ = v_x_4186_;
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v_x_4186_);
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
lean_object* v_a_4204_; uint8_t v___x_4205_; 
v_a_4204_ = lean_ctor_get(v_x_4186_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v_x_4186_, 1);
v___x_4205_ = lean_unbox(v_a_4204_);
lean_dec(v_a_4204_);
if (v___x_4205_ == 0)
{
v___y_4189_ = v___x_4185_;
goto v___jp_4188_;
}
else
{
v___y_4189_ = v_sentMessage_4183_;
goto v___jp_4188_;
}
}
v___jp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4190_ = lean_box(v___y_4189_);
v___x_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4193_, v_sentMessage_4183_, v___x_4192_, v___f_4184_);
return v___x_4194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4206_, lean_object* v___f_4207_, lean_object* v___x_4208_, lean_object* v_x_4209_, lean_object* v___y_4210_){
_start:
{
uint8_t v_sentMessage_boxed_4211_; uint8_t v___x_3791__boxed_4212_; lean_object* v_res_4213_; 
v_sentMessage_boxed_4211_ = lean_unbox(v_sentMessage_4206_);
v___x_3791__boxed_4212_ = lean_unbox(v___x_4208_);
v_res_4213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4211_, v___f_4207_, v___x_3791__boxed_4212_, v_x_4209_);
return v_res_4213_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___f_4214_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4215_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4216_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4217_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4217_, 0, lean_box(0));
lean_closure_set(v___x_4217_, 1, lean_box(0));
lean_closure_set(v___x_4217_, 2, v___x_4216_);
lean_closure_set(v___x_4217_, 3, lean_box(0));
lean_closure_set(v___x_4217_, 4, lean_box(0));
lean_closure_set(v___x_4217_, 5, v___x_4215_);
lean_closure_set(v___x_4217_, 6, v___f_4214_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4218_, lean_object* v_connectionContext_4219_, lean_object* v_state_4220_){
_start:
{
lean_object* v_machine_4222_; lean_object* v_writer_4223_; lean_object* v_requestStream_4224_; lean_object* v_keepAliveTimeout_4225_; lean_object* v_currentTimeout_4226_; lean_object* v_headerTimeout_4227_; lean_object* v_response_4228_; lean_object* v_respStream_4229_; uint8_t v_requiresData_4230_; lean_object* v_expectData_4231_; uint8_t v_handlerDispatched_4232_; lean_object* v_reader_4233_; uint8_t v_pullBodyStalled_4234_; uint8_t v_sentMessage_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___f_4240_; lean_object* v___f_4241_; uint8_t v___y_4243_; 
v_machine_4222_ = lean_ctor_get(v_state_4220_, 0);
lean_inc_ref(v_machine_4222_);
v_writer_4223_ = lean_ctor_get(v_machine_4222_, 1);
lean_inc_ref(v_writer_4223_);
v_requestStream_4224_ = lean_ctor_get(v_state_4220_, 1);
lean_inc_ref_n(v_requestStream_4224_, 2);
v_keepAliveTimeout_4225_ = lean_ctor_get(v_state_4220_, 2);
lean_inc(v_keepAliveTimeout_4225_);
v_currentTimeout_4226_ = lean_ctor_get(v_state_4220_, 3);
lean_inc(v_currentTimeout_4226_);
v_headerTimeout_4227_ = lean_ctor_get(v_state_4220_, 4);
lean_inc(v_headerTimeout_4227_);
v_response_4228_ = lean_ctor_get(v_state_4220_, 5);
lean_inc_ref(v_response_4228_);
v_respStream_4229_ = lean_ctor_get(v_state_4220_, 6);
lean_inc(v_respStream_4229_);
v_requiresData_4230_ = lean_ctor_get_uint8(v_state_4220_, sizeof(void*)*9);
v_expectData_4231_ = lean_ctor_get(v_state_4220_, 7);
lean_inc(v_expectData_4231_);
v_handlerDispatched_4232_ = lean_ctor_get_uint8(v_state_4220_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4220_);
v_reader_4233_ = lean_ctor_get(v_machine_4222_, 0);
lean_inc_ref_n(v_reader_4233_, 2);
v_pullBodyStalled_4234_ = lean_ctor_get_uint8(v_machine_4222_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4222_);
v_sentMessage_4235_ = lean_ctor_get_uint8(v_writer_4223_, sizeof(void*)*6);
lean_dec_ref(v_writer_4223_);
v___x_4236_ = lean_box(v_handlerDispatched_4232_);
v___x_4237_ = lean_box(v_requiresData_4230_);
v___x_4238_ = lean_box(v_sentMessage_4235_);
v___x_4239_ = lean_box(v_pullBodyStalled_4234_);
v___f_4240_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4240_, 0, v_connectionContext_4219_);
lean_closure_set(v___f_4240_, 1, v___x_4236_);
lean_closure_set(v___f_4240_, 2, v_keepAliveTimeout_4225_);
lean_closure_set(v___f_4240_, 3, v_respStream_4229_);
lean_closure_set(v___f_4240_, 4, v_headerTimeout_4227_);
lean_closure_set(v___f_4240_, 5, v_expectData_4231_);
lean_closure_set(v___f_4240_, 6, v_currentTimeout_4226_);
lean_closure_set(v___f_4240_, 7, v_response_4228_);
lean_closure_set(v___f_4240_, 8, v_socket_4218_);
lean_closure_set(v___f_4240_, 9, v___x_4237_);
lean_closure_set(v___f_4240_, 10, v___x_4238_);
lean_closure_set(v___f_4240_, 11, v_reader_4233_);
lean_closure_set(v___f_4240_, 12, v___x_4239_);
lean_closure_set(v___f_4240_, 13, v_requestStream_4224_);
v___f_4241_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4241_, 0, v___f_4240_);
if (v_sentMessage_4235_ == 0)
{
lean_object* v_state_4249_; 
v_state_4249_ = lean_ctor_get(v_reader_4233_, 0);
lean_inc(v_state_4249_);
lean_dec_ref(v_reader_4233_);
if (lean_obj_tag(v_state_4249_) == 2)
{
lean_object* v___x_4250_; lean_object* v___f_4251_; lean_object* v___f_4252_; lean_object* v___x_4253_; lean_object* v___x_3305__overap_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___f_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_dec_ref_known(v_state_4249_, 1);
v___x_4250_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4251_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4252_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4253_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3305__overap_4254_ = l_Std_Mutex_atomically___redArg(v___x_4250_, v___f_4251_, v___f_4252_, v_requestStream_4224_, v___x_4253_);
v___x_4255_ = lean_apply_1(v___x_3305__overap_4254_, lean_box(0));
v___x_4256_ = 1;
v___x_4257_ = lean_box(v_sentMessage_4235_);
v___x_4258_ = lean_box(v___x_4256_);
v___f_4259_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4259_, 0, v___x_4257_);
lean_closure_set(v___f_4259_, 1, v___f_4241_);
lean_closure_set(v___f_4259_, 2, v___x_4258_);
v___x_4260_ = lean_unsigned_to_nat(0u);
v___x_4261_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4260_, v_sentMessage_4235_, v___x_4255_, v___f_4259_);
return v___x_4261_;
}
else
{
lean_dec(v_state_4249_);
lean_dec_ref(v_requestStream_4224_);
v___y_4243_ = v_sentMessage_4235_;
goto v___jp_4242_;
}
}
else
{
uint8_t v___x_4262_; 
lean_dec_ref(v_reader_4233_);
lean_dec_ref(v_requestStream_4224_);
v___x_4262_ = 0;
v___y_4243_ = v___x_4262_;
goto v___jp_4242_;
}
v___jp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4244_ = lean_box(v___y_4243_);
v___x_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
v___x_4247_ = lean_unsigned_to_nat(0u);
v___x_4248_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4247_, v___y_4243_, v___x_4246_, v___f_4241_);
return v___x_4248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4263_, lean_object* v_connectionContext_4264_, lean_object* v_state_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4263_, v_connectionContext_4264_, v_state_4265_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4268_, lean_object* v_00_u03b2_4269_, lean_object* v_inst_4270_, lean_object* v_socket_4271_, lean_object* v_connectionContext_4272_, lean_object* v_state_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4271_, v_connectionContext_4272_, v_state_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4276_, lean_object* v_00_u03b2_4277_, lean_object* v_inst_4278_, lean_object* v_socket_4279_, lean_object* v_connectionContext_4280_, lean_object* v_state_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4276_, v_00_u03b2_4277_, v_inst_4278_, v_socket_4279_, v_connectionContext_4280_, v_state_4281_);
lean_dec_ref(v_inst_4278_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4284_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4294_; 
v_a_4286_ = lean_ctor_get(v_x_4284_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v_x_4284_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4288_ = v_x_4284_;
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v_x_4284_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
return v___x_4292_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4313_; 
v_a_4295_ = lean_ctor_get(v_x_4284_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v_x_4284_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4297_ = v_x_4284_;
v_isShared_4298_ = v_isSharedCheck_4313_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v_x_4284_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4313_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v_snd_4299_; uint8_t v___x_4300_; 
v_snd_4299_ = lean_ctor_get(v_a_4295_, 1);
v___x_4300_ = lean_unbox(v_snd_4299_);
if (v___x_4300_ == 0)
{
lean_object* v_fst_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v_fst_4301_ = lean_ctor_get(v_a_4295_, 0);
lean_inc(v_fst_4301_);
lean_dec(v_a_4295_);
v___x_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4302_, 0, v_fst_4301_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4302_);
v___x_4304_ = v___x_4297_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; 
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
return v___x_4305_;
}
}
else
{
lean_object* v_fst_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v_fst_4307_ = lean_ctor_get(v_a_4295_, 0);
lean_inc(v_fst_4307_);
lean_dec(v_a_4295_);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v_fst_4307_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4308_);
v___x_4310_ = v___x_4297_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4311_; 
v___x_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
return v___x_4311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4314_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4317_){
_start:
{
if (lean_obj_tag(v_x_4317_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4327_; 
v_a_4319_ = lean_ctor_get(v_x_4317_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_x_4317_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4321_ = v_x_4317_;
v_isShared_4322_ = v_isSharedCheck_4327_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v_x_4317_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4327_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4337_; 
v_a_4328_ = lean_ctor_get(v_x_4317_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v_x_4317_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4330_ = v_x_4317_;
v_isShared_4331_ = v_isSharedCheck_4337_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v_x_4317_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4337_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4332_; lean_object* v___x_4334_; 
v___x_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4332_, 0, v_a_4328_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v___x_4332_);
v___x_4334_ = v___x_4330_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
return v___x_4335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4338_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4345_){
_start:
{
if (lean_obj_tag(v_x_4345_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4355_; 
v_a_4347_ = lean_ctor_get(v_x_4345_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_x_4345_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4349_ = v_x_4345_;
v_isShared_4350_ = v_isSharedCheck_4355_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v_x_4345_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4355_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4353_; 
v___x_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
return v___x_4353_;
}
}
}
else
{
lean_object* v___x_4356_; 
lean_dec_ref_known(v_x_4345_, 1);
v___x_4356_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4357_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4360_, lean_object* v_handler_4361_, lean_object* v___f_4362_, lean_object* v_x_4363_){
_start:
{
if (lean_obj_tag(v_x_4363_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; 
v_a_4365_ = lean_ctor_get(v_x_4363_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v_x_4363_, 1);
v___x_4366_ = lean_apply_3(v_onFailure_4360_, v_handler_4361_, v_a_4365_, lean_box(0));
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = 0;
v___x_4369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4367_, v___x_4368_, v___x_4366_, v___f_4362_);
return v___x_4369_;
}
else
{
lean_object* v___x_4370_; 
lean_dec_ref(v___f_4362_);
lean_dec(v_handler_4361_);
lean_dec_ref(v_onFailure_4360_);
v___x_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4370_, 0, v_x_4363_);
return v___x_4370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4371_, lean_object* v_handler_4372_, lean_object* v___f_4373_, lean_object* v_x_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4371_, v_handler_4372_, v___f_4373_, v_x_4374_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4377_, lean_object* v_socket_4378_, lean_object* v_____r_4379_){
_start:
{
lean_object* v_val_4382_; lean_object* v_close_4384_; lean_object* v___x_4385_; 
v_close_4384_ = lean_ctor_get(v_inst_4377_, 3);
lean_inc_ref(v_close_4384_);
lean_dec_ref(v_inst_4377_);
v___x_4385_ = lean_apply_2(v_close_4384_, v_socket_4378_, lean_box(0));
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set_tag(v___x_4388_, 1);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
v_val_4382_ = v___x_4391_;
goto v___jp_4381_;
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
v_a_4394_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4385_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4385_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set_tag(v___x_4396_, 0);
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
v_val_4382_ = v___x_4399_;
goto v___jp_4381_;
}
}
}
v___jp_4381_:
{
lean_object* v___x_4383_; 
v___x_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4383_, 0, v_val_4382_);
return v___x_4383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4402_, lean_object* v_socket_4403_, lean_object* v_____r_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4402_, v_socket_4403_, v_____r_4404_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4407_, lean_object* v_x_4408_){
_start:
{
if (lean_obj_tag(v_x_4408_) == 0)
{
lean_object* v___x_4410_; 
lean_dec_ref(v___f_4407_);
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v_x_4408_);
return v___x_4410_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v_x_4408_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v_x_4408_, 1);
v___x_4412_ = lean_apply_2(v___f_4407_, v_a_4411_, lean_box(0));
return v___x_4412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4413_, lean_object* v_x_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4413_, v_x_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4417_, lean_object* v_val_4418_, lean_object* v___f_4419_, lean_object* v___f_4420_, lean_object* v_x_4421_){
_start:
{
if (lean_obj_tag(v_x_4421_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4431_; 
lean_dec_ref(v___f_4420_);
lean_dec_ref(v___f_4419_);
lean_dec(v_val_4418_);
lean_dec_ref(v_close_4417_);
v_a_4423_ = lean_ctor_get(v_x_4421_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_x_4421_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4425_ = v_x_4421_;
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v_x_4421_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
}
else
{
lean_object* v_a_4432_; uint8_t v___x_4433_; 
v_a_4432_ = lean_ctor_get(v_x_4421_, 0);
lean_inc(v_a_4432_);
lean_dec_ref_known(v_x_4421_, 1);
v___x_4433_ = lean_unbox(v_a_4432_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; 
lean_dec_ref(v___f_4420_);
v___x_4434_ = lean_apply_2(v_close_4417_, v_val_4418_, lean_box(0));
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = lean_unbox(v_a_4432_);
lean_dec(v_a_4432_);
v___x_4437_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4435_, v___x_4436_, v___x_4434_, v___f_4419_);
return v___x_4437_;
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec(v_a_4432_);
lean_dec_ref(v___f_4419_);
lean_dec(v_val_4418_);
lean_dec_ref(v_close_4417_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_apply_2(v___f_4420_, v___x_4438_, lean_box(0));
return v___x_4439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4440_, lean_object* v_val_4441_, lean_object* v___f_4442_, lean_object* v___f_4443_, lean_object* v_x_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4440_, v_val_4441_, v___f_4442_, v___f_4443_, v_x_4444_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4447_, lean_object* v_responseBodyInstance_4448_, lean_object* v___f_4449_, lean_object* v___f_4450_, lean_object* v_____r_4451_){
_start:
{
if (lean_obj_tag(v_respStream_4447_) == 1)
{
lean_object* v_val_4453_; lean_object* v_close_4454_; lean_object* v_isClosed_4455_; lean_object* v___x_4456_; lean_object* v___f_4457_; lean_object* v___x_4458_; uint8_t v___x_4459_; lean_object* v___x_4460_; 
v_val_4453_ = lean_ctor_get(v_respStream_4447_, 0);
lean_inc_n(v_val_4453_, 2);
lean_dec_ref_known(v_respStream_4447_, 1);
v_close_4454_ = lean_ctor_get(v_responseBodyInstance_4448_, 1);
lean_inc_ref(v_close_4454_);
v_isClosed_4455_ = lean_ctor_get(v_responseBodyInstance_4448_, 2);
lean_inc_ref(v_isClosed_4455_);
lean_dec_ref(v_responseBodyInstance_4448_);
v___x_4456_ = lean_apply_2(v_isClosed_4455_, v_val_4453_, lean_box(0));
v___f_4457_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4457_, 0, v_close_4454_);
lean_closure_set(v___f_4457_, 1, v_val_4453_);
lean_closure_set(v___f_4457_, 2, v___f_4449_);
lean_closure_set(v___f_4457_, 3, v___f_4450_);
v___x_4458_ = lean_unsigned_to_nat(0u);
v___x_4459_ = 0;
v___x_4460_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4458_, v___x_4459_, v___x_4456_, v___f_4457_);
return v___x_4460_;
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
lean_dec_ref(v___f_4449_);
lean_dec_ref(v_responseBodyInstance_4448_);
lean_dec(v_respStream_4447_);
v___x_4461_ = lean_box(0);
v___x_4462_ = lean_apply_2(v___f_4450_, v___x_4461_, lean_box(0));
return v___x_4462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4463_, lean_object* v_responseBodyInstance_4464_, lean_object* v___f_4465_, lean_object* v___f_4466_, lean_object* v_____r_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4463_, v_responseBodyInstance_4464_, v___f_4465_, v___f_4466_, v_____r_4467_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4470_, lean_object* v___f_4471_, lean_object* v___f_4472_, lean_object* v_x_4473_){
_start:
{
if (lean_obj_tag(v_x_4473_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v___f_4472_);
lean_dec_ref(v___f_4471_);
lean_dec_ref(v_requestStream_4470_);
v_a_4475_ = lean_ctor_get(v_x_4473_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_x_4473_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4477_ = v_x_4473_;
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v_x_4473_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4481_; 
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
return v___x_4481_;
}
}
}
else
{
lean_object* v_a_4484_; uint8_t v___x_4485_; 
v_a_4484_ = lean_ctor_get(v_x_4473_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v_x_4473_, 1);
v___x_4485_ = lean_unbox(v_a_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; lean_object* v___x_4489_; 
lean_dec_ref(v___f_4472_);
v___x_4486_ = l_Std_Http_Body_Stream_close(v_requestStream_4470_);
v___x_4487_ = lean_unsigned_to_nat(0u);
v___x_4488_ = lean_unbox(v_a_4484_);
lean_dec(v_a_4484_);
v___x_4489_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4487_, v___x_4488_, v___x_4486_, v___f_4471_);
return v___x_4489_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_dec(v_a_4484_);
lean_dec_ref(v___f_4471_);
lean_dec_ref(v_requestStream_4470_);
v___x_4490_ = lean_box(0);
v___x_4491_ = lean_apply_2(v___f_4472_, v___x_4490_, lean_box(0));
return v___x_4491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4492_, lean_object* v___f_4493_, lean_object* v___f_4494_, lean_object* v_x_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4492_, v___f_4493_, v___f_4494_, v_x_4495_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4498_, lean_object* v_responseBodyInstance_4499_, lean_object* v___f_4500_, lean_object* v___f_4501_, lean_object* v_x_4502_){
_start:
{
if (lean_obj_tag(v_x_4502_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref(v___f_4501_);
lean_dec_ref(v___f_4500_);
lean_dec_ref(v_responseBodyInstance_4499_);
lean_dec_ref(v___f_4498_);
v_a_4504_ = lean_ctor_get(v_x_4502_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_x_4502_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4506_ = v_x_4502_;
v_isShared_4507_ = v_isSharedCheck_4512_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v_x_4502_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4512_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4510_; 
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v_requestStream_4514_; lean_object* v_respStream_4515_; lean_object* v___x_4516_; lean_object* v___f_4517_; lean_object* v___f_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_5017__overap_4521_; lean_object* v___x_4522_; lean_object* v___f_4523_; lean_object* v___f_4524_; lean_object* v___f_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; lean_object* v___x_4528_; 
v_a_4513_ = lean_ctor_get(v_x_4502_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v_x_4502_, 1);
v_requestStream_4514_ = lean_ctor_get(v_a_4513_, 1);
lean_inc_ref_n(v_requestStream_4514_, 2);
v_respStream_4515_ = lean_ctor_get(v_a_4513_, 6);
lean_inc(v_respStream_4515_);
lean_dec(v_a_4513_);
v___x_4516_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4517_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4518_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4519_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4520_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4520_, 0, lean_box(0));
lean_closure_set(v___x_4520_, 1, lean_box(0));
lean_closure_set(v___x_4520_, 2, v___x_4516_);
lean_closure_set(v___x_4520_, 3, lean_box(0));
lean_closure_set(v___x_4520_, 4, lean_box(0));
lean_closure_set(v___x_4520_, 5, v___x_4519_);
lean_closure_set(v___x_4520_, 6, v___f_4498_);
v___x_5017__overap_4521_ = l_Std_Mutex_atomically___redArg(v___x_4516_, v___f_4517_, v___f_4518_, v_requestStream_4514_, v___x_4520_);
v___x_4522_ = lean_apply_1(v___x_5017__overap_4521_, lean_box(0));
v___f_4523_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4523_, 0, v_respStream_4515_);
lean_closure_set(v___f_4523_, 1, v_responseBodyInstance_4499_);
lean_closure_set(v___f_4523_, 2, v___f_4500_);
lean_closure_set(v___f_4523_, 3, v___f_4501_);
lean_inc_ref(v___f_4523_);
v___f_4524_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4524_, 0, v___f_4523_);
v___f_4525_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4525_, 0, v_requestStream_4514_);
lean_closure_set(v___f_4525_, 1, v___f_4524_);
lean_closure_set(v___f_4525_, 2, v___f_4523_);
v___x_4526_ = lean_unsigned_to_nat(0u);
v___x_4527_ = 0;
v___x_4528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4526_, v___x_4527_, v___x_4522_, v___f_4525_);
return v___x_4528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4529_, lean_object* v_responseBodyInstance_4530_, lean_object* v___f_4531_, lean_object* v___f_4532_, lean_object* v_x_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4529_, v_responseBodyInstance_4530_, v___f_4531_, v___f_4532_, v_x_4533_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4536_, lean_object* v_responseBodyInstance_4537_, lean_object* v_handler_4538_, lean_object* v_config_4539_, lean_object* v___x_4540_, uint8_t v___x_4541_, lean_object* v___f_4542_, lean_object* v_x_4543_){
_start:
{
if (lean_obj_tag(v_x_4543_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4553_; 
lean_dec_ref(v___f_4542_);
lean_dec_ref(v___x_4540_);
lean_dec_ref(v_config_4539_);
lean_dec(v_handler_4538_);
lean_dec_ref(v_responseBodyInstance_4537_);
lean_dec_ref(v_h_4536_);
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
lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v_a_4554_ = lean_ctor_get(v_x_4543_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v_x_4543_, 1);
v___x_4555_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4536_, v_responseBodyInstance_4537_, v_handler_4538_, v_config_4539_, v_a_4554_, v___x_4540_);
v___x_4556_ = lean_unsigned_to_nat(0u);
v___x_4557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4556_, v___x_4541_, v___x_4555_, v___f_4542_);
return v___x_4557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4558_, lean_object* v_responseBodyInstance_4559_, lean_object* v_handler_4560_, lean_object* v_config_4561_, lean_object* v___x_4562_, lean_object* v___x_4563_, lean_object* v___f_4564_, lean_object* v_x_4565_, lean_object* v___y_4566_){
_start:
{
uint8_t v___x_5688__boxed_4567_; lean_object* v_res_4568_; 
v___x_5688__boxed_4567_ = lean_unbox(v___x_4563_);
v_res_4568_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4558_, v_responseBodyInstance_4559_, v_handler_4560_, v_config_4561_, v___x_4562_, v___x_5688__boxed_4567_, v___f_4564_, v_x_4565_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4569_, lean_object* v_h_4570_, lean_object* v_responseBodyInstance_4571_, lean_object* v_config_4572_, lean_object* v_handler_4573_, uint8_t v___x_4574_, lean_object* v___f_4575_, lean_object* v_x_4576_){
_start:
{
if (lean_obj_tag(v_x_4576_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v___f_4575_);
lean_dec(v_handler_4573_);
lean_dec_ref(v_config_4572_);
lean_dec_ref(v_responseBodyInstance_4571_);
lean_dec_ref(v_h_4570_);
lean_dec_ref(v_inst_4569_);
v_a_4578_ = lean_ctor_get(v_x_4576_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_x_4576_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4580_ = v_x_4576_;
v_isShared_4581_ = v_isSharedCheck_4586_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v_x_4576_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4586_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v_a_4587_ = lean_ctor_get(v_x_4576_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v_x_4576_, 1);
v___x_4588_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4569_, v_h_4570_, v_responseBodyInstance_4571_, v_config_4572_, v_handler_4573_, v_a_4587_);
v___x_4589_ = lean_unsigned_to_nat(0u);
v___x_4590_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4589_, v___x_4574_, v___x_4588_, v___f_4575_);
return v___x_4590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4591_, lean_object* v_h_4592_, lean_object* v_responseBodyInstance_4593_, lean_object* v_config_4594_, lean_object* v_handler_4595_, lean_object* v___x_4596_, lean_object* v___f_4597_, lean_object* v_x_4598_, lean_object* v___y_4599_){
_start:
{
uint8_t v___x_5729__boxed_4600_; lean_object* v_res_4601_; 
v___x_5729__boxed_4600_ = lean_unbox(v___x_4596_);
v_res_4601_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4591_, v_h_4592_, v_responseBodyInstance_4593_, v_config_4594_, v_handler_4595_, v___x_5729__boxed_4600_, v___f_4597_, v_x_4598_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4602_, lean_object* v_socket_4603_, lean_object* v_connectionContext_4604_, lean_object* v_h_4605_, lean_object* v_responseBodyInstance_4606_, lean_object* v_handler_4607_, lean_object* v_config_4608_, lean_object* v___f_4609_, lean_object* v_inst_4610_, lean_object* v_x_4611_){
_start:
{
if (lean_obj_tag(v_x_4611_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4621_; 
lean_dec_ref(v_inst_4610_);
lean_dec_ref(v___f_4609_);
lean_dec_ref(v_config_4608_);
lean_dec(v_handler_4607_);
lean_dec_ref(v_responseBodyInstance_4606_);
lean_dec_ref(v_h_4605_);
lean_dec_ref(v_connectionContext_4604_);
lean_dec(v_socket_4603_);
v_a_4613_ = lean_ctor_get(v_x_4611_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_x_4611_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4615_ = v_x_4611_;
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v_x_4611_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
return v___x_4619_;
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4656_; 
v_a_4622_ = lean_ctor_get(v_x_4611_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v_x_4611_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4624_ = v_x_4611_;
v_isShared_4625_ = v_isSharedCheck_4656_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v_x_4611_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4656_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v_machine_4632_; lean_object* v_requestStream_4633_; lean_object* v_keepAliveTimeout_4634_; lean_object* v_currentTimeout_4635_; lean_object* v_headerTimeout_4636_; lean_object* v_response_4637_; lean_object* v_respStream_4638_; uint8_t v_requiresData_4639_; lean_object* v_expectData_4640_; uint8_t v_handlerDispatched_4641_; lean_object* v_pendingHead_4642_; 
v_machine_4632_ = lean_ctor_get(v_a_4622_, 0);
v_requestStream_4633_ = lean_ctor_get(v_a_4622_, 1);
v_keepAliveTimeout_4634_ = lean_ctor_get(v_a_4622_, 2);
v_currentTimeout_4635_ = lean_ctor_get(v_a_4622_, 3);
v_headerTimeout_4636_ = lean_ctor_get(v_a_4622_, 4);
v_response_4637_ = lean_ctor_get(v_a_4622_, 5);
v_respStream_4638_ = lean_ctor_get(v_a_4622_, 6);
v_requiresData_4639_ = lean_ctor_get_uint8(v_a_4622_, sizeof(void*)*9);
v_expectData_4640_ = lean_ctor_get(v_a_4622_, 7);
v_handlerDispatched_4641_ = lean_ctor_get_uint8(v_a_4622_, sizeof(void*)*9 + 1);
v_pendingHead_4642_ = lean_ctor_get(v_a_4622_, 8);
if (v_requiresData_4639_ == 0)
{
if (v_handlerDispatched_4641_ == 0)
{
if (lean_obj_tag(v_respStream_4638_) == 0)
{
lean_object* v_writer_4652_; uint8_t v_sentMessage_4653_; 
v_writer_4652_ = lean_ctor_get(v_machine_4632_, 1);
v_sentMessage_4653_ = lean_ctor_get_uint8(v_writer_4652_, sizeof(void*)*6);
if (v_sentMessage_4653_ == 0)
{
lean_object* v_reader_4654_; lean_object* v_state_4655_; 
v_reader_4654_ = lean_ctor_get(v_machine_4632_, 0);
v_state_4655_ = lean_ctor_get(v_reader_4654_, 0);
if (lean_obj_tag(v_state_4655_) == 2)
{
lean_inc(v_respStream_4638_);
lean_inc(v_pendingHead_4642_);
lean_inc(v_expectData_4640_);
lean_inc_ref(v_response_4637_);
lean_inc(v_headerTimeout_4636_);
lean_inc(v_currentTimeout_4635_);
lean_inc(v_keepAliveTimeout_4634_);
lean_inc_ref(v_requestStream_4633_);
lean_inc_ref(v_machine_4632_);
lean_del_object(v___x_4624_);
lean_dec(v_a_4622_);
goto v___jp_4643_;
}
else
{
lean_dec_ref(v_inst_4610_);
lean_dec_ref(v___f_4609_);
lean_dec_ref(v_config_4608_);
lean_dec(v_handler_4607_);
lean_dec_ref(v_responseBodyInstance_4606_);
lean_dec_ref(v_h_4605_);
lean_dec_ref(v_connectionContext_4604_);
lean_dec(v_socket_4603_);
goto v___jp_4626_;
}
}
else
{
lean_dec_ref(v_inst_4610_);
lean_dec_ref(v___f_4609_);
lean_dec_ref(v_config_4608_);
lean_dec(v_handler_4607_);
lean_dec_ref(v_responseBodyInstance_4606_);
lean_dec_ref(v_h_4605_);
lean_dec_ref(v_connectionContext_4604_);
lean_dec(v_socket_4603_);
goto v___jp_4626_;
}
}
else
{
lean_inc_ref(v_respStream_4638_);
lean_inc(v_pendingHead_4642_);
lean_inc(v_expectData_4640_);
lean_inc_ref(v_response_4637_);
lean_inc(v_headerTimeout_4636_);
lean_inc(v_currentTimeout_4635_);
lean_inc(v_keepAliveTimeout_4634_);
lean_inc_ref(v_requestStream_4633_);
lean_inc_ref(v_machine_4632_);
lean_del_object(v___x_4624_);
lean_dec(v_a_4622_);
goto v___jp_4643_;
}
}
else
{
lean_inc(v_pendingHead_4642_);
lean_inc(v_expectData_4640_);
lean_inc(v_respStream_4638_);
lean_inc_ref(v_response_4637_);
lean_inc(v_headerTimeout_4636_);
lean_inc(v_currentTimeout_4635_);
lean_inc(v_keepAliveTimeout_4634_);
lean_inc_ref(v_requestStream_4633_);
lean_inc_ref(v_machine_4632_);
lean_del_object(v___x_4624_);
lean_dec(v_a_4622_);
goto v___jp_4643_;
}
}
else
{
lean_inc(v_pendingHead_4642_);
lean_inc(v_expectData_4640_);
lean_inc(v_respStream_4638_);
lean_inc_ref(v_response_4637_);
lean_inc(v_headerTimeout_4636_);
lean_inc(v_currentTimeout_4635_);
lean_inc(v_keepAliveTimeout_4634_);
lean_inc_ref(v_requestStream_4633_);
lean_inc_ref(v_machine_4632_);
lean_del_object(v___x_4624_);
lean_dec(v_a_4622_);
goto v___jp_4643_;
}
v___jp_4626_:
{
lean_object* v___x_4627_; lean_object* v___x_4629_; 
v___x_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_a_4622_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4627_);
v___x_4629_ = v___x_4624_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4627_);
v___x_4629_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
lean_object* v___x_4630_; 
v___x_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
return v___x_4630_;
}
}
v___jp_4643_:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___f_4647_; lean_object* v___x_4648_; lean_object* v___f_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4644_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4644_, 0, v_machine_4632_);
lean_ctor_set(v___x_4644_, 1, v_requestStream_4633_);
lean_ctor_set(v___x_4644_, 2, v_keepAliveTimeout_4634_);
lean_ctor_set(v___x_4644_, 3, v_currentTimeout_4635_);
lean_ctor_set(v___x_4644_, 4, v_headerTimeout_4636_);
lean_ctor_set(v___x_4644_, 5, v_response_4637_);
lean_ctor_set(v___x_4644_, 6, v_respStream_4638_);
lean_ctor_set(v___x_4644_, 7, v_expectData_4640_);
lean_ctor_set(v___x_4644_, 8, v_pendingHead_4642_);
lean_ctor_set_uint8(v___x_4644_, sizeof(void*)*9, v___x_4602_);
lean_ctor_set_uint8(v___x_4644_, sizeof(void*)*9 + 1, v_handlerDispatched_4641_);
lean_inc_ref(v___x_4644_);
v___x_4645_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4603_, v_connectionContext_4604_, v___x_4644_);
v___x_4646_ = lean_box(v___x_4602_);
lean_inc_ref(v_config_4608_);
lean_inc(v_handler_4607_);
lean_inc_ref(v_responseBodyInstance_4606_);
lean_inc_ref(v_h_4605_);
v___f_4647_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4647_, 0, v_h_4605_);
lean_closure_set(v___f_4647_, 1, v_responseBodyInstance_4606_);
lean_closure_set(v___f_4647_, 2, v_handler_4607_);
lean_closure_set(v___f_4647_, 3, v_config_4608_);
lean_closure_set(v___f_4647_, 4, v___x_4644_);
lean_closure_set(v___f_4647_, 5, v___x_4646_);
lean_closure_set(v___f_4647_, 6, v___f_4609_);
v___x_4648_ = lean_box(v___x_4602_);
v___f_4649_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4649_, 0, v_inst_4610_);
lean_closure_set(v___f_4649_, 1, v_h_4605_);
lean_closure_set(v___f_4649_, 2, v_responseBodyInstance_4606_);
lean_closure_set(v___f_4649_, 3, v_config_4608_);
lean_closure_set(v___f_4649_, 4, v_handler_4607_);
lean_closure_set(v___f_4649_, 5, v___x_4648_);
lean_closure_set(v___f_4649_, 6, v___f_4647_);
v___x_4650_ = lean_unsigned_to_nat(0u);
v___x_4651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4650_, v___x_4602_, v___x_4645_, v___f_4649_);
return v___x_4651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4657_, lean_object* v_socket_4658_, lean_object* v_connectionContext_4659_, lean_object* v_h_4660_, lean_object* v_responseBodyInstance_4661_, lean_object* v_handler_4662_, lean_object* v_config_4663_, lean_object* v___f_4664_, lean_object* v_inst_4665_, lean_object* v_x_4666_, lean_object* v___y_4667_){
_start:
{
uint8_t v___x_5769__boxed_4668_; lean_object* v_res_4669_; 
v___x_5769__boxed_4668_ = lean_unbox(v___x_4657_);
v_res_4669_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5769__boxed_4668_, v_socket_4658_, v_connectionContext_4659_, v_h_4660_, v_responseBodyInstance_4661_, v_handler_4662_, v_config_4663_, v___f_4664_, v_inst_4665_, v_x_4666_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4670_, lean_object* v_handler_4671_, lean_object* v_extensions_4672_, lean_object* v_connectionContext_4673_, uint8_t v___x_4674_, lean_object* v___f_4675_, lean_object* v_x_4676_){
_start:
{
if (lean_obj_tag(v_x_4676_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4686_; 
lean_dec_ref(v___f_4675_);
lean_dec_ref(v_connectionContext_4673_);
lean_dec(v_extensions_4672_);
lean_dec(v_handler_4671_);
lean_dec_ref(v_h_4670_);
v_a_4678_ = lean_ctor_get(v_x_4676_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_x_4676_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4680_ = v_x_4676_;
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v_x_4676_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
return v___x_4684_;
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v_a_4687_ = lean_ctor_get(v_x_4676_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v_x_4676_, 1);
v___x_4688_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4670_, v_handler_4671_, v_extensions_4672_, v_connectionContext_4673_, v_a_4687_);
v___x_4689_ = lean_unsigned_to_nat(0u);
v___x_4690_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4689_, v___x_4674_, v___x_4688_, v___f_4675_);
return v___x_4690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4691_, lean_object* v_handler_4692_, lean_object* v_extensions_4693_, lean_object* v_connectionContext_4694_, lean_object* v___x_4695_, lean_object* v___f_4696_, lean_object* v_x_4697_, lean_object* v___y_4698_){
_start:
{
uint8_t v___x_5844__boxed_4699_; lean_object* v_res_4700_; 
v___x_5844__boxed_4699_ = lean_unbox(v___x_4695_);
v_res_4700_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4691_, v_handler_4692_, v_extensions_4693_, v_connectionContext_4694_, v___x_5844__boxed_4699_, v___f_4696_, v_x_4697_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4701_, lean_object* v_responseBodyInstance_4702_, lean_object* v_handler_4703_, lean_object* v_config_4704_, lean_object* v_connectionContext_4705_, lean_object* v_events_4706_, lean_object* v___x_4707_, uint8_t v___x_4708_, lean_object* v___f_4709_, lean_object* v_____r_4710_){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4712_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4701_, v_responseBodyInstance_4702_, v_handler_4703_, v_config_4704_, v_connectionContext_4705_, v_events_4706_, v___x_4707_);
v___x_4713_ = lean_unsigned_to_nat(0u);
v___x_4714_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4713_, v___x_4708_, v___x_4712_, v___f_4709_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4715_, lean_object* v_responseBodyInstance_4716_, lean_object* v_handler_4717_, lean_object* v_config_4718_, lean_object* v_connectionContext_4719_, lean_object* v_events_4720_, lean_object* v___x_4721_, lean_object* v___x_4722_, lean_object* v___f_4723_, lean_object* v_____r_4724_, lean_object* v___y_4725_){
_start:
{
uint8_t v___x_5883__boxed_4726_; lean_object* v_res_4727_; 
v___x_5883__boxed_4726_ = lean_unbox(v___x_4722_);
v_res_4727_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4715_, v_responseBodyInstance_4716_, v_handler_4717_, v_config_4718_, v_connectionContext_4719_, v_events_4720_, v___x_4721_, v___x_5883__boxed_4726_, v___f_4723_, v_____r_4724_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4728_, lean_object* v___f_4729_, lean_object* v_x_4730_){
_start:
{
if (lean_obj_tag(v_x_4730_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4740_; 
lean_dec_ref(v___f_4729_);
lean_dec_ref(v___x_4728_);
v_a_4732_ = lean_ctor_get(v_x_4730_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_x_4730_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4734_ = v_x_4730_;
v_isShared_4735_ = v_isSharedCheck_4740_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v_x_4730_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4740_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
lean_object* v___x_4738_; 
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
return v___x_4738_;
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4752_; 
v_a_4741_ = lean_ctor_get(v_x_4730_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_x_4730_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4743_ = v_x_4730_;
v_isShared_4744_ = v_isSharedCheck_4752_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v_x_4730_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4752_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
if (lean_obj_tag(v_a_4741_) == 0)
{
lean_object* v___x_4745_; lean_object* v___x_4747_; 
lean_dec_ref(v___f_4729_);
v___x_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4728_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4745_);
v___x_4747_ = v___x_4743_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4745_);
v___x_4747_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4748_; 
v___x_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
return v___x_4748_;
}
}
else
{
lean_object* v_val_4750_; lean_object* v___x_4751_; 
lean_del_object(v___x_4743_);
lean_dec_ref(v___x_4728_);
v_val_4750_ = lean_ctor_get(v_a_4741_, 0);
lean_inc(v_val_4750_);
lean_dec_ref_known(v_a_4741_, 1);
v___x_4751_ = lean_apply_2(v___f_4729_, v_val_4750_, lean_box(0));
return v___x_4751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4753_, lean_object* v___f_4754_, lean_object* v_x_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4753_, v___f_4754_, v_x_4755_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4758_, lean_object* v_responseBodyInstance_4759_, lean_object* v_handler_4760_, lean_object* v_config_4761_, lean_object* v_connectionContext_4762_, uint8_t v___x_4763_, lean_object* v___f_4764_, lean_object* v_inst_4765_, lean_object* v_socket_4766_, lean_object* v___f_4767_, lean_object* v___f_4768_, lean_object* v_x_4769_, lean_object* v_____s_4770_){
_start:
{
lean_object* v_machine_4772_; lean_object* v_reader_4773_; lean_object* v_requestStream_4774_; lean_object* v_keepAliveTimeout_4775_; lean_object* v_currentTimeout_4776_; lean_object* v_headerTimeout_4777_; lean_object* v_response_4778_; lean_object* v_respStream_4779_; uint8_t v_requiresData_4780_; lean_object* v_expectData_4781_; uint8_t v_handlerDispatched_4782_; lean_object* v_pendingHead_4783_; lean_object* v_writer_4784_; lean_object* v_state_4785_; uint8_t v___x_4786_; 
v_machine_4772_ = lean_ctor_get(v_____s_4770_, 0);
v_reader_4773_ = lean_ctor_get(v_machine_4772_, 0);
v_requestStream_4774_ = lean_ctor_get(v_____s_4770_, 1);
v_keepAliveTimeout_4775_ = lean_ctor_get(v_____s_4770_, 2);
v_currentTimeout_4776_ = lean_ctor_get(v_____s_4770_, 3);
v_headerTimeout_4777_ = lean_ctor_get(v_____s_4770_, 4);
v_response_4778_ = lean_ctor_get(v_____s_4770_, 5);
v_respStream_4779_ = lean_ctor_get(v_____s_4770_, 6);
v_requiresData_4780_ = lean_ctor_get_uint8(v_____s_4770_, sizeof(void*)*9);
v_expectData_4781_ = lean_ctor_get(v_____s_4770_, 7);
v_handlerDispatched_4782_ = lean_ctor_get_uint8(v_____s_4770_, sizeof(void*)*9 + 1);
v_pendingHead_4783_ = lean_ctor_get(v_____s_4770_, 8);
v_writer_4784_ = lean_ctor_get(v_machine_4772_, 1);
v_state_4785_ = lean_ctor_get(v_reader_4773_, 0);
v___x_4786_ = 0;
if (lean_obj_tag(v_state_4785_) == 6)
{
lean_object* v_state_4808_; 
v_state_4808_ = lean_ctor_get(v_writer_4784_, 2);
if (lean_obj_tag(v_state_4808_) == 7)
{
lean_object* v_outputData_4809_; lean_object* v_size_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; 
v_outputData_4809_ = lean_ctor_get(v_writer_4784_, 1);
v_size_4810_ = lean_ctor_get(v_outputData_4809_, 1);
v___x_4811_ = lean_unsigned_to_nat(0u);
v___x_4812_ = lean_nat_dec_eq(v_size_4810_, v___x_4811_);
if (v___x_4812_ == 0)
{
lean_inc(v_pendingHead_4783_);
lean_inc(v_expectData_4781_);
lean_inc(v_respStream_4779_);
lean_inc_ref(v_response_4778_);
lean_inc(v_headerTimeout_4777_);
lean_inc(v_currentTimeout_4776_);
lean_inc(v_keepAliveTimeout_4775_);
lean_inc_ref(v_requestStream_4774_);
lean_inc_ref(v_machine_4772_);
lean_dec_ref(v_____s_4770_);
goto v___jp_4787_;
}
else
{
if (v___x_4812_ == 0)
{
lean_inc(v_pendingHead_4783_);
lean_inc(v_expectData_4781_);
lean_inc(v_respStream_4779_);
lean_inc_ref(v_response_4778_);
lean_inc(v_headerTimeout_4777_);
lean_inc(v_currentTimeout_4776_);
lean_inc(v_keepAliveTimeout_4775_);
lean_inc_ref(v_requestStream_4774_);
lean_inc_ref(v_machine_4772_);
lean_dec_ref(v_____s_4770_);
goto v___jp_4787_;
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec_ref(v___f_4768_);
lean_dec_ref(v___f_4767_);
lean_dec(v_socket_4766_);
lean_dec_ref(v_inst_4765_);
lean_dec_ref(v___f_4764_);
lean_dec_ref(v_connectionContext_4762_);
lean_dec_ref(v_config_4761_);
lean_dec(v_handler_4760_);
lean_dec_ref(v_responseBodyInstance_4759_);
lean_dec_ref(v_h_4758_);
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_____s_4770_);
v___x_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4813_);
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
return v___x_4815_;
}
}
}
else
{
lean_inc(v_pendingHead_4783_);
lean_inc(v_expectData_4781_);
lean_inc(v_respStream_4779_);
lean_inc_ref(v_response_4778_);
lean_inc(v_headerTimeout_4777_);
lean_inc(v_currentTimeout_4776_);
lean_inc(v_keepAliveTimeout_4775_);
lean_inc_ref(v_requestStream_4774_);
lean_inc_ref(v_machine_4772_);
lean_dec_ref(v_____s_4770_);
goto v___jp_4787_;
}
}
else
{
lean_inc(v_pendingHead_4783_);
lean_inc(v_expectData_4781_);
lean_inc(v_respStream_4779_);
lean_inc_ref(v_response_4778_);
lean_inc(v_headerTimeout_4777_);
lean_inc(v_currentTimeout_4776_);
lean_inc(v_keepAliveTimeout_4775_);
lean_inc_ref(v_requestStream_4774_);
lean_inc_ref(v_machine_4772_);
lean_dec_ref(v_____s_4770_);
goto v___jp_4787_;
}
v___jp_4787_:
{
lean_object* v___x_4788_; lean_object* v_snd_4789_; lean_object* v_output_4790_; lean_object* v_fst_4791_; lean_object* v_events_4792_; lean_object* v_data_4793_; lean_object* v_size_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___f_4797_; lean_object* v___x_4798_; uint8_t v___x_4799_; 
v___x_4788_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4786_, v_machine_4772_);
v_snd_4789_ = lean_ctor_get(v___x_4788_, 1);
lean_inc(v_snd_4789_);
v_output_4790_ = lean_ctor_get(v_snd_4789_, 1);
lean_inc_ref(v_output_4790_);
v_fst_4791_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_fst_4791_);
lean_dec_ref(v___x_4788_);
v_events_4792_ = lean_ctor_get(v_snd_4789_, 0);
lean_inc_ref_n(v_events_4792_, 2);
lean_dec(v_snd_4789_);
v_data_4793_ = lean_ctor_get(v_output_4790_, 0);
lean_inc_ref(v_data_4793_);
v_size_4794_ = lean_ctor_get(v_output_4790_, 1);
lean_inc(v_size_4794_);
lean_dec_ref(v_output_4790_);
v___x_4795_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4795_, 0, v_fst_4791_);
lean_ctor_set(v___x_4795_, 1, v_requestStream_4774_);
lean_ctor_set(v___x_4795_, 2, v_keepAliveTimeout_4775_);
lean_ctor_set(v___x_4795_, 3, v_currentTimeout_4776_);
lean_ctor_set(v___x_4795_, 4, v_headerTimeout_4777_);
lean_ctor_set(v___x_4795_, 5, v_response_4778_);
lean_ctor_set(v___x_4795_, 6, v_respStream_4779_);
lean_ctor_set(v___x_4795_, 7, v_expectData_4781_);
lean_ctor_set(v___x_4795_, 8, v_pendingHead_4783_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*9, v_requiresData_4780_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*9 + 1, v_handlerDispatched_4782_);
v___x_4796_ = lean_box(v___x_4763_);
lean_inc_ref(v___f_4764_);
lean_inc_ref(v___x_4795_);
lean_inc_ref(v_connectionContext_4762_);
lean_inc_ref(v_config_4761_);
lean_inc(v_handler_4760_);
lean_inc_ref(v_responseBodyInstance_4759_);
lean_inc_ref(v_h_4758_);
v___f_4797_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4797_, 0, v_h_4758_);
lean_closure_set(v___f_4797_, 1, v_responseBodyInstance_4759_);
lean_closure_set(v___f_4797_, 2, v_handler_4760_);
lean_closure_set(v___f_4797_, 3, v_config_4761_);
lean_closure_set(v___f_4797_, 4, v_connectionContext_4762_);
lean_closure_set(v___f_4797_, 5, v_events_4792_);
lean_closure_set(v___f_4797_, 6, v___x_4795_);
lean_closure_set(v___f_4797_, 7, v___x_4796_);
lean_closure_set(v___f_4797_, 8, v___f_4764_);
v___x_4798_ = lean_unsigned_to_nat(0u);
v___x_4799_ = lean_nat_dec_lt(v___x_4798_, v_size_4794_);
lean_dec(v_size_4794_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
lean_dec_ref(v___f_4797_);
lean_dec_ref(v_data_4793_);
lean_dec_ref(v___f_4768_);
lean_dec_ref(v___f_4767_);
lean_dec(v_socket_4766_);
lean_dec_ref(v_inst_4765_);
v___x_4800_ = lean_box(0);
v___x_4801_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4758_, v_responseBodyInstance_4759_, v_handler_4760_, v_config_4761_, v_connectionContext_4762_, v_events_4792_, v___x_4795_, v___x_4763_, v___f_4764_, v___x_4800_);
return v___x_4801_;
}
else
{
lean_object* v_sendAll_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___f_4806_; lean_object* v___x_4807_; 
lean_dec_ref(v_events_4792_);
lean_dec_ref(v___f_4764_);
lean_dec_ref(v_connectionContext_4762_);
lean_dec_ref(v_config_4761_);
lean_dec(v_handler_4760_);
lean_dec_ref(v_responseBodyInstance_4759_);
lean_dec_ref(v_h_4758_);
v_sendAll_4802_ = lean_ctor_get(v_inst_4765_, 1);
lean_inc_ref(v_sendAll_4802_);
lean_dec_ref(v_inst_4765_);
v___x_4803_ = lean_apply_3(v_sendAll_4802_, v_socket_4766_, v_data_4793_, lean_box(0));
v___x_4804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4798_, v___x_4763_, v___x_4803_, v___f_4767_);
v___x_4805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4798_, v___x_4763_, v___x_4804_, v___f_4768_);
v___f_4806_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4806_, 0, v___x_4795_);
lean_closure_set(v___f_4806_, 1, v___f_4797_);
v___x_4807_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4798_, v___x_4763_, v___x_4805_, v___f_4806_);
return v___x_4807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4816_, lean_object* v_responseBodyInstance_4817_, lean_object* v_handler_4818_, lean_object* v_config_4819_, lean_object* v_connectionContext_4820_, lean_object* v___x_4821_, lean_object* v___f_4822_, lean_object* v_inst_4823_, lean_object* v_socket_4824_, lean_object* v___f_4825_, lean_object* v___f_4826_, lean_object* v_x_4827_, lean_object* v_____s_4828_, lean_object* v___y_4829_){
_start:
{
uint8_t v___x_5957__boxed_4830_; lean_object* v_res_4831_; 
v___x_5957__boxed_4830_ = lean_unbox(v___x_4821_);
v_res_4831_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4816_, v_responseBodyInstance_4817_, v_handler_4818_, v_config_4819_, v_connectionContext_4820_, v___x_5957__boxed_4830_, v___f_4822_, v_inst_4823_, v_socket_4824_, v___f_4825_, v___f_4826_, v_x_4827_, v_____s_4828_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4832_, lean_object* v_x_4833_){
_start:
{
if (lean_obj_tag(v_x_4833_) == 0)
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4843_; 
v_a_4835_ = lean_ctor_get(v_x_4833_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_x_4833_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4837_ = v_x_4833_;
v_isShared_4838_ = v_isSharedCheck_4843_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v_x_4833_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4843_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
}
}
else
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
lean_dec_ref_known(v_x_4833_, 1);
v___x_4844_ = l_IO_Promise_result_x21___redArg(v_a_4832_);
v___x_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
return v___x_4845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4846_, lean_object* v_x_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4846_, v_x_4847_);
lean_dec(v_a_4846_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4850_, lean_object* v___x_4851_, lean_object* v___x_4852_, uint8_t v___x_4853_, lean_object* v_x_4854_){
_start:
{
if (lean_obj_tag(v_x_4854_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref(v___x_4852_);
lean_dec(v___x_4851_);
lean_dec_ref(v___f_4850_);
v_a_4856_ = lean_ctor_get(v_x_4854_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v_x_4854_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4858_ = v_x_4854_;
v_isShared_4859_ = v_isSharedCheck_4864_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v_x_4854_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4864_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
lean_object* v___x_4862_; 
v___x_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
return v___x_4862_;
}
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4876_; 
v_a_4865_ = lean_ctor_get(v_x_4854_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v_x_4854_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4867_ = v_x_4854_;
v_isShared_4868_ = v_isSharedCheck_4876_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v_x_4854_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4876_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4869_; lean_object* v___f_4870_; lean_object* v___x_4872_; 
lean_inc(v_a_4865_);
lean_inc(v___x_4851_);
v___x_4869_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4850_, v___x_4851_, v_a_4865_, v___x_4852_);
v___f_4870_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4870_, 0, v_a_4865_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 0, v___x_4869_);
v___x_4872_ = v___x_4867_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4869_);
v___x_4872_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
v___x_4874_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4851_, v___x_4853_, v___x_4873_, v___f_4870_);
return v___x_4874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4877_, lean_object* v___x_4878_, lean_object* v___x_4879_, lean_object* v___x_4880_, lean_object* v_x_4881_, lean_object* v___y_4882_){
_start:
{
uint8_t v___x_6060__boxed_4883_; lean_object* v_res_4884_; 
v___x_6060__boxed_4883_ = lean_unbox(v___x_4880_);
v_res_4884_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4877_, v___x_4878_, v___x_4879_, v___x_6060__boxed_4883_, v_x_4881_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4885_, lean_object* v_machine_4886_, lean_object* v_a_4887_, lean_object* v___x_4888_, lean_object* v_socket_4889_, lean_object* v_connectionContext_4890_, lean_object* v_h_4891_, lean_object* v_responseBodyInstance_4892_, lean_object* v_handler_4893_, lean_object* v___f_4894_, lean_object* v_inst_4895_, lean_object* v_extensions_4896_, lean_object* v___f_4897_, lean_object* v___f_4898_, lean_object* v___f_4899_, lean_object* v_x_4900_){
_start:
{
if (lean_obj_tag(v_x_4900_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4910_; 
lean_dec_ref(v___f_4899_);
lean_dec_ref(v___f_4898_);
lean_dec_ref(v___f_4897_);
lean_dec(v_extensions_4896_);
lean_dec_ref(v_inst_4895_);
lean_dec_ref(v___f_4894_);
lean_dec(v_handler_4893_);
lean_dec_ref(v_responseBodyInstance_4892_);
lean_dec_ref(v_h_4891_);
lean_dec_ref(v_connectionContext_4890_);
lean_dec(v_socket_4889_);
lean_dec(v___x_4888_);
lean_dec_ref(v_a_4887_);
lean_dec_ref(v_machine_4886_);
lean_dec_ref(v_config_4885_);
v_a_4902_ = lean_ctor_get(v_x_4900_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v_x_4900_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4904_ = v_x_4900_;
v_isShared_4905_ = v_isSharedCheck_4910_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v_x_4900_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4910_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; 
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
return v___x_4908_;
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4936_; 
v_a_4911_ = lean_ctor_get(v_x_4900_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v_x_4900_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4913_ = v_x_4900_;
v_isShared_4914_ = v_isSharedCheck_4936_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v_x_4900_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4936_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v_keepAliveTimeout_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___f_4922_; lean_object* v___x_4923_; lean_object* v___f_4924_; lean_object* v___x_4925_; lean_object* v___f_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___f_4929_; lean_object* v___x_4931_; 
v_keepAliveTimeout_4915_ = lean_ctor_get(v_config_4885_, 5);
lean_inc_n(v_keepAliveTimeout_4915_, 2);
v___x_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4916_, 0, v_keepAliveTimeout_4915_);
v___x_4917_ = lean_box(0);
v___x_4918_ = 0;
v___x_4919_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4919_, 0, v_machine_4886_);
lean_ctor_set(v___x_4919_, 1, v_a_4887_);
lean_ctor_set(v___x_4919_, 2, v___x_4916_);
lean_ctor_set(v___x_4919_, 3, v_keepAliveTimeout_4915_);
lean_ctor_set(v___x_4919_, 4, v___x_4917_);
lean_ctor_set(v___x_4919_, 5, v_a_4911_);
lean_ctor_set(v___x_4919_, 6, v___x_4917_);
lean_ctor_set(v___x_4919_, 7, v___x_4888_);
lean_ctor_set(v___x_4919_, 8, v___x_4917_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*9, v___x_4918_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*9 + 1, v___x_4918_);
v___x_4920_ = lean_io_promise_new();
v___x_4921_ = lean_box(v___x_4918_);
lean_inc_ref(v_inst_4895_);
lean_inc_ref(v_config_4885_);
lean_inc_n(v_handler_4893_, 2);
lean_inc_ref(v_responseBodyInstance_4892_);
lean_inc_ref_n(v_h_4891_, 2);
lean_inc_ref_n(v_connectionContext_4890_, 2);
lean_inc(v_socket_4889_);
v___f_4922_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4922_, 0, v___x_4921_);
lean_closure_set(v___f_4922_, 1, v_socket_4889_);
lean_closure_set(v___f_4922_, 2, v_connectionContext_4890_);
lean_closure_set(v___f_4922_, 3, v_h_4891_);
lean_closure_set(v___f_4922_, 4, v_responseBodyInstance_4892_);
lean_closure_set(v___f_4922_, 5, v_handler_4893_);
lean_closure_set(v___f_4922_, 6, v_config_4885_);
lean_closure_set(v___f_4922_, 7, v___f_4894_);
lean_closure_set(v___f_4922_, 8, v_inst_4895_);
v___x_4923_ = lean_box(v___x_4918_);
v___f_4924_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4924_, 0, v_h_4891_);
lean_closure_set(v___f_4924_, 1, v_handler_4893_);
lean_closure_set(v___f_4924_, 2, v_extensions_4896_);
lean_closure_set(v___f_4924_, 3, v_connectionContext_4890_);
lean_closure_set(v___f_4924_, 4, v___x_4923_);
lean_closure_set(v___f_4924_, 5, v___f_4922_);
v___x_4925_ = lean_box(v___x_4918_);
v___f_4926_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4926_, 0, v_h_4891_);
lean_closure_set(v___f_4926_, 1, v_responseBodyInstance_4892_);
lean_closure_set(v___f_4926_, 2, v_handler_4893_);
lean_closure_set(v___f_4926_, 3, v_config_4885_);
lean_closure_set(v___f_4926_, 4, v_connectionContext_4890_);
lean_closure_set(v___f_4926_, 5, v___x_4925_);
lean_closure_set(v___f_4926_, 6, v___f_4924_);
lean_closure_set(v___f_4926_, 7, v_inst_4895_);
lean_closure_set(v___f_4926_, 8, v_socket_4889_);
lean_closure_set(v___f_4926_, 9, v___f_4897_);
lean_closure_set(v___f_4926_, 10, v___f_4898_);
v___x_4927_ = lean_unsigned_to_nat(0u);
v___x_4928_ = lean_box(v___x_4918_);
v___f_4929_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4929_, 0, v___f_4926_);
lean_closure_set(v___f_4929_, 1, v___x_4927_);
lean_closure_set(v___f_4929_, 2, v___x_4919_);
lean_closure_set(v___f_4929_, 3, v___x_4928_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4920_);
v___x_4931_ = v___x_4913_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4920_);
v___x_4931_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
v___x_4933_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4927_, v___x_4918_, v___x_4932_, v___f_4929_);
v___x_4934_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4927_, v___x_4918_, v___x_4933_, v___f_4899_);
return v___x_4934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4937_ = _args[0];
lean_object* v_machine_4938_ = _args[1];
lean_object* v_a_4939_ = _args[2];
lean_object* v___x_4940_ = _args[3];
lean_object* v_socket_4941_ = _args[4];
lean_object* v_connectionContext_4942_ = _args[5];
lean_object* v_h_4943_ = _args[6];
lean_object* v_responseBodyInstance_4944_ = _args[7];
lean_object* v_handler_4945_ = _args[8];
lean_object* v___f_4946_ = _args[9];
lean_object* v_inst_4947_ = _args[10];
lean_object* v_extensions_4948_ = _args[11];
lean_object* v___f_4949_ = _args[12];
lean_object* v___f_4950_ = _args[13];
lean_object* v___f_4951_ = _args[14];
lean_object* v_x_4952_ = _args[15];
lean_object* v___y_4953_ = _args[16];
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4937_, v_machine_4938_, v_a_4939_, v___x_4940_, v_socket_4941_, v_connectionContext_4942_, v_h_4943_, v_responseBodyInstance_4944_, v_handler_4945_, v___f_4946_, v_inst_4947_, v_extensions_4948_, v___f_4949_, v___f_4950_, v___f_4951_, v_x_4952_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4955_, lean_object* v_machine_4956_, lean_object* v_socket_4957_, lean_object* v_connectionContext_4958_, lean_object* v_h_4959_, lean_object* v_responseBodyInstance_4960_, lean_object* v_handler_4961_, lean_object* v___f_4962_, lean_object* v_inst_4963_, lean_object* v_extensions_4964_, lean_object* v___f_4965_, lean_object* v___f_4966_, lean_object* v___f_4967_, lean_object* v_x_4968_){
_start:
{
if (lean_obj_tag(v_x_4968_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4978_; 
lean_dec_ref(v___f_4967_);
lean_dec_ref(v___f_4966_);
lean_dec_ref(v___f_4965_);
lean_dec(v_extensions_4964_);
lean_dec_ref(v_inst_4963_);
lean_dec_ref(v___f_4962_);
lean_dec(v_handler_4961_);
lean_dec_ref(v_responseBodyInstance_4960_);
lean_dec_ref(v_h_4959_);
lean_dec_ref(v_connectionContext_4958_);
lean_dec(v_socket_4957_);
lean_dec_ref(v_machine_4956_);
lean_dec_ref(v_config_4955_);
v_a_4970_ = lean_ctor_get(v_x_4968_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v_x_4968_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4972_ = v_x_4968_;
v_isShared_4973_ = v_isSharedCheck_4978_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v_x_4968_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4978_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
return v___x_4976_;
}
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4993_; 
v_a_4979_ = lean_ctor_get(v_x_4968_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v_x_4968_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4981_ = v_x_4968_;
v_isShared_4982_ = v_isSharedCheck_4993_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v_x_4968_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4993_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___f_4985_; lean_object* v___x_4987_; 
v___x_4983_ = lean_box(0);
v___x_4984_ = l_Std_CloseableChannel_new___redArg(v___x_4983_);
v___f_4985_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4985_, 0, v_config_4955_);
lean_closure_set(v___f_4985_, 1, v_machine_4956_);
lean_closure_set(v___f_4985_, 2, v_a_4979_);
lean_closure_set(v___f_4985_, 3, v___x_4983_);
lean_closure_set(v___f_4985_, 4, v_socket_4957_);
lean_closure_set(v___f_4985_, 5, v_connectionContext_4958_);
lean_closure_set(v___f_4985_, 6, v_h_4959_);
lean_closure_set(v___f_4985_, 7, v_responseBodyInstance_4960_);
lean_closure_set(v___f_4985_, 8, v_handler_4961_);
lean_closure_set(v___f_4985_, 9, v___f_4962_);
lean_closure_set(v___f_4985_, 10, v_inst_4963_);
lean_closure_set(v___f_4985_, 11, v_extensions_4964_);
lean_closure_set(v___f_4985_, 12, v___f_4965_);
lean_closure_set(v___f_4985_, 13, v___f_4966_);
lean_closure_set(v___f_4985_, 14, v___f_4967_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 0, v___x_4984_);
v___x_4987_ = v___x_4981_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4984_);
v___x_4987_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; lean_object* v___x_4991_; 
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
v___x_4989_ = lean_unsigned_to_nat(0u);
v___x_4990_ = 0;
v___x_4991_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4989_, v___x_4990_, v___x_4988_, v___f_4985_);
return v___x_4991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4994_, lean_object* v_machine_4995_, lean_object* v_socket_4996_, lean_object* v_connectionContext_4997_, lean_object* v_h_4998_, lean_object* v_responseBodyInstance_4999_, lean_object* v_handler_5000_, lean_object* v___f_5001_, lean_object* v_inst_5002_, lean_object* v_extensions_5003_, lean_object* v___f_5004_, lean_object* v___f_5005_, lean_object* v___f_5006_, lean_object* v_x_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4994_, v_machine_4995_, v_socket_4996_, v_connectionContext_4997_, v_h_4998_, v_responseBodyInstance_4999_, v_handler_5000_, v___f_5001_, v_inst_5002_, v_extensions_5003_, v___f_5004_, v___f_5005_, v___f_5006_, v_x_5007_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_5013_, lean_object* v_h_5014_, lean_object* v_connection_5015_, lean_object* v_config_5016_, lean_object* v_connectionContext_5017_, lean_object* v_handler_5018_){
_start:
{
lean_object* v_responseBodyInstance_5020_; lean_object* v_onFailure_5021_; lean_object* v___x_5022_; lean_object* v_socket_5023_; lean_object* v_machine_5024_; lean_object* v_extensions_5025_; lean_object* v___f_5026_; lean_object* v___f_5027_; lean_object* v___f_5028_; lean_object* v___f_5029_; lean_object* v___f_5030_; lean_object* v___f_5031_; lean_object* v___f_5032_; lean_object* v___f_5033_; lean_object* v___f_5034_; lean_object* v___x_5035_; uint8_t v___x_5036_; lean_object* v___x_5037_; 
v_responseBodyInstance_5020_ = lean_ctor_get(v_h_5014_, 0);
lean_inc_ref_n(v_responseBodyInstance_5020_, 2);
v_onFailure_5021_ = lean_ctor_get(v_h_5014_, 2);
v___x_5022_ = l_Std_Http_Body_mkStream();
v_socket_5023_ = lean_ctor_get(v_connection_5015_, 0);
lean_inc_n(v_socket_5023_, 2);
v_machine_5024_ = lean_ctor_get(v_connection_5015_, 1);
lean_inc_ref(v_machine_5024_);
v_extensions_5025_ = lean_ctor_get(v_connection_5015_, 2);
lean_inc(v_extensions_5025_);
lean_dec_ref(v_connection_5015_);
v___f_5026_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_5027_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_5028_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_5029_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_5018_);
lean_inc_ref(v_onFailure_5021_);
v___f_5030_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5030_, 0, v_onFailure_5021_);
lean_closure_set(v___f_5030_, 1, v_handler_5018_);
lean_closure_set(v___f_5030_, 2, v___f_5029_);
lean_inc_ref(v_inst_5013_);
v___f_5031_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5031_, 0, v_inst_5013_);
lean_closure_set(v___f_5031_, 1, v_socket_5023_);
lean_inc_ref(v___f_5031_);
v___f_5032_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_5032_, 0, v___f_5031_);
v___f_5033_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_5033_, 0, v___f_5026_);
lean_closure_set(v___f_5033_, 1, v_responseBodyInstance_5020_);
lean_closure_set(v___f_5033_, 2, v___f_5032_);
lean_closure_set(v___f_5033_, 3, v___f_5031_);
v___f_5034_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_5034_, 0, v_config_5016_);
lean_closure_set(v___f_5034_, 1, v_machine_5024_);
lean_closure_set(v___f_5034_, 2, v_socket_5023_);
lean_closure_set(v___f_5034_, 3, v_connectionContext_5017_);
lean_closure_set(v___f_5034_, 4, v_h_5014_);
lean_closure_set(v___f_5034_, 5, v_responseBodyInstance_5020_);
lean_closure_set(v___f_5034_, 6, v_handler_5018_);
lean_closure_set(v___f_5034_, 7, v___f_5027_);
lean_closure_set(v___f_5034_, 8, v_inst_5013_);
lean_closure_set(v___f_5034_, 9, v_extensions_5025_);
lean_closure_set(v___f_5034_, 10, v___f_5028_);
lean_closure_set(v___f_5034_, 11, v___f_5030_);
lean_closure_set(v___f_5034_, 12, v___f_5033_);
v___x_5035_ = lean_unsigned_to_nat(0u);
v___x_5036_ = 0;
v___x_5037_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5035_, v___x_5036_, v___x_5022_, v___f_5034_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_5038_, lean_object* v_h_5039_, lean_object* v_connection_5040_, lean_object* v_config_5041_, lean_object* v_connectionContext_5042_, lean_object* v_handler_5043_, lean_object* v_a_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_5038_, v_h_5039_, v_connection_5040_, v_config_5041_, v_connectionContext_5042_, v_handler_5043_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_5046_, lean_object* v_00_u03c3_5047_, lean_object* v_inst_5048_, lean_object* v_h_5049_, lean_object* v_connection_5050_, lean_object* v_config_5051_, lean_object* v_connectionContext_5052_, lean_object* v_handler_5053_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_5048_, v_h_5049_, v_connection_5050_, v_config_5051_, v_connectionContext_5052_, v_handler_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_5056_, lean_object* v_00_u03c3_5057_, lean_object* v_inst_5058_, lean_object* v_h_5059_, lean_object* v_connection_5060_, lean_object* v_config_5061_, lean_object* v_connectionContext_5062_, lean_object* v_handler_5063_, lean_object* v_a_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_5056_, v_00_u03c3_5057_, v_inst_5058_, v_h_5059_, v_connection_5060_, v_config_5061_, v_connectionContext_5062_, v_handler_5063_);
return v_res_5065_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = 0;
v___x_5067_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_5066_);
return v___x_5067_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = lean_unsigned_to_nat(4096u);
v___x_5069_ = lean_mk_empty_byte_array(v___x_5068_);
return v___x_5069_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_5071_ = l_ByteArray_mkIterator(v___x_5070_);
return v___x_5071_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5072_ = 0;
v___x_5073_ = lean_unsigned_to_nat(0u);
v___x_5074_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_5075_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_5076_ = lean_box(0);
v___x_5077_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
lean_ctor_set(v___x_5077_, 1, v___x_5075_);
lean_ctor_set(v___x_5077_, 2, v___x_5074_);
lean_ctor_set(v___x_5077_, 3, v___x_5073_);
lean_ctor_set(v___x_5077_, 4, v___x_5073_);
lean_ctor_set(v___x_5077_, 5, v___x_5073_);
lean_ctor_set_uint8(v___x_5077_, sizeof(void*)*6, v___x_5072_);
return v___x_5077_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = 1;
v___x_5086_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_5085_);
return v___x_5086_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_5087_; uint8_t v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5087_ = lean_unsigned_to_nat(0u);
v___x_5088_ = 0;
v___x_5089_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_5090_ = lean_box(0);
v___x_5091_ = lean_box(0);
v___x_5092_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_5093_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_5094_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
lean_ctor_set(v___x_5094_, 1, v___x_5092_);
lean_ctor_set(v___x_5094_, 2, v___x_5091_);
lean_ctor_set(v___x_5094_, 3, v___x_5090_);
lean_ctor_set(v___x_5094_, 4, v___x_5089_);
lean_ctor_set(v___x_5094_, 5, v___x_5087_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*6, v___x_5088_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*6 + 1, v___x_5088_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*6 + 2, v___x_5088_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_5095_, lean_object* v_client_5096_, lean_object* v_extensions_5097_, lean_object* v_inst_5098_, lean_object* v_inst_5099_, lean_object* v_handler_5100_, lean_object* v_x_5101_){
_start:
{
if (lean_obj_tag(v_x_5101_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5111_; 
lean_dec(v_handler_5100_);
lean_dec_ref(v_inst_5099_);
lean_dec_ref(v_inst_5098_);
lean_dec(v_extensions_5097_);
lean_dec(v_client_5096_);
lean_dec_ref(v_config_5095_);
v_a_5103_ = lean_ctor_get(v_x_5101_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v_x_5101_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5105_ = v_x_5101_;
v_isShared_5106_ = v_isSharedCheck_5111_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v_x_5101_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5111_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5109_; 
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
}
}
else
{
lean_object* v_a_5112_; uint8_t v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; uint8_t v_enableKeepAlive_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_a_5112_ = lean_ctor_get(v_x_5101_, 0);
lean_inc(v_a_5112_);
lean_dec_ref_known(v_x_5101_, 1);
v___x_5113_ = 0;
v___x_5114_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_5115_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_5116_ = lean_box(0);
v___x_5117_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_5118_ = l_Std_Http_Config_toH1Config(v_config_5095_);
v_enableKeepAlive_5119_ = lean_ctor_get_uint8(v___x_5118_, sizeof(void*)*18);
v___x_5120_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_5120_, 0, v___x_5114_);
lean_ctor_set(v___x_5120_, 1, v___x_5117_);
lean_ctor_set(v___x_5120_, 2, v___x_5118_);
lean_ctor_set(v___x_5120_, 3, v___x_5115_);
lean_ctor_set(v___x_5120_, 4, v___x_5116_);
lean_ctor_set(v___x_5120_, 5, v___x_5116_);
lean_ctor_set_uint8(v___x_5120_, sizeof(void*)*6, v_enableKeepAlive_5119_);
lean_ctor_set_uint8(v___x_5120_, sizeof(void*)*6 + 1, v___x_5113_);
lean_ctor_set_uint8(v___x_5120_, sizeof(void*)*6 + 2, v___x_5113_);
v___x_5121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5121_, 0, v_client_5096_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
lean_ctor_set(v___x_5121_, 2, v_extensions_5097_);
v___x_5122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_5098_, v_inst_5099_, v___x_5121_, v_config_5095_, v_a_5112_, v_handler_5100_);
return v___x_5122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_5123_, lean_object* v_client_5124_, lean_object* v_extensions_5125_, lean_object* v_inst_5126_, lean_object* v_inst_5127_, lean_object* v_handler_5128_, lean_object* v_x_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_5123_, v_client_5124_, v_extensions_5125_, v_inst_5126_, v_inst_5127_, v_handler_5128_, v_x_5129_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_5132_, lean_object* v_inst_5133_, lean_object* v_client_5134_, lean_object* v_handler_5135_, lean_object* v_config_5136_, lean_object* v_extensions_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v___f_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; uint8_t v___x_5144_; lean_object* v___x_5145_; 
v___f_5140_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5140_, 0, v_config_5136_);
lean_closure_set(v___f_5140_, 1, v_client_5134_);
lean_closure_set(v___f_5140_, 2, v_extensions_5137_);
lean_closure_set(v___f_5140_, 3, v_inst_5132_);
lean_closure_set(v___f_5140_, 4, v_inst_5133_);
lean_closure_set(v___f_5140_, 5, v_handler_5135_);
lean_inc_ref(v_a_5138_);
v___x_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5141_, 0, v_a_5138_);
v___x_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
v___x_5143_ = lean_unsigned_to_nat(0u);
v___x_5144_ = 0;
v___x_5145_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5143_, v___x_5144_, v___x_5142_, v___f_5140_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_5146_, lean_object* v_inst_5147_, lean_object* v_client_5148_, lean_object* v_handler_5149_, lean_object* v_config_5150_, lean_object* v_extensions_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_Std_Http_Server_serveConnection___redArg(v_inst_5146_, v_inst_5147_, v_client_5148_, v_handler_5149_, v_config_5150_, v_extensions_5151_, v_a_5152_);
lean_dec_ref(v_a_5152_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_5155_, lean_object* v_00_u03c3_5156_, lean_object* v_inst_5157_, lean_object* v_inst_5158_, lean_object* v_client_5159_, lean_object* v_handler_5160_, lean_object* v_config_5161_, lean_object* v_extensions_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Std_Http_Server_serveConnection___redArg(v_inst_5157_, v_inst_5158_, v_client_5159_, v_handler_5160_, v_config_5161_, v_extensions_5162_, v_a_5163_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_5166_, lean_object* v_00_u03c3_5167_, lean_object* v_inst_5168_, lean_object* v_inst_5169_, lean_object* v_client_5170_, lean_object* v_handler_5171_, lean_object* v_config_5172_, lean_object* v_extensions_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Std_Http_Server_serveConnection(v_t_5166_, v_00_u03c3_5167_, v_inst_5168_, v_inst_5169_, v_client_5170_, v_handler_5171_, v_config_5172_, v_extensions_5173_, v_a_5174_);
lean_dec_ref(v_a_5174_);
return v_res_5176_;
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
