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
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_date;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "request header timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
return v_x_805_;
}
else
{
lean_object* v_key_807_; lean_object* v_value_808_; lean_object* v_tail_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_832_; 
v_key_807_ = lean_ctor_get(v_x_806_, 0);
v_value_808_ = lean_ctor_get(v_x_806_, 1);
v_tail_809_ = lean_ctor_get(v_x_806_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_806_);
if (v_isSharedCheck_832_ == 0)
{
v___x_811_ = v_x_806_;
v_isShared_812_ = v_isSharedCheck_832_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_tail_809_);
lean_inc(v_value_808_);
lean_inc(v_key_807_);
lean_dec(v_x_806_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_832_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; uint64_t v___x_816_; uint64_t v_fold_817_; uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_813_ = lean_array_get_size(v_x_805_);
v___x_814_ = lean_string_hash(v_key_807_);
v___x_815_ = 32ULL;
v___x_816_ = lean_uint64_shift_right(v___x_814_, v___x_815_);
v_fold_817_ = lean_uint64_xor(v___x_814_, v___x_816_);
v___x_818_ = 16ULL;
v___x_819_ = lean_uint64_shift_right(v_fold_817_, v___x_818_);
v___x_820_ = lean_uint64_xor(v_fold_817_, v___x_819_);
v___x_821_ = lean_uint64_to_usize(v___x_820_);
v___x_822_ = lean_usize_of_nat(v___x_813_);
v___x_823_ = ((size_t)1ULL);
v___x_824_ = lean_usize_sub(v___x_822_, v___x_823_);
v___x_825_ = lean_usize_land(v___x_821_, v___x_824_);
v___x_826_ = lean_array_uget_borrowed(v_x_805_, v___x_825_);
lean_inc(v___x_826_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 2, v___x_826_);
v___x_828_ = v___x_811_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_key_807_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_value_808_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_826_);
v___x_828_ = v_reuseFailAlloc_831_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_array_uset(v_x_805_, v___x_825_, v___x_828_);
v_x_805_ = v___x_829_;
v_x_806_ = v_tail_809_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(lean_object* v_i_833_, lean_object* v_source_834_, lean_object* v_target_835_){
_start:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_array_get_size(v_source_834_);
v___x_837_ = lean_nat_dec_lt(v_i_833_, v___x_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v_source_834_);
lean_dec(v_i_833_);
return v_target_835_;
}
else
{
lean_object* v_es_838_; lean_object* v___x_839_; lean_object* v_source_840_; lean_object* v_target_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_es_838_ = lean_array_fget(v_source_834_, v_i_833_);
v___x_839_ = lean_box(0);
v_source_840_ = lean_array_fset(v_source_834_, v_i_833_, v___x_839_);
v_target_841_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_target_835_, v_es_838_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v_i_833_, v___x_842_);
lean_dec(v_i_833_);
v_i_833_ = v___x_843_;
v_source_834_ = v_source_840_;
v_target_835_ = v_target_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object* v_data_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_nbuckets_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_846_ = lean_array_get_size(v_data_845_);
v___x_847_ = lean_unsigned_to_nat(2u);
v_nbuckets_848_ = lean_nat_mul(v___x_846_, v___x_847_);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_box(0);
v___x_851_ = lean_mk_array(v_nbuckets_848_, v___x_850_);
v___x_852_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v___x_849_, v_data_845_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_853_, lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_mk_empty_array_with_capacity(v___x_855_);
v___x_857_ = lean_array_push(v___x_856_, v_i_853_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
v_val_859_ = lean_ctor_get(v_x_854_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_854_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v_x_854_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_val_859_);
lean_dec(v_x_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_array_push(v_val_859_, v_i_853_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_868_, lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_val_873_; lean_object* v___x_874_; 
v___x_871_ = lean_box(0);
v___x_872_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_868_, v___x_871_);
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec(v___x_872_);
v___x_874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_874_, 0, v_a_869_);
lean_ctor_set(v___x_874_, 1, v_val_873_);
lean_ctor_set(v___x_874_, 2, v_x_870_);
return v___x_874_;
}
else
{
lean_object* v_key_875_; lean_object* v_value_876_; lean_object* v_tail_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_892_; 
v_key_875_ = lean_ctor_get(v_x_870_, 0);
v_value_876_ = lean_ctor_get(v_x_870_, 1);
v_tail_877_ = lean_ctor_get(v_x_870_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_870_);
if (v_isSharedCheck_892_ == 0)
{
v___x_879_ = v_x_870_;
v_isShared_880_ = v_isSharedCheck_892_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_tail_877_);
lean_inc(v_value_876_);
lean_inc(v_key_875_);
lean_dec(v_x_870_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_892_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; 
v___x_881_ = lean_string_dec_eq(v_key_875_, v_a_869_);
if (v___x_881_ == 0)
{
lean_object* v_tail_882_; lean_object* v___x_884_; 
v_tail_882_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_868_, v_a_869_, v_tail_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 2, v_tail_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_key_875_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_value_876_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_tail_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_val_888_; lean_object* v___x_890_; 
lean_dec(v_key_875_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v_value_876_);
v___x_887_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_868_, v___x_886_);
v_val_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_888_);
lean_dec(v___x_887_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_val_888_);
lean_ctor_set(v___x_879_, 0, v_a_869_);
v___x_890_ = v___x_879_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_869_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_val_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_tail_877_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
uint8_t v___x_895_; 
v___x_895_ = 0;
return v___x_895_;
}
else
{
lean_object* v_key_896_; lean_object* v_tail_897_; uint8_t v___x_898_; 
v_key_896_ = lean_ctor_get(v_x_894_, 0);
v_tail_897_ = lean_ctor_get(v_x_894_, 2);
v___x_898_ = lean_string_dec_eq(v_key_896_, v_a_893_);
if (v___x_898_ == 0)
{
v_x_894_ = v_tail_897_;
goto _start;
}
else
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_900_, lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_900_, v_x_901_);
lean_dec(v_x_901_);
lean_dec_ref(v_a_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_904_, lean_object* v_m_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_size_907_; lean_object* v_buckets_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_958_; 
v_size_907_ = lean_ctor_get(v_m_905_, 0);
v_buckets_908_ = lean_ctor_get(v_m_905_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_m_905_);
if (v_isSharedCheck_958_ == 0)
{
v___x_910_ = v_m_905_;
v_isShared_911_ = v_isSharedCheck_958_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_buckets_908_);
lean_inc(v_size_907_);
lean_dec(v_m_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_958_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v_fold_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v_bkt_925_; uint8_t v___x_926_; 
v___x_912_ = lean_array_get_size(v_buckets_908_);
v___x_913_ = lean_string_hash(v_a_906_);
v___x_914_ = 32ULL;
v___x_915_ = lean_uint64_shift_right(v___x_913_, v___x_914_);
v_fold_916_ = lean_uint64_xor(v___x_913_, v___x_915_);
v___x_917_ = 16ULL;
v___x_918_ = lean_uint64_shift_right(v_fold_916_, v___x_917_);
v___x_919_ = lean_uint64_xor(v_fold_916_, v___x_918_);
v___x_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = lean_usize_of_nat(v___x_912_);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_sub(v___x_921_, v___x_922_);
v___x_924_ = lean_usize_land(v___x_920_, v___x_923_);
v_bkt_925_ = lean_array_uget_borrowed(v_buckets_908_, v___x_924_);
v___x_926_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_906_, v_bkt_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_size_x27_930_; lean_object* v___x_931_; lean_object* v_buckets_x27_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_mk_empty_array_with_capacity(v___x_927_);
v___x_929_ = lean_array_push(v___x_928_, v_i_904_);
v_size_x27_930_ = lean_nat_add(v_size_907_, v___x_927_);
lean_dec(v_size_907_);
lean_inc(v_bkt_925_);
v___x_931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_931_, 0, v_a_906_);
lean_ctor_set(v___x_931_, 1, v___x_929_);
lean_ctor_set(v___x_931_, 2, v_bkt_925_);
v_buckets_x27_932_ = lean_array_uset(v_buckets_908_, v___x_924_, v___x_931_);
v___x_933_ = lean_unsigned_to_nat(4u);
v___x_934_ = lean_nat_mul(v_size_x27_930_, v___x_933_);
v___x_935_ = lean_unsigned_to_nat(3u);
v___x_936_ = lean_nat_div(v___x_934_, v___x_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_array_get_size(v_buckets_x27_932_);
v___x_938_ = lean_nat_dec_le(v___x_936_, v___x_937_);
lean_dec(v___x_936_);
if (v___x_938_ == 0)
{
lean_object* v_val_939_; lean_object* v___x_941_; 
v_val_939_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_932_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_val_939_);
lean_ctor_set(v___x_910_, 0, v_size_x27_930_);
v___x_941_ = v___x_910_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_size_x27_930_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_val_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v___x_944_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_buckets_x27_932_);
lean_ctor_set(v___x_910_, 0, v_size_x27_930_);
v___x_944_ = v___x_910_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_size_x27_930_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_buckets_x27_932_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v___x_946_; lean_object* v_buckets_x27_947_; lean_object* v_bkt_x27_948_; lean_object* v___y_950_; uint8_t v___x_955_; 
lean_inc(v_bkt_925_);
v___x_946_ = lean_box(0);
v_buckets_x27_947_ = lean_array_uset(v_buckets_908_, v___x_924_, v___x_946_);
lean_inc_ref(v_a_906_);
v_bkt_x27_948_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_904_, v_a_906_, v_bkt_925_);
v___x_955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_906_, v_bkt_x27_948_);
lean_dec_ref(v_a_906_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_sub(v_size_907_, v___x_956_);
lean_dec(v_size_907_);
v___y_950_ = v___x_957_;
goto v___jp_949_;
}
else
{
v___y_950_ = v_size_907_;
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_array_uset(v_buckets_x27_947_, v___x_924_, v_bkt_x27_948_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v___x_951_);
lean_ctor_set(v___x_910_, 0, v___y_950_);
v___x_953_ = v___x_910_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___y_950_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_959_, lean_object* v_indexes_960_, lean_object* v_status_961_, uint8_t v_version_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_status_961_);
lean_dec_ref(v_indexes_960_);
lean_dec_ref(v_entries_959_);
v_a_965_ = lean_ctor_get(v_x_963_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_x_963_);
if (v_isSharedCheck_973_ == 0)
{
v___x_967_ = v_x_963_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v_x_963_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_991_; 
v_a_974_ = lean_ctor_get(v_x_963_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_963_);
if (v_isSharedCheck_991_ == 0)
{
v___x_976_ = v_x_963_;
v_isShared_977_ = v_isSharedCheck_991_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v_x_963_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_991_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_i_981_; lean_object* v___x_982_; lean_object* v_entries_983_; lean_object* v_indexes_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_978_ = l_Std_Http_Header_Name_date;
v___x_979_ = l_Std_Time_DateTime_toRFC822String(v_a_974_);
v___x_980_ = l_Std_Http_Header_Value_ofString_x21(v___x_979_);
v_i_981_ = lean_array_get_size(v_entries_959_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_978_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
v_entries_983_ = lean_array_push(v_entries_959_, v___x_982_);
v_indexes_984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_981_, v_indexes_960_, v___x_978_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_entries_983_);
lean_ctor_set(v___x_985_, 1, v_indexes_984_);
v___x_986_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_986_, 0, v_status_961_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*2, v_version_962_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_986_);
v___x_988_ = v___x_976_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_992_, lean_object* v_indexes_993_, lean_object* v_status_994_, lean_object* v_version_995_, lean_object* v_x_996_, lean_object* v___y_997_){
_start:
{
uint8_t v_version_boxed_998_; lean_object* v_res_999_; 
v_version_boxed_998_ = lean_unbox(v_version_995_);
v_res_999_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_992_, v_indexes_993_, v_status_994_, v_version_boxed_998_, v_x_996_);
return v_res_999_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_nat_to_int(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v___y_1002_, lean_object* v_a_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_offset_1005_; lean_object* v_second_1006_; lean_object* v_nano_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_offset_1005_ = lean_ctor_get(v___y_1002_, 0);
v_second_1006_ = lean_ctor_get(v_a_1003_, 0);
v_nano_1007_ = lean_ctor_get(v_a_1003_, 1);
v___x_1008_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_1009_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_1010_ = lean_int_mul(v_second_1006_, v___x_1009_);
v___x_1011_ = lean_int_add(v___x_1010_, v_nano_1007_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_int_mul(v_offset_1005_, v___x_1009_);
v___x_1013_ = lean_int_add(v___x_1012_, v___x_1008_);
lean_dec(v___x_1012_);
v___x_1014_ = lean_int_add(v___x_1011_, v___x_1013_);
lean_dec(v___x_1013_);
lean_dec(v___x_1011_);
v___x_1015_ = l_Std_Time_Duration_ofNanoseconds(v___x_1014_);
lean_dec(v___x_1014_);
v___x_1016_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v___y_1017_, lean_object* v_a_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v___y_1017_, v_a_1018_, v_x_1019_);
lean_dec_ref(v_a_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(lean_object* v_m_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_buckets_1023_; lean_object* v___x_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; uint64_t v_fold_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_buckets_1023_ = lean_ctor_get(v_m_1021_, 1);
v___x_1024_ = lean_array_get_size(v_buckets_1023_);
v___x_1025_ = lean_string_hash(v_a_1022_);
v___x_1026_ = 32ULL;
v___x_1027_ = lean_uint64_shift_right(v___x_1025_, v___x_1026_);
v_fold_1028_ = lean_uint64_xor(v___x_1025_, v___x_1027_);
v___x_1029_ = 16ULL;
v___x_1030_ = lean_uint64_shift_right(v_fold_1028_, v___x_1029_);
v___x_1031_ = lean_uint64_xor(v_fold_1028_, v___x_1030_);
v___x_1032_ = lean_uint64_to_usize(v___x_1031_);
v___x_1033_ = lean_usize_of_nat(v___x_1024_);
v___x_1034_ = ((size_t)1ULL);
v___x_1035_ = lean_usize_sub(v___x_1033_, v___x_1034_);
v___x_1036_ = lean_usize_land(v___x_1032_, v___x_1035_);
v___x_1037_ = lean_array_uget_borrowed(v_buckets_1023_, v___x_1036_);
v___x_1038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1022_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg___boxed(lean_object* v_m_1039_, lean_object* v_a_1040_){
_start:
{
uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_res_1041_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_m_1039_, v_a_1040_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v_m_1039_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1044_, lean_object* v_head_1045_){
_start:
{
uint8_t v_generateDate_1050_; 
v_generateDate_1050_ = lean_ctor_get_uint8(v_config_1044_, sizeof(void*)*24 + 1);
if (v_generateDate_1050_ == 0)
{
goto v___jp_1047_;
}
else
{
lean_object* v_headers_1051_; lean_object* v_status_1052_; uint8_t v_version_1053_; lean_object* v_entries_1054_; lean_object* v_indexes_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_headers_1051_ = lean_ctor_get(v_head_1045_, 1);
v_status_1052_ = lean_ctor_get(v_head_1045_, 0);
v_version_1053_ = lean_ctor_get_uint8(v_head_1045_, sizeof(void*)*2);
v_entries_1054_ = lean_ctor_get(v_headers_1051_, 0);
v_indexes_1055_ = lean_ctor_get(v_headers_1051_, 1);
v___x_1056_ = l_Std_Http_Header_Name_date;
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_indexes_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v_val_1061_; lean_object* v_a_1066_; lean_object* v___x_1068_; 
lean_inc_ref(v_indexes_1055_);
lean_inc_ref(v_entries_1054_);
lean_inc(v_status_1052_);
lean_dec_ref(v_head_1045_);
v___x_1058_ = lean_box(v_version_1053_);
v___f_1059_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1059_, 0, v_entries_1054_);
lean_closure_set(v___f_1059_, 1, v_indexes_1055_);
lean_closure_set(v___f_1059_, 2, v_status_1052_);
lean_closure_set(v___f_1059_, 3, v___x_1058_);
v___x_1068_ = lean_get_current_time();
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1071_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1089_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1089_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1089_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___y_1077_; lean_object* v_initialLocalTimeType_1084_; lean_object* v_transitions_1085_; lean_object* v___x_1086_; 
v_initialLocalTimeType_1084_ = lean_ctor_get(v_a_1072_, 0);
v_transitions_1085_ = lean_ctor_get(v_a_1072_, 1);
v___x_1086_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1085_, v_a_1069_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref_known(v___x_1086_, 1);
v___x_1087_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1084_);
v___y_1077_ = v___x_1087_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1088_; 
v_a_1088_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1086_, 1);
v___y_1077_ = v_a_1088_;
goto v___jp_1076_;
}
v___jp_1076_:
{
lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_inc(v_a_1069_);
lean_inc_ref(v___y_1077_);
v___f_1078_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1078_, 0, v___y_1077_);
lean_closure_set(v___f_1078_, 1, v_a_1069_);
v___x_1079_ = lean_mk_thunk(v___f_1078_);
v___x_1080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_a_1069_);
lean_ctor_set(v___x_1080_, 2, v_a_1072_);
lean_ctor_set(v___x_1080_, 3, v___y_1077_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1080_);
v___x_1082_ = v___x_1074_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
v_val_1061_ = v___x_1082_;
goto v___jp_1060_;
}
}
}
}
else
{
lean_object* v_a_1090_; 
lean_dec(v_a_1069_);
v_a_1090_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1071_, 1);
v_a_1066_ = v_a_1090_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1091_; 
v_a_1091_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1068_, 1);
v_a_1066_ = v_a_1091_;
goto v___jp_1065_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_val_1061_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1063_, v___x_1057_, v___x_1062_, v___f_1059_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_a_1066_);
v_val_1061_ = v___x_1067_;
goto v___jp_1060_;
}
}
else
{
goto v___jp_1047_;
}
}
v___jp_1047_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_head_1045_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1092_, lean_object* v_head_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1092_, v_head_1093_);
lean_dec_ref(v_config_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_nat_to_int(v_a_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_nat_to_int(v_a_1098_);
v___x_1100_ = l_Rat_ofInt(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_00_u03b2_1101_, lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_m_1102_, v_a_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___boxed(lean_object* v_00_u03b2_1105_, lean_object* v_m_1106_, lean_object* v_a_1107_){
_start:
{
uint8_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(v_00_u03b2_1105_, v_m_1106_, v_a_1107_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_m_1106_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec_ref(v_a_1115_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1119_, lean_object* v_data_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1122_, lean_object* v_i_1123_, lean_object* v_source_1124_, lean_object* v_target_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v_i_1123_, v_source_1124_, v_target_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1128_, v_x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1131_, lean_object* v_____r_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1131_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1138_, lean_object* v_____r_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1138_, v_____r_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v___f_1142_);
v_a_1145_ = lean_ctor_get(v_x_1143_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1143_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v_x_1143_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v_x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1155_; 
v_a_1154_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v_x_1143_, 1);
v___x_1155_ = lean_apply_2(v___f_1142_, v_a_1154_, lean_box(0));
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1156_, v_x_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1160_, lean_object* v_body_1161_, lean_object* v___f_1162_, lean_object* v___f_1163_, lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v___f_1163_);
lean_dec_ref(v___f_1162_);
lean_dec(v_body_1161_);
lean_dec_ref(v_close_1160_);
v_a_1166_ = lean_ctor_get(v_x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1168_ = v_x_1164_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v_x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; uint8_t v___x_1176_; 
v_a_1175_ = lean_ctor_get(v_x_1164_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v_x_1164_, 1);
v___x_1176_ = lean_unbox(v_a_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v___f_1163_);
v___x_1177_ = lean_apply_2(v_close_1160_, v_body_1161_, lean_box(0));
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = lean_unbox(v_a_1175_);
lean_dec(v_a_1175_);
v___x_1180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1178_, v___x_1179_, v___x_1177_, v___f_1162_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v_a_1175_);
lean_dec_ref(v___f_1162_);
lean_dec(v_body_1161_);
lean_dec_ref(v_close_1160_);
v___x_1181_ = lean_box(0);
v___x_1182_ = lean_apply_2(v___f_1163_, v___x_1181_, lean_box(0));
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1183_, lean_object* v_body_1184_, lean_object* v___f_1185_, lean_object* v___f_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1183_, v_body_1184_, v___f_1185_, v___f_1186_, v_x_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v___x_1190_, lean_object* v_x1_1191_, lean_object* v_x2_1192_){
_start:
{
lean_object* v_fst_1193_; uint8_t v___x_1194_; 
v_fst_1193_ = lean_ctor_get(v_x2_1192_, 0);
v___x_1194_ = lean_string_dec_eq(v_fst_1193_, v___x_1190_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_array_push(v_x1_1191_, v_x2_1192_);
return v___x_1195_;
}
else
{
lean_dec_ref(v_x2_1192_);
return v_x1_1191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v___x_1196_, lean_object* v_x1_1197_, lean_object* v_x2_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v___x_1196_, v_x1_1197_, v_x2_1198_);
lean_dec_ref(v___x_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___f_1200_, lean_object* v___f_1201_, lean_object* v_x1_1202_, lean_object* v_x2_1203_){
_start:
{
lean_object* v_fst_1204_; lean_object* v_entries_1205_; lean_object* v_indexes_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1217_; 
v_fst_1204_ = lean_ctor_get(v_x2_1203_, 0);
lean_inc(v_fst_1204_);
v_entries_1205_ = lean_ctor_get(v_x1_1202_, 0);
v_indexes_1206_ = lean_ctor_get(v_x1_1202_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x1_1202_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1208_ = v_x1_1202_;
v_isShared_1209_ = v_isSharedCheck_1217_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_indexes_1206_);
lean_inc(v_entries_1205_);
lean_dec(v_x1_1202_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1217_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_i_1210_; lean_object* v_f_1211_; lean_object* v_entries_1212_; lean_object* v_indexes_1213_; lean_object* v___x_1215_; 
v_i_1210_ = lean_array_get_size(v_entries_1205_);
v_f_1211_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1211_, 0, v_i_1210_);
v_entries_1212_ = lean_array_push(v_entries_1205_, v_x2_1203_);
v_indexes_1213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1200_, v___f_1201_, v_indexes_1206_, v_fst_1204_, v_f_1211_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v_indexes_1213_);
lean_ctor_set(v___x_1208_, 0, v_entries_1212_);
v___x_1215_ = v___x_1208_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_entries_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_indexes_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___f_1240_; 
v___x_1239_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1240_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1240_, 0, v___x_1239_);
return v___f_1240_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___f_1247_; 
v___x_1246_ = l_Std_Http_Header_Name_contentLength;
v___f_1247_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1247_, 0, v___x_1246_);
return v___f_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v___y_1248_, lean_object* v_body_1249_, lean_object* v_isClosed_1250_, lean_object* v_close_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v___y_1255_; uint8_t v_omitBody_1256_; lean_object* v___y_1269_; lean_object* v___y_1304_; uint8_t v___y_1305_; uint8_t v___y_1306_; 
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_close_1251_);
lean_dec_ref(v_isClosed_1250_);
lean_dec(v_body_1249_);
lean_dec_ref(v___y_1248_);
v_a_1309_ = lean_ctor_get(v_x_1252_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v_x_1252_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v_x_1252_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
else
{
lean_object* v_writer_1318_; lean_object* v_a_1319_; lean_object* v_reader_1320_; lean_object* v_config_1321_; lean_object* v_events_1322_; lean_object* v_error_1323_; lean_object* v_instant_1324_; uint8_t v_keepAlive_1325_; uint8_t v_forcedFlush_1326_; uint8_t v_pullBodyStalled_1327_; lean_object* v_userData_1328_; lean_object* v_outputData_1329_; lean_object* v_state_1330_; lean_object* v_knownSize_1331_; lean_object* v_messageHead_1332_; uint8_t v_sentMessage_1333_; uint8_t v_userClosedBody_1334_; uint8_t v_omitBody_1335_; lean_object* v_userDataBytes_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1487_; 
v_writer_1318_ = lean_ctor_get(v___y_1248_, 1);
lean_inc_ref(v_writer_1318_);
v_a_1319_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v_x_1252_, 1);
v_reader_1320_ = lean_ctor_get(v___y_1248_, 0);
v_config_1321_ = lean_ctor_get(v___y_1248_, 2);
v_events_1322_ = lean_ctor_get(v___y_1248_, 3);
v_error_1323_ = lean_ctor_get(v___y_1248_, 4);
v_instant_1324_ = lean_ctor_get(v___y_1248_, 5);
v_keepAlive_1325_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*6);
v_forcedFlush_1326_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1327_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*6 + 2);
v_userData_1328_ = lean_ctor_get(v_writer_1318_, 0);
v_outputData_1329_ = lean_ctor_get(v_writer_1318_, 1);
v_state_1330_ = lean_ctor_get(v_writer_1318_, 2);
v_knownSize_1331_ = lean_ctor_get(v_writer_1318_, 3);
v_messageHead_1332_ = lean_ctor_get(v_writer_1318_, 4);
v_sentMessage_1333_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6);
v_userClosedBody_1334_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6 + 1);
v_omitBody_1335_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6 + 2);
v_userDataBytes_1336_ = lean_ctor_get(v_writer_1318_, 5);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_writer_1318_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1338_ = v_writer_1318_;
v_isShared_1339_ = v_isSharedCheck_1487_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_userDataBytes_1336_);
lean_inc(v_messageHead_1332_);
lean_inc(v_knownSize_1331_);
lean_inc(v_state_1330_);
lean_inc(v_outputData_1329_);
lean_inc(v_userData_1328_);
lean_dec(v_writer_1318_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1487_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; uint8_t v___x_1436_; lean_object* v___y_1438_; uint8_t v___y_1439_; uint8_t v___y_1440_; uint8_t v___y_1441_; uint8_t v___y_1442_; uint8_t v___y_1443_; uint8_t v___y_1450_; uint8_t v___y_1451_; uint8_t v___y_1452_; uint8_t v___y_1465_; uint8_t v___y_1466_; uint8_t v___y_1469_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1436_ = 0;
v___x_1485_ = lean_box(1);
v___x_1486_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1330_, v___x_1485_);
if (v___x_1486_ == 0)
{
v___y_1469_ = v___x_1486_;
goto v___jp_1468_;
}
else
{
if (v_sentMessage_1333_ == 0)
{
v___y_1469_ = v___x_1486_;
goto v___jp_1468_;
}
else
{
lean_del_object(v___x_1338_);
lean_dec(v_userDataBytes_1336_);
lean_dec(v_messageHead_1332_);
lean_dec(v_knownSize_1331_);
lean_dec(v_state_1330_);
lean_dec_ref(v_outputData_1329_);
lean_dec_ref(v_userData_1328_);
lean_dec(v_a_1319_);
v___y_1255_ = v___y_1248_;
v_omitBody_1256_ = v_omitBody_1335_;
goto v___jp_1254_;
}
}
v___jp_1340_:
{
lean_object* v_message_1343_; lean_object* v___x_2280__overap_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_message_1343_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1341_, v_a_1319_, v___y_1342_);
v___x_2280__overap_1344_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1341_);
v___x_1345_ = lean_apply_2(v___x_2280__overap_1344_, v_outputData_1329_, v_message_1343_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v___x_1345_);
v___x_1347_ = v___x_1338_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_userData_1328_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_state_1330_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_knownSize_1331_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_messageHead_1332_);
lean_ctor_set(v_reuseFailAlloc_1349_, 5, v_userDataBytes_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*6, v_sentMessage_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*6 + 1, v_userClosedBody_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*6 + 2, v_omitBody_1335_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1348_, 0, v_reader_1320_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
lean_ctor_set(v___x_1348_, 2, v_config_1321_);
lean_ctor_set(v___x_1348_, 3, v_events_1322_);
lean_ctor_set(v___x_1348_, 4, v_error_1323_);
lean_ctor_set(v___x_1348_, 5, v_instant_1324_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*6, v_keepAlive_1325_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*6 + 1, v_forcedFlush_1326_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*6 + 2, v_pullBodyStalled_1327_);
v___y_1255_ = v___x_1348_;
v_omitBody_1256_ = v_omitBody_1335_;
goto v___jp_1254_;
}
}
v___jp_1350_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_array_get_size(v___y_1355_);
v___x_1357_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1358_ = lean_nat_dec_lt(v___y_1352_, v___x_1356_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v___y_1355_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___y_1353_;
goto v___jp_1340_;
}
else
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_nat_dec_le(v___x_1356_, v___x_1356_);
if (v___x_1359_ == 0)
{
if (v___x_1358_ == 0)
{
lean_dec_ref(v___y_1355_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___y_1353_;
goto v___jp_1340_;
}
else
{
size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = lean_usize_of_nat(v___x_1356_);
lean_inc_ref(v___y_1351_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1357_, v___y_1351_, v___y_1355_, v___x_1360_, v___x_1361_, v___y_1353_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___x_1362_;
goto v___jp_1340_;
}
}
else
{
size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = ((size_t)0ULL);
v___x_1364_ = lean_usize_of_nat(v___x_1356_);
lean_inc_ref(v___y_1351_);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1357_, v___y_1351_, v___y_1355_, v___x_1363_, v___x_1364_, v___y_1353_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___x_1365_;
goto v___jp_1340_;
}
}
}
v___jp_1366_:
{
lean_object* v_entries_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_entries_1373_ = lean_ctor_get(v___y_1370_, 0);
lean_inc_ref(v_entries_1373_);
lean_dec_ref(v___y_1370_);
v___x_1374_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1371_, v___y_1369_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v___y_1371_);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_array_get_size(v_entries_1373_);
v___x_1377_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1378_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1379_ = lean_nat_dec_lt(v___x_1375_, v___x_1376_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v_entries_1373_);
v___y_1351_ = v___y_1367_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1374_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1377_;
goto v___jp_1350_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_le(v___x_1376_, v___x_1376_);
if (v___x_1380_ == 0)
{
if (v___x_1379_ == 0)
{
lean_dec_ref(v_entries_1373_);
v___y_1351_ = v___y_1367_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1374_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1377_;
goto v___jp_1350_;
}
else
{
size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = lean_usize_of_nat(v___x_1376_);
lean_inc_ref(v___y_1368_);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1378_, v___y_1368_, v_entries_1373_, v___x_1381_, v___x_1382_, v___x_1377_);
v___y_1351_ = v___y_1367_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1374_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1383_;
goto v___jp_1350_;
}
}
else
{
size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = lean_usize_of_nat(v___x_1376_);
lean_inc_ref(v___y_1368_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1378_, v___y_1368_, v_entries_1373_, v___x_1384_, v___x_1385_, v___x_1377_);
v___y_1351_ = v___y_1367_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1374_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1386_;
goto v___jp_1350_;
}
}
}
v___jp_1387_:
{
lean_object* v___x_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___f_1395_; uint8_t v___x_1396_; 
v___x_1391_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1392_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___f_1393_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1394_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1395_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1396_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1393_, v___f_1394_, v___x_1391_, v___y_1390_);
if (v___x_1396_ == 0)
{
if (v___y_1388_ == 0)
{
v___y_1367_ = v___f_1395_;
v___y_1368_ = v___f_1392_;
v___y_1369_ = v___f_1394_;
v___y_1370_ = v___y_1390_;
v___y_1371_ = v___f_1393_;
v___y_1372_ = v___y_1389_;
goto v___jp_1366_;
}
else
{
v___y_1341_ = v___y_1389_;
v___y_1342_ = v___y_1390_;
goto v___jp_1340_;
}
}
else
{
v___y_1367_ = v___f_1395_;
v___y_1368_ = v___f_1392_;
v___y_1369_ = v___f_1394_;
v___y_1370_ = v___y_1390_;
v___y_1371_ = v___f_1393_;
v___y_1372_ = v___y_1389_;
goto v___jp_1366_;
}
}
v___jp_1397_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_array_get_size(v___y_1403_);
v___x_1405_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1406_ = lean_nat_dec_lt(v___y_1401_, v___x_1404_);
if (v___x_1406_ == 0)
{
lean_dec_ref(v___y_1403_);
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___y_1399_;
goto v___jp_1387_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_le(v___x_1404_, v___x_1404_);
if (v___x_1407_ == 0)
{
if (v___x_1406_ == 0)
{
lean_dec_ref(v___y_1403_);
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___y_1399_;
goto v___jp_1387_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1404_);
lean_inc_ref(v___y_1398_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1405_, v___y_1398_, v___y_1403_, v___x_1408_, v___x_1409_, v___y_1399_);
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___x_1410_;
goto v___jp_1387_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1404_);
lean_inc_ref(v___y_1398_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1405_, v___y_1398_, v___y_1403_, v___x_1411_, v___x_1412_, v___y_1399_);
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___x_1413_;
goto v___jp_1387_;
}
}
}
v___jp_1414_:
{
lean_object* v_entries_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_entries_1422_ = lean_ctor_get(v___y_1417_, 0);
lean_inc_ref(v_entries_1422_);
lean_dec_ref(v___y_1417_);
v___x_1423_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1418_, v___y_1416_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v___y_1418_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_array_get_size(v_entries_1422_);
v___x_1426_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1427_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1428_ = lean_nat_dec_lt(v___x_1424_, v___x_1425_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v_entries_1422_);
v___y_1398_ = v___y_1415_;
v___y_1399_ = v___x_1423_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___x_1424_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___x_1426_;
goto v___jp_1397_;
}
else
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_nat_dec_le(v___x_1425_, v___x_1425_);
if (v___x_1429_ == 0)
{
if (v___x_1428_ == 0)
{
lean_dec_ref(v_entries_1422_);
v___y_1398_ = v___y_1415_;
v___y_1399_ = v___x_1423_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___x_1424_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___x_1426_;
goto v___jp_1397_;
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1425_);
lean_inc_ref(v___y_1420_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1427_, v___y_1420_, v_entries_1422_, v___x_1430_, v___x_1431_, v___x_1426_);
v___y_1398_ = v___y_1415_;
v___y_1399_ = v___x_1423_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___x_1424_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___x_1432_;
goto v___jp_1397_;
}
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1425_);
lean_inc_ref(v___y_1420_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1427_, v___y_1420_, v_entries_1422_, v___x_1433_, v___x_1434_, v___x_1426_);
v___y_1398_ = v___y_1415_;
v___y_1399_ = v___x_1423_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___x_1424_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___x_1435_;
goto v___jp_1397_;
}
}
}
v___jp_1437_:
{
lean_object* v_headerSize_1444_; lean_object* v_machine_1445_; lean_object* v_machine_1446_; lean_object* v_reader_1447_; lean_object* v_state_1448_; 
v_headerSize_1444_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1442_, v_a_1319_, v___y_1440_);
v_machine_1445_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1436_, v___y_1438_, v_headerSize_1444_, v___y_1443_);
v_machine_1446_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1436_, v_machine_1445_, v_a_1319_);
lean_dec(v_a_1319_);
v_reader_1447_ = lean_ctor_get(v_machine_1446_, 0);
lean_inc_ref(v_reader_1447_);
v_state_1448_ = lean_ctor_get(v_reader_1447_, 0);
lean_inc(v_state_1448_);
lean_dec_ref(v_reader_1447_);
if (lean_obj_tag(v_state_1448_) == 7)
{
lean_dec_ref_known(v_state_1448_, 1);
v___y_1304_ = v_machine_1446_;
v___y_1305_ = v___y_1441_;
v___y_1306_ = v___y_1439_;
goto v___jp_1303_;
}
else
{
lean_dec(v_state_1448_);
v___y_1304_ = v_machine_1446_;
v___y_1305_ = v___y_1441_;
v___y_1306_ = v___y_1440_;
goto v___jp_1303_;
}
}
v___jp_1449_:
{
uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v_indexes_1455_; lean_object* v___x_1456_; lean_object* v_machine_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___f_1460_; uint8_t v___x_1461_; 
v___x_1453_ = 1;
v___x_1454_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1453_, v_a_1319_);
v_indexes_1455_ = lean_ctor_get(v___x_1454_, 1);
lean_inc_ref(v_indexes_1455_);
lean_dec_ref(v___x_1454_);
lean_inc(v_a_1319_);
v___x_1456_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1456_, 0, v_userData_1328_);
lean_ctor_set(v___x_1456_, 1, v_outputData_1329_);
lean_ctor_set(v___x_1456_, 2, v_state_1330_);
lean_ctor_set(v___x_1456_, 3, v_knownSize_1331_);
lean_ctor_set(v___x_1456_, 4, v_a_1319_);
lean_ctor_set(v___x_1456_, 5, v_userDataBytes_1336_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*6, v___y_1450_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*6 + 1, v_userClosedBody_1334_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*6 + 2, v_omitBody_1335_);
v_machine_1457_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1457_, 0, v_reader_1320_);
lean_ctor_set(v_machine_1457_, 1, v___x_1456_);
lean_ctor_set(v_machine_1457_, 2, v_config_1321_);
lean_ctor_set(v_machine_1457_, 3, v_events_1322_);
lean_ctor_set(v_machine_1457_, 4, v_error_1323_);
lean_ctor_set(v_machine_1457_, 5, v_instant_1324_);
lean_ctor_set_uint8(v_machine_1457_, sizeof(void*)*6, v_keepAlive_1325_);
lean_ctor_set_uint8(v_machine_1457_, sizeof(void*)*6 + 1, v_forcedFlush_1326_);
lean_ctor_set_uint8(v_machine_1457_, sizeof(void*)*6 + 2, v_pullBodyStalled_1327_);
v___x_1458_ = l_Std_Http_Header_Name_contentLength;
v___f_1459_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1460_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1459_, v___f_1460_, v_indexes_1455_, v___x_1458_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1459_, v___f_1460_, v_indexes_1455_, v___x_1462_);
lean_dec_ref(v_indexes_1455_);
v___y_1438_ = v_machine_1457_;
v___y_1439_ = v___y_1450_;
v___y_1440_ = v___y_1451_;
v___y_1441_ = v___y_1452_;
v___y_1442_ = v___x_1453_;
v___y_1443_ = v___x_1463_;
goto v___jp_1437_;
}
else
{
lean_dec_ref(v_indexes_1455_);
v___y_1438_ = v_machine_1457_;
v___y_1439_ = v___y_1450_;
v___y_1440_ = v___y_1451_;
v___y_1441_ = v___y_1452_;
v___y_1442_ = v___x_1453_;
v___y_1443_ = v___x_1461_;
goto v___jp_1437_;
}
}
v___jp_1464_:
{
lean_object* v_state_1467_; 
v_state_1467_ = lean_ctor_get(v_reader_1320_, 0);
if (lean_obj_tag(v_state_1467_) == 7)
{
v___y_1450_ = v___y_1465_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1465_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___y_1465_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1466_;
goto v___jp_1449_;
}
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_userDataBytes_1336_);
lean_dec(v_messageHead_1332_);
lean_dec(v_knownSize_1331_);
lean_dec(v_state_1330_);
lean_dec_ref(v_outputData_1329_);
lean_dec_ref(v_userData_1328_);
lean_dec(v_a_1319_);
v___y_1255_ = v___y_1248_;
v_omitBody_1256_ = v_omitBody_1335_;
goto v___jp_1254_;
}
else
{
lean_object* v_status_1470_; uint8_t v___x_1471_; uint16_t v___x_1472_; uint16_t v___x_1473_; uint8_t v___x_1474_; 
lean_inc(v_instant_1324_);
lean_inc(v_error_1323_);
lean_inc_ref(v_events_1322_);
lean_inc_ref(v_config_1321_);
lean_inc_ref(v_reader_1320_);
lean_dec_ref(v___y_1248_);
v_status_1470_ = lean_ctor_get(v_a_1319_, 0);
v___x_1471_ = 0;
v___x_1472_ = 100;
v___x_1473_ = l_Std_Http_Status_toCode(v_status_1470_);
v___x_1474_ = lean_uint16_dec_le(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_messageHead_1332_);
v___y_1465_ = v___y_1469_;
v___y_1466_ = v___x_1471_;
goto v___jp_1464_;
}
else
{
uint16_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = 200;
v___x_1476_ = lean_uint16_dec_lt(v___x_1473_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_messageHead_1332_);
v___y_1465_ = v___y_1469_;
v___y_1466_ = v___x_1471_;
goto v___jp_1464_;
}
else
{
uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; uint8_t v___x_1484_; 
v___x_1477_ = 1;
v___x_1478_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1477_, v_a_1319_);
v___x_1479_ = l_Std_Http_Header_Name_contentLength;
v___f_1480_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15);
v___f_1481_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1482_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1483_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1484_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1481_, v___f_1482_, v___x_1479_, v___x_1478_);
if (v___x_1484_ == 0)
{
if (v___x_1476_ == 0)
{
v___y_1415_ = v___f_1483_;
v___y_1416_ = v___f_1482_;
v___y_1417_ = v___x_1478_;
v___y_1418_ = v___f_1481_;
v___y_1419_ = v___x_1476_;
v___y_1420_ = v___f_1480_;
v___y_1421_ = v___x_1477_;
goto v___jp_1414_;
}
else
{
v___y_1388_ = v___x_1476_;
v___y_1389_ = v___x_1477_;
v___y_1390_ = v___x_1478_;
goto v___jp_1387_;
}
}
else
{
v___y_1415_ = v___f_1483_;
v___y_1416_ = v___f_1482_;
v___y_1417_ = v___x_1478_;
v___y_1418_ = v___f_1481_;
v___y_1419_ = v___x_1476_;
v___y_1420_ = v___f_1480_;
v___y_1421_ = v___x_1477_;
goto v___jp_1414_;
}
}
}
}
}
}
}
v___jp_1254_:
{
if (v_omitBody_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v_close_1251_);
lean_dec_ref(v_isClosed_1250_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_body_1249_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___y_1255_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
lean_inc(v_body_1249_);
v___x_1261_ = lean_apply_2(v_isClosed_1250_, v_body_1249_, lean_box(0));
v___f_1262_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1262_, 0, v___y_1255_);
lean_inc_ref(v___f_1262_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1263_, 0, v___f_1262_);
v___f_1264_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1264_, 0, v_close_1251_);
lean_closure_set(v___f_1264_, 1, v_body_1249_);
lean_closure_set(v___f_1264_, 2, v___f_1263_);
lean_closure_set(v___f_1264_, 3, v___f_1262_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = 0;
v___x_1267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1265_, v___x_1266_, v___x_1261_, v___f_1264_);
return v___x_1267_;
}
}
v___jp_1268_:
{
lean_object* v_writer_1270_; lean_object* v_reader_1271_; lean_object* v_config_1272_; lean_object* v_events_1273_; lean_object* v_error_1274_; lean_object* v_instant_1275_; uint8_t v_keepAlive_1276_; uint8_t v_forcedFlush_1277_; uint8_t v_pullBodyStalled_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1302_; 
v_writer_1270_ = lean_ctor_get(v___y_1269_, 1);
v_reader_1271_ = lean_ctor_get(v___y_1269_, 0);
v_config_1272_ = lean_ctor_get(v___y_1269_, 2);
v_events_1273_ = lean_ctor_get(v___y_1269_, 3);
v_error_1274_ = lean_ctor_get(v___y_1269_, 4);
v_instant_1275_ = lean_ctor_get(v___y_1269_, 5);
v_keepAlive_1276_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*6);
v_forcedFlush_1277_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1278_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*6 + 2);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___y_1269_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1280_ = v___y_1269_;
v_isShared_1281_ = v_isSharedCheck_1302_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_instant_1275_);
lean_inc(v_error_1274_);
lean_inc(v_events_1273_);
lean_inc(v_config_1272_);
lean_inc(v_writer_1270_);
lean_inc(v_reader_1271_);
lean_dec(v___y_1269_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1302_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_userData_1282_; lean_object* v_outputData_1283_; lean_object* v_knownSize_1284_; lean_object* v_messageHead_1285_; uint8_t v_sentMessage_1286_; uint8_t v_userClosedBody_1287_; uint8_t v_omitBody_1288_; lean_object* v_userDataBytes_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1300_; 
v_userData_1282_ = lean_ctor_get(v_writer_1270_, 0);
v_outputData_1283_ = lean_ctor_get(v_writer_1270_, 1);
v_knownSize_1284_ = lean_ctor_get(v_writer_1270_, 3);
v_messageHead_1285_ = lean_ctor_get(v_writer_1270_, 4);
v_sentMessage_1286_ = lean_ctor_get_uint8(v_writer_1270_, sizeof(void*)*6);
v_userClosedBody_1287_ = lean_ctor_get_uint8(v_writer_1270_, sizeof(void*)*6 + 1);
v_omitBody_1288_ = lean_ctor_get_uint8(v_writer_1270_, sizeof(void*)*6 + 2);
v_userDataBytes_1289_ = lean_ctor_get(v_writer_1270_, 5);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_writer_1270_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_writer_1270_, 2);
lean_dec(v_unused_1301_);
v___x_1291_ = v_writer_1270_;
v_isShared_1292_ = v_isSharedCheck_1300_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_userDataBytes_1289_);
lean_inc(v_messageHead_1285_);
lean_inc(v_knownSize_1284_);
lean_inc(v_outputData_1283_);
lean_inc(v_userData_1282_);
lean_dec(v_writer_1270_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1300_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = lean_box(2);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 2, v___x_1293_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_userData_1282_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_outputData_1283_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_knownSize_1284_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_messageHead_1285_);
lean_ctor_set(v_reuseFailAlloc_1299_, 5, v_userDataBytes_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*6, v_sentMessage_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*6 + 1, v_userClosedBody_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*6 + 2, v_omitBody_1288_);
v___x_1295_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1297_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1295_);
v___x_1297_ = v___x_1280_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_reader_1271_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_config_1272_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_events_1273_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v_error_1274_);
lean_ctor_set(v_reuseFailAlloc_1298_, 5, v_instant_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*6, v_keepAlive_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*6 + 1, v_forcedFlush_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*6 + 2, v_pullBodyStalled_1278_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v___y_1255_ = v___x_1297_;
v_omitBody_1256_ = v_omitBody_1288_;
goto v___jp_1254_;
}
}
}
}
}
v___jp_1303_:
{
if (v___y_1306_ == 0)
{
v___y_1269_ = v___y_1304_;
goto v___jp_1268_;
}
else
{
if (v___y_1305_ == 0)
{
lean_object* v_writer_1307_; uint8_t v_omitBody_1308_; 
v_writer_1307_ = lean_ctor_get(v___y_1304_, 1);
v_omitBody_1308_ = lean_ctor_get_uint8(v_writer_1307_, sizeof(void*)*6 + 2);
v___y_1255_ = v___y_1304_;
v_omitBody_1256_ = v_omitBody_1308_;
goto v___jp_1254_;
}
else
{
v___y_1269_ = v___y_1304_;
goto v___jp_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1488_, lean_object* v_body_1489_, lean_object* v_isClosed_1490_, lean_object* v_close_1491_, lean_object* v_x_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1488_, v_body_1489_, v_isClosed_1490_, v_close_1491_, v_x_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v_config_1495_, lean_object* v_line_1496_, lean_object* v_body_1497_, lean_object* v_isClosed_1498_, lean_object* v_close_1499_, lean_object* v_machine_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___y_1504_; 
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_machine_1500_);
lean_dec_ref(v_close_1499_);
lean_dec_ref(v_isClosed_1498_);
lean_dec(v_body_1497_);
lean_dec_ref(v_line_1496_);
v_a_1510_ = lean_ctor_get(v_x_1501_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v_x_1501_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v_x_1501_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1519_; 
v_a_1519_ = lean_ctor_get(v_x_1501_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v_x_1501_, 1);
if (lean_obj_tag(v_a_1519_) == 1)
{
lean_object* v_writer_1520_; lean_object* v_reader_1521_; lean_object* v_config_1522_; lean_object* v_events_1523_; lean_object* v_error_1524_; lean_object* v_instant_1525_; uint8_t v_keepAlive_1526_; uint8_t v_forcedFlush_1527_; uint8_t v_pullBodyStalled_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1551_; 
v_writer_1520_ = lean_ctor_get(v_machine_1500_, 1);
v_reader_1521_ = lean_ctor_get(v_machine_1500_, 0);
v_config_1522_ = lean_ctor_get(v_machine_1500_, 2);
v_events_1523_ = lean_ctor_get(v_machine_1500_, 3);
v_error_1524_ = lean_ctor_get(v_machine_1500_, 4);
v_instant_1525_ = lean_ctor_get(v_machine_1500_, 5);
v_keepAlive_1526_ = lean_ctor_get_uint8(v_machine_1500_, sizeof(void*)*6);
v_forcedFlush_1527_ = lean_ctor_get_uint8(v_machine_1500_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1528_ = lean_ctor_get_uint8(v_machine_1500_, sizeof(void*)*6 + 2);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_machine_1500_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1530_ = v_machine_1500_;
v_isShared_1531_ = v_isSharedCheck_1551_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_instant_1525_);
lean_inc(v_error_1524_);
lean_inc(v_events_1523_);
lean_inc(v_config_1522_);
lean_inc(v_writer_1520_);
lean_inc(v_reader_1521_);
lean_dec(v_machine_1500_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1551_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_userData_1532_; lean_object* v_outputData_1533_; lean_object* v_state_1534_; lean_object* v_messageHead_1535_; uint8_t v_sentMessage_1536_; uint8_t v_userClosedBody_1537_; uint8_t v_omitBody_1538_; lean_object* v_userDataBytes_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1549_; 
v_userData_1532_ = lean_ctor_get(v_writer_1520_, 0);
v_outputData_1533_ = lean_ctor_get(v_writer_1520_, 1);
v_state_1534_ = lean_ctor_get(v_writer_1520_, 2);
v_messageHead_1535_ = lean_ctor_get(v_writer_1520_, 4);
v_sentMessage_1536_ = lean_ctor_get_uint8(v_writer_1520_, sizeof(void*)*6);
v_userClosedBody_1537_ = lean_ctor_get_uint8(v_writer_1520_, sizeof(void*)*6 + 1);
v_omitBody_1538_ = lean_ctor_get_uint8(v_writer_1520_, sizeof(void*)*6 + 2);
v_userDataBytes_1539_ = lean_ctor_get(v_writer_1520_, 5);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_writer_1520_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_writer_1520_, 3);
lean_dec(v_unused_1550_);
v___x_1541_ = v_writer_1520_;
v_isShared_1542_ = v_isSharedCheck_1549_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_userDataBytes_1539_);
lean_inc(v_messageHead_1535_);
lean_inc(v_state_1534_);
lean_inc(v_outputData_1533_);
lean_inc(v_userData_1532_);
lean_dec(v_writer_1520_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1549_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 3, v_a_1519_);
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_userData_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_outputData_1533_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_state_1534_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_a_1519_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_messageHead_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_userDataBytes_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*6, v_sentMessage_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*6 + 1, v_userClosedBody_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*6 + 2, v_omitBody_1538_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1544_);
v___x_1546_ = v___x_1530_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_reader_1521_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_config_1522_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_events_1523_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_error_1524_);
lean_ctor_set(v_reuseFailAlloc_1547_, 5, v_instant_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*6, v_keepAlive_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*6 + 1, v_forcedFlush_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*6 + 2, v_pullBodyStalled_1528_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v___y_1504_ = v___x_1546_;
goto v___jp_1503_;
}
}
}
}
}
else
{
lean_dec(v_a_1519_);
v___y_1504_ = v_machine_1500_;
goto v___jp_1503_;
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1505_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1495_, v_line_1496_);
v___f_1506_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1506_, 0, v___y_1504_);
lean_closure_set(v___f_1506_, 1, v_body_1497_);
lean_closure_set(v___f_1506_, 2, v_isClosed_1498_);
lean_closure_set(v___f_1506_, 3, v_close_1499_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = 0;
v___x_1509_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1507_, v___x_1508_, v___x_1505_, v___f_1506_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v_config_1552_, lean_object* v_line_1553_, lean_object* v_body_1554_, lean_object* v_isClosed_1555_, lean_object* v_close_1556_, lean_object* v_machine_1557_, lean_object* v_x_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v_config_1552_, v_line_1553_, v_body_1554_, v_isClosed_1555_, v_close_1556_, v_machine_1557_, v_x_1558_);
lean_dec_ref(v_config_1552_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1561_, lean_object* v_config_1562_, lean_object* v_machine_1563_, lean_object* v_res_1564_){
_start:
{
lean_object* v_close_1566_; lean_object* v_isClosed_1567_; lean_object* v_getKnownSize_1568_; lean_object* v_line_1569_; lean_object* v_body_1570_; lean_object* v___x_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; 
v_close_1566_ = lean_ctor_get(v_inst_1561_, 1);
lean_inc_ref(v_close_1566_);
v_isClosed_1567_ = lean_ctor_get(v_inst_1561_, 2);
lean_inc_ref(v_isClosed_1567_);
v_getKnownSize_1568_ = lean_ctor_get(v_inst_1561_, 5);
lean_inc_ref(v_getKnownSize_1568_);
lean_dec_ref(v_inst_1561_);
v_line_1569_ = lean_ctor_get(v_res_1564_, 0);
lean_inc_ref(v_line_1569_);
v_body_1570_ = lean_ctor_get(v_res_1564_, 1);
lean_inc_n(v_body_1570_, 2);
lean_dec_ref(v_res_1564_);
v___x_1571_ = lean_apply_2(v_getKnownSize_1568_, v_body_1570_, lean_box(0));
v___f_1572_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_1572_, 0, v_config_1562_);
lean_closure_set(v___f_1572_, 1, v_line_1569_);
lean_closure_set(v___f_1572_, 2, v_body_1570_);
lean_closure_set(v___f_1572_, 3, v_isClosed_1567_);
lean_closure_set(v___f_1572_, 4, v_close_1566_);
lean_closure_set(v___f_1572_, 5, v_machine_1563_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = 0;
v___x_1575_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1573_, v___x_1574_, v___x_1571_, v___f_1572_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1576_, lean_object* v_config_1577_, lean_object* v_machine_1578_, lean_object* v_res_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1576_, v_config_1577_, v_machine_1578_, v_res_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1582_, lean_object* v_inst_1583_, lean_object* v_config_1584_, lean_object* v_machine_1585_, lean_object* v_res_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1583_, v_config_1584_, v_machine_1585_, v_res_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1589_, lean_object* v_inst_1590_, lean_object* v_config_1591_, lean_object* v_machine_1592_, lean_object* v_res_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1589_, v_inst_1590_, v_config_1591_, v_machine_1592_, v_res_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v_closed_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_closed_1599_ = lean_ctor_get_uint8(v_____do__lift_1596_, sizeof(void*)*5);
v___x_1600_ = lean_box(v_closed_1599_);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v_____do__lift_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_pendingProducer_1615_; lean_object* v_pendingConsumer_1616_; lean_object* v_interestWaiter_1617_; uint8_t v_closed_1618_; lean_object* v_pendingIncompleteChunk_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1628_; 
v___x_1614_ = lean_st_ref_take(v___y_1612_);
v_pendingProducer_1615_ = lean_ctor_get(v___x_1614_, 0);
v_pendingConsumer_1616_ = lean_ctor_get(v___x_1614_, 1);
v_interestWaiter_1617_ = lean_ctor_get(v___x_1614_, 2);
v_closed_1618_ = lean_ctor_get_uint8(v___x_1614_, sizeof(void*)*5);
v_pendingIncompleteChunk_1619_ = lean_ctor_get(v___x_1614_, 4);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v___x_1614_, 3);
lean_dec(v_unused_1629_);
v___x_1621_ = v___x_1614_;
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1619_);
lean_inc(v_interestWaiter_1617_);
lean_inc(v_pendingConsumer_1616_);
lean_inc(v_pendingProducer_1615_);
lean_dec(v___x_1614_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 3, v___x_1611_);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_pendingProducer_1615_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_pendingConsumer_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_interestWaiter_1617_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_pendingIncompleteChunk_1619_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*5, v_closed_1618_);
v___x_1624_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_st_ref_set(v___y_1612_, v___x_1624_);
v___x_1626_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1630_, v___y_1631_);
lean_dec(v___y_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1634_, lean_object* v_x_1635_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___x_1634_);
v_a_1637_ = lean_ctor_get(v_x_1635_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1635_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1639_ = v_x_1635_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v_x_1635_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
}
else
{
lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1654_; 
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1635_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v_x_1635_, 0);
lean_dec(v_unused_1655_);
v___x_1647_ = v_x_1635_;
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
else
{
lean_dec(v_x_1635_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1634_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1649_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1656_, lean_object* v_x_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1656_, v_x_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1660_, lean_object* v_requestStream_1661_, lean_object* v_keepAliveTimeout_1662_, lean_object* v_currentTimeout_1663_, lean_object* v_headerTimeout_1664_, lean_object* v_response_1665_, lean_object* v_respStream_1666_, lean_object* v_expectData_1667_, uint8_t v_handlerDispatched_1668_, lean_object* v_____r_1669_){
_start:
{
uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1671_ = 0;
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1673_, 0, v_machine_1660_);
lean_ctor_set(v___x_1673_, 1, v_requestStream_1661_);
lean_ctor_set(v___x_1673_, 2, v_keepAliveTimeout_1662_);
lean_ctor_set(v___x_1673_, 3, v_currentTimeout_1663_);
lean_ctor_set(v___x_1673_, 4, v_headerTimeout_1664_);
lean_ctor_set(v___x_1673_, 5, v_response_1665_);
lean_ctor_set(v___x_1673_, 6, v_respStream_1666_);
lean_ctor_set(v___x_1673_, 7, v_expectData_1667_);
lean_ctor_set(v___x_1673_, 8, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*9, v___x_1671_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*9 + 1, v_handlerDispatched_1668_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1677_, lean_object* v_requestStream_1678_, lean_object* v_keepAliveTimeout_1679_, lean_object* v_currentTimeout_1680_, lean_object* v_headerTimeout_1681_, lean_object* v_response_1682_, lean_object* v_respStream_1683_, lean_object* v_expectData_1684_, lean_object* v_handlerDispatched_1685_, lean_object* v_____r_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v_handlerDispatched_boxed_1688_; lean_object* v_res_1689_; 
v_handlerDispatched_boxed_1688_ = lean_unbox(v_handlerDispatched_1685_);
v_res_1689_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1677_, v_requestStream_1678_, v_keepAliveTimeout_1679_, v_currentTimeout_1680_, v_headerTimeout_1681_, v_response_1682_, v_respStream_1683_, v_expectData_1684_, v_handlerDispatched_boxed_1688_, v_____r_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v___f_1690_);
v_a_1693_ = lean_ctor_get(v_x_1691_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v_x_1691_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v_x_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1703_; 
v_a_1702_ = lean_ctor_get(v_x_1691_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v_x_1691_, 1);
v___x_1703_ = lean_apply_2(v___f_1690_, v_a_1702_, lean_box(0));
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1704_, v_x_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1708_, lean_object* v___f_1709_, lean_object* v___f_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v___f_1710_);
lean_dec_ref(v___f_1709_);
lean_dec_ref(v_requestStream_1708_);
v_a_1713_ = lean_ctor_get(v_x_1711_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1715_ = v_x_1711_;
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v_x_1711_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; uint8_t v___x_1723_; 
v_a_1722_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1723_ = lean_unbox(v_a_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___f_1710_);
v___x_1724_ = l_Std_Http_Body_Stream_close(v_requestStream_1708_);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
v___x_1727_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1725_, v___x_1726_, v___x_1724_, v___f_1709_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v_a_1722_);
lean_dec_ref(v___f_1709_);
lean_dec_ref(v_requestStream_1708_);
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_apply_2(v___f_1710_, v___x_1728_, lean_box(0));
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1730_, lean_object* v___f_1731_, lean_object* v___f_1732_, lean_object* v_x_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1730_, v___f_1731_, v___f_1732_, v_x_1733_);
return v_res_1735_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1736_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1737_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; 
v___x_1743_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1744_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1745_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1745_, 0, v___f_1744_);
lean_closure_set(v___f_1745_, 1, v___x_1743_);
return v___f_1745_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; 
v___x_1754_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1755_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1756_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1756_, 0, v___f_1755_);
lean_closure_set(v___f_1756_, 1, v___x_1754_);
return v___f_1756_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1757_; lean_object* v___x_1758_; 
v___f_1757_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1758_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1758_, 0, lean_box(0));
lean_closure_set(v___x_1758_, 1, lean_box(0));
lean_closure_set(v___x_1758_, 2, lean_box(0));
lean_closure_set(v___x_1758_, 3, v___f_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1759_, lean_object* v___f_1760_, lean_object* v_x_1761_){
_start:
{
if (lean_obj_tag(v_x_1761_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v___f_1760_);
lean_dec_ref(v___y_1759_);
v_a_1763_ = lean_ctor_get(v_x_1761_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_x_1761_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1765_ = v_x_1761_;
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v_x_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
}
else
{
lean_object* v_machine_1772_; lean_object* v_requestStream_1773_; lean_object* v_keepAliveTimeout_1774_; lean_object* v_currentTimeout_1775_; lean_object* v_headerTimeout_1776_; lean_object* v_response_1777_; lean_object* v_respStream_1778_; lean_object* v_expectData_1779_; uint8_t v_handlerDispatched_1780_; lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_4928__overap_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___f_1789_; lean_object* v___f_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref_known(v_x_1761_, 1);
v_machine_1772_ = lean_ctor_get(v___y_1759_, 0);
lean_inc_ref(v_machine_1772_);
v_requestStream_1773_ = lean_ctor_get(v___y_1759_, 1);
lean_inc_ref_n(v_requestStream_1773_, 3);
v_keepAliveTimeout_1774_ = lean_ctor_get(v___y_1759_, 2);
lean_inc(v_keepAliveTimeout_1774_);
v_currentTimeout_1775_ = lean_ctor_get(v___y_1759_, 3);
lean_inc(v_currentTimeout_1775_);
v_headerTimeout_1776_ = lean_ctor_get(v___y_1759_, 4);
lean_inc(v_headerTimeout_1776_);
v_response_1777_ = lean_ctor_get(v___y_1759_, 5);
lean_inc_ref(v_response_1777_);
v_respStream_1778_ = lean_ctor_get(v___y_1759_, 6);
lean_inc(v_respStream_1778_);
v_expectData_1779_ = lean_ctor_get(v___y_1759_, 7);
lean_inc(v_expectData_1779_);
v_handlerDispatched_1780_ = lean_ctor_get_uint8(v___y_1759_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1759_);
v___x_1781_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1782_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1783_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1784_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1785_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1785_, 0, lean_box(0));
lean_closure_set(v___x_1785_, 1, lean_box(0));
lean_closure_set(v___x_1785_, 2, lean_box(0));
lean_closure_set(v___x_1785_, 3, v___x_1781_);
lean_closure_set(v___x_1785_, 4, lean_box(0));
lean_closure_set(v___x_1785_, 5, lean_box(0));
lean_closure_set(v___x_1785_, 6, v___x_1784_);
lean_closure_set(v___x_1785_, 7, v___f_1760_);
v___x_4928__overap_1786_ = l_Std_Mutex_atomically___redArg(v___x_1781_, v___f_1782_, v___f_1783_, v_requestStream_1773_, v___x_1785_);
v___x_1787_ = lean_apply_1(v___x_4928__overap_1786_, lean_box(0));
v___x_1788_ = lean_box(v_handlerDispatched_1780_);
v___f_1789_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1789_, 0, v_machine_1772_);
lean_closure_set(v___f_1789_, 1, v_requestStream_1773_);
lean_closure_set(v___f_1789_, 2, v_keepAliveTimeout_1774_);
lean_closure_set(v___f_1789_, 3, v_currentTimeout_1775_);
lean_closure_set(v___f_1789_, 4, v_headerTimeout_1776_);
lean_closure_set(v___f_1789_, 5, v_response_1777_);
lean_closure_set(v___f_1789_, 6, v_respStream_1778_);
lean_closure_set(v___f_1789_, 7, v_expectData_1779_);
lean_closure_set(v___f_1789_, 8, v___x_1788_);
lean_inc_ref(v___f_1789_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1790_, 0, v___f_1789_);
v___f_1791_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1791_, 0, v_requestStream_1773_);
lean_closure_set(v___f_1791_, 1, v___f_1790_);
lean_closure_set(v___f_1791_, 2, v___f_1789_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = 0;
v___x_1794_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1792_, v___x_1793_, v___x_1787_, v___f_1791_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1795_, lean_object* v___f_1796_, lean_object* v_x_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1795_, v___f_1796_, v_x_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1800_, lean_object* v_x_1801_){
_start:
{
if (lean_obj_tag(v_x_1801_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1811_; 
lean_dec_ref(v___y_1800_);
v_a_1803_ = lean_ctor_get(v_x_1801_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_x_1801_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1805_ = v_x_1801_;
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v_x_1801_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
}
}
else
{
lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v_x_1801_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v_x_1801_, 0);
lean_dec(v_unused_1821_);
v___x_1813_ = v_x_1801_;
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
else
{
lean_dec(v_x_1801_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___y_1800_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1822_, v_x_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1826_, lean_object* v___f_1827_, lean_object* v___y_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1829_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___f_1827_);
lean_dec_ref(v_requestStream_1826_);
v_a_1831_ = lean_ctor_get(v_x_1829_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1833_ = v_x_1829_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v_x_1829_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1854_; 
v_a_1840_ = lean_ctor_get(v_x_1829_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1842_ = v_x_1829_;
v_isShared_1843_ = v_isSharedCheck_1854_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v_x_1829_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1854_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_unbox(v_a_1840_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; 
lean_del_object(v___x_1842_);
lean_dec_ref(v___y_1828_);
v___x_1845_ = l_Std_Http_Body_Stream_close(v_requestStream_1826_);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = lean_unbox(v_a_1840_);
lean_dec(v_a_1840_);
v___x_1848_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1846_, v___x_1847_, v___x_1845_, v___f_1827_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v_a_1840_);
lean_dec_ref(v___f_1827_);
lean_dec_ref(v_requestStream_1826_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___y_1828_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1849_);
v___x_1851_ = v___x_1842_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1855_, lean_object* v___f_1856_, lean_object* v___y_1857_, lean_object* v_x_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1855_, v___f_1856_, v___y_1857_, v_x_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1861_, lean_object* v_machine_1862_, lean_object* v_a_1863_, uint8_t v_requiresData_1864_, lean_object* v_expectData_1865_, lean_object* v_pendingHead_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_pendingHead_1866_);
lean_dec(v_expectData_1865_);
lean_dec_ref(v_a_1863_);
lean_dec_ref(v_machine_1862_);
v_a_1869_ = lean_ctor_get(v_x_1867_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1871_ = v_x_1867_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v_x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1892_; 
v_a_1878_ = lean_ctor_get(v_x_1867_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1880_ = v_x_1867_;
v_isShared_1881_ = v_isSharedCheck_1892_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v_x_1867_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1892_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_keepAliveTimeout_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v_keepAliveTimeout_1882_ = lean_ctor_get(v_config_1861_, 5);
lean_inc_n(v_keepAliveTimeout_1882_, 2);
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_keepAliveTimeout_1882_);
v___x_1884_ = lean_box(0);
v___x_1885_ = 0;
v___x_1886_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1886_, 0, v_machine_1862_);
lean_ctor_set(v___x_1886_, 1, v_a_1863_);
lean_ctor_set(v___x_1886_, 2, v___x_1883_);
lean_ctor_set(v___x_1886_, 3, v_keepAliveTimeout_1882_);
lean_ctor_set(v___x_1886_, 4, v___x_1884_);
lean_ctor_set(v___x_1886_, 5, v_a_1878_);
lean_ctor_set(v___x_1886_, 6, v___x_1884_);
lean_ctor_set(v___x_1886_, 7, v_expectData_1865_);
lean_ctor_set(v___x_1886_, 8, v_pendingHead_1866_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*9, v_requiresData_1864_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*9 + 1, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1887_);
v___x_1889_ = v___x_1880_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1893_, lean_object* v_machine_1894_, lean_object* v_a_1895_, lean_object* v_requiresData_1896_, lean_object* v_expectData_1897_, lean_object* v_pendingHead_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v_requiresData_boxed_1901_; lean_object* v_res_1902_; 
v_requiresData_boxed_1901_ = lean_unbox(v_requiresData_1896_);
v_res_1902_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1893_, v_machine_1894_, v_a_1895_, v_requiresData_boxed_1901_, v_expectData_1897_, v_pendingHead_1898_, v_x_1899_);
lean_dec_ref(v_config_1893_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1903_, lean_object* v_machine_1904_, uint8_t v_requiresData_1905_, lean_object* v_expectData_1906_, lean_object* v_pendingHead_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_pendingHead_1907_);
lean_dec(v_expectData_1906_);
lean_dec_ref(v_machine_1904_);
lean_dec_ref(v_config_1903_);
v_a_1910_ = lean_ctor_get(v_x_1908_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1912_ = v_x_1908_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v_x_1908_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1934_; 
v_a_1919_ = lean_ctor_get(v_x_1908_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1921_ = v_x_1908_;
v_isShared_1922_ = v_isSharedCheck_1934_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v_x_1908_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1934_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___x_1928_; 
v___x_1923_ = lean_box(0);
v___x_1924_ = l_Std_CloseableChannel_new___redArg(v___x_1923_);
v___x_1925_ = lean_box(v_requiresData_1905_);
v___f_1926_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1926_, 0, v_config_1903_);
lean_closure_set(v___f_1926_, 1, v_machine_1904_);
lean_closure_set(v___f_1926_, 2, v_a_1919_);
lean_closure_set(v___f_1926_, 3, v___x_1925_);
lean_closure_set(v___f_1926_, 4, v_expectData_1906_);
lean_closure_set(v___f_1926_, 5, v_pendingHead_1907_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1924_);
v___x_1928_ = v___x_1921_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1924_);
v___x_1928_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = 0;
v___x_1932_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1930_, v___x_1931_, v___x_1929_, v___f_1926_);
return v___x_1932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1935_, lean_object* v_machine_1936_, lean_object* v_requiresData_1937_, lean_object* v_expectData_1938_, lean_object* v_pendingHead_1939_, lean_object* v_x_1940_, lean_object* v___y_1941_){
_start:
{
uint8_t v_requiresData_boxed_1942_; lean_object* v_res_1943_; 
v_requiresData_boxed_1942_ = lean_unbox(v_requiresData_1937_);
v_res_1943_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1935_, v_machine_1936_, v_requiresData_boxed_1942_, v_expectData_1938_, v_pendingHead_1939_, v_x_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1944_, lean_object* v_____r_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1947_ = l_Std_Http_Body_mkStream();
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = 0;
v___x_1950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1948_, v___x_1949_, v___x_1947_, v___f_1944_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1951_, lean_object* v_____r_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1951_, v_____r_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1955_, lean_object* v_val_1956_, lean_object* v___f_1957_, lean_object* v___f_1958_, lean_object* v_x_1959_){
_start:
{
if (lean_obj_tag(v_x_1959_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v___f_1958_);
lean_dec_ref(v___f_1957_);
lean_dec(v_val_1956_);
lean_dec_ref(v_close_1955_);
v_a_1961_ = lean_ctor_get(v_x_1959_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_x_1959_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1963_ = v_x_1959_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v_x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1970_; uint8_t v___x_1971_; 
v_a_1970_ = lean_ctor_get(v_x_1959_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v_x_1959_, 1);
v___x_1971_ = lean_unbox(v_a_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; 
lean_dec_ref(v___f_1958_);
v___x_1972_ = lean_apply_2(v_close_1955_, v_val_1956_, lean_box(0));
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_unbox(v_a_1970_);
lean_dec(v_a_1970_);
v___x_1975_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1973_, v___x_1974_, v___x_1972_, v___f_1957_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec(v_a_1970_);
lean_dec_ref(v___f_1957_);
lean_dec(v_val_1956_);
lean_dec_ref(v_close_1955_);
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_apply_2(v___f_1958_, v___x_1976_, lean_box(0));
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1978_, lean_object* v_val_1979_, lean_object* v___f_1980_, lean_object* v___f_1981_, lean_object* v_x_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1978_, v_val_1979_, v___f_1980_, v___f_1981_, v_x_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1985_, lean_object* v_inst_1986_, lean_object* v___f_1987_, lean_object* v___f_1988_, lean_object* v_____r_1989_){
_start:
{
if (lean_obj_tag(v_respStream_1985_) == 1)
{
lean_object* v_val_1991_; lean_object* v_close_1992_; lean_object* v_isClosed_1993_; lean_object* v___x_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; 
v_val_1991_ = lean_ctor_get(v_respStream_1985_, 0);
lean_inc_n(v_val_1991_, 2);
lean_dec_ref_known(v_respStream_1985_, 1);
v_close_1992_ = lean_ctor_get(v_inst_1986_, 1);
lean_inc_ref(v_close_1992_);
v_isClosed_1993_ = lean_ctor_get(v_inst_1986_, 2);
lean_inc_ref(v_isClosed_1993_);
lean_dec_ref(v_inst_1986_);
v___x_1994_ = lean_apply_2(v_isClosed_1993_, v_val_1991_, lean_box(0));
v___f_1995_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1995_, 0, v_close_1992_);
lean_closure_set(v___f_1995_, 1, v_val_1991_);
lean_closure_set(v___f_1995_, 2, v___f_1987_);
lean_closure_set(v___f_1995_, 3, v___f_1988_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = 0;
v___x_1998_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1996_, v___x_1997_, v___x_1994_, v___f_1995_);
return v___x_1998_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec_ref(v___f_1987_);
lean_dec_ref(v_inst_1986_);
lean_dec(v_respStream_1985_);
v___x_1999_ = lean_box(0);
v___x_2000_ = lean_apply_2(v___f_1988_, v___x_1999_, lean_box(0));
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_2001_, lean_object* v_inst_2002_, lean_object* v___f_2003_, lean_object* v___f_2004_, lean_object* v_____r_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_2001_, v_inst_2002_, v___f_2003_, v___f_2004_, v_____r_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2008_, lean_object* v_keepAliveTimeout_2009_, lean_object* v_currentTimeout_2010_, lean_object* v_headerTimeout_2011_, lean_object* v_response_2012_, lean_object* v_respStream_2013_, uint8_t v_requiresData_2014_, lean_object* v_expectData_2015_, uint8_t v_handlerDispatched_2016_, lean_object* v_pendingHead_2017_, lean_object* v_x_2018_){
_start:
{
if (lean_obj_tag(v_x_2018_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_pendingHead_2017_);
lean_dec(v_expectData_2015_);
lean_dec(v_respStream_2013_);
lean_dec_ref(v_response_2012_);
lean_dec(v_headerTimeout_2011_);
lean_dec(v_currentTimeout_2010_);
lean_dec(v_keepAliveTimeout_2009_);
lean_dec_ref(v_requestStream_2008_);
v_a_2020_ = lean_ctor_get(v_x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2022_ = v_x_2018_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v_x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2050_; 
v_a_2029_ = lean_ctor_get(v_x_2018_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_x_2018_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2031_ = v_x_2018_;
v_isShared_2032_ = v_isSharedCheck_2050_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v_x_2018_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2050_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_snd_2033_; uint8_t v___x_2034_; 
v_snd_2033_ = lean_ctor_get(v_a_2029_, 1);
v___x_2034_ = lean_unbox(v_snd_2033_);
if (v___x_2034_ == 0)
{
lean_object* v_fst_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v_fst_2035_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_fst_2035_);
lean_dec(v_a_2029_);
v___x_2036_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2036_, 0, v_fst_2035_);
lean_ctor_set(v___x_2036_, 1, v_requestStream_2008_);
lean_ctor_set(v___x_2036_, 2, v_keepAliveTimeout_2009_);
lean_ctor_set(v___x_2036_, 3, v_currentTimeout_2010_);
lean_ctor_set(v___x_2036_, 4, v_headerTimeout_2011_);
lean_ctor_set(v___x_2036_, 5, v_response_2012_);
lean_ctor_set(v___x_2036_, 6, v_respStream_2013_);
lean_ctor_set(v___x_2036_, 7, v_expectData_2015_);
lean_ctor_set(v___x_2036_, 8, v_pendingHead_2017_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*9, v_requiresData_2014_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*9 + 1, v_handlerDispatched_2016_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2037_);
v___x_2039_ = v___x_2031_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
else
{
lean_object* v_fst_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_pendingHead_2017_);
v_fst_2042_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_fst_2042_);
lean_dec(v_a_2029_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2044_, 0, v_fst_2042_);
lean_ctor_set(v___x_2044_, 1, v_requestStream_2008_);
lean_ctor_set(v___x_2044_, 2, v_keepAliveTimeout_2009_);
lean_ctor_set(v___x_2044_, 3, v_currentTimeout_2010_);
lean_ctor_set(v___x_2044_, 4, v_headerTimeout_2011_);
lean_ctor_set(v___x_2044_, 5, v_response_2012_);
lean_ctor_set(v___x_2044_, 6, v_respStream_2013_);
lean_ctor_set(v___x_2044_, 7, v_expectData_2015_);
lean_ctor_set(v___x_2044_, 8, v___x_2043_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*9, v_requiresData_2014_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*9 + 1, v_handlerDispatched_2016_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2045_);
v___x_2047_ = v___x_2031_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2051_, lean_object* v_keepAliveTimeout_2052_, lean_object* v_currentTimeout_2053_, lean_object* v_headerTimeout_2054_, lean_object* v_response_2055_, lean_object* v_respStream_2056_, lean_object* v_requiresData_2057_, lean_object* v_expectData_2058_, lean_object* v_handlerDispatched_2059_, lean_object* v_pendingHead_2060_, lean_object* v_x_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v_requiresData_boxed_2063_; uint8_t v_handlerDispatched_boxed_2064_; lean_object* v_res_2065_; 
v_requiresData_boxed_2063_ = lean_unbox(v_requiresData_2057_);
v_handlerDispatched_boxed_2064_ = lean_unbox(v_handlerDispatched_2059_);
v_res_2065_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2051_, v_keepAliveTimeout_2052_, v_currentTimeout_2053_, v_headerTimeout_2054_, v_response_2055_, v_respStream_2056_, v_requiresData_boxed_2063_, v_expectData_2058_, v_handlerDispatched_boxed_2064_, v_pendingHead_2060_, v_x_2061_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2078_, lean_object* v_inst_2079_, lean_object* v___f_2080_, lean_object* v_handler_2081_, lean_object* v___f_2082_, lean_object* v___f_2083_, lean_object* v_inst_2084_, lean_object* v_connectionContext_2085_, lean_object* v_a_2086_, lean_object* v_x_2087_, lean_object* v___y_2088_){
_start:
{
switch(lean_obj_tag(v_a_2086_))
{
case 0:
{
lean_object* v_head_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_connectionContext_2085_);
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v___f_2082_);
lean_dec(v_handler_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v_inst_2079_);
v_head_2090_ = lean_ctor_get(v_a_2086_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2086_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2092_ = v_a_2086_;
v_isShared_2093_ = v_isSharedCheck_2133_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_head_2090_);
lean_dec(v_a_2086_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2133_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_machine_2094_; lean_object* v_requestStream_2095_; lean_object* v_response_2096_; lean_object* v_respStream_2097_; uint8_t v_requiresData_2098_; lean_object* v_expectData_2099_; uint8_t v_handlerDispatched_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2128_; 
v_machine_2094_ = lean_ctor_get(v___y_2088_, 0);
v_requestStream_2095_ = lean_ctor_get(v___y_2088_, 1);
v_response_2096_ = lean_ctor_get(v___y_2088_, 5);
v_respStream_2097_ = lean_ctor_get(v___y_2088_, 6);
v_requiresData_2098_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*9);
v_expectData_2099_ = lean_ctor_get(v___y_2088_, 7);
v_handlerDispatched_2100_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*9 + 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___y_2088_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2129_ = lean_ctor_get(v___y_2088_, 8);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v___y_2088_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v___y_2088_, 3);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v___y_2088_, 2);
lean_dec(v_unused_2132_);
v___x_2102_ = v___y_2088_;
v_isShared_2103_ = v_isSharedCheck_2128_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_expectData_2099_);
lean_inc(v_respStream_2097_);
lean_inc(v_response_2096_);
lean_inc(v_requestStream_2095_);
lean_inc(v_machine_2094_);
lean_dec(v___y_2088_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2128_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_lingeringTimeout_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v_lingeringTimeout_2104_ = lean_ctor_get(v_config_2078_, 4);
lean_inc(v_lingeringTimeout_2104_);
lean_dec_ref(v_config_2078_);
v___x_2105_ = lean_box(0);
lean_inc(v_head_2090_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
v___x_2107_ = v___x_2092_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_head_2090_);
v___x_2107_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
lean_inc_ref(v_requestStream_2095_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 8, v___x_2107_);
lean_ctor_set(v___x_2102_, 4, v___x_2105_);
lean_ctor_set(v___x_2102_, 3, v_lingeringTimeout_2104_);
lean_ctor_set(v___x_2102_, 2, v___x_2105_);
v___x_2109_ = v___x_2102_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_machine_2094_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_requestStream_2095_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_lingeringTimeout_2104_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2126_, 5, v_response_2096_);
lean_ctor_set(v_reuseFailAlloc_2126_, 6, v_respStream_2097_);
lean_ctor_set(v_reuseFailAlloc_2126_, 7, v_expectData_2099_);
lean_ctor_set(v_reuseFailAlloc_2126_, 8, v___x_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2126_, sizeof(void*)*9, v_requiresData_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2126_, sizeof(void*)*9 + 1, v_handlerDispatched_2100_);
v___x_2109_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
uint8_t v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = 0;
v___x_2111_ = 1;
v___x_2112_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2110_, v_head_2090_, v___x_2111_);
lean_dec(v_head_2090_);
if (lean_obj_tag(v___x_2112_) == 1)
{
lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___f_2116_; lean_object* v___x_5121__overap_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; 
v___f_2113_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2113_, 0, v___x_2112_);
v___x_2114_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2115_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2116_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5121__overap_2117_ = l_Std_Mutex_atomically___redArg(v___x_2114_, v___f_2115_, v___f_2116_, v_requestStream_2095_, v___f_2113_);
v___x_2118_ = lean_apply_1(v___x_5121__overap_2117_, lean_box(0));
v___f_2119_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2119_, 0, v___x_2109_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = 0;
v___x_2122_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2120_, v___x_2121_, v___x_2118_, v___f_2119_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v___x_2112_);
lean_dec_ref(v_requestStream_2095_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2109_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_connectionContext_2085_);
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v___f_2082_);
lean_dec(v_handler_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v_inst_2079_);
lean_dec_ref(v_config_2078_);
v_size_2134_ = lean_ctor_get(v_a_2086_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2086_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2136_ = v_a_2086_;
v_isShared_2137_ = v_isSharedCheck_2161_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_size_2134_);
lean_dec(v_a_2086_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2161_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_machine_2138_; lean_object* v_requestStream_2139_; lean_object* v_keepAliveTimeout_2140_; lean_object* v_currentTimeout_2141_; lean_object* v_headerTimeout_2142_; lean_object* v_response_2143_; lean_object* v_respStream_2144_; uint8_t v_handlerDispatched_2145_; lean_object* v_pendingHead_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2159_; 
v_machine_2138_ = lean_ctor_get(v___y_2088_, 0);
v_requestStream_2139_ = lean_ctor_get(v___y_2088_, 1);
v_keepAliveTimeout_2140_ = lean_ctor_get(v___y_2088_, 2);
v_currentTimeout_2141_ = lean_ctor_get(v___y_2088_, 3);
v_headerTimeout_2142_ = lean_ctor_get(v___y_2088_, 4);
v_response_2143_ = lean_ctor_get(v___y_2088_, 5);
v_respStream_2144_ = lean_ctor_get(v___y_2088_, 6);
v_handlerDispatched_2145_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*9 + 1);
v_pendingHead_2146_ = lean_ctor_get(v___y_2088_, 8);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___y_2088_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v___y_2088_, 7);
lean_dec(v_unused_2160_);
v___x_2148_ = v___y_2088_;
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_pendingHead_2146_);
lean_inc(v_respStream_2144_);
lean_inc(v_response_2143_);
lean_inc(v_headerTimeout_2142_);
lean_inc(v_currentTimeout_2141_);
lean_inc(v_keepAliveTimeout_2140_);
lean_inc(v_requestStream_2139_);
lean_inc(v_machine_2138_);
lean_dec(v___y_2088_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
uint8_t v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = 1;
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 7, v_size_2134_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_machine_2138_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_requestStream_2139_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_keepAliveTimeout_2140_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_currentTimeout_2141_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_headerTimeout_2142_);
lean_ctor_set(v_reuseFailAlloc_2158_, 5, v_response_2143_);
lean_ctor_set(v_reuseFailAlloc_2158_, 6, v_respStream_2144_);
lean_ctor_set(v_reuseFailAlloc_2158_, 7, v_size_2134_);
lean_ctor_set(v_reuseFailAlloc_2158_, 8, v_pendingHead_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*9 + 1, v_handlerDispatched_2145_);
v___x_2152_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*9, v___x_2150_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2152_);
v___x_2154_ = v___x_2136_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2162_; lean_object* v_onFailure_2163_; lean_object* v___f_2164_; lean_object* v___y_2166_; 
lean_dec_ref(v_connectionContext_2085_);
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v_config_2078_);
v_err_2162_ = lean_ctor_get(v_a_2086_, 0);
lean_inc(v_err_2162_);
lean_dec_ref_known(v_a_2086_, 1);
v_onFailure_2163_ = lean_ctor_get(v_inst_2079_, 2);
lean_inc_ref(v_onFailure_2163_);
lean_dec_ref(v_inst_2079_);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2164_, 0, v___y_2088_);
lean_closure_set(v___f_2164_, 1, v___f_2080_);
switch(lean_obj_tag(v_err_2162_))
{
case 0:
{
lean_object* v___x_2172_; 
v___x_2172_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2166_ = v___x_2172_;
goto v___jp_2165_;
}
case 1:
{
lean_object* v___x_2173_; 
v___x_2173_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2166_ = v___x_2173_;
goto v___jp_2165_;
}
case 2:
{
lean_object* v___x_2174_; 
v___x_2174_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2166_ = v___x_2174_;
goto v___jp_2165_;
}
case 3:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2166_ = v___x_2175_;
goto v___jp_2165_;
}
case 4:
{
lean_object* v___x_2176_; 
v___x_2176_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2166_ = v___x_2176_;
goto v___jp_2165_;
}
case 5:
{
lean_object* v___x_2177_; 
v___x_2177_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2166_ = v___x_2177_;
goto v___jp_2165_;
}
case 6:
{
lean_object* v___x_2178_; 
v___x_2178_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2166_ = v___x_2178_;
goto v___jp_2165_;
}
case 7:
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2166_ = v___x_2179_;
goto v___jp_2165_;
}
case 8:
{
lean_object* v___x_2180_; 
v___x_2180_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2166_ = v___x_2180_;
goto v___jp_2165_;
}
case 9:
{
lean_object* v___x_2181_; 
v___x_2181_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2166_ = v___x_2181_;
goto v___jp_2165_;
}
case 10:
{
lean_object* v___x_2182_; 
v___x_2182_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2166_ = v___x_2182_;
goto v___jp_2165_;
}
default: 
{
lean_object* v_message_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_message_2183_ = lean_ctor_get(v_err_2162_, 0);
lean_inc_ref(v_message_2183_);
lean_dec_ref_known(v_err_2162_, 1);
v___x_2184_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2185_ = lean_string_append(v___x_2184_, v_message_2183_);
lean_dec_ref(v_message_2183_);
v___y_2166_ = v___x_2185_;
goto v___jp_2165_;
}
}
v___jp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2167_ = lean_mk_io_user_error(v___y_2166_);
v___x_2168_ = lean_apply_3(v_onFailure_2163_, v_handler_2081_, v___x_2167_, lean_box(0));
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = 0;
v___x_2171_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2169_, v___x_2170_, v___x_2168_, v___f_2164_);
return v___x_2171_;
}
}
case 4:
{
lean_object* v_requestStream_2186_; lean_object* v___x_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_5177__overap_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_connectionContext_2085_);
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v___f_2083_);
lean_dec(v_handler_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v_inst_2079_);
lean_dec_ref(v_config_2078_);
v_requestStream_2186_ = lean_ctor_get(v___y_2088_, 1);
lean_inc_ref_n(v_requestStream_2186_, 2);
v___x_2187_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2188_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2189_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2190_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2191_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2191_, 0, lean_box(0));
lean_closure_set(v___x_2191_, 1, lean_box(0));
lean_closure_set(v___x_2191_, 2, lean_box(0));
lean_closure_set(v___x_2191_, 3, v___x_2187_);
lean_closure_set(v___x_2191_, 4, lean_box(0));
lean_closure_set(v___x_2191_, 5, lean_box(0));
lean_closure_set(v___x_2191_, 6, v___x_2190_);
lean_closure_set(v___x_2191_, 7, v___f_2082_);
v___x_5177__overap_2192_ = l_Std_Mutex_atomically___redArg(v___x_2187_, v___f_2188_, v___f_2189_, v_requestStream_2186_, v___x_2191_);
v___x_2193_ = lean_apply_1(v___x_5177__overap_2192_, lean_box(0));
lean_inc_ref(v___y_2088_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2194_, 0, v___y_2088_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2195_, 0, v_requestStream_2186_);
lean_closure_set(v___f_2195_, 1, v___f_2194_);
lean_closure_set(v___f_2195_, 2, v___y_2088_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = 0;
v___x_2198_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2196_, v___x_2197_, v___x_2193_, v___f_2195_);
return v___x_2198_;
}
case 6:
{
lean_object* v_machine_2199_; lean_object* v_requestStream_2200_; lean_object* v_respStream_2201_; uint8_t v_requiresData_2202_; lean_object* v_expectData_2203_; lean_object* v_pendingHead_2204_; lean_object* v___x_2205_; lean_object* v___f_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_5198__overap_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v_connectionContext_2085_);
lean_dec_ref(v___f_2082_);
lean_dec(v_handler_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v_inst_2079_);
v_machine_2199_ = lean_ctor_get(v___y_2088_, 0);
lean_inc_ref(v_machine_2199_);
v_requestStream_2200_ = lean_ctor_get(v___y_2088_, 1);
lean_inc_ref_n(v_requestStream_2200_, 2);
v_respStream_2201_ = lean_ctor_get(v___y_2088_, 6);
lean_inc(v_respStream_2201_);
v_requiresData_2202_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*9);
v_expectData_2203_ = lean_ctor_get(v___y_2088_, 7);
lean_inc(v_expectData_2203_);
v_pendingHead_2204_ = lean_ctor_get(v___y_2088_, 8);
lean_inc(v_pendingHead_2204_);
lean_dec_ref(v___y_2088_);
v___x_2205_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2206_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2207_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2208_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2209_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2209_, 0, lean_box(0));
lean_closure_set(v___x_2209_, 1, lean_box(0));
lean_closure_set(v___x_2209_, 2, lean_box(0));
lean_closure_set(v___x_2209_, 3, v___x_2205_);
lean_closure_set(v___x_2209_, 4, lean_box(0));
lean_closure_set(v___x_2209_, 5, lean_box(0));
lean_closure_set(v___x_2209_, 6, v___x_2208_);
lean_closure_set(v___x_2209_, 7, v___f_2083_);
v___x_5198__overap_2210_ = l_Std_Mutex_atomically___redArg(v___x_2205_, v___f_2206_, v___f_2207_, v_requestStream_2200_, v___x_2209_);
v___x_2211_ = lean_apply_1(v___x_5198__overap_2210_, lean_box(0));
v___x_2212_ = lean_box(v_requiresData_2202_);
v___f_2213_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2213_, 0, v_config_2078_);
lean_closure_set(v___f_2213_, 1, v_machine_2199_);
lean_closure_set(v___f_2213_, 2, v___x_2212_);
lean_closure_set(v___f_2213_, 3, v_expectData_2203_);
lean_closure_set(v___f_2213_, 4, v_pendingHead_2204_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2214_, 0, v___f_2213_);
lean_inc_ref(v___f_2214_);
v___f_2215_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2215_, 0, v___f_2214_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2216_, 0, v_respStream_2201_);
lean_closure_set(v___f_2216_, 1, v_inst_2084_);
lean_closure_set(v___f_2216_, 2, v___f_2215_);
lean_closure_set(v___f_2216_, 3, v___f_2214_);
lean_inc_ref(v___f_2216_);
v___f_2217_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2217_, 0, v___f_2216_);
v___f_2218_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2218_, 0, v_requestStream_2200_);
lean_closure_set(v___f_2218_, 1, v___f_2217_);
lean_closure_set(v___f_2218_, 2, v___f_2216_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = 0;
v___x_2221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2219_, v___x_2220_, v___x_2211_, v___f_2218_);
return v___x_2221_;
}
case 7:
{
lean_object* v_pendingHead_2222_; 
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v___f_2080_);
v_pendingHead_2222_ = lean_ctor_get(v___y_2088_, 8);
if (lean_obj_tag(v_pendingHead_2222_) == 1)
{
lean_object* v_machine_2223_; lean_object* v_requestStream_2224_; lean_object* v_keepAliveTimeout_2225_; lean_object* v_currentTimeout_2226_; lean_object* v_headerTimeout_2227_; lean_object* v_response_2228_; lean_object* v_respStream_2229_; uint8_t v_requiresData_2230_; lean_object* v_expectData_2231_; uint8_t v_handlerDispatched_2232_; lean_object* v_val_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
lean_inc_ref(v_pendingHead_2222_);
v_machine_2223_ = lean_ctor_get(v___y_2088_, 0);
lean_inc_ref(v_machine_2223_);
v_requestStream_2224_ = lean_ctor_get(v___y_2088_, 1);
lean_inc_ref(v_requestStream_2224_);
v_keepAliveTimeout_2225_ = lean_ctor_get(v___y_2088_, 2);
lean_inc(v_keepAliveTimeout_2225_);
v_currentTimeout_2226_ = lean_ctor_get(v___y_2088_, 3);
lean_inc(v_currentTimeout_2226_);
v_headerTimeout_2227_ = lean_ctor_get(v___y_2088_, 4);
lean_inc(v_headerTimeout_2227_);
v_response_2228_ = lean_ctor_get(v___y_2088_, 5);
lean_inc_ref(v_response_2228_);
v_respStream_2229_ = lean_ctor_get(v___y_2088_, 6);
lean_inc(v_respStream_2229_);
v_requiresData_2230_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*9);
v_expectData_2231_ = lean_ctor_get(v___y_2088_, 7);
lean_inc(v_expectData_2231_);
v_handlerDispatched_2232_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2088_);
v_val_2233_ = lean_ctor_get(v_pendingHead_2222_, 0);
lean_inc(v_val_2233_);
v___x_2234_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2079_, v_handler_2081_, v_machine_2223_, v_val_2233_, v_config_2078_, v_connectionContext_2085_);
v___x_2235_ = lean_box(v_requiresData_2230_);
v___x_2236_ = lean_box(v_handlerDispatched_2232_);
v___f_2237_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2237_, 0, v_requestStream_2224_);
lean_closure_set(v___f_2237_, 1, v_keepAliveTimeout_2225_);
lean_closure_set(v___f_2237_, 2, v_currentTimeout_2226_);
lean_closure_set(v___f_2237_, 3, v_headerTimeout_2227_);
lean_closure_set(v___f_2237_, 4, v_response_2228_);
lean_closure_set(v___f_2237_, 5, v_respStream_2229_);
lean_closure_set(v___f_2237_, 6, v___x_2235_);
lean_closure_set(v___f_2237_, 7, v_expectData_2231_);
lean_closure_set(v___f_2237_, 8, v___x_2236_);
lean_closure_set(v___f_2237_, 9, v_pendingHead_2222_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = 0;
v___x_2240_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2238_, v___x_2239_, v___x_2234_, v___f_2237_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec_ref(v_connectionContext_2085_);
lean_dec(v_handler_2081_);
lean_dec_ref(v_inst_2079_);
lean_dec_ref(v_config_2078_);
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___y_2088_);
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
}
default: 
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v_a_2086_);
lean_dec_ref(v_connectionContext_2085_);
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v___f_2082_);
lean_dec(v_handler_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v_inst_2079_);
lean_dec_ref(v_config_2078_);
v___x_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___y_2088_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2247_, lean_object* v_inst_2248_, lean_object* v___f_2249_, lean_object* v_handler_2250_, lean_object* v___f_2251_, lean_object* v___f_2252_, lean_object* v_inst_2253_, lean_object* v_connectionContext_2254_, lean_object* v_a_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2247_, v_inst_2248_, v___f_2249_, v_handler_2250_, v___f_2251_, v___f_2252_, v_inst_2253_, v_connectionContext_2254_, v_a_2255_, v_x_2256_, v___y_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v_x_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_handler_2270_, lean_object* v_config_2271_, lean_object* v_connectionContext_2272_, lean_object* v_events_2273_, lean_object* v_state_2274_){
_start:
{
lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; size_t v_sz_2279_; size_t v___x_2280_; lean_object* v___x_4110__overap_2281_; lean_object* v___x_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; 
v___f_2276_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2277_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2277_, 0, v_config_2271_);
lean_closure_set(v___f_2277_, 1, v_inst_2268_);
lean_closure_set(v___f_2277_, 2, v___f_2276_);
lean_closure_set(v___f_2277_, 3, v_handler_2270_);
lean_closure_set(v___f_2277_, 4, v___f_2276_);
lean_closure_set(v___f_2277_, 5, v___f_2276_);
lean_closure_set(v___f_2277_, 6, v_inst_2269_);
lean_closure_set(v___f_2277_, 7, v_connectionContext_2272_);
v___x_2278_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2279_ = lean_array_size(v_events_2273_);
v___x_2280_ = ((size_t)0ULL);
v___x_4110__overap_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2278_, v_events_2273_, v___f_2277_, v_sz_2279_, v___x_2280_, v_state_2274_);
v___x_2282_ = lean_apply_1(v___x_4110__overap_2281_, lean_box(0));
v___f_2283_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = 0;
v___x_2286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2284_, v___x_2285_, v___x_2282_, v___f_2283_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_handler_2289_, lean_object* v_config_2290_, lean_object* v_connectionContext_2291_, lean_object* v_events_2292_, lean_object* v_state_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2287_, v_inst_2288_, v_handler_2289_, v_config_2290_, v_connectionContext_2291_, v_events_2292_, v_state_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_handler_2300_, lean_object* v_config_2301_, lean_object* v_connectionContext_2302_, lean_object* v_events_2303_, lean_object* v_state_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2298_, v_inst_2299_, v_handler_2300_, v_config_2301_, v_connectionContext_2302_, v_events_2303_, v_state_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2307_, lean_object* v_00_u03b2_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_handler_2311_, lean_object* v_config_2312_, lean_object* v_connectionContext_2313_, lean_object* v_events_2314_, lean_object* v_state_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2307_, v_00_u03b2_2308_, v_inst_2309_, v_inst_2310_, v_handler_2311_, v_config_2312_, v_connectionContext_2313_, v_events_2314_, v_state_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2318_){
_start:
{
if (lean_obj_tag(v_x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v_x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v_x_2318_, 1);
v___x_2320_ = lean_task_pure(v_a_2319_);
return v___x_2320_;
}
else
{
lean_object* v_a_2321_; 
v_a_2321_ = lean_ctor_get(v_x_2318_, 0);
lean_inc_ref(v_a_2321_);
lean_dec_ref_known(v_x_2318_, 1);
return v_a_2321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2322_, lean_object* v_requestStream_2323_, lean_object* v_keepAliveTimeout_2324_, lean_object* v_currentTimeout_2325_, lean_object* v_headerTimeout_2326_, lean_object* v_response_2327_, lean_object* v_respStream_2328_, uint8_t v_requiresData_2329_, lean_object* v_expectData_2330_, lean_object* v_x_2331_){
_start:
{
if (lean_obj_tag(v_x_2331_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_expectData_2330_);
lean_dec(v_respStream_2328_);
lean_dec_ref(v_response_2327_);
lean_dec(v_headerTimeout_2326_);
lean_dec(v_currentTimeout_2325_);
lean_dec(v_keepAliveTimeout_2324_);
lean_dec_ref(v_requestStream_2323_);
lean_dec_ref(v_machine_2322_);
v_a_2333_ = lean_ctor_get(v_x_2331_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_x_2331_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2335_ = v_x_2331_;
v_isShared_2336_ = v_isSharedCheck_2341_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v_x_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2341_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
}
}
else
{
lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2352_; 
v_isSharedCheck_2352_ = !lean_is_exclusive(v_x_2331_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_x_2331_, 0);
lean_dec(v_unused_2353_);
v___x_2343_ = v_x_2331_;
v_isShared_2344_ = v_isSharedCheck_2352_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v_x_2331_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2352_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2345_ = 1;
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2347_, 0, v_machine_2322_);
lean_ctor_set(v___x_2347_, 1, v_requestStream_2323_);
lean_ctor_set(v___x_2347_, 2, v_keepAliveTimeout_2324_);
lean_ctor_set(v___x_2347_, 3, v_currentTimeout_2325_);
lean_ctor_set(v___x_2347_, 4, v_headerTimeout_2326_);
lean_ctor_set(v___x_2347_, 5, v_response_2327_);
lean_ctor_set(v___x_2347_, 6, v_respStream_2328_);
lean_ctor_set(v___x_2347_, 7, v_expectData_2330_);
lean_ctor_set(v___x_2347_, 8, v___x_2346_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*9, v_requiresData_2329_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*9 + 1, v___x_2345_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2347_);
v___x_2349_ = v___x_2343_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2354_, lean_object* v_requestStream_2355_, lean_object* v_keepAliveTimeout_2356_, lean_object* v_currentTimeout_2357_, lean_object* v_headerTimeout_2358_, lean_object* v_response_2359_, lean_object* v_respStream_2360_, lean_object* v_requiresData_2361_, lean_object* v_expectData_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v_requiresData_boxed_2365_; lean_object* v_res_2366_; 
v_requiresData_boxed_2365_ = lean_unbox(v_requiresData_2361_);
v_res_2366_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2354_, v_requestStream_2355_, v_keepAliveTimeout_2356_, v_currentTimeout_2357_, v_headerTimeout_2358_, v_response_2359_, v_respStream_2360_, v_requiresData_boxed_2365_, v_expectData_2362_, v_x_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2367_, lean_object* v_response_2368_, lean_object* v___x_2369_, lean_object* v___f_2370_, lean_object* v_x_2371_){
_start:
{
if (lean_obj_tag(v_x_2371_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v___f_2370_);
lean_dec(v___x_2369_);
lean_dec_ref(v_response_2368_);
lean_dec_ref(v_toFunctor_2367_);
v_a_2373_ = lean_ctor_get(v_x_2371_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_x_2371_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2375_ = v_x_2371_;
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v_x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2396_; 
v_a_2382_ = lean_ctor_get(v_x_2371_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_x_2371_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2384_ = v_x_2371_;
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v_x_2371_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2386_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2386_, 0, lean_box(0));
lean_closure_set(v___x_2386_, 1, lean_box(0));
lean_closure_set(v___x_2386_, 2, v_toFunctor_2367_);
v___x_2387_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2387_, 0, lean_box(0));
lean_closure_set(v___x_2387_, 1, v_response_2368_);
v___x_2388_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2388_, 0, lean_box(0));
lean_closure_set(v___x_2388_, 1, lean_box(0));
lean_closure_set(v___x_2388_, 2, lean_box(0));
lean_closure_set(v___x_2388_, 3, v___x_2386_);
lean_closure_set(v___x_2388_, 4, v___x_2387_);
v___x_2389_ = 0;
lean_inc(v___x_2369_);
v___x_2390_ = l_BaseIO_chainTask___redArg(v_a_2382_, v___x_2388_, v___x_2369_, v___x_2389_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2390_);
v___x_2392_ = v___x_2384_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
v___x_2394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2369_, v___x_2389_, v___x_2393_, v___f_2370_);
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2397_, lean_object* v_response_2398_, lean_object* v___x_2399_, lean_object* v___f_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2397_, v_response_2398_, v___x_2399_, v___f_2400_, v_x_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2405_, lean_object* v_handler_2406_, lean_object* v_extensions_2407_, lean_object* v_connectionContext_2408_, lean_object* v_state_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v_toApplicative_2412_; lean_object* v_pendingHead_2413_; 
v___x_2411_ = l_instMonadBaseIO;
v_toApplicative_2412_ = lean_ctor_get(v___x_2411_, 0);
v_pendingHead_2413_ = lean_ctor_get(v_state_2409_, 8);
lean_inc(v_pendingHead_2413_);
if (lean_obj_tag(v_pendingHead_2413_) == 1)
{
lean_object* v_toFunctor_2414_; lean_object* v_machine_2415_; lean_object* v_requestStream_2416_; lean_object* v_keepAliveTimeout_2417_; lean_object* v_currentTimeout_2418_; lean_object* v_headerTimeout_2419_; lean_object* v_response_2420_; lean_object* v_respStream_2421_; uint8_t v_requiresData_2422_; lean_object* v_expectData_2423_; lean_object* v_val_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2446_; 
v_toFunctor_2414_ = lean_ctor_get(v_toApplicative_2412_, 0);
v_machine_2415_ = lean_ctor_get(v_state_2409_, 0);
lean_inc_ref(v_machine_2415_);
v_requestStream_2416_ = lean_ctor_get(v_state_2409_, 1);
lean_inc_ref(v_requestStream_2416_);
v_keepAliveTimeout_2417_ = lean_ctor_get(v_state_2409_, 2);
lean_inc(v_keepAliveTimeout_2417_);
v_currentTimeout_2418_ = lean_ctor_get(v_state_2409_, 3);
lean_inc(v_currentTimeout_2418_);
v_headerTimeout_2419_ = lean_ctor_get(v_state_2409_, 4);
lean_inc(v_headerTimeout_2419_);
v_response_2420_ = lean_ctor_get(v_state_2409_, 5);
lean_inc_ref(v_response_2420_);
v_respStream_2421_ = lean_ctor_get(v_state_2409_, 6);
lean_inc(v_respStream_2421_);
v_requiresData_2422_ = lean_ctor_get_uint8(v_state_2409_, sizeof(void*)*9);
v_expectData_2423_ = lean_ctor_get(v_state_2409_, 7);
lean_inc(v_expectData_2423_);
lean_dec_ref(v_state_2409_);
v_val_2424_ = lean_ctor_get(v_pendingHead_2413_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_pendingHead_2413_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2426_ = v_pendingHead_2413_;
v_isShared_2427_ = v_isSharedCheck_2446_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_val_2424_);
lean_dec(v_pendingHead_2413_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2446_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_onRequest_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v___f_2436_; lean_object* v___f_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v_onRequest_2428_ = lean_ctor_get(v_inst_2405_, 1);
lean_inc_ref(v_onRequest_2428_);
lean_dec_ref(v_inst_2405_);
lean_inc_ref(v_requestStream_2416_);
v___x_2429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2429_, 0, v_val_2424_);
lean_ctor_set(v___x_2429_, 1, v_requestStream_2416_);
lean_ctor_set(v___x_2429_, 2, v_extensions_2407_);
v___x_2430_ = lean_apply_3(v_onRequest_2428_, v_handler_2406_, v___x_2429_, v_connectionContext_2408_);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2432_, 0, lean_box(0));
lean_closure_set(v___x_2432_, 1, v___x_2430_);
v___x_2433_ = lean_io_as_task(v___x_2432_, v___x_2431_);
v___f_2434_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2435_ = lean_box(v_requiresData_2422_);
lean_inc_ref(v_response_2420_);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2436_, 0, v_machine_2415_);
lean_closure_set(v___f_2436_, 1, v_requestStream_2416_);
lean_closure_set(v___f_2436_, 2, v_keepAliveTimeout_2417_);
lean_closure_set(v___f_2436_, 3, v_currentTimeout_2418_);
lean_closure_set(v___f_2436_, 4, v_headerTimeout_2419_);
lean_closure_set(v___f_2436_, 5, v_response_2420_);
lean_closure_set(v___f_2436_, 6, v_respStream_2421_);
lean_closure_set(v___f_2436_, 7, v___x_2435_);
lean_closure_set(v___f_2436_, 8, v_expectData_2423_);
lean_inc_ref(v_toFunctor_2414_);
v___f_2437_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2437_, 0, v_toFunctor_2414_);
lean_closure_set(v___f_2437_, 1, v_response_2420_);
lean_closure_set(v___f_2437_, 2, v___x_2431_);
lean_closure_set(v___f_2437_, 3, v___f_2436_);
v___x_2438_ = 1;
v___x_2439_ = lean_task_bind(v___x_2433_, v___f_2434_, v___x_2431_, v___x_2438_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2439_);
v___x_2441_ = v___x_2426_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
v___x_2443_ = 0;
v___x_2444_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2431_, v___x_2443_, v___x_2442_, v___f_2437_);
return v___x_2444_;
}
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v_pendingHead_2413_);
lean_dec_ref(v_connectionContext_2408_);
lean_dec(v_extensions_2407_);
lean_dec(v_handler_2406_);
lean_dec_ref(v_inst_2405_);
v___x_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2447_, 0, v_state_2409_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2449_, lean_object* v_handler_2450_, lean_object* v_extensions_2451_, lean_object* v_connectionContext_2452_, lean_object* v_state_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2449_, v_handler_2450_, v_extensions_2451_, v_connectionContext_2452_, v_state_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2456_, lean_object* v_inst_2457_, lean_object* v_handler_2458_, lean_object* v_extensions_2459_, lean_object* v_connectionContext_2460_, lean_object* v_state_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2457_, v_handler_2458_, v_extensions_2459_, v_connectionContext_2460_, v_state_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2464_, lean_object* v_inst_2465_, lean_object* v_handler_2466_, lean_object* v_extensions_2467_, lean_object* v_connectionContext_2468_, lean_object* v_state_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2464_, v_inst_2465_, v_handler_2466_, v_extensions_2467_, v_connectionContext_2468_, v_state_2469_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2472_, lean_object* v_____r_2473_){
_start:
{
lean_object* v_writer_2475_; lean_object* v_reader_2476_; lean_object* v_config_2477_; lean_object* v_events_2478_; lean_object* v_error_2479_; lean_object* v_instant_2480_; uint8_t v_keepAlive_2481_; uint8_t v_forcedFlush_2482_; uint8_t v_pullBodyStalled_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2510_; 
v_writer_2475_ = lean_ctor_get(v_machine_2472_, 1);
v_reader_2476_ = lean_ctor_get(v_machine_2472_, 0);
v_config_2477_ = lean_ctor_get(v_machine_2472_, 2);
v_events_2478_ = lean_ctor_get(v_machine_2472_, 3);
v_error_2479_ = lean_ctor_get(v_machine_2472_, 4);
v_instant_2480_ = lean_ctor_get(v_machine_2472_, 5);
v_keepAlive_2481_ = lean_ctor_get_uint8(v_machine_2472_, sizeof(void*)*6);
v_forcedFlush_2482_ = lean_ctor_get_uint8(v_machine_2472_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2483_ = lean_ctor_get_uint8(v_machine_2472_, sizeof(void*)*6 + 2);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_machine_2472_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2485_ = v_machine_2472_;
v_isShared_2486_ = v_isSharedCheck_2510_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_instant_2480_);
lean_inc(v_error_2479_);
lean_inc(v_events_2478_);
lean_inc(v_config_2477_);
lean_inc(v_writer_2475_);
lean_inc(v_reader_2476_);
lean_dec(v_machine_2472_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2510_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_userData_2487_; lean_object* v_outputData_2488_; lean_object* v_state_2489_; lean_object* v_knownSize_2490_; lean_object* v_messageHead_2491_; uint8_t v_sentMessage_2492_; uint8_t v_omitBody_2493_; lean_object* v_userDataBytes_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2509_; 
v_userData_2487_ = lean_ctor_get(v_writer_2475_, 0);
v_outputData_2488_ = lean_ctor_get(v_writer_2475_, 1);
v_state_2489_ = lean_ctor_get(v_writer_2475_, 2);
v_knownSize_2490_ = lean_ctor_get(v_writer_2475_, 3);
v_messageHead_2491_ = lean_ctor_get(v_writer_2475_, 4);
v_sentMessage_2492_ = lean_ctor_get_uint8(v_writer_2475_, sizeof(void*)*6);
v_omitBody_2493_ = lean_ctor_get_uint8(v_writer_2475_, sizeof(void*)*6 + 2);
v_userDataBytes_2494_ = lean_ctor_get(v_writer_2475_, 5);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_writer_2475_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2496_ = v_writer_2475_;
v_isShared_2497_ = v_isSharedCheck_2509_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_userDataBytes_2494_);
lean_inc(v_messageHead_2491_);
lean_inc(v_knownSize_2490_);
lean_inc(v_state_2489_);
lean_inc(v_outputData_2488_);
lean_inc(v_userData_2487_);
lean_dec(v_writer_2475_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2509_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
uint8_t v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = 1;
if (v_isShared_2497_ == 0)
{
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_userData_2487_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_outputData_2488_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_state_2489_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_knownSize_2490_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_messageHead_2491_);
lean_ctor_set(v_reuseFailAlloc_2508_, 5, v_userDataBytes_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*6, v_sentMessage_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*6 + 2, v_omitBody_2493_);
v___x_2500_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2502_; 
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*6 + 1, v___x_2498_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2500_);
v___x_2502_ = v___x_2485_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_reader_2476_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_config_2477_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v_events_2478_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v_error_2479_);
lean_ctor_set(v_reuseFailAlloc_2507_, 5, v_instant_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, sizeof(void*)*6, v_keepAlive_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, sizeof(void*)*6 + 1, v_forcedFlush_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, sizeof(void*)*6 + 2, v_pullBodyStalled_2483_);
v___x_2502_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2511_, lean_object* v_____r_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2511_, v_____r_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2515_, lean_object* v_x2_2516_){
_start:
{
lean_object* v_data_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_data_2517_ = lean_ctor_get(v_x2_2516_, 0);
v___x_2518_ = lean_byte_array_size(v_data_2517_);
v___x_2519_ = lean_nat_add(v_x1_2515_, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2520_, lean_object* v_x2_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2520_, v_x2_2521_);
lean_dec_ref(v_x2_2521_);
lean_dec(v_x1_2520_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2523_, lean_object* v_machine_2524_, lean_object* v_isClosed_2525_, lean_object* v___f_2526_, lean_object* v___f_2527_, lean_object* v_x_2528_){
_start:
{
lean_object* v___y_2531_; 
if (lean_obj_tag(v_x_2528_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_isClosed_2525_);
lean_dec_ref(v_machine_2524_);
lean_dec(v_body_2523_);
v_a_2536_ = lean_ctor_get(v_x_2528_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_x_2528_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v_x_2528_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v_x_2528_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2612_; 
v_a_2545_ = lean_ctor_get(v_x_2528_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_x_2528_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2547_ = v_x_2528_;
v_isShared_2548_ = v_isSharedCheck_2612_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v_x_2528_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2612_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
if (lean_obj_tag(v_a_2545_) == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec_ref(v___f_2527_);
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_isClosed_2525_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_body_2523_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_machine_2524_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2550_);
v___x_2552_ = v___x_2547_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
}
else
{
lean_object* v_val_2555_; 
lean_del_object(v___x_2547_);
v_val_2555_ = lean_ctor_get(v_a_2545_, 0);
lean_inc(v_val_2555_);
lean_dec_ref_known(v_a_2545_, 1);
if (lean_obj_tag(v_val_2555_) == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; 
lean_dec_ref(v___f_2527_);
lean_dec_ref(v_machine_2524_);
v___x_2556_ = lean_apply_2(v_isClosed_2525_, v_body_2523_, lean_box(0));
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = 0;
v___x_2559_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2557_, v___x_2558_, v___x_2556_, v___f_2526_);
return v___x_2559_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_isClosed_2525_);
v_val_2560_ = lean_ctor_get(v_val_2555_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v_val_2555_, 1);
v___x_2561_ = lean_unsigned_to_nat(1u);
v___x_2562_ = lean_mk_empty_array_with_capacity(v___x_2561_);
v___x_2563_ = lean_array_push(v___x_2562_, v_val_2560_);
v___x_2564_ = lean_array_get_size(v___x_2563_);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = lean_nat_dec_eq(v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v_reader_2567_; lean_object* v_writer_2568_; lean_object* v_config_2569_; lean_object* v_events_2570_; lean_object* v_error_2571_; lean_object* v_instant_2572_; uint8_t v_keepAlive_2573_; uint8_t v_forcedFlush_2574_; uint8_t v_pullBodyStalled_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2611_; 
v_reader_2567_ = lean_ctor_get(v_machine_2524_, 0);
v_writer_2568_ = lean_ctor_get(v_machine_2524_, 1);
v_config_2569_ = lean_ctor_get(v_machine_2524_, 2);
v_events_2570_ = lean_ctor_get(v_machine_2524_, 3);
v_error_2571_ = lean_ctor_get(v_machine_2524_, 4);
v_instant_2572_ = lean_ctor_get(v_machine_2524_, 5);
v_keepAlive_2573_ = lean_ctor_get_uint8(v_machine_2524_, sizeof(void*)*6);
v_forcedFlush_2574_ = lean_ctor_get_uint8(v_machine_2524_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2575_ = lean_ctor_get_uint8(v_machine_2524_, sizeof(void*)*6 + 2);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_machine_2524_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2577_ = v_machine_2524_;
v_isShared_2578_ = v_isSharedCheck_2611_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_instant_2572_);
lean_inc(v_error_2571_);
lean_inc(v_events_2570_);
lean_inc(v_config_2569_);
lean_inc(v_writer_2568_);
lean_inc(v_reader_2567_);
lean_dec(v_machine_2524_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2611_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___y_2580_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2603_ = lean_nat_dec_lt(v___x_2565_, v___x_2564_);
if (v___x_2603_ == 0)
{
lean_dec_ref(v___f_2527_);
v___y_2580_ = v___x_2565_;
goto v___jp_2579_;
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_nat_dec_le(v___x_2564_, v___x_2564_);
if (v___x_2604_ == 0)
{
if (v___x_2603_ == 0)
{
lean_dec_ref(v___f_2527_);
v___y_2580_ = v___x_2565_;
goto v___jp_2579_;
}
else
{
size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2564_);
lean_inc_ref(v___x_2563_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2602_, v___f_2527_, v___x_2563_, v___x_2605_, v___x_2606_, v___x_2565_);
v___y_2580_ = v___x_2607_;
goto v___jp_2579_;
}
}
else
{
size_t v___x_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = ((size_t)0ULL);
v___x_2609_ = lean_usize_of_nat(v___x_2564_);
lean_inc_ref(v___x_2563_);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2602_, v___f_2527_, v___x_2563_, v___x_2608_, v___x_2609_, v___x_2565_);
v___y_2580_ = v___x_2610_;
goto v___jp_2579_;
}
}
v___jp_2579_:
{
lean_object* v_userData_2581_; lean_object* v_outputData_2582_; lean_object* v_state_2583_; lean_object* v_knownSize_2584_; lean_object* v_messageHead_2585_; uint8_t v_sentMessage_2586_; uint8_t v_userClosedBody_2587_; uint8_t v_omitBody_2588_; lean_object* v_userDataBytes_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2601_; 
v_userData_2581_ = lean_ctor_get(v_writer_2568_, 0);
v_outputData_2582_ = lean_ctor_get(v_writer_2568_, 1);
v_state_2583_ = lean_ctor_get(v_writer_2568_, 2);
v_knownSize_2584_ = lean_ctor_get(v_writer_2568_, 3);
v_messageHead_2585_ = lean_ctor_get(v_writer_2568_, 4);
v_sentMessage_2586_ = lean_ctor_get_uint8(v_writer_2568_, sizeof(void*)*6);
v_userClosedBody_2587_ = lean_ctor_get_uint8(v_writer_2568_, sizeof(void*)*6 + 1);
v_omitBody_2588_ = lean_ctor_get_uint8(v_writer_2568_, sizeof(void*)*6 + 2);
v_userDataBytes_2589_ = lean_ctor_get(v_writer_2568_, 5);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_writer_2568_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2591_ = v_writer_2568_;
v_isShared_2592_ = v_isSharedCheck_2601_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_userDataBytes_2589_);
lean_inc(v_messageHead_2585_);
lean_inc(v_knownSize_2584_);
lean_inc(v_state_2583_);
lean_inc(v_outputData_2582_);
lean_inc(v_userData_2581_);
lean_dec(v_writer_2568_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2601_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = l_Array_append___redArg(v_userData_2581_, v___x_2563_);
lean_dec_ref(v___x_2563_);
v___x_2594_ = lean_nat_add(v_userDataBytes_2589_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec(v_userDataBytes_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 5, v___x_2594_);
lean_ctor_set(v___x_2591_, 0, v___x_2593_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_outputData_2582_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_state_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_knownSize_2584_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_messageHead_2585_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v___x_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*6, v_sentMessage_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*6 + 1, v_userClosedBody_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*6 + 2, v_omitBody_2588_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 1, v___x_2596_);
v___x_2598_ = v___x_2577_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_reader_2567_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_config_2569_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_events_2570_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_error_2571_);
lean_ctor_set(v_reuseFailAlloc_2599_, 5, v_instant_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*6, v_keepAlive_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*6 + 1, v_forcedFlush_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*6 + 2, v_pullBodyStalled_2575_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
v___y_2531_ = v___x_2598_;
goto v___jp_2530_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2563_);
lean_dec_ref(v___f_2527_);
v___y_2531_ = v_machine_2524_;
goto v___jp_2530_;
}
}
}
}
}
v___jp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_body_2523_);
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___y_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2613_, lean_object* v_machine_2614_, lean_object* v_isClosed_2615_, lean_object* v___f_2616_, lean_object* v___f_2617_, lean_object* v_x_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2613_, v_machine_2614_, v_isClosed_2615_, v___f_2616_, v___f_2617_, v_x_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2622_, lean_object* v_machine_2623_, lean_object* v_body_2624_){
_start:
{
lean_object* v_close_2626_; lean_object* v_isClosed_2627_; lean_object* v_tryRecv_2628_; lean_object* v___x_2629_; lean_object* v___f_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v___f_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; 
v_close_2626_ = lean_ctor_get(v_inst_2622_, 1);
lean_inc_ref(v_close_2626_);
v_isClosed_2627_ = lean_ctor_get(v_inst_2622_, 2);
lean_inc_ref(v_isClosed_2627_);
v_tryRecv_2628_ = lean_ctor_get(v_inst_2622_, 4);
lean_inc_ref(v_tryRecv_2628_);
lean_dec_ref(v_inst_2622_);
lean_inc_n(v_body_2624_, 2);
v___x_2629_ = lean_apply_2(v_tryRecv_2628_, v_body_2624_, lean_box(0));
lean_inc_ref(v_machine_2623_);
v___f_2630_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2630_, 0, v_machine_2623_);
lean_inc_ref(v___f_2630_);
v___f_2631_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2631_, 0, v___f_2630_);
v___f_2632_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2632_, 0, v_close_2626_);
lean_closure_set(v___f_2632_, 1, v_body_2624_);
lean_closure_set(v___f_2632_, 2, v___f_2631_);
lean_closure_set(v___f_2632_, 3, v___f_2630_);
v___f_2633_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2634_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2634_, 0, v_body_2624_);
lean_closure_set(v___f_2634_, 1, v_machine_2623_);
lean_closure_set(v___f_2634_, 2, v_isClosed_2627_);
lean_closure_set(v___f_2634_, 3, v___f_2632_);
lean_closure_set(v___f_2634_, 4, v___f_2633_);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = 0;
v___x_2637_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2635_, v___x_2636_, v___x_2629_, v___f_2634_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2638_, lean_object* v_machine_2639_, lean_object* v_body_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2638_, v_machine_2639_, v_body_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2643_, lean_object* v_inst_2644_, lean_object* v_machine_2645_, lean_object* v_body_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2644_, v_machine_2645_, v_body_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2649_, lean_object* v_inst_2650_, lean_object* v_machine_2651_, lean_object* v_body_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2649_, v_inst_2650_, v_machine_2651_, v_body_2652_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2661_, lean_object* v_____r_2662_, lean_object* v_st_2663_){
_start:
{
lean_object* v_machine_2665_; lean_object* v_requestStream_2666_; lean_object* v_keepAliveTimeout_2667_; lean_object* v_currentTimeout_2668_; lean_object* v_headerTimeout_2669_; lean_object* v_response_2670_; lean_object* v_respStream_2671_; uint8_t v_requiresData_2672_; lean_object* v_expectData_2673_; uint8_t v_handlerDispatched_2674_; lean_object* v_pendingHead_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2757_; 
v_machine_2665_ = lean_ctor_get(v_st_2663_, 0);
v_requestStream_2666_ = lean_ctor_get(v_st_2663_, 1);
v_keepAliveTimeout_2667_ = lean_ctor_get(v_st_2663_, 2);
v_currentTimeout_2668_ = lean_ctor_get(v_st_2663_, 3);
v_headerTimeout_2669_ = lean_ctor_get(v_st_2663_, 4);
v_response_2670_ = lean_ctor_get(v_st_2663_, 5);
v_respStream_2671_ = lean_ctor_get(v_st_2663_, 6);
v_requiresData_2672_ = lean_ctor_get_uint8(v_st_2663_, sizeof(void*)*9);
v_expectData_2673_ = lean_ctor_get(v_st_2663_, 7);
v_handlerDispatched_2674_ = lean_ctor_get_uint8(v_st_2663_, sizeof(void*)*9 + 1);
v_pendingHead_2675_ = lean_ctor_get(v_st_2663_, 8);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_st_2663_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2677_ = v_st_2663_;
v_isShared_2678_ = v_isSharedCheck_2757_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_pendingHead_2675_);
lean_inc(v_expectData_2673_);
lean_inc(v_respStream_2671_);
lean_inc(v_response_2670_);
lean_inc(v_headerTimeout_2669_);
lean_inc(v_currentTimeout_2668_);
lean_inc(v_keepAliveTimeout_2667_);
lean_inc(v_requestStream_2666_);
lean_inc(v_machine_2665_);
lean_dec(v_st_2663_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2757_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___y_2680_; lean_object* v_reader_2689_; lean_object* v_state_2690_; 
v_reader_2689_ = lean_ctor_get(v_machine_2665_, 0);
lean_inc_ref(v_reader_2689_);
v_state_2690_ = lean_ctor_get(v_reader_2689_, 0);
lean_inc(v_state_2690_);
if (lean_obj_tag(v_state_2690_) == 6)
{
lean_dec_ref(v_reader_2689_);
lean_dec_ref(v_val_2661_);
v___y_2680_ = v_machine_2665_;
goto v___jp_2679_;
}
else
{
if (lean_obj_tag(v_state_2690_) == 7)
{
lean_dec_ref_known(v_state_2690_, 1);
lean_dec_ref(v_reader_2689_);
lean_dec_ref(v_val_2661_);
v___y_2680_ = v_machine_2665_;
goto v___jp_2679_;
}
else
{
lean_object* v_input_2691_; lean_object* v_writer_2692_; lean_object* v_config_2693_; lean_object* v_events_2694_; lean_object* v_error_2695_; lean_object* v_instant_2696_; uint8_t v_keepAlive_2697_; uint8_t v_forcedFlush_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2755_; 
v_input_2691_ = lean_ctor_get(v_reader_2689_, 1);
lean_inc_ref(v_input_2691_);
v_writer_2692_ = lean_ctor_get(v_machine_2665_, 1);
v_config_2693_ = lean_ctor_get(v_machine_2665_, 2);
v_events_2694_ = lean_ctor_get(v_machine_2665_, 3);
v_error_2695_ = lean_ctor_get(v_machine_2665_, 4);
v_instant_2696_ = lean_ctor_get(v_machine_2665_, 5);
v_keepAlive_2697_ = lean_ctor_get_uint8(v_machine_2665_, sizeof(void*)*6);
v_forcedFlush_2698_ = lean_ctor_get_uint8(v_machine_2665_, sizeof(void*)*6 + 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_machine_2665_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v_machine_2665_, 0);
lean_dec(v_unused_2756_);
v___x_2700_ = v_machine_2665_;
v_isShared_2701_ = v_isSharedCheck_2755_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_instant_2696_);
lean_inc(v_error_2695_);
lean_inc(v_events_2694_);
lean_inc(v_config_2693_);
lean_inc(v_writer_2692_);
lean_dec(v_machine_2665_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2755_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_messageHead_2702_; lean_object* v_messageCount_2703_; lean_object* v_bodyBytesRead_2704_; lean_object* v_headerBytesRead_2705_; uint8_t v_noMoreInput_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2752_; 
v_messageHead_2702_ = lean_ctor_get(v_reader_2689_, 2);
v_messageCount_2703_ = lean_ctor_get(v_reader_2689_, 3);
v_bodyBytesRead_2704_ = lean_ctor_get(v_reader_2689_, 4);
v_headerBytesRead_2705_ = lean_ctor_get(v_reader_2689_, 5);
v_noMoreInput_2706_ = lean_ctor_get_uint8(v_reader_2689_, sizeof(void*)*6);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_reader_2689_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; lean_object* v_unused_2754_; 
v_unused_2753_ = lean_ctor_get(v_reader_2689_, 1);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_reader_2689_, 0);
lean_dec(v_unused_2754_);
v___x_2708_ = v_reader_2689_;
v_isShared_2709_ = v_isSharedCheck_2752_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_headerBytesRead_2705_);
lean_inc(v_bodyBytesRead_2704_);
lean_inc(v_messageCount_2703_);
lean_inc(v_messageHead_2702_);
lean_dec(v_reader_2689_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2752_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_array_2710_; lean_object* v_idx_2711_; uint8_t v___x_2712_; lean_object* v___y_2714_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v_array_2710_ = lean_ctor_get(v_input_2691_, 0);
lean_inc_ref(v_array_2710_);
v_idx_2711_ = lean_ctor_get(v_input_2691_, 1);
lean_inc(v_idx_2711_);
lean_dec_ref(v_input_2691_);
v___x_2712_ = 0;
v___x_2743_ = lean_byte_array_size(v_array_2710_);
v___x_2744_ = lean_nat_dec_le(v___x_2743_, v_idx_2711_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2745_ = l_ByteArray_extract(v_array_2710_, v_idx_2711_, v___x_2743_);
lean_dec_ref(v_array_2710_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_byte_array_size(v___x_2745_);
v___x_2748_ = lean_byte_array_size(v_val_2661_);
v___x_2749_ = lean_byte_array_copy_slice(v_val_2661_, v___x_2746_, v___x_2745_, v___x_2747_, v___x_2748_, v___x_2744_);
lean_dec_ref(v_val_2661_);
v___x_2750_ = l_ByteArray_mkIterator(v___x_2749_);
v___y_2714_ = v___x_2750_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2751_; 
lean_dec(v_idx_2711_);
lean_dec_ref(v_array_2710_);
v___x_2751_ = l_ByteArray_mkIterator(v_val_2661_);
v___y_2714_ = v___x_2751_;
goto v___jp_2713_;
}
v___jp_2713_:
{
lean_object* v_maxHeaderBytes_2715_; lean_object* v_maxStartLineLength_2716_; lean_object* v_maxChunkLineLength_2717_; lean_object* v_maxBodySize_2718_; lean_object* v_array_2719_; lean_object* v_idx_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v_maxHeaderBytes_2715_ = lean_ctor_get(v_config_2693_, 2);
v_maxStartLineLength_2716_ = lean_ctor_get(v_config_2693_, 5);
v_maxChunkLineLength_2717_ = lean_ctor_get(v_config_2693_, 13);
v_maxBodySize_2718_ = lean_ctor_get(v_config_2693_, 15);
v_array_2719_ = lean_ctor_get(v___y_2714_, 0);
v_idx_2720_ = lean_ctor_get(v___y_2714_, 1);
v___x_2721_ = lean_nat_add(v_maxBodySize_2718_, v_maxHeaderBytes_2715_);
v___x_2722_ = lean_nat_add(v___x_2721_, v_maxStartLineLength_2716_);
lean_dec(v___x_2721_);
v___x_2723_ = lean_nat_add(v___x_2722_, v_maxChunkLineLength_2717_);
lean_dec(v___x_2722_);
v___x_2724_ = lean_byte_array_size(v_array_2719_);
v___x_2725_ = lean_nat_sub(v___x_2724_, v_idx_2720_);
v___x_2726_ = lean_nat_dec_lt(v___x_2723_, v___x_2725_);
lean_dec(v___x_2725_);
lean_dec(v___x_2723_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2728_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 1, v___y_2714_);
v___x_2728_ = v___x_2708_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_state_2690_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___y_2714_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_messageHead_2702_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_messageCount_2703_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_bodyBytesRead_2704_);
lean_ctor_set(v_reuseFailAlloc_2732_, 5, v_headerBytesRead_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2732_, sizeof(void*)*6, v_noMoreInput_2706_);
v___x_2728_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v_machine_2730_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2728_);
v_machine_2730_ = v___x_2700_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_writer_2692_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_config_2693_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_events_2694_);
lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_error_2695_);
lean_ctor_set(v_reuseFailAlloc_2731_, 5, v_instant_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, sizeof(void*)*6, v_keepAlive_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, sizeof(void*)*6 + 1, v_forcedFlush_2698_);
v_machine_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_ctor_set_uint8(v_machine_2730_, sizeof(void*)*6 + 2, v___x_2712_);
v___y_2680_ = v_machine_2730_;
goto v___jp_2679_;
}
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_dec(v_error_2695_);
lean_dec(v_state_2690_);
v___x_2733_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2734_ = lean_array_push(v_events_2694_, v___x_2733_);
v___x_2735_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 1, v___y_2714_);
lean_ctor_set(v___x_2708_, 0, v___x_2735_);
v___x_2737_ = v___x_2708_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___y_2714_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_messageHead_2702_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_messageCount_2703_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_bodyBytesRead_2704_);
lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_headerBytesRead_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2742_, sizeof(void*)*6, v_noMoreInput_2706_);
v___x_2737_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 4, v___x_2738_);
lean_ctor_set(v___x_2700_, 3, v___x_2734_);
lean_ctor_set(v___x_2700_, 0, v___x_2737_);
v___x_2740_ = v___x_2700_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_writer_2692_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_config_2693_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2741_, 5, v_instant_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2741_, sizeof(void*)*6, v_keepAlive_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2741_, sizeof(void*)*6 + 1, v_forcedFlush_2698_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*6 + 2, v___x_2712_);
v___y_2680_ = v___x_2740_;
goto v___jp_2679_;
}
}
}
}
}
}
}
}
v___jp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___y_2680_);
v___x_2682_ = v___x_2677_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___y_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_requestStream_2666_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_keepAliveTimeout_2667_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_currentTimeout_2668_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_headerTimeout_2669_);
lean_ctor_set(v_reuseFailAlloc_2688_, 5, v_response_2670_);
lean_ctor_set(v_reuseFailAlloc_2688_, 6, v_respStream_2671_);
lean_ctor_set(v_reuseFailAlloc_2688_, 7, v_expectData_2673_);
lean_ctor_set(v_reuseFailAlloc_2688_, 8, v_pendingHead_2675_);
lean_ctor_set_uint8(v_reuseFailAlloc_2688_, sizeof(void*)*9, v_requiresData_2672_);
lean_ctor_set_uint8(v_reuseFailAlloc_2688_, sizeof(void*)*9 + 1, v_handlerDispatched_2674_);
v___x_2682_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2683_ = 0;
v___x_2684_ = lean_box(v___x_2683_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2682_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2758_, lean_object* v_____r_2759_, lean_object* v_st_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2758_, v_____r_2759_, v_st_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2763_, lean_object* v_machine_2764_, lean_object* v_requestStream_2765_, lean_object* v_currentTimeout_2766_, lean_object* v_response_2767_, lean_object* v_respStream_2768_, uint8_t v_requiresData_2769_, lean_object* v_expectData_2770_, uint8_t v_handlerDispatched_2771_, lean_object* v_pendingHead_2772_, lean_object* v___f_2773_, lean_object* v_x_2774_){
_start:
{
if (lean_obj_tag(v_x_2774_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v___f_2773_);
lean_dec(v_pendingHead_2772_);
lean_dec(v_expectData_2770_);
lean_dec(v_respStream_2768_);
lean_dec_ref(v_response_2767_);
lean_dec(v_currentTimeout_2766_);
lean_dec_ref(v_requestStream_2765_);
lean_dec_ref(v_machine_2764_);
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
lean_object* v_a_2785_; lean_object* v_headerTimeout_2786_; lean_object* v_second_2787_; lean_object* v_nano_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v_second_2792_; lean_object* v_nano_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2785_ = lean_ctor_get(v_x_2774_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v_x_2774_, 1);
v_headerTimeout_2786_ = lean_ctor_get(v_config_2763_, 6);
v_second_2787_ = lean_ctor_get(v_a_2785_, 0);
lean_inc(v_second_2787_);
v_nano_2788_ = lean_ctor_get(v_a_2785_, 1);
lean_inc(v_nano_2788_);
lean_dec(v_a_2785_);
v___x_2789_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2790_ = lean_int_mul(v_headerTimeout_2786_, v___x_2789_);
v___x_2791_ = l_Std_Time_Duration_ofNanoseconds(v___x_2790_);
lean_dec(v___x_2790_);
v_second_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_second_2792_);
v_nano_2793_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_nano_2793_);
lean_dec_ref(v___x_2791_);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2796_ = lean_int_mul(v_second_2787_, v___x_2795_);
lean_dec(v_second_2787_);
v___x_2797_ = lean_int_add(v___x_2796_, v_nano_2788_);
lean_dec(v_nano_2788_);
lean_dec(v___x_2796_);
v___x_2798_ = lean_int_mul(v_second_2792_, v___x_2795_);
lean_dec(v_second_2792_);
v___x_2799_ = lean_int_add(v___x_2798_, v_nano_2793_);
lean_dec(v_nano_2793_);
lean_dec(v___x_2798_);
v___x_2800_ = lean_int_add(v___x_2797_, v___x_2799_);
lean_dec(v___x_2799_);
lean_dec(v___x_2797_);
v___x_2801_ = l_Std_Time_Duration_ofNanoseconds(v___x_2800_);
lean_dec(v___x_2800_);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2803_, 0, v_machine_2764_);
lean_ctor_set(v___x_2803_, 1, v_requestStream_2765_);
lean_ctor_set(v___x_2803_, 2, v___x_2794_);
lean_ctor_set(v___x_2803_, 3, v_currentTimeout_2766_);
lean_ctor_set(v___x_2803_, 4, v___x_2802_);
lean_ctor_set(v___x_2803_, 5, v_response_2767_);
lean_ctor_set(v___x_2803_, 6, v_respStream_2768_);
lean_ctor_set(v___x_2803_, 7, v_expectData_2770_);
lean_ctor_set(v___x_2803_, 8, v_pendingHead_2772_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*9, v_requiresData_2769_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*9 + 1, v_handlerDispatched_2771_);
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_apply_3(v___f_2773_, v___x_2804_, v___x_2803_, lean_box(0));
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2806_, lean_object* v_machine_2807_, lean_object* v_requestStream_2808_, lean_object* v_currentTimeout_2809_, lean_object* v_response_2810_, lean_object* v_respStream_2811_, lean_object* v_requiresData_2812_, lean_object* v_expectData_2813_, lean_object* v_handlerDispatched_2814_, lean_object* v_pendingHead_2815_, lean_object* v___f_2816_, lean_object* v_x_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v_requiresData_boxed_2819_; uint8_t v_handlerDispatched_boxed_2820_; lean_object* v_res_2821_; 
v_requiresData_boxed_2819_ = lean_unbox(v_requiresData_2812_);
v_handlerDispatched_boxed_2820_ = lean_unbox(v_handlerDispatched_2814_);
v_res_2821_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2806_, v_machine_2807_, v_requestStream_2808_, v_currentTimeout_2809_, v_response_2810_, v_respStream_2811_, v_requiresData_boxed_2819_, v_expectData_2813_, v_handlerDispatched_boxed_2820_, v_pendingHead_2815_, v___f_2816_, v_x_2817_);
lean_dec_ref(v_config_2806_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2822_, lean_object* v_requestStream_2823_, lean_object* v_keepAliveTimeout_2824_, lean_object* v_currentTimeout_2825_, lean_object* v_headerTimeout_2826_, lean_object* v_response_2827_, uint8_t v_requiresData_2828_, lean_object* v_expectData_2829_, uint8_t v_handlerDispatched_2830_, lean_object* v_pendingHead_2831_, lean_object* v_____r_2832_){
_start:
{
lean_object* v_writer_2834_; lean_object* v_reader_2835_; lean_object* v_config_2836_; lean_object* v_events_2837_; lean_object* v_error_2838_; lean_object* v_instant_2839_; uint8_t v_keepAlive_2840_; uint8_t v_forcedFlush_2841_; uint8_t v_pullBodyStalled_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2872_; 
v_writer_2834_ = lean_ctor_get(v_machine_2822_, 1);
v_reader_2835_ = lean_ctor_get(v_machine_2822_, 0);
v_config_2836_ = lean_ctor_get(v_machine_2822_, 2);
v_events_2837_ = lean_ctor_get(v_machine_2822_, 3);
v_error_2838_ = lean_ctor_get(v_machine_2822_, 4);
v_instant_2839_ = lean_ctor_get(v_machine_2822_, 5);
v_keepAlive_2840_ = lean_ctor_get_uint8(v_machine_2822_, sizeof(void*)*6);
v_forcedFlush_2841_ = lean_ctor_get_uint8(v_machine_2822_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2842_ = lean_ctor_get_uint8(v_machine_2822_, sizeof(void*)*6 + 2);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_machine_2822_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2844_ = v_machine_2822_;
v_isShared_2845_ = v_isSharedCheck_2872_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_instant_2839_);
lean_inc(v_error_2838_);
lean_inc(v_events_2837_);
lean_inc(v_config_2836_);
lean_inc(v_writer_2834_);
lean_inc(v_reader_2835_);
lean_dec(v_machine_2822_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2872_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_userData_2846_; lean_object* v_outputData_2847_; lean_object* v_state_2848_; lean_object* v_knownSize_2849_; lean_object* v_messageHead_2850_; uint8_t v_sentMessage_2851_; uint8_t v_omitBody_2852_; lean_object* v_userDataBytes_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2871_; 
v_userData_2846_ = lean_ctor_get(v_writer_2834_, 0);
v_outputData_2847_ = lean_ctor_get(v_writer_2834_, 1);
v_state_2848_ = lean_ctor_get(v_writer_2834_, 2);
v_knownSize_2849_ = lean_ctor_get(v_writer_2834_, 3);
v_messageHead_2850_ = lean_ctor_get(v_writer_2834_, 4);
v_sentMessage_2851_ = lean_ctor_get_uint8(v_writer_2834_, sizeof(void*)*6);
v_omitBody_2852_ = lean_ctor_get_uint8(v_writer_2834_, sizeof(void*)*6 + 2);
v_userDataBytes_2853_ = lean_ctor_get(v_writer_2834_, 5);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_writer_2834_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2855_ = v_writer_2834_;
v_isShared_2856_ = v_isSharedCheck_2871_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_userDataBytes_2853_);
lean_inc(v_messageHead_2850_);
lean_inc(v_knownSize_2849_);
lean_inc(v_state_2848_);
lean_inc(v_outputData_2847_);
lean_inc(v_userData_2846_);
lean_dec(v_writer_2834_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2871_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
uint8_t v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = 1;
if (v_isShared_2856_ == 0)
{
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_userData_2846_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_outputData_2847_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_state_2848_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_knownSize_2849_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_messageHead_2850_);
lean_ctor_set(v_reuseFailAlloc_2870_, 5, v_userDataBytes_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2870_, sizeof(void*)*6, v_sentMessage_2851_);
lean_ctor_set_uint8(v_reuseFailAlloc_2870_, sizeof(void*)*6 + 2, v_omitBody_2852_);
v___x_2859_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*6 + 1, v___x_2857_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2859_);
v___x_2861_ = v___x_2844_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_reader_2835_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_config_2836_);
lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_events_2837_);
lean_ctor_set(v_reuseFailAlloc_2869_, 4, v_error_2838_);
lean_ctor_set(v_reuseFailAlloc_2869_, 5, v_instant_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*6, v_keepAlive_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*6 + 1, v_forcedFlush_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*6 + 2, v_pullBodyStalled_2842_);
v___x_2861_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2862_ = lean_box(0);
v___x_2863_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v_requestStream_2823_);
lean_ctor_set(v___x_2863_, 2, v_keepAliveTimeout_2824_);
lean_ctor_set(v___x_2863_, 3, v_currentTimeout_2825_);
lean_ctor_set(v___x_2863_, 4, v_headerTimeout_2826_);
lean_ctor_set(v___x_2863_, 5, v_response_2827_);
lean_ctor_set(v___x_2863_, 6, v___x_2862_);
lean_ctor_set(v___x_2863_, 7, v_expectData_2829_);
lean_ctor_set(v___x_2863_, 8, v_pendingHead_2831_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*9, v_requiresData_2828_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*9 + 1, v_handlerDispatched_2830_);
v___x_2864_ = 0;
v___x_2865_ = lean_box(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2863_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2873_, lean_object* v_requestStream_2874_, lean_object* v_keepAliveTimeout_2875_, lean_object* v_currentTimeout_2876_, lean_object* v_headerTimeout_2877_, lean_object* v_response_2878_, lean_object* v_requiresData_2879_, lean_object* v_expectData_2880_, lean_object* v_handlerDispatched_2881_, lean_object* v_pendingHead_2882_, lean_object* v_____r_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v_requiresData_boxed_2885_; uint8_t v_handlerDispatched_boxed_2886_; lean_object* v_res_2887_; 
v_requiresData_boxed_2885_ = lean_unbox(v_requiresData_2879_);
v_handlerDispatched_boxed_2886_ = lean_unbox(v_handlerDispatched_2881_);
v_res_2887_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2873_, v_requestStream_2874_, v_keepAliveTimeout_2875_, v_currentTimeout_2876_, v_headerTimeout_2877_, v_response_2878_, v_requiresData_boxed_2885_, v_expectData_2880_, v_handlerDispatched_boxed_2886_, v_pendingHead_2882_, v_____r_2883_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2888_, lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
lean_dec_ref(v___f_2888_);
v_a_2891_ = lean_ctor_get(v_x_2889_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v_x_2889_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v_x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2901_; 
v_a_2900_ = lean_ctor_get(v_x_2889_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v_x_2889_, 1);
v___x_2901_ = lean_apply_2(v___f_2888_, v_a_2900_, lean_box(0));
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2902_, lean_object* v_x_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2902_, v_x_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2906_, lean_object* v_val_2907_, lean_object* v___f_2908_, lean_object* v___f_2909_, lean_object* v_x_2910_){
_start:
{
if (lean_obj_tag(v_x_2910_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___f_2909_);
lean_dec_ref(v___f_2908_);
lean_dec(v_val_2907_);
lean_dec_ref(v_close_2906_);
v_a_2912_ = lean_ctor_get(v_x_2910_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_x_2910_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2914_ = v_x_2910_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v_x_2910_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2921_; uint8_t v___x_2922_; 
v_a_2921_ = lean_ctor_get(v_x_2910_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v_x_2910_, 1);
v___x_2922_ = lean_unbox(v_a_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref(v___f_2909_);
v___x_2923_ = lean_apply_2(v_close_2906_, v_val_2907_, lean_box(0));
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_unbox(v_a_2921_);
lean_dec(v_a_2921_);
v___x_2926_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2924_, v___x_2925_, v___x_2923_, v___f_2908_);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec(v_a_2921_);
lean_dec_ref(v___f_2908_);
lean_dec(v_val_2907_);
lean_dec_ref(v_close_2906_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_apply_2(v___f_2909_, v___x_2927_, lean_box(0));
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2929_, lean_object* v_val_2930_, lean_object* v___f_2931_, lean_object* v___f_2932_, lean_object* v_x_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2929_, v_val_2930_, v___f_2931_, v___f_2932_, v_x_2933_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2936_, lean_object* v_handler_2937_, lean_object* v_x_2938_){
_start:
{
if (lean_obj_tag(v_x_2938_) == 0)
{
lean_object* v_a_2940_; lean_object* v_onFailure_2941_; lean_object* v___x_2942_; 
v_a_2940_ = lean_ctor_get(v_x_2938_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v_x_2938_, 1);
v_onFailure_2941_ = lean_ctor_get(v_inst_2936_, 2);
lean_inc_ref(v_onFailure_2941_);
lean_dec_ref(v_inst_2936_);
v___x_2942_ = lean_apply_3(v_onFailure_2941_, v_handler_2937_, v_a_2940_, lean_box(0));
return v___x_2942_;
}
else
{
lean_object* v___x_2943_; 
lean_dec(v_handler_2937_);
lean_dec_ref(v_inst_2936_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_x_2938_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2944_, lean_object* v_handler_2945_, lean_object* v_x_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2944_, v_handler_2945_, v_x_2946_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2949_, lean_object* v_____r_2950_){
_start:
{
uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2952_ = 0;
v___x_2953_ = lean_box(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v_st_2949_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2957_, lean_object* v_____r_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2957_, v_____r_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2961_, lean_object* v___f_2962_, lean_object* v___f_2963_, lean_object* v_x_2964_){
_start:
{
if (lean_obj_tag(v_x_2964_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v___f_2963_);
lean_dec_ref(v___f_2962_);
lean_dec_ref(v_requestStream_2961_);
v_a_2966_ = lean_ctor_get(v_x_2964_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_x_2964_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2968_ = v_x_2964_;
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v_x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
}
else
{
lean_object* v_a_2975_; uint8_t v___x_2976_; 
v_a_2975_ = lean_ctor_get(v_x_2964_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v_x_2964_, 1);
v___x_2976_ = lean_unbox(v_a_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; 
lean_dec_ref(v___f_2963_);
v___x_2977_ = l_Std_Http_Body_Stream_close(v_requestStream_2961_);
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = lean_unbox(v_a_2975_);
lean_dec(v_a_2975_);
v___x_2980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2978_, v___x_2979_, v___x_2977_, v___f_2962_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec(v_a_2975_);
lean_dec_ref(v___f_2962_);
lean_dec_ref(v_requestStream_2961_);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_apply_2(v___f_2963_, v___x_2981_, lean_box(0));
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2983_, lean_object* v___f_2984_, lean_object* v___f_2985_, lean_object* v_x_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2983_, v___f_2984_, v___f_2985_, v_x_2986_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2989_, lean_object* v___f_2990_, lean_object* v___f_2991_, lean_object* v_requestStream_2992_, lean_object* v___f_2993_, lean_object* v_x_2994_){
_start:
{
if (lean_obj_tag(v_x_2994_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v___f_2993_);
lean_dec_ref(v_requestStream_2992_);
lean_dec_ref(v___f_2991_);
lean_dec_ref(v___f_2990_);
v_a_2996_ = lean_ctor_get(v_x_2994_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_x_2994_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2998_ = v_x_2994_;
v_isShared_2999_ = v_isSharedCheck_3004_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v_x_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3004_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
}
else
{
lean_dec_ref_known(v_x_2994_, 1);
if (v_final_2989_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec_ref(v___f_2993_);
lean_dec_ref(v_requestStream_2992_);
lean_dec_ref(v___f_2991_);
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_apply_2(v___f_2990_, v___x_3005_, lean_box(0));
return v___x_3006_;
}
else
{
lean_object* v___x_3007_; lean_object* v___f_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_7002__overap_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; 
lean_dec_ref(v___f_2990_);
v___x_3007_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3008_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3009_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3010_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3011_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3011_, 0, lean_box(0));
lean_closure_set(v___x_3011_, 1, lean_box(0));
lean_closure_set(v___x_3011_, 2, lean_box(0));
lean_closure_set(v___x_3011_, 3, v___x_3007_);
lean_closure_set(v___x_3011_, 4, lean_box(0));
lean_closure_set(v___x_3011_, 5, lean_box(0));
lean_closure_set(v___x_3011_, 6, v___x_3010_);
lean_closure_set(v___x_3011_, 7, v___f_2991_);
v___x_7002__overap_3012_ = l_Std_Mutex_atomically___redArg(v___x_3007_, v___f_3008_, v___f_3009_, v_requestStream_2992_, v___x_3011_);
v___x_3013_ = lean_apply_1(v___x_7002__overap_3012_, lean_box(0));
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = 0;
v___x_3016_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3014_, v___x_3015_, v___x_3013_, v___f_2993_);
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3017_, lean_object* v___f_3018_, lean_object* v___f_3019_, lean_object* v_requestStream_3020_, lean_object* v___f_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v_final_boxed_3024_; lean_object* v_res_3025_; 
v_final_boxed_3024_ = lean_unbox(v_final_3017_);
v_res_3025_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3024_, v___f_3018_, v___f_3019_, v_requestStream_3020_, v___f_3021_, v_x_3022_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3026_, lean_object* v_x_3027_){
_start:
{
if (lean_obj_tag(v_x_3027_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v_state_3026_);
v_a_3029_ = lean_ctor_get(v_x_3027_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_x_3027_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3031_ = v_x_3027_;
v_isShared_3032_ = v_isSharedCheck_3037_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v_x_3027_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3037_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
}
else
{
lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3067_; 
v_isSharedCheck_3067_ = !lean_is_exclusive(v_x_3027_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v_x_3027_, 0);
lean_dec(v_unused_3068_);
v___x_3039_ = v_x_3027_;
v_isShared_3040_ = v_isSharedCheck_3067_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v_x_3027_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3067_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_machine_3041_; lean_object* v_requestStream_3042_; lean_object* v_keepAliveTimeout_3043_; lean_object* v_currentTimeout_3044_; lean_object* v_headerTimeout_3045_; lean_object* v_response_3046_; lean_object* v_respStream_3047_; uint8_t v_requiresData_3048_; lean_object* v_expectData_3049_; lean_object* v_pendingHead_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3066_; 
v_machine_3041_ = lean_ctor_get(v_state_3026_, 0);
v_requestStream_3042_ = lean_ctor_get(v_state_3026_, 1);
v_keepAliveTimeout_3043_ = lean_ctor_get(v_state_3026_, 2);
v_currentTimeout_3044_ = lean_ctor_get(v_state_3026_, 3);
v_headerTimeout_3045_ = lean_ctor_get(v_state_3026_, 4);
v_response_3046_ = lean_ctor_get(v_state_3026_, 5);
v_respStream_3047_ = lean_ctor_get(v_state_3026_, 6);
v_requiresData_3048_ = lean_ctor_get_uint8(v_state_3026_, sizeof(void*)*9);
v_expectData_3049_ = lean_ctor_get(v_state_3026_, 7);
v_pendingHead_3050_ = lean_ctor_get(v_state_3026_, 8);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_state_3026_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3052_ = v_state_3026_;
v_isShared_3053_ = v_isSharedCheck_3066_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_pendingHead_3050_);
lean_inc(v_expectData_3049_);
lean_inc(v_respStream_3047_);
lean_inc(v_response_3046_);
lean_inc(v_headerTimeout_3045_);
lean_inc(v_currentTimeout_3044_);
lean_inc(v_keepAliveTimeout_3043_);
lean_inc(v_requestStream_3042_);
lean_inc(v_machine_3041_);
lean_dec(v_state_3026_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3066_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3058_; 
v___x_3054_ = lean_box(52);
v___x_3055_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3041_, v___x_3054_);
v___x_3056_ = 0;
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3055_);
v___x_3058_ = v___x_3052_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_requestStream_3042_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_keepAliveTimeout_3043_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_currentTimeout_3044_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_headerTimeout_3045_);
lean_ctor_set(v_reuseFailAlloc_3065_, 5, v_response_3046_);
lean_ctor_set(v_reuseFailAlloc_3065_, 6, v_respStream_3047_);
lean_ctor_set(v_reuseFailAlloc_3065_, 7, v_expectData_3049_);
lean_ctor_set(v_reuseFailAlloc_3065_, 8, v_pendingHead_3050_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*9, v_requiresData_3048_);
v___x_3058_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
lean_ctor_set_uint8(v___x_3058_, sizeof(void*)*9 + 1, v___x_3056_);
v___x_3059_ = lean_box(v___x_3056_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3060_);
v___x_3062_ = v___x_3039_;
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3069_, lean_object* v_x_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3069_, v_x_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3073_, lean_object* v_requestStream_3074_, lean_object* v_keepAliveTimeout_3075_, lean_object* v_currentTimeout_3076_, lean_object* v_headerTimeout_3077_, lean_object* v_response_3078_, lean_object* v_respStream_3079_, uint8_t v_requiresData_3080_, lean_object* v_expectData_3081_, lean_object* v_pendingHead_3082_, lean_object* v_____r_3083_){
_start:
{
uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3085_ = 0;
v___x_3086_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3086_, 0, v_machine_3073_);
lean_ctor_set(v___x_3086_, 1, v_requestStream_3074_);
lean_ctor_set(v___x_3086_, 2, v_keepAliveTimeout_3075_);
lean_ctor_set(v___x_3086_, 3, v_currentTimeout_3076_);
lean_ctor_set(v___x_3086_, 4, v_headerTimeout_3077_);
lean_ctor_set(v___x_3086_, 5, v_response_3078_);
lean_ctor_set(v___x_3086_, 6, v_respStream_3079_);
lean_ctor_set(v___x_3086_, 7, v_expectData_3081_);
lean_ctor_set(v___x_3086_, 8, v_pendingHead_3082_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*9, v_requiresData_3080_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*9 + 1, v___x_3085_);
v___x_3087_ = lean_box(v___x_3085_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3091_, lean_object* v_requestStream_3092_, lean_object* v_keepAliveTimeout_3093_, lean_object* v_currentTimeout_3094_, lean_object* v_headerTimeout_3095_, lean_object* v_response_3096_, lean_object* v_respStream_3097_, lean_object* v_requiresData_3098_, lean_object* v_expectData_3099_, lean_object* v_pendingHead_3100_, lean_object* v_____r_3101_, lean_object* v___y_3102_){
_start:
{
uint8_t v_requiresData_boxed_3103_; lean_object* v_res_3104_; 
v_requiresData_boxed_3103_ = lean_unbox(v_requiresData_3098_);
v_res_3104_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3091_, v_requestStream_3092_, v_keepAliveTimeout_3093_, v_currentTimeout_3094_, v_headerTimeout_3095_, v_response_3096_, v_respStream_3097_, v_requiresData_boxed_3103_, v_expectData_3099_, v_pendingHead_3100_, v_____r_3101_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3105_, lean_object* v_body_3106_, lean_object* v___f_3107_, lean_object* v___f_3108_, lean_object* v_x_3109_){
_start:
{
if (lean_obj_tag(v_x_3109_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___f_3108_);
lean_dec_ref(v___f_3107_);
lean_dec(v_body_3106_);
lean_dec_ref(v_close_3105_);
v_a_3111_ = lean_ctor_get(v_x_3109_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v_x_3109_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v_x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; 
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
return v___x_3117_;
}
}
}
else
{
lean_object* v_a_3120_; uint8_t v___x_3121_; 
v_a_3120_ = lean_ctor_get(v_x_3109_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v_x_3109_, 1);
v___x_3121_ = lean_unbox(v_a_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; 
lean_dec_ref(v___f_3108_);
v___x_3122_ = lean_apply_2(v_close_3105_, v_body_3106_, lean_box(0));
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_unbox(v_a_3120_);
lean_dec(v_a_3120_);
v___x_3125_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3123_, v___x_3124_, v___x_3122_, v___f_3107_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v_a_3120_);
lean_dec_ref(v___f_3107_);
lean_dec(v_body_3106_);
lean_dec_ref(v_close_3105_);
v___x_3126_ = lean_box(0);
v___x_3127_ = lean_apply_2(v___f_3108_, v___x_3126_, lean_box(0));
return v___x_3127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3128_, lean_object* v_body_3129_, lean_object* v___f_3130_, lean_object* v___f_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3128_, v_body_3129_, v___f_3130_, v___f_3131_, v_x_3132_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3135_, lean_object* v_keepAliveTimeout_3136_, lean_object* v_currentTimeout_3137_, lean_object* v_headerTimeout_3138_, lean_object* v_response_3139_, uint8_t v_requiresData_3140_, lean_object* v_expectData_3141_, uint8_t v___x_3142_, lean_object* v_pendingHead_3143_, lean_object* v_____x_3144_){
_start:
{
lean_object* v_fst_3146_; lean_object* v_snd_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3158_; 
v_fst_3146_ = lean_ctor_get(v_____x_3144_, 0);
v_snd_3147_ = lean_ctor_get(v_____x_3144_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_____x_3144_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3149_ = v_____x_3144_;
v_isShared_3150_ = v_isSharedCheck_3158_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_snd_3147_);
lean_inc(v_fst_3146_);
lean_dec(v_____x_3144_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3158_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3151_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3151_, 0, v_fst_3146_);
lean_ctor_set(v___x_3151_, 1, v_requestStream_3135_);
lean_ctor_set(v___x_3151_, 2, v_keepAliveTimeout_3136_);
lean_ctor_set(v___x_3151_, 3, v_currentTimeout_3137_);
lean_ctor_set(v___x_3151_, 4, v_headerTimeout_3138_);
lean_ctor_set(v___x_3151_, 5, v_response_3139_);
lean_ctor_set(v___x_3151_, 6, v_snd_3147_);
lean_ctor_set(v___x_3151_, 7, v_expectData_3141_);
lean_ctor_set(v___x_3151_, 8, v_pendingHead_3143_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*9, v_requiresData_3140_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*9 + 1, v___x_3142_);
v___x_3152_ = lean_box(v___x_3142_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___x_3152_);
lean_ctor_set(v___x_3149_, 0, v___x_3151_);
v___x_3154_ = v___x_3149_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3159_, lean_object* v_keepAliveTimeout_3160_, lean_object* v_currentTimeout_3161_, lean_object* v_headerTimeout_3162_, lean_object* v_response_3163_, lean_object* v_requiresData_3164_, lean_object* v_expectData_3165_, lean_object* v___x_3166_, lean_object* v_pendingHead_3167_, lean_object* v_____x_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v_requiresData_boxed_3170_; uint8_t v___x_7758__boxed_3171_; lean_object* v_res_3172_; 
v_requiresData_boxed_3170_ = lean_unbox(v_requiresData_3164_);
v___x_7758__boxed_3171_ = lean_unbox(v___x_3166_);
v_res_3172_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3159_, v_keepAliveTimeout_3160_, v_currentTimeout_3161_, v_headerTimeout_3162_, v_response_3163_, v_requiresData_boxed_3170_, v_expectData_3165_, v___x_7758__boxed_3171_, v_pendingHead_3167_, v_____x_3168_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3173_, lean_object* v_x_3174_){
_start:
{
if (lean_obj_tag(v_x_3174_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v___f_3173_);
v_a_3176_ = lean_ctor_get(v_x_3174_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_x_3174_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3178_ = v_x_3174_;
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v_x_3174_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3186_; 
v_a_3185_ = lean_ctor_get(v_x_3174_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v_x_3174_, 1);
v___x_3186_ = lean_apply_2(v___f_3173_, v_a_3185_, lean_box(0));
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3187_, lean_object* v_x_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3187_, v_x_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3191_, lean_object* v___f_3192_, lean_object* v_inst_3193_, lean_object* v___f_3194_, lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3195_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v___f_3194_);
lean_dec_ref(v_inst_3193_);
lean_dec_ref(v___f_3192_);
v_a_3197_ = lean_ctor_get(v_x_3195_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_x_3195_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3199_ = v_x_3195_;
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v_x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v_snd_3207_; 
v_a_3206_ = lean_ctor_get(v_x_3195_, 0);
v_snd_3207_ = lean_ctor_get(v_a_3206_, 1);
if (lean_obj_tag(v_snd_3207_) == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec_ref(v___f_3194_);
lean_dec_ref(v_inst_3193_);
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_x_3195_);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3209_, v___x_3191_, v___x_3208_, v___f_3192_);
return v___x_3210_;
}
else
{
lean_object* v_fst_3211_; lean_object* v_val_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_inc_ref(v_snd_3207_);
lean_inc(v_a_3206_);
lean_dec_ref_known(v_x_3195_, 1);
lean_dec_ref(v___f_3192_);
v_fst_3211_ = lean_ctor_get(v_a_3206_, 0);
lean_inc(v_fst_3211_);
lean_dec(v_a_3206_);
v_val_3212_ = lean_ctor_get(v_snd_3207_, 0);
lean_inc(v_val_3212_);
lean_dec_ref_known(v_snd_3207_, 1);
v___x_3213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3193_, v_fst_3211_, v_val_3212_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3214_, v___x_3191_, v___x_3213_, v___f_3194_);
return v___x_3215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3216_, lean_object* v___f_3217_, lean_object* v_inst_3218_, lean_object* v___f_3219_, lean_object* v_x_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v___x_7824__boxed_3222_; lean_object* v_res_3223_; 
v___x_7824__boxed_3222_ = lean_unbox(v___x_3216_);
v_res_3223_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7824__boxed_3222_, v___f_3217_, v_inst_3218_, v___f_3219_, v_x_3220_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_state_3224_, lean_object* v_x_3225_){
_start:
{
if (lean_obj_tag(v_x_3225_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v_state_3224_);
v_a_3227_ = lean_ctor_get(v_x_3225_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3225_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3229_ = v_x_3225_;
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v_x_3225_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
}
else
{
lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3265_; 
v_isSharedCheck_3265_ = !lean_is_exclusive(v_x_3225_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v_x_3225_, 0);
lean_dec(v_unused_3266_);
v___x_3237_ = v_x_3225_;
v_isShared_3238_ = v_isSharedCheck_3265_;
goto v_resetjp_3236_;
}
else
{
lean_dec(v_x_3225_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3265_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_machine_3239_; lean_object* v_requestStream_3240_; lean_object* v_keepAliveTimeout_3241_; lean_object* v_currentTimeout_3242_; lean_object* v_headerTimeout_3243_; lean_object* v_response_3244_; lean_object* v_respStream_3245_; uint8_t v_requiresData_3246_; lean_object* v_expectData_3247_; lean_object* v_pendingHead_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3264_; 
v_machine_3239_ = lean_ctor_get(v_state_3224_, 0);
v_requestStream_3240_ = lean_ctor_get(v_state_3224_, 1);
v_keepAliveTimeout_3241_ = lean_ctor_get(v_state_3224_, 2);
v_currentTimeout_3242_ = lean_ctor_get(v_state_3224_, 3);
v_headerTimeout_3243_ = lean_ctor_get(v_state_3224_, 4);
v_response_3244_ = lean_ctor_get(v_state_3224_, 5);
v_respStream_3245_ = lean_ctor_get(v_state_3224_, 6);
v_requiresData_3246_ = lean_ctor_get_uint8(v_state_3224_, sizeof(void*)*9);
v_expectData_3247_ = lean_ctor_get(v_state_3224_, 7);
v_pendingHead_3248_ = lean_ctor_get(v_state_3224_, 8);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_state_3224_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3250_ = v_state_3224_;
v_isShared_3251_ = v_isSharedCheck_3264_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_pendingHead_3248_);
lean_inc(v_expectData_3247_);
lean_inc(v_respStream_3245_);
lean_inc(v_response_3244_);
lean_inc(v_headerTimeout_3243_);
lean_inc(v_currentTimeout_3242_);
lean_inc(v_keepAliveTimeout_3241_);
lean_inc(v_requestStream_3240_);
lean_inc(v_machine_3239_);
lean_dec(v_state_3224_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3264_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3256_; 
v___x_3252_ = lean_box(31);
v___x_3253_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3239_, v___x_3252_);
v___x_3254_ = 0;
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3253_);
v___x_3256_ = v___x_3250_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_requestStream_3240_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_keepAliveTimeout_3241_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_currentTimeout_3242_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_headerTimeout_3243_);
lean_ctor_set(v_reuseFailAlloc_3263_, 5, v_response_3244_);
lean_ctor_set(v_reuseFailAlloc_3263_, 6, v_respStream_3245_);
lean_ctor_set(v_reuseFailAlloc_3263_, 7, v_expectData_3247_);
lean_ctor_set(v_reuseFailAlloc_3263_, 8, v_pendingHead_3248_);
lean_ctor_set_uint8(v_reuseFailAlloc_3263_, sizeof(void*)*9, v_requiresData_3246_);
v___x_3256_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*9 + 1, v___x_3254_);
v___x_3257_ = lean_box(v___x_3254_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3258_);
v___x_3260_ = v___x_3237_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_state_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_state_3267_, v_x_3268_);
return v_res_3270_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3273_ = lean_mk_io_user_error(v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_handler_3276_, lean_object* v_config_3277_, lean_object* v_event_3278_, lean_object* v_state_3279_){
_start:
{
switch(lean_obj_tag(v_event_3278_))
{
case 0:
{
lean_object* v_x_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_handler_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
v_x_3281_ = lean_ctor_get(v_event_3278_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_event_3278_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3283_ = v_event_3278_;
v_isShared_3284_ = v_isSharedCheck_3388_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_x_3281_);
lean_dec(v_event_3278_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3388_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
if (lean_obj_tag(v_x_3281_) == 0)
{
lean_object* v_machine_3285_; lean_object* v_reader_3286_; lean_object* v_requestStream_3287_; lean_object* v_keepAliveTimeout_3288_; lean_object* v_currentTimeout_3289_; lean_object* v_headerTimeout_3290_; lean_object* v_response_3291_; lean_object* v_respStream_3292_; uint8_t v_requiresData_3293_; lean_object* v_expectData_3294_; uint8_t v_handlerDispatched_3295_; lean_object* v_pendingHead_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v_config_3277_);
v_machine_3285_ = lean_ctor_get(v_state_3279_, 0);
lean_inc_ref(v_machine_3285_);
v_reader_3286_ = lean_ctor_get(v_machine_3285_, 0);
lean_inc_ref(v_reader_3286_);
v_requestStream_3287_ = lean_ctor_get(v_state_3279_, 1);
v_keepAliveTimeout_3288_ = lean_ctor_get(v_state_3279_, 2);
v_currentTimeout_3289_ = lean_ctor_get(v_state_3279_, 3);
v_headerTimeout_3290_ = lean_ctor_get(v_state_3279_, 4);
v_response_3291_ = lean_ctor_get(v_state_3279_, 5);
v_respStream_3292_ = lean_ctor_get(v_state_3279_, 6);
v_requiresData_3293_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3294_ = lean_ctor_get(v_state_3279_, 7);
v_handlerDispatched_3295_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9 + 1);
v_pendingHead_3296_ = lean_ctor_get(v_state_3279_, 8);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_state_3279_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; 
v_unused_3340_ = lean_ctor_get(v_state_3279_, 0);
lean_dec(v_unused_3340_);
v___x_3298_ = v_state_3279_;
v_isShared_3299_ = v_isSharedCheck_3339_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_pendingHead_3296_);
lean_inc(v_expectData_3294_);
lean_inc(v_respStream_3292_);
lean_inc(v_response_3291_);
lean_inc(v_headerTimeout_3290_);
lean_inc(v_currentTimeout_3289_);
lean_inc(v_keepAliveTimeout_3288_);
lean_inc(v_requestStream_3287_);
lean_dec(v_state_3279_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3339_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v_writer_3300_; lean_object* v_config_3301_; lean_object* v_events_3302_; lean_object* v_error_3303_; lean_object* v_instant_3304_; uint8_t v_keepAlive_3305_; uint8_t v_forcedFlush_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3337_; 
v_writer_3300_ = lean_ctor_get(v_machine_3285_, 1);
v_config_3301_ = lean_ctor_get(v_machine_3285_, 2);
v_events_3302_ = lean_ctor_get(v_machine_3285_, 3);
v_error_3303_ = lean_ctor_get(v_machine_3285_, 4);
v_instant_3304_ = lean_ctor_get(v_machine_3285_, 5);
v_keepAlive_3305_ = lean_ctor_get_uint8(v_machine_3285_, sizeof(void*)*6);
v_forcedFlush_3306_ = lean_ctor_get_uint8(v_machine_3285_, sizeof(void*)*6 + 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_machine_3285_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v_machine_3285_, 0);
lean_dec(v_unused_3338_);
v___x_3308_ = v_machine_3285_;
v_isShared_3309_ = v_isSharedCheck_3337_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_instant_3304_);
lean_inc(v_error_3303_);
lean_inc(v_events_3302_);
lean_inc(v_config_3301_);
lean_inc(v_writer_3300_);
lean_dec(v_machine_3285_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3337_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_state_3310_; lean_object* v_input_3311_; lean_object* v_messageHead_3312_; lean_object* v_messageCount_3313_; lean_object* v_bodyBytesRead_3314_; lean_object* v_headerBytesRead_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3336_; 
v_state_3310_ = lean_ctor_get(v_reader_3286_, 0);
v_input_3311_ = lean_ctor_get(v_reader_3286_, 1);
v_messageHead_3312_ = lean_ctor_get(v_reader_3286_, 2);
v_messageCount_3313_ = lean_ctor_get(v_reader_3286_, 3);
v_bodyBytesRead_3314_ = lean_ctor_get(v_reader_3286_, 4);
v_headerBytesRead_3315_ = lean_ctor_get(v_reader_3286_, 5);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_reader_3286_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3317_ = v_reader_3286_;
v_isShared_3318_ = v_isSharedCheck_3336_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_headerBytesRead_3315_);
lean_inc(v_bodyBytesRead_3314_);
lean_inc(v_messageCount_3313_);
lean_inc(v_messageHead_3312_);
lean_inc(v_input_3311_);
lean_inc(v_state_3310_);
lean_dec(v_reader_3286_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3336_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
uint8_t v___x_3319_; lean_object* v___x_3321_; 
v___x_3319_ = 1;
if (v_isShared_3318_ == 0)
{
v___x_3321_ = v___x_3317_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_state_3310_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_input_3311_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_messageHead_3312_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_messageCount_3313_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_bodyBytesRead_3314_);
lean_ctor_set(v_reuseFailAlloc_3335_, 5, v_headerBytesRead_3315_);
v___x_3321_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
uint8_t v___x_3322_; lean_object* v___x_3324_; 
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*6, v___x_3319_);
v___x_3322_ = 0;
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3321_);
v___x_3324_ = v___x_3308_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_writer_3300_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_config_3301_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_events_3302_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_error_3303_);
lean_ctor_set(v_reuseFailAlloc_3334_, 5, v_instant_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*6, v_keepAlive_3305_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*6 + 1, v_forcedFlush_3306_);
v___x_3324_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*6 + 2, v___x_3322_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3324_);
v___x_3326_ = v___x_3298_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_requestStream_3287_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_keepAliveTimeout_3288_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v_currentTimeout_3289_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v_headerTimeout_3290_);
lean_ctor_set(v_reuseFailAlloc_3333_, 5, v_response_3291_);
lean_ctor_set(v_reuseFailAlloc_3333_, 6, v_respStream_3292_);
lean_ctor_set(v_reuseFailAlloc_3333_, 7, v_expectData_3294_);
lean_ctor_set(v_reuseFailAlloc_3333_, 8, v_pendingHead_3296_);
lean_ctor_set_uint8(v_reuseFailAlloc_3333_, sizeof(void*)*9, v_requiresData_3293_);
lean_ctor_set_uint8(v_reuseFailAlloc_3333_, sizeof(void*)*9 + 1, v_handlerDispatched_3295_);
v___x_3326_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3327_ = lean_box(v___x_3322_);
v___x_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 1);
lean_ctor_set(v___x_3283_, 0, v___x_3328_);
v___x_3330_ = v___x_3283_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3328_);
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
}
}
}
}
}
else
{
lean_object* v_val_3341_; lean_object* v_machine_3342_; lean_object* v_requestStream_3343_; lean_object* v_keepAliveTimeout_3344_; lean_object* v_currentTimeout_3345_; lean_object* v_response_3346_; lean_object* v_respStream_3347_; uint8_t v_requiresData_3348_; lean_object* v_expectData_3349_; uint8_t v_handlerDispatched_3350_; lean_object* v_pendingHead_3351_; lean_object* v___f_3352_; 
lean_del_object(v___x_3283_);
v_val_3341_ = lean_ctor_get(v_x_3281_, 0);
lean_inc_n(v_val_3341_, 2);
lean_dec_ref_known(v_x_3281_, 1);
v_machine_3342_ = lean_ctor_get(v_state_3279_, 0);
v_requestStream_3343_ = lean_ctor_get(v_state_3279_, 1);
v_keepAliveTimeout_3344_ = lean_ctor_get(v_state_3279_, 2);
lean_inc(v_keepAliveTimeout_3344_);
v_currentTimeout_3345_ = lean_ctor_get(v_state_3279_, 3);
v_response_3346_ = lean_ctor_get(v_state_3279_, 5);
v_respStream_3347_ = lean_ctor_get(v_state_3279_, 6);
v_requiresData_3348_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3349_ = lean_ctor_get(v_state_3279_, 7);
v_handlerDispatched_3350_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9 + 1);
v_pendingHead_3351_ = lean_ctor_get(v_state_3279_, 8);
v___f_3352_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3352_, 0, v_val_3341_);
if (lean_obj_tag(v_keepAliveTimeout_3344_) == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec_ref(v___f_3352_);
lean_dec_ref(v_config_3277_);
v___x_3353_ = lean_box(0);
v___x_3354_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3341_, v___x_3353_, v_state_3279_);
return v___x_3354_;
}
else
{
lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3386_; 
lean_inc(v_pendingHead_3351_);
lean_inc(v_expectData_3349_);
lean_inc(v_respStream_3347_);
lean_inc_ref(v_response_3346_);
lean_inc(v_currentTimeout_3345_);
lean_inc_ref(v_requestStream_3343_);
lean_inc_ref(v_machine_3342_);
lean_dec(v_val_3341_);
lean_dec_ref(v_state_3279_);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_keepAliveTimeout_3344_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_keepAliveTimeout_3344_, 0);
lean_dec(v_unused_3387_);
v___x_3356_ = v_keepAliveTimeout_3344_;
v_isShared_3357_ = v_isSharedCheck_3386_;
goto v_resetjp_3355_;
}
else
{
lean_dec(v_keepAliveTimeout_3344_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3386_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v_val_3362_; lean_object* v___x_3369_; 
v___x_3358_ = lean_box(v_requiresData_3348_);
v___x_3359_ = lean_box(v_handlerDispatched_3350_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3360_, 0, v_config_3277_);
lean_closure_set(v___f_3360_, 1, v_machine_3342_);
lean_closure_set(v___f_3360_, 2, v_requestStream_3343_);
lean_closure_set(v___f_3360_, 3, v_currentTimeout_3345_);
lean_closure_set(v___f_3360_, 4, v_response_3346_);
lean_closure_set(v___f_3360_, 5, v_respStream_3347_);
lean_closure_set(v___f_3360_, 6, v___x_3358_);
lean_closure_set(v___f_3360_, 7, v_expectData_3349_);
lean_closure_set(v___f_3360_, 8, v___x_3359_);
lean_closure_set(v___f_3360_, 9, v_pendingHead_3351_);
lean_closure_set(v___f_3360_, 10, v___f_3352_);
v___x_3369_ = lean_get_current_time();
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set_tag(v___x_3372_, 1);
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
v_val_3362_ = v___x_3375_;
goto v___jp_3361_;
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
v_a_3378_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3369_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3369_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 0);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
v_val_3362_ = v___x_3383_;
goto v___jp_3361_;
}
}
}
v___jp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set_tag(v___x_3356_, 0);
lean_ctor_set(v___x_3356_, 0, v_val_3362_);
v___x_3364_ = v___x_3356_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_val_3362_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = 0;
v___x_3367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3365_, v___x_3366_, v___x_3364_, v___f_3360_);
return v___x_3367_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_config_3277_);
lean_dec(v_handler_3276_);
lean_dec_ref(v_inst_3274_);
v_x_3389_ = lean_ctor_get(v_event_3278_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_event_3278_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3391_ = v_event_3278_;
v_isShared_3392_ = v_isSharedCheck_3504_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_x_3389_);
lean_dec(v_event_3278_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3504_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
if (lean_obj_tag(v_x_3389_) == 0)
{
lean_object* v_machine_3393_; lean_object* v_requestStream_3394_; lean_object* v_keepAliveTimeout_3395_; lean_object* v_currentTimeout_3396_; lean_object* v_headerTimeout_3397_; lean_object* v_response_3398_; lean_object* v_respStream_3399_; uint8_t v_requiresData_3400_; lean_object* v_expectData_3401_; uint8_t v_handlerDispatched_3402_; lean_object* v_pendingHead_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___f_3406_; 
lean_del_object(v___x_3391_);
v_machine_3393_ = lean_ctor_get(v_state_3279_, 0);
lean_inc_ref_n(v_machine_3393_, 2);
v_requestStream_3394_ = lean_ctor_get(v_state_3279_, 1);
lean_inc_ref_n(v_requestStream_3394_, 2);
v_keepAliveTimeout_3395_ = lean_ctor_get(v_state_3279_, 2);
lean_inc_n(v_keepAliveTimeout_3395_, 2);
v_currentTimeout_3396_ = lean_ctor_get(v_state_3279_, 3);
lean_inc_n(v_currentTimeout_3396_, 2);
v_headerTimeout_3397_ = lean_ctor_get(v_state_3279_, 4);
lean_inc_n(v_headerTimeout_3397_, 2);
v_response_3398_ = lean_ctor_get(v_state_3279_, 5);
lean_inc_ref_n(v_response_3398_, 2);
v_respStream_3399_ = lean_ctor_get(v_state_3279_, 6);
lean_inc(v_respStream_3399_);
v_requiresData_3400_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3401_ = lean_ctor_get(v_state_3279_, 7);
lean_inc_n(v_expectData_3401_, 2);
v_handlerDispatched_3402_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9 + 1);
v_pendingHead_3403_ = lean_ctor_get(v_state_3279_, 8);
lean_inc_n(v_pendingHead_3403_, 2);
lean_dec_ref(v_state_3279_);
v___x_3404_ = lean_box(v_requiresData_3400_);
v___x_3405_ = lean_box(v_handlerDispatched_3402_);
v___f_3406_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3406_, 0, v_machine_3393_);
lean_closure_set(v___f_3406_, 1, v_requestStream_3394_);
lean_closure_set(v___f_3406_, 2, v_keepAliveTimeout_3395_);
lean_closure_set(v___f_3406_, 3, v_currentTimeout_3396_);
lean_closure_set(v___f_3406_, 4, v_headerTimeout_3397_);
lean_closure_set(v___f_3406_, 5, v_response_3398_);
lean_closure_set(v___f_3406_, 6, v___x_3404_);
lean_closure_set(v___f_3406_, 7, v_expectData_3401_);
lean_closure_set(v___f_3406_, 8, v___x_3405_);
lean_closure_set(v___f_3406_, 9, v_pendingHead_3403_);
if (lean_obj_tag(v_respStream_3399_) == 1)
{
lean_object* v_val_3407_; lean_object* v_close_3408_; lean_object* v_isClosed_3409_; lean_object* v___x_3410_; lean_object* v___f_3411_; lean_object* v___f_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v_pendingHead_3403_);
lean_dec(v_expectData_3401_);
lean_dec_ref(v_response_3398_);
lean_dec(v_headerTimeout_3397_);
lean_dec(v_currentTimeout_3396_);
lean_dec(v_keepAliveTimeout_3395_);
lean_dec_ref(v_requestStream_3394_);
lean_dec_ref(v_machine_3393_);
v_val_3407_ = lean_ctor_get(v_respStream_3399_, 0);
lean_inc_n(v_val_3407_, 2);
lean_dec_ref_known(v_respStream_3399_, 1);
v_close_3408_ = lean_ctor_get(v_inst_3275_, 1);
lean_inc_ref(v_close_3408_);
v_isClosed_3409_ = lean_ctor_get(v_inst_3275_, 2);
lean_inc_ref(v_isClosed_3409_);
lean_dec_ref(v_inst_3275_);
v___x_3410_ = lean_apply_2(v_isClosed_3409_, v_val_3407_, lean_box(0));
lean_inc_ref(v___f_3406_);
v___f_3411_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3411_, 0, v___f_3406_);
v___f_3412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3412_, 0, v_close_3408_);
lean_closure_set(v___f_3412_, 1, v_val_3407_);
lean_closure_set(v___f_3412_, 2, v___f_3411_);
lean_closure_set(v___f_3412_, 3, v___f_3406_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = 0;
v___x_3415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3413_, v___x_3414_, v___x_3410_, v___f_3412_);
return v___x_3415_;
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec_ref(v___f_3406_);
lean_dec(v_respStream_3399_);
lean_dec_ref(v_inst_3275_);
v___x_3416_ = lean_box(0);
v___x_3417_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3393_, v_requestStream_3394_, v_keepAliveTimeout_3395_, v_currentTimeout_3396_, v_headerTimeout_3397_, v_response_3398_, v_requiresData_3400_, v_expectData_3401_, v_handlerDispatched_3402_, v_pendingHead_3403_, v___x_3416_);
return v___x_3417_;
}
}
else
{
lean_object* v_val_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_inst_3275_);
v_val_3418_ = lean_ctor_get(v_x_3389_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_x_3389_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3420_ = v_x_3389_;
v_isShared_3421_ = v_isSharedCheck_3503_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_val_3418_);
lean_dec(v_x_3389_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3503_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_machine_3422_; lean_object* v_requestStream_3423_; lean_object* v_keepAliveTimeout_3424_; lean_object* v_currentTimeout_3425_; lean_object* v_headerTimeout_3426_; lean_object* v_response_3427_; lean_object* v_respStream_3428_; uint8_t v_requiresData_3429_; lean_object* v_expectData_3430_; uint8_t v_handlerDispatched_3431_; lean_object* v_pendingHead_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3502_; 
v_machine_3422_ = lean_ctor_get(v_state_3279_, 0);
v_requestStream_3423_ = lean_ctor_get(v_state_3279_, 1);
v_keepAliveTimeout_3424_ = lean_ctor_get(v_state_3279_, 2);
v_currentTimeout_3425_ = lean_ctor_get(v_state_3279_, 3);
v_headerTimeout_3426_ = lean_ctor_get(v_state_3279_, 4);
v_response_3427_ = lean_ctor_get(v_state_3279_, 5);
v_respStream_3428_ = lean_ctor_get(v_state_3279_, 6);
v_requiresData_3429_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3430_ = lean_ctor_get(v_state_3279_, 7);
v_handlerDispatched_3431_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9 + 1);
v_pendingHead_3432_ = lean_ctor_get(v_state_3279_, 8);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_state_3279_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3434_ = v_state_3279_;
v_isShared_3435_ = v_isSharedCheck_3502_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_pendingHead_3432_);
lean_inc(v_expectData_3430_);
lean_inc(v_respStream_3428_);
lean_inc(v_response_3427_);
lean_inc(v_headerTimeout_3426_);
lean_inc(v_currentTimeout_3425_);
lean_inc(v_keepAliveTimeout_3424_);
lean_inc(v_requestStream_3423_);
lean_inc(v_machine_3422_);
lean_dec(v_state_3279_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3502_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___y_3437_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v___x_3450_ = lean_unsigned_to_nat(1u);
v___x_3451_ = lean_mk_empty_array_with_capacity(v___x_3450_);
v___x_3452_ = lean_array_push(v___x_3451_, v_val_3418_);
v___x_3453_ = lean_array_get_size(v___x_3452_);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_nat_dec_eq(v___x_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v_reader_3456_; lean_object* v_writer_3457_; lean_object* v_config_3458_; lean_object* v_events_3459_; lean_object* v_error_3460_; lean_object* v_instant_3461_; uint8_t v_keepAlive_3462_; uint8_t v_forcedFlush_3463_; uint8_t v_pullBodyStalled_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3501_; 
v_reader_3456_ = lean_ctor_get(v_machine_3422_, 0);
v_writer_3457_ = lean_ctor_get(v_machine_3422_, 1);
v_config_3458_ = lean_ctor_get(v_machine_3422_, 2);
v_events_3459_ = lean_ctor_get(v_machine_3422_, 3);
v_error_3460_ = lean_ctor_get(v_machine_3422_, 4);
v_instant_3461_ = lean_ctor_get(v_machine_3422_, 5);
v_keepAlive_3462_ = lean_ctor_get_uint8(v_machine_3422_, sizeof(void*)*6);
v_forcedFlush_3463_ = lean_ctor_get_uint8(v_machine_3422_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3464_ = lean_ctor_get_uint8(v_machine_3422_, sizeof(void*)*6 + 2);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_machine_3422_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3466_ = v_machine_3422_;
v_isShared_3467_ = v_isSharedCheck_3501_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_instant_3461_);
lean_inc(v_error_3460_);
lean_inc(v_events_3459_);
lean_inc(v_config_3458_);
lean_inc(v_writer_3457_);
lean_inc(v_reader_3456_);
lean_dec(v_machine_3422_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3501_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___y_3469_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3491_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3492_ = lean_nat_dec_lt(v___x_3454_, v___x_3453_);
if (v___x_3492_ == 0)
{
v___y_3469_ = v___x_3454_;
goto v___jp_3468_;
}
else
{
lean_object* v___f_3493_; uint8_t v___x_3494_; 
v___f_3493_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3494_ = lean_nat_dec_le(v___x_3453_, v___x_3453_);
if (v___x_3494_ == 0)
{
if (v___x_3492_ == 0)
{
v___y_3469_ = v___x_3454_;
goto v___jp_3468_;
}
else
{
size_t v___x_3495_; size_t v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = ((size_t)0ULL);
v___x_3496_ = lean_usize_of_nat(v___x_3453_);
lean_inc_ref(v___x_3452_);
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3491_, v___f_3493_, v___x_3452_, v___x_3495_, v___x_3496_, v___x_3454_);
v___y_3469_ = v___x_3497_;
goto v___jp_3468_;
}
}
else
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = lean_usize_of_nat(v___x_3453_);
lean_inc_ref(v___x_3452_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3491_, v___f_3493_, v___x_3452_, v___x_3498_, v___x_3499_, v___x_3454_);
v___y_3469_ = v___x_3500_;
goto v___jp_3468_;
}
}
v___jp_3468_:
{
lean_object* v_userData_3470_; lean_object* v_outputData_3471_; lean_object* v_state_3472_; lean_object* v_knownSize_3473_; lean_object* v_messageHead_3474_; uint8_t v_sentMessage_3475_; uint8_t v_userClosedBody_3476_; uint8_t v_omitBody_3477_; lean_object* v_userDataBytes_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3490_; 
v_userData_3470_ = lean_ctor_get(v_writer_3457_, 0);
v_outputData_3471_ = lean_ctor_get(v_writer_3457_, 1);
v_state_3472_ = lean_ctor_get(v_writer_3457_, 2);
v_knownSize_3473_ = lean_ctor_get(v_writer_3457_, 3);
v_messageHead_3474_ = lean_ctor_get(v_writer_3457_, 4);
v_sentMessage_3475_ = lean_ctor_get_uint8(v_writer_3457_, sizeof(void*)*6);
v_userClosedBody_3476_ = lean_ctor_get_uint8(v_writer_3457_, sizeof(void*)*6 + 1);
v_omitBody_3477_ = lean_ctor_get_uint8(v_writer_3457_, sizeof(void*)*6 + 2);
v_userDataBytes_3478_ = lean_ctor_get(v_writer_3457_, 5);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_writer_3457_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3480_ = v_writer_3457_;
v_isShared_3481_ = v_isSharedCheck_3490_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_userDataBytes_3478_);
lean_inc(v_messageHead_3474_);
lean_inc(v_knownSize_3473_);
lean_inc(v_state_3472_);
lean_inc(v_outputData_3471_);
lean_inc(v_userData_3470_);
lean_dec(v_writer_3457_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3490_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3482_ = l_Array_append___redArg(v_userData_3470_, v___x_3452_);
lean_dec_ref(v___x_3452_);
v___x_3483_ = lean_nat_add(v_userDataBytes_3478_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec(v_userDataBytes_3478_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 5, v___x_3483_);
lean_ctor_set(v___x_3480_, 0, v___x_3482_);
v___x_3485_ = v___x_3480_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_outputData_3471_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_state_3472_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_knownSize_3473_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v_messageHead_3474_);
lean_ctor_set(v_reuseFailAlloc_3489_, 5, v___x_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*6, v_sentMessage_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*6 + 1, v_userClosedBody_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*6 + 2, v_omitBody_3477_);
v___x_3485_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3487_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v___x_3485_);
v___x_3487_ = v___x_3466_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_reader_3456_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_config_3458_);
lean_ctor_set(v_reuseFailAlloc_3488_, 3, v_events_3459_);
lean_ctor_set(v_reuseFailAlloc_3488_, 4, v_error_3460_);
lean_ctor_set(v_reuseFailAlloc_3488_, 5, v_instant_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*6, v_keepAlive_3462_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*6 + 1, v_forcedFlush_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*6 + 2, v_pullBodyStalled_3464_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
v___y_3437_ = v___x_3487_;
goto v___jp_3436_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3452_);
v___y_3437_ = v_machine_3422_;
goto v___jp_3436_;
}
v___jp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___y_3437_);
v___x_3439_ = v___x_3434_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___y_3437_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_requestStream_3423_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_keepAliveTimeout_3424_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_currentTimeout_3425_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_headerTimeout_3426_);
lean_ctor_set(v_reuseFailAlloc_3449_, 5, v_response_3427_);
lean_ctor_set(v_reuseFailAlloc_3449_, 6, v_respStream_3428_);
lean_ctor_set(v_reuseFailAlloc_3449_, 7, v_expectData_3430_);
lean_ctor_set(v_reuseFailAlloc_3449_, 8, v_pendingHead_3432_);
lean_ctor_set_uint8(v_reuseFailAlloc_3449_, sizeof(void*)*9, v_requiresData_3429_);
lean_ctor_set_uint8(v_reuseFailAlloc_3449_, sizeof(void*)*9 + 1, v_handlerDispatched_3431_);
v___x_3439_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3440_ = 0;
v___x_3441_ = lean_box(v___x_3440_);
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3439_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3442_);
v___x_3444_ = v___x_3420_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3444_);
v___x_3446_ = v___x_3391_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
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
uint8_t v_x_3505_; 
lean_dec_ref(v_config_3277_);
lean_dec_ref(v_inst_3275_);
v_x_3505_ = lean_ctor_get_uint8(v_event_3278_, 0);
lean_dec_ref_known(v_event_3278_, 0);
if (v_x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec(v_handler_3276_);
lean_dec_ref(v_inst_3274_);
v___x_3506_ = lean_box(v_x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v_state_3279_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
return v___x_3509_;
}
else
{
lean_object* v_machine_3510_; lean_object* v_requestStream_3511_; lean_object* v_keepAliveTimeout_3512_; lean_object* v_currentTimeout_3513_; lean_object* v_headerTimeout_3514_; lean_object* v_response_3515_; lean_object* v_respStream_3516_; uint8_t v_requiresData_3517_; lean_object* v_expectData_3518_; uint8_t v_handlerDispatched_3519_; lean_object* v_pendingHead_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3570_; 
v_machine_3510_ = lean_ctor_get(v_state_3279_, 0);
v_requestStream_3511_ = lean_ctor_get(v_state_3279_, 1);
v_keepAliveTimeout_3512_ = lean_ctor_get(v_state_3279_, 2);
v_currentTimeout_3513_ = lean_ctor_get(v_state_3279_, 3);
v_headerTimeout_3514_ = lean_ctor_get(v_state_3279_, 4);
v_response_3515_ = lean_ctor_get(v_state_3279_, 5);
v_respStream_3516_ = lean_ctor_get(v_state_3279_, 6);
v_requiresData_3517_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3518_ = lean_ctor_get(v_state_3279_, 7);
v_handlerDispatched_3519_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9 + 1);
v_pendingHead_3520_ = lean_ctor_get(v_state_3279_, 8);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_state_3279_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3522_ = v_state_3279_;
v_isShared_3523_ = v_isSharedCheck_3570_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_pendingHead_3520_);
lean_inc(v_expectData_3518_);
lean_inc(v_respStream_3516_);
lean_inc(v_response_3515_);
lean_inc(v_headerTimeout_3514_);
lean_inc(v_currentTimeout_3513_);
lean_inc(v_keepAliveTimeout_3512_);
lean_inc(v_requestStream_3511_);
lean_inc(v_machine_3510_);
lean_dec(v_state_3279_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3570_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v_fst_3526_; lean_object* v_snd_3527_; lean_object* v_reader_3528_; lean_object* v_writer_3529_; lean_object* v_config_3530_; lean_object* v_events_3531_; lean_object* v_error_3532_; lean_object* v_instant_3533_; uint8_t v_keepAlive_3534_; uint8_t v_forcedFlush_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3569_; 
v___x_3524_ = 0;
v___x_3525_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3524_, v_machine_3510_);
v_fst_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_fst_3526_);
v_snd_3527_ = lean_ctor_get(v___x_3525_, 1);
lean_inc(v_snd_3527_);
lean_dec_ref(v___x_3525_);
v_reader_3528_ = lean_ctor_get(v_fst_3526_, 0);
v_writer_3529_ = lean_ctor_get(v_fst_3526_, 1);
v_config_3530_ = lean_ctor_get(v_fst_3526_, 2);
v_events_3531_ = lean_ctor_get(v_fst_3526_, 3);
v_error_3532_ = lean_ctor_get(v_fst_3526_, 4);
v_instant_3533_ = lean_ctor_get(v_fst_3526_, 5);
v_keepAlive_3534_ = lean_ctor_get_uint8(v_fst_3526_, sizeof(void*)*6);
v_forcedFlush_3535_ = lean_ctor_get_uint8(v_fst_3526_, sizeof(void*)*6 + 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_fst_3526_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3537_ = v_fst_3526_;
v_isShared_3538_ = v_isSharedCheck_3569_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_instant_3533_);
lean_inc(v_error_3532_);
lean_inc(v_events_3531_);
lean_inc(v_config_3530_);
lean_inc(v_writer_3529_);
lean_inc(v_reader_3528_);
lean_dec(v_fst_3526_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3569_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___f_3539_; lean_object* v___f_3540_; uint8_t v___y_3542_; 
v___f_3539_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3539_, 0, v_inst_3274_);
lean_closure_set(v___f_3539_, 1, v_handler_3276_);
v___f_3540_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3527_) == 0)
{
uint8_t v_sentMessage_3565_; 
v_sentMessage_3565_ = lean_ctor_get_uint8(v_writer_3529_, sizeof(void*)*6);
if (v_sentMessage_3565_ == 0)
{
lean_object* v_state_3566_; 
v_state_3566_ = lean_ctor_get(v_reader_3528_, 0);
if (lean_obj_tag(v_state_3566_) == 2)
{
v___y_3542_ = v_x_3505_;
goto v___jp_3541_;
}
else
{
v___y_3542_ = v_sentMessage_3565_;
goto v___jp_3541_;
}
}
else
{
uint8_t v___x_3567_; 
v___x_3567_ = 0;
v___y_3542_ = v___x_3567_;
goto v___jp_3541_;
}
}
else
{
uint8_t v___x_3568_; 
v___x_3568_ = 0;
v___y_3542_ = v___x_3568_;
goto v___jp_3541_;
}
v___jp_3541_:
{
lean_object* v___x_3544_; 
if (v_isShared_3538_ == 0)
{
v___x_3544_ = v___x_3537_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_reader_3528_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_writer_3529_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_config_3530_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_events_3531_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_error_3532_);
lean_ctor_set(v_reuseFailAlloc_3564_, 5, v_instant_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*6, v_keepAlive_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*6 + 1, v_forcedFlush_3535_);
v___x_3544_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v_st_3546_; 
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*6 + 2, v___y_3542_);
lean_inc_ref(v_requestStream_3511_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3544_);
v_st_3546_ = v___x_3522_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_requestStream_3511_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_keepAliveTimeout_3512_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_currentTimeout_3513_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_headerTimeout_3514_);
lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_response_3515_);
lean_ctor_set(v_reuseFailAlloc_3563_, 6, v_respStream_3516_);
lean_ctor_set(v_reuseFailAlloc_3563_, 7, v_expectData_3518_);
lean_ctor_set(v_reuseFailAlloc_3563_, 8, v_pendingHead_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*9, v_requiresData_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*9 + 1, v_handlerDispatched_3519_);
v_st_3546_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___f_3547_; 
lean_inc_ref(v_st_3546_);
v___f_3547_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3547_, 0, v_st_3546_);
if (lean_obj_tag(v_snd_3527_) == 1)
{
lean_object* v_val_3548_; uint8_t v_final_3549_; uint8_t v_incomplete_3550_; lean_object* v_chunk_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___f_3556_; lean_object* v___f_3557_; lean_object* v___x_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; 
lean_dec_ref(v_st_3546_);
v_val_3548_ = lean_ctor_get(v_snd_3527_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v_snd_3527_, 1);
v_final_3549_ = lean_ctor_get_uint8(v_val_3548_, sizeof(void*)*1);
v_incomplete_3550_ = lean_ctor_get_uint8(v_val_3548_, sizeof(void*)*1 + 1);
v_chunk_3551_ = lean_ctor_get(v_val_3548_, 0);
lean_inc_ref(v_chunk_3551_);
lean_dec(v_val_3548_);
lean_inc_ref_n(v_requestStream_3511_, 2);
v___x_3552_ = l_Std_Http_Body_Stream_send(v_requestStream_3511_, v_chunk_3551_, v_incomplete_3550_);
v___x_3553_ = lean_unsigned_to_nat(0u);
v___x_3554_ = 0;
v___x_3555_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3553_, v___x_3554_, v___x_3552_, v___f_3539_);
lean_inc_ref_n(v___f_3547_, 2);
v___f_3556_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3556_, 0, v___f_3547_);
v___f_3557_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3557_, 0, v_requestStream_3511_);
lean_closure_set(v___f_3557_, 1, v___f_3556_);
lean_closure_set(v___f_3557_, 2, v___f_3547_);
v___x_3558_ = lean_box(v_final_3549_);
v___f_3559_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3559_, 0, v___x_3558_);
lean_closure_set(v___f_3559_, 1, v___f_3547_);
lean_closure_set(v___f_3559_, 2, v___f_3540_);
lean_closure_set(v___f_3559_, 3, v_requestStream_3511_);
lean_closure_set(v___f_3559_, 4, v___f_3557_);
v___x_3560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3553_, v___x_3554_, v___x_3555_, v___f_3559_);
return v___x_3560_;
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec_ref(v___f_3547_);
lean_dec_ref(v___f_3539_);
lean_dec(v_snd_3527_);
lean_dec_ref(v_requestStream_3511_);
v___x_3561_ = lean_box(0);
v___x_3562_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3546_, v___x_3561_);
return v___x_3562_;
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
lean_object* v_x_3571_; 
v_x_3571_ = lean_ctor_get(v_event_3278_, 0);
lean_inc_ref(v_x_3571_);
lean_dec_ref_known(v_event_3278_, 1);
if (lean_obj_tag(v_x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v_onFailure_3573_; lean_object* v___x_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v_config_3277_);
lean_dec_ref(v_inst_3275_);
v_a_3572_ = lean_ctor_get(v_x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v_x_3571_, 1);
v_onFailure_3573_ = lean_ctor_get(v_inst_3274_, 2);
lean_inc_ref(v_onFailure_3573_);
lean_dec_ref(v_inst_3274_);
v___x_3574_ = lean_apply_3(v_onFailure_3573_, v_handler_3276_, v_a_3572_, lean_box(0));
v___f_3575_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3575_, 0, v_state_3279_);
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = 0;
v___x_3578_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3576_, v___x_3577_, v___x_3574_, v___f_3575_);
return v___x_3578_;
}
else
{
lean_object* v_machine_3579_; lean_object* v_reader_3580_; lean_object* v_state_3581_; 
lean_dec(v_handler_3276_);
lean_dec_ref(v_inst_3274_);
v_machine_3579_ = lean_ctor_get(v_state_3279_, 0);
lean_inc_ref(v_machine_3579_);
v_reader_3580_ = lean_ctor_get(v_machine_3579_, 0);
v_state_3581_ = lean_ctor_get(v_reader_3580_, 0);
if (lean_obj_tag(v_state_3581_) == 7)
{
lean_object* v_a_3582_; lean_object* v_requestStream_3583_; lean_object* v_keepAliveTimeout_3584_; lean_object* v_currentTimeout_3585_; lean_object* v_headerTimeout_3586_; lean_object* v_response_3587_; lean_object* v_respStream_3588_; uint8_t v_requiresData_3589_; lean_object* v_expectData_3590_; lean_object* v_pendingHead_3591_; lean_object* v_close_3592_; lean_object* v_isClosed_3593_; lean_object* v_body_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___f_3597_; lean_object* v___f_3598_; lean_object* v___f_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; lean_object* v___x_3602_; 
lean_dec_ref(v_config_3277_);
v_a_3582_ = lean_ctor_get(v_x_3571_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v_x_3571_, 1);
v_requestStream_3583_ = lean_ctor_get(v_state_3279_, 1);
lean_inc_ref(v_requestStream_3583_);
v_keepAliveTimeout_3584_ = lean_ctor_get(v_state_3279_, 2);
lean_inc(v_keepAliveTimeout_3584_);
v_currentTimeout_3585_ = lean_ctor_get(v_state_3279_, 3);
lean_inc(v_currentTimeout_3585_);
v_headerTimeout_3586_ = lean_ctor_get(v_state_3279_, 4);
lean_inc(v_headerTimeout_3586_);
v_response_3587_ = lean_ctor_get(v_state_3279_, 5);
lean_inc_ref(v_response_3587_);
v_respStream_3588_ = lean_ctor_get(v_state_3279_, 6);
lean_inc(v_respStream_3588_);
v_requiresData_3589_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3590_ = lean_ctor_get(v_state_3279_, 7);
lean_inc(v_expectData_3590_);
v_pendingHead_3591_ = lean_ctor_get(v_state_3279_, 8);
lean_inc(v_pendingHead_3591_);
lean_dec_ref(v_state_3279_);
v_close_3592_ = lean_ctor_get(v_inst_3275_, 1);
lean_inc_ref(v_close_3592_);
v_isClosed_3593_ = lean_ctor_get(v_inst_3275_, 2);
lean_inc_ref(v_isClosed_3593_);
lean_dec_ref(v_inst_3275_);
v_body_3594_ = lean_ctor_get(v_a_3582_, 1);
lean_inc_n(v_body_3594_, 2);
lean_dec(v_a_3582_);
v___x_3595_ = lean_apply_2(v_isClosed_3593_, v_body_3594_, lean_box(0));
v___x_3596_ = lean_box(v_requiresData_3589_);
v___f_3597_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3597_, 0, v_machine_3579_);
lean_closure_set(v___f_3597_, 1, v_requestStream_3583_);
lean_closure_set(v___f_3597_, 2, v_keepAliveTimeout_3584_);
lean_closure_set(v___f_3597_, 3, v_currentTimeout_3585_);
lean_closure_set(v___f_3597_, 4, v_headerTimeout_3586_);
lean_closure_set(v___f_3597_, 5, v_response_3587_);
lean_closure_set(v___f_3597_, 6, v_respStream_3588_);
lean_closure_set(v___f_3597_, 7, v___x_3596_);
lean_closure_set(v___f_3597_, 8, v_expectData_3590_);
lean_closure_set(v___f_3597_, 9, v_pendingHead_3591_);
lean_inc_ref(v___f_3597_);
v___f_3598_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3598_, 0, v___f_3597_);
v___f_3599_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3599_, 0, v_close_3592_);
lean_closure_set(v___f_3599_, 1, v_body_3594_);
lean_closure_set(v___f_3599_, 2, v___f_3598_);
lean_closure_set(v___f_3599_, 3, v___f_3597_);
v___x_3600_ = lean_unsigned_to_nat(0u);
v___x_3601_ = 0;
v___x_3602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3600_, v___x_3601_, v___x_3595_, v___f_3599_);
return v___x_3602_;
}
else
{
lean_object* v_a_3603_; lean_object* v_requestStream_3604_; lean_object* v_keepAliveTimeout_3605_; lean_object* v_currentTimeout_3606_; lean_object* v_headerTimeout_3607_; lean_object* v_response_3608_; uint8_t v_requiresData_3609_; lean_object* v_expectData_3610_; lean_object* v_pendingHead_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___f_3616_; lean_object* v___f_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_a_3603_ = lean_ctor_get(v_x_3571_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v_x_3571_, 1);
v_requestStream_3604_ = lean_ctor_get(v_state_3279_, 1);
lean_inc_ref(v_requestStream_3604_);
v_keepAliveTimeout_3605_ = lean_ctor_get(v_state_3279_, 2);
lean_inc(v_keepAliveTimeout_3605_);
v_currentTimeout_3606_ = lean_ctor_get(v_state_3279_, 3);
lean_inc(v_currentTimeout_3606_);
v_headerTimeout_3607_ = lean_ctor_get(v_state_3279_, 4);
lean_inc(v_headerTimeout_3607_);
v_response_3608_ = lean_ctor_get(v_state_3279_, 5);
lean_inc_ref(v_response_3608_);
v_requiresData_3609_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3610_ = lean_ctor_get(v_state_3279_, 7);
lean_inc(v_expectData_3610_);
v_pendingHead_3611_ = lean_ctor_get(v_state_3279_, 8);
lean_inc(v_pendingHead_3611_);
lean_dec_ref(v_state_3279_);
lean_inc_ref(v_inst_3275_);
v___x_3612_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3275_, v_config_3277_, v_machine_3579_, v_a_3603_);
v___x_3613_ = 0;
v___x_3614_ = lean_box(v_requiresData_3609_);
v___x_3615_ = lean_box(v___x_3613_);
v___f_3616_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3616_, 0, v_requestStream_3604_);
lean_closure_set(v___f_3616_, 1, v_keepAliveTimeout_3605_);
lean_closure_set(v___f_3616_, 2, v_currentTimeout_3606_);
lean_closure_set(v___f_3616_, 3, v_headerTimeout_3607_);
lean_closure_set(v___f_3616_, 4, v_response_3608_);
lean_closure_set(v___f_3616_, 5, v___x_3614_);
lean_closure_set(v___f_3616_, 6, v_expectData_3610_);
lean_closure_set(v___f_3616_, 7, v___x_3615_);
lean_closure_set(v___f_3616_, 8, v_pendingHead_3611_);
v___f_3617_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3617_, 0, v___f_3616_);
v___x_3618_ = lean_box(v___x_3613_);
lean_inc_ref(v___f_3617_);
v___f_3619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 6, 4);
lean_closure_set(v___f_3619_, 0, v___x_3618_);
lean_closure_set(v___f_3619_, 1, v___f_3617_);
lean_closure_set(v___f_3619_, 2, v_inst_3275_);
lean_closure_set(v___f_3619_, 3, v___f_3617_);
v___x_3620_ = lean_unsigned_to_nat(0u);
v___x_3621_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3620_, v___x_3613_, v___x_3612_, v___f_3619_);
return v___x_3621_;
}
}
}
case 4:
{
lean_object* v_onFailure_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; 
lean_dec_ref(v_config_3277_);
lean_dec_ref(v_inst_3275_);
v_onFailure_3622_ = lean_ctor_get(v_inst_3274_, 2);
lean_inc_ref(v_onFailure_3622_);
lean_dec_ref(v_inst_3274_);
v___x_3623_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_3624_ = lean_apply_3(v_onFailure_3622_, v_handler_3276_, v___x_3623_, lean_box(0));
v___f_3625_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 3, 1);
lean_closure_set(v___f_3625_, 0, v_state_3279_);
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = 0;
v___x_3628_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3626_, v___x_3627_, v___x_3624_, v___f_3625_);
return v___x_3628_;
}
case 5:
{
lean_object* v_machine_3629_; lean_object* v_requestStream_3630_; lean_object* v_keepAliveTimeout_3631_; lean_object* v_currentTimeout_3632_; lean_object* v_headerTimeout_3633_; lean_object* v_response_3634_; lean_object* v_respStream_3635_; uint8_t v_requiresData_3636_; lean_object* v_expectData_3637_; lean_object* v_pendingHead_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3652_; 
lean_dec_ref(v_config_3277_);
lean_dec(v_handler_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
v_machine_3629_ = lean_ctor_get(v_state_3279_, 0);
v_requestStream_3630_ = lean_ctor_get(v_state_3279_, 1);
v_keepAliveTimeout_3631_ = lean_ctor_get(v_state_3279_, 2);
v_currentTimeout_3632_ = lean_ctor_get(v_state_3279_, 3);
v_headerTimeout_3633_ = lean_ctor_get(v_state_3279_, 4);
v_response_3634_ = lean_ctor_get(v_state_3279_, 5);
v_respStream_3635_ = lean_ctor_get(v_state_3279_, 6);
v_requiresData_3636_ = lean_ctor_get_uint8(v_state_3279_, sizeof(void*)*9);
v_expectData_3637_ = lean_ctor_get(v_state_3279_, 7);
v_pendingHead_3638_ = lean_ctor_get(v_state_3279_, 8);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_state_3279_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3640_ = v_state_3279_;
v_isShared_3641_ = v_isSharedCheck_3652_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_pendingHead_3638_);
lean_inc(v_expectData_3637_);
lean_inc(v_respStream_3635_);
lean_inc(v_response_3634_);
lean_inc(v_headerTimeout_3633_);
lean_inc(v_currentTimeout_3632_);
lean_inc(v_keepAliveTimeout_3631_);
lean_inc(v_requestStream_3630_);
lean_inc(v_machine_3629_);
lean_dec(v_state_3279_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3652_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; lean_object* v___x_3646_; 
v___x_3642_ = lean_box(55);
v___x_3643_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3629_, v___x_3642_);
v___x_3644_ = 0;
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3643_);
v___x_3646_ = v___x_3640_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_requestStream_3630_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_keepAliveTimeout_3631_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_currentTimeout_3632_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_headerTimeout_3633_);
lean_ctor_set(v_reuseFailAlloc_3651_, 5, v_response_3634_);
lean_ctor_set(v_reuseFailAlloc_3651_, 6, v_respStream_3635_);
lean_ctor_set(v_reuseFailAlloc_3651_, 7, v_expectData_3637_);
lean_ctor_set(v_reuseFailAlloc_3651_, 8, v_pendingHead_3638_);
lean_ctor_set_uint8(v_reuseFailAlloc_3651_, sizeof(void*)*9, v_requiresData_3636_);
v___x_3646_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_ctor_set_uint8(v___x_3646_, sizeof(void*)*9 + 1, v___x_3644_);
v___x_3647_ = lean_box(v___x_3644_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
return v___x_3650_;
}
}
}
default: 
{
uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec_ref(v_config_3277_);
lean_dec(v_handler_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
v___x_3653_ = 1;
v___x_3654_ = lean_box(v___x_3653_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_state_3279_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_handler_3660_, lean_object* v_config_3661_, lean_object* v_event_3662_, lean_object* v_state_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3658_, v_inst_3659_, v_handler_3660_, v_config_3661_, v_event_3662_, v_state_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3666_, lean_object* v_00_u03b2_3667_, lean_object* v_inst_3668_, lean_object* v_inst_3669_, lean_object* v_handler_3670_, lean_object* v_config_3671_, lean_object* v_event_3672_, lean_object* v_state_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3668_, v_inst_3669_, v_handler_3670_, v_config_3671_, v_event_3672_, v_state_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3676_, lean_object* v_00_u03b2_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_handler_3680_, lean_object* v_config_3681_, lean_object* v_event_3682_, lean_object* v_state_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3676_, v_00_u03b2_3677_, v_inst_3678_, v_inst_3679_, v_handler_3680_, v_config_3681_, v_event_3682_, v_state_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3686_, uint8_t v_handlerDispatched_3687_, lean_object* v_headerTimeout_3688_, lean_object* v_expectData_3689_, lean_object* v_respStream_3690_, lean_object* v_keepAliveTimeout_3691_, lean_object* v_currentTimeout_3692_, lean_object* v_response_3693_, lean_object* v_socket_3694_, uint8_t v_requiresData_3695_, uint8_t v_sentMessage_3696_, lean_object* v_reader_3697_, uint8_t v_requestBodyInterested_3698_, lean_object* v_requestBody_3699_){
_start:
{
lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3713_; 
if (v_requiresData_3695_ == 0)
{
if (v_handlerDispatched_3687_ == 0)
{
goto v___jp_3716_;
}
else
{
if (lean_obj_tag(v_respStream_3690_) == 0)
{
if (v_sentMessage_3696_ == 0)
{
lean_object* v_state_3720_; 
v_state_3720_ = lean_ctor_get(v_reader_3697_, 0);
if (lean_obj_tag(v_state_3720_) == 2)
{
if (v_requestBodyInterested_3698_ == 0)
{
lean_dec(v_socket_3694_);
goto v___jp_3718_;
}
else
{
goto v___jp_3716_;
}
}
else
{
lean_dec(v_socket_3694_);
goto v___jp_3718_;
}
}
else
{
goto v___jp_3716_;
}
}
else
{
goto v___jp_3716_;
}
}
}
else
{
goto v___jp_3716_;
}
v___jp_3701_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3709_, 0, v___y_3702_);
lean_ctor_set(v___x_3709_, 1, v___y_3704_);
lean_ctor_set(v___x_3709_, 2, v___y_3708_);
lean_ctor_set(v___x_3709_, 3, v___y_3705_);
lean_ctor_set(v___x_3709_, 4, v_requestBody_3699_);
lean_ctor_set(v___x_3709_, 5, v___y_3707_);
lean_ctor_set(v___x_3709_, 6, v___y_3706_);
lean_ctor_set(v___x_3709_, 7, v___y_3703_);
lean_ctor_set(v___x_3709_, 8, v_connectionContext_3686_);
v___x_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
v___jp_3712_:
{
if (v_handlerDispatched_3687_ == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref(v_response_3693_);
v___x_3714_ = lean_box(0);
v___y_3702_ = v___y_3713_;
v___y_3703_ = v_headerTimeout_3688_;
v___y_3704_ = v_expectData_3689_;
v___y_3705_ = v_respStream_3690_;
v___y_3706_ = v_keepAliveTimeout_3691_;
v___y_3707_ = v_currentTimeout_3692_;
v___y_3708_ = v___x_3714_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_response_3693_);
v___y_3702_ = v___y_3713_;
v___y_3703_ = v_headerTimeout_3688_;
v___y_3704_ = v_expectData_3689_;
v___y_3705_ = v_respStream_3690_;
v___y_3706_ = v_keepAliveTimeout_3691_;
v___y_3707_ = v_currentTimeout_3692_;
v___y_3708_ = v___x_3715_;
goto v___jp_3701_;
}
}
v___jp_3716_:
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3717_, 0, v_socket_3694_);
v___y_3713_ = v___x_3717_;
goto v___jp_3712_;
}
v___jp_3718_:
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_box(0);
v___y_3713_ = v___x_3719_;
goto v___jp_3712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3721_, lean_object* v_handlerDispatched_3722_, lean_object* v_headerTimeout_3723_, lean_object* v_expectData_3724_, lean_object* v_respStream_3725_, lean_object* v_keepAliveTimeout_3726_, lean_object* v_currentTimeout_3727_, lean_object* v_response_3728_, lean_object* v_socket_3729_, lean_object* v_requiresData_3730_, lean_object* v_sentMessage_3731_, lean_object* v_reader_3732_, lean_object* v_requestBodyInterested_3733_, lean_object* v_requestBody_3734_, lean_object* v___y_3735_){
_start:
{
uint8_t v_handlerDispatched_boxed_3736_; uint8_t v_requiresData_boxed_3737_; uint8_t v_sentMessage_boxed_3738_; uint8_t v_requestBodyInterested_boxed_3739_; lean_object* v_res_3740_; 
v_handlerDispatched_boxed_3736_ = lean_unbox(v_handlerDispatched_3722_);
v_requiresData_boxed_3737_ = lean_unbox(v_requiresData_3730_);
v_sentMessage_boxed_3738_ = lean_unbox(v_sentMessage_3731_);
v_requestBodyInterested_boxed_3739_ = lean_unbox(v_requestBodyInterested_3733_);
v_res_3740_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3721_, v_handlerDispatched_boxed_3736_, v_headerTimeout_3723_, v_expectData_3724_, v_respStream_3725_, v_keepAliveTimeout_3726_, v_currentTimeout_3727_, v_response_3728_, v_socket_3729_, v_requiresData_boxed_3737_, v_sentMessage_boxed_3738_, v_reader_3732_, v_requestBodyInterested_boxed_3739_, v_requestBody_3734_);
lean_dec_ref(v_reader_3732_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3741_, lean_object* v_x_3742_){
_start:
{
if (lean_obj_tag(v_x_3742_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3752_; 
lean_dec_ref(v___f_3741_);
v_a_3744_ = lean_ctor_get(v_x_3742_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_x_3742_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3746_ = v_x_3742_;
v_isShared_3747_ = v_isSharedCheck_3752_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v_x_3742_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3752_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3754_; 
v_a_3753_ = lean_ctor_get(v_x_3742_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v_x_3742_, 1);
v___x_3754_ = lean_apply_2(v___f_3741_, v_a_3753_, lean_box(0));
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3755_, lean_object* v_x_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3755_, v_x_3756_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3763_, uint8_t v_handlerDispatched_3764_, lean_object* v_headerTimeout_3765_, lean_object* v_expectData_3766_, lean_object* v_respStream_3767_, lean_object* v_keepAliveTimeout_3768_, lean_object* v_currentTimeout_3769_, lean_object* v_response_3770_, lean_object* v_socket_3771_, uint8_t v_requiresData_3772_, uint8_t v_sentMessage_3773_, lean_object* v_reader_3774_, uint8_t v_pullBodyStalled_3775_, uint8_t v_requestBodyOpen_3776_, lean_object* v_requestStream_3777_, uint8_t v_requestBodyInterested_3778_){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___f_3784_; lean_object* v___f_3785_; 
v___x_3780_ = lean_box(v_handlerDispatched_3764_);
v___x_3781_ = lean_box(v_requiresData_3772_);
v___x_3782_ = lean_box(v_sentMessage_3773_);
v___x_3783_ = lean_box(v_requestBodyInterested_3778_);
lean_inc_ref(v_reader_3774_);
v___f_3784_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3784_, 0, v_connectionContext_3763_);
lean_closure_set(v___f_3784_, 1, v___x_3780_);
lean_closure_set(v___f_3784_, 2, v_headerTimeout_3765_);
lean_closure_set(v___f_3784_, 3, v_expectData_3766_);
lean_closure_set(v___f_3784_, 4, v_respStream_3767_);
lean_closure_set(v___f_3784_, 5, v_keepAliveTimeout_3768_);
lean_closure_set(v___f_3784_, 6, v_currentTimeout_3769_);
lean_closure_set(v___f_3784_, 7, v_response_3770_);
lean_closure_set(v___f_3784_, 8, v_socket_3771_);
lean_closure_set(v___f_3784_, 9, v___x_3781_);
lean_closure_set(v___f_3784_, 10, v___x_3782_);
lean_closure_set(v___f_3784_, 11, v_reader_3774_);
lean_closure_set(v___f_3784_, 12, v___x_3783_);
v___f_3785_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3785_, 0, v___f_3784_);
if (v_sentMessage_3773_ == 0)
{
lean_object* v_state_3791_; 
v_state_3791_ = lean_ctor_get(v_reader_3774_, 0);
lean_inc(v_state_3791_);
lean_dec_ref(v_reader_3774_);
if (lean_obj_tag(v_state_3791_) == 2)
{
lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3802_; 
v_isSharedCheck_3802_ = !lean_is_exclusive(v_state_3791_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v_state_3791_, 0);
lean_dec(v_unused_3803_);
v___x_3793_ = v_state_3791_;
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
else
{
lean_dec(v_state_3791_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
if (v_pullBodyStalled_3775_ == 0)
{
if (v_requestBodyOpen_3776_ == 0)
{
lean_del_object(v___x_3793_);
lean_dec_ref(v_requestStream_3777_);
goto v___jp_3786_;
}
else
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 1);
lean_ctor_set(v___x_3793_, 0, v_requestStream_3777_);
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_requestStream_3777_);
v___x_3796_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = lean_unsigned_to_nat(0u);
v___x_3800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3799_, v_pullBodyStalled_3775_, v___x_3798_, v___f_3785_);
return v___x_3800_;
}
}
}
else
{
lean_del_object(v___x_3793_);
lean_dec_ref(v_requestStream_3777_);
goto v___jp_3786_;
}
}
}
else
{
lean_dec(v_state_3791_);
lean_dec_ref(v_requestStream_3777_);
goto v___jp_3786_;
}
}
else
{
lean_dec_ref(v_requestStream_3777_);
lean_dec_ref(v_reader_3774_);
goto v___jp_3786_;
}
v___jp_3786_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; lean_object* v___x_3790_; 
v___x_3787_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3788_ = lean_unsigned_to_nat(0u);
v___x_3789_ = 0;
v___x_3790_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3788_, v___x_3789_, v___x_3787_, v___f_3785_);
return v___x_3790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3804_ = _args[0];
lean_object* v_handlerDispatched_3805_ = _args[1];
lean_object* v_headerTimeout_3806_ = _args[2];
lean_object* v_expectData_3807_ = _args[3];
lean_object* v_respStream_3808_ = _args[4];
lean_object* v_keepAliveTimeout_3809_ = _args[5];
lean_object* v_currentTimeout_3810_ = _args[6];
lean_object* v_response_3811_ = _args[7];
lean_object* v_socket_3812_ = _args[8];
lean_object* v_requiresData_3813_ = _args[9];
lean_object* v_sentMessage_3814_ = _args[10];
lean_object* v_reader_3815_ = _args[11];
lean_object* v_pullBodyStalled_3816_ = _args[12];
lean_object* v_requestBodyOpen_3817_ = _args[13];
lean_object* v_requestStream_3818_ = _args[14];
lean_object* v_requestBodyInterested_3819_ = _args[15];
lean_object* v___y_3820_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3821_; uint8_t v_requiresData_boxed_3822_; uint8_t v_sentMessage_boxed_3823_; uint8_t v_pullBodyStalled_boxed_3824_; uint8_t v_requestBodyOpen_boxed_3825_; uint8_t v_requestBodyInterested_boxed_3826_; lean_object* v_res_3827_; 
v_handlerDispatched_boxed_3821_ = lean_unbox(v_handlerDispatched_3805_);
v_requiresData_boxed_3822_ = lean_unbox(v_requiresData_3813_);
v_sentMessage_boxed_3823_ = lean_unbox(v_sentMessage_3814_);
v_pullBodyStalled_boxed_3824_ = lean_unbox(v_pullBodyStalled_3816_);
v_requestBodyOpen_boxed_3825_ = lean_unbox(v_requestBodyOpen_3817_);
v_requestBodyInterested_boxed_3826_ = lean_unbox(v_requestBodyInterested_3819_);
v_res_3827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3804_, v_handlerDispatched_boxed_3821_, v_headerTimeout_3806_, v_expectData_3807_, v_respStream_3808_, v_keepAliveTimeout_3809_, v_currentTimeout_3810_, v_response_3811_, v_socket_3812_, v_requiresData_boxed_3822_, v_sentMessage_boxed_3823_, v_reader_3815_, v_pullBodyStalled_boxed_3824_, v_requestBodyOpen_boxed_3825_, v_requestStream_3818_, v_requestBodyInterested_boxed_3826_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3828_, lean_object* v_x_3829_){
_start:
{
if (lean_obj_tag(v_x_3829_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v___f_3828_);
v_a_3831_ = lean_ctor_get(v_x_3829_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_x_3829_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3833_ = v_x_3829_;
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v_x_3829_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
return v___x_3837_;
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3841_; 
v_a_3840_ = lean_ctor_get(v_x_3829_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v_x_3829_, 1);
v___x_3841_ = lean_apply_2(v___f_3828_, v_a_3840_, lean_box(0));
return v___x_3841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3842_, lean_object* v_x_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3842_, v_x_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3851_, uint8_t v_handlerDispatched_3852_, lean_object* v_headerTimeout_3853_, lean_object* v_expectData_3854_, lean_object* v_respStream_3855_, lean_object* v_keepAliveTimeout_3856_, lean_object* v_currentTimeout_3857_, lean_object* v_response_3858_, lean_object* v_socket_3859_, uint8_t v_requiresData_3860_, uint8_t v_sentMessage_3861_, lean_object* v_reader_3862_, uint8_t v_pullBodyStalled_3863_, lean_object* v_requestStream_3864_, uint8_t v_requestBodyOpen_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___f_3872_; lean_object* v___f_3873_; 
v___x_3867_ = lean_box(v_handlerDispatched_3852_);
v___x_3868_ = lean_box(v_requiresData_3860_);
v___x_3869_ = lean_box(v_sentMessage_3861_);
v___x_3870_ = lean_box(v_pullBodyStalled_3863_);
v___x_3871_ = lean_box(v_requestBodyOpen_3865_);
lean_inc_ref(v_requestStream_3864_);
lean_inc_ref(v_reader_3862_);
v___f_3872_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3872_, 0, v_connectionContext_3851_);
lean_closure_set(v___f_3872_, 1, v___x_3867_);
lean_closure_set(v___f_3872_, 2, v_headerTimeout_3853_);
lean_closure_set(v___f_3872_, 3, v_expectData_3854_);
lean_closure_set(v___f_3872_, 4, v_respStream_3855_);
lean_closure_set(v___f_3872_, 5, v_keepAliveTimeout_3856_);
lean_closure_set(v___f_3872_, 6, v_currentTimeout_3857_);
lean_closure_set(v___f_3872_, 7, v_response_3858_);
lean_closure_set(v___f_3872_, 8, v_socket_3859_);
lean_closure_set(v___f_3872_, 9, v___x_3868_);
lean_closure_set(v___f_3872_, 10, v___x_3869_);
lean_closure_set(v___f_3872_, 11, v_reader_3862_);
lean_closure_set(v___f_3872_, 12, v___x_3870_);
lean_closure_set(v___f_3872_, 13, v___x_3871_);
lean_closure_set(v___f_3872_, 14, v_requestStream_3864_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3873_, 0, v___f_3872_);
if (v_sentMessage_3861_ == 0)
{
lean_object* v_state_3879_; 
v_state_3879_ = lean_ctor_get(v_reader_3862_, 0);
lean_inc(v_state_3879_);
lean_dec_ref(v_reader_3862_);
if (lean_obj_tag(v_state_3879_) == 2)
{
lean_dec_ref_known(v_state_3879_, 1);
if (v_requestBodyOpen_3865_ == 0)
{
lean_dec_ref(v_requestStream_3864_);
goto v___jp_3874_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3864_);
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3881_, v_sentMessage_3861_, v___x_3880_, v___f_3873_);
return v___x_3882_;
}
}
else
{
lean_dec(v_state_3879_);
lean_dec_ref(v_requestStream_3864_);
goto v___jp_3874_;
}
}
else
{
lean_dec_ref(v_requestStream_3864_);
lean_dec_ref(v_reader_3862_);
goto v___jp_3874_;
}
v___jp_3874_:
{
uint8_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3875_ = 0;
v___x_3876_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3877_, v___x_3875_, v___x_3876_, v___f_3873_);
return v___x_3878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3883_, lean_object* v_handlerDispatched_3884_, lean_object* v_headerTimeout_3885_, lean_object* v_expectData_3886_, lean_object* v_respStream_3887_, lean_object* v_keepAliveTimeout_3888_, lean_object* v_currentTimeout_3889_, lean_object* v_response_3890_, lean_object* v_socket_3891_, lean_object* v_requiresData_3892_, lean_object* v_sentMessage_3893_, lean_object* v_reader_3894_, lean_object* v_pullBodyStalled_3895_, lean_object* v_requestStream_3896_, lean_object* v_requestBodyOpen_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v_handlerDispatched_boxed_3899_; uint8_t v_requiresData_boxed_3900_; uint8_t v_sentMessage_boxed_3901_; uint8_t v_pullBodyStalled_boxed_3902_; uint8_t v_requestBodyOpen_boxed_3903_; lean_object* v_res_3904_; 
v_handlerDispatched_boxed_3899_ = lean_unbox(v_handlerDispatched_3884_);
v_requiresData_boxed_3900_ = lean_unbox(v_requiresData_3892_);
v_sentMessage_boxed_3901_ = lean_unbox(v_sentMessage_3893_);
v_pullBodyStalled_boxed_3902_ = lean_unbox(v_pullBodyStalled_3895_);
v_requestBodyOpen_boxed_3903_ = lean_unbox(v_requestBodyOpen_3897_);
v_res_3904_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3883_, v_handlerDispatched_boxed_3899_, v_headerTimeout_3885_, v_expectData_3886_, v_respStream_3887_, v_keepAliveTimeout_3888_, v_currentTimeout_3889_, v_response_3890_, v_socket_3891_, v_requiresData_boxed_3900_, v_sentMessage_boxed_3901_, v_reader_3894_, v_pullBodyStalled_boxed_3902_, v_requestStream_3896_, v_requestBodyOpen_boxed_3903_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3905_, lean_object* v___f_3906_, uint8_t v___x_3907_, lean_object* v_x_3908_){
_start:
{
uint8_t v___y_3911_; 
if (lean_obj_tag(v_x_3908_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v___f_3906_);
v_a_3917_ = lean_ctor_get(v_x_3908_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_x_3908_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3919_ = v_x_3908_;
v_isShared_3920_ = v_isSharedCheck_3925_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v_x_3908_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3925_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; 
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
return v___x_3923_;
}
}
}
else
{
lean_object* v_a_3926_; uint8_t v___x_3927_; 
v_a_3926_ = lean_ctor_get(v_x_3908_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v_x_3908_, 1);
v___x_3927_ = lean_unbox(v_a_3926_);
lean_dec(v_a_3926_);
if (v___x_3927_ == 0)
{
v___y_3911_ = v___x_3907_;
goto v___jp_3910_;
}
else
{
v___y_3911_ = v_sentMessage_3905_;
goto v___jp_3910_;
}
}
v___jp_3910_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3912_ = lean_box(v___y_3911_);
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3915_, v_sentMessage_3905_, v___x_3914_, v___f_3906_);
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3928_, lean_object* v___f_3929_, lean_object* v___x_3930_, lean_object* v_x_3931_, lean_object* v___y_3932_){
_start:
{
uint8_t v_sentMessage_boxed_3933_; uint8_t v___x_3791__boxed_3934_; lean_object* v_res_3935_; 
v_sentMessage_boxed_3933_ = lean_unbox(v_sentMessage_3928_);
v___x_3791__boxed_3934_ = lean_unbox(v___x_3930_);
v_res_3935_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3933_, v___f_3929_, v___x_3791__boxed_3934_, v_x_3931_);
return v_res_3935_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___f_3936_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3937_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3938_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3939_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3939_, 0, lean_box(0));
lean_closure_set(v___x_3939_, 1, lean_box(0));
lean_closure_set(v___x_3939_, 2, lean_box(0));
lean_closure_set(v___x_3939_, 3, v___x_3938_);
lean_closure_set(v___x_3939_, 4, lean_box(0));
lean_closure_set(v___x_3939_, 5, lean_box(0));
lean_closure_set(v___x_3939_, 6, v___x_3937_);
lean_closure_set(v___x_3939_, 7, v___f_3936_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3940_, lean_object* v_connectionContext_3941_, lean_object* v_state_3942_){
_start:
{
lean_object* v_machine_3944_; lean_object* v_writer_3945_; lean_object* v_requestStream_3946_; lean_object* v_keepAliveTimeout_3947_; lean_object* v_currentTimeout_3948_; lean_object* v_headerTimeout_3949_; lean_object* v_response_3950_; lean_object* v_respStream_3951_; uint8_t v_requiresData_3952_; lean_object* v_expectData_3953_; uint8_t v_handlerDispatched_3954_; lean_object* v_reader_3955_; uint8_t v_pullBodyStalled_3956_; uint8_t v_sentMessage_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___f_3962_; lean_object* v___f_3963_; uint8_t v___y_3965_; 
v_machine_3944_ = lean_ctor_get(v_state_3942_, 0);
lean_inc_ref(v_machine_3944_);
v_writer_3945_ = lean_ctor_get(v_machine_3944_, 1);
lean_inc_ref(v_writer_3945_);
v_requestStream_3946_ = lean_ctor_get(v_state_3942_, 1);
lean_inc_ref_n(v_requestStream_3946_, 2);
v_keepAliveTimeout_3947_ = lean_ctor_get(v_state_3942_, 2);
lean_inc(v_keepAliveTimeout_3947_);
v_currentTimeout_3948_ = lean_ctor_get(v_state_3942_, 3);
lean_inc(v_currentTimeout_3948_);
v_headerTimeout_3949_ = lean_ctor_get(v_state_3942_, 4);
lean_inc(v_headerTimeout_3949_);
v_response_3950_ = lean_ctor_get(v_state_3942_, 5);
lean_inc_ref(v_response_3950_);
v_respStream_3951_ = lean_ctor_get(v_state_3942_, 6);
lean_inc(v_respStream_3951_);
v_requiresData_3952_ = lean_ctor_get_uint8(v_state_3942_, sizeof(void*)*9);
v_expectData_3953_ = lean_ctor_get(v_state_3942_, 7);
lean_inc(v_expectData_3953_);
v_handlerDispatched_3954_ = lean_ctor_get_uint8(v_state_3942_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3942_);
v_reader_3955_ = lean_ctor_get(v_machine_3944_, 0);
lean_inc_ref_n(v_reader_3955_, 2);
v_pullBodyStalled_3956_ = lean_ctor_get_uint8(v_machine_3944_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3944_);
v_sentMessage_3957_ = lean_ctor_get_uint8(v_writer_3945_, sizeof(void*)*6);
lean_dec_ref(v_writer_3945_);
v___x_3958_ = lean_box(v_handlerDispatched_3954_);
v___x_3959_ = lean_box(v_requiresData_3952_);
v___x_3960_ = lean_box(v_sentMessage_3957_);
v___x_3961_ = lean_box(v_pullBodyStalled_3956_);
v___f_3962_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3962_, 0, v_connectionContext_3941_);
lean_closure_set(v___f_3962_, 1, v___x_3958_);
lean_closure_set(v___f_3962_, 2, v_headerTimeout_3949_);
lean_closure_set(v___f_3962_, 3, v_expectData_3953_);
lean_closure_set(v___f_3962_, 4, v_respStream_3951_);
lean_closure_set(v___f_3962_, 5, v_keepAliveTimeout_3947_);
lean_closure_set(v___f_3962_, 6, v_currentTimeout_3948_);
lean_closure_set(v___f_3962_, 7, v_response_3950_);
lean_closure_set(v___f_3962_, 8, v_socket_3940_);
lean_closure_set(v___f_3962_, 9, v___x_3959_);
lean_closure_set(v___f_3962_, 10, v___x_3960_);
lean_closure_set(v___f_3962_, 11, v_reader_3955_);
lean_closure_set(v___f_3962_, 12, v___x_3961_);
lean_closure_set(v___f_3962_, 13, v_requestStream_3946_);
v___f_3963_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3963_, 0, v___f_3962_);
if (v_sentMessage_3957_ == 0)
{
lean_object* v_state_3971_; 
v_state_3971_ = lean_ctor_get(v_reader_3955_, 0);
lean_inc(v_state_3971_);
lean_dec_ref(v_reader_3955_);
if (lean_obj_tag(v_state_3971_) == 2)
{
lean_object* v___x_3972_; lean_object* v___f_3973_; lean_object* v___f_3974_; lean_object* v___x_3975_; lean_object* v___x_3305__overap_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___f_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_dec_ref_known(v_state_3971_, 1);
v___x_3972_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3973_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3974_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3975_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3305__overap_3976_ = l_Std_Mutex_atomically___redArg(v___x_3972_, v___f_3973_, v___f_3974_, v_requestStream_3946_, v___x_3975_);
v___x_3977_ = lean_apply_1(v___x_3305__overap_3976_, lean_box(0));
v___x_3978_ = 1;
v___x_3979_ = lean_box(v_sentMessage_3957_);
v___x_3980_ = lean_box(v___x_3978_);
v___f_3981_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3981_, 0, v___x_3979_);
lean_closure_set(v___f_3981_, 1, v___f_3963_);
lean_closure_set(v___f_3981_, 2, v___x_3980_);
v___x_3982_ = lean_unsigned_to_nat(0u);
v___x_3983_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3982_, v_sentMessage_3957_, v___x_3977_, v___f_3981_);
return v___x_3983_;
}
else
{
lean_dec(v_state_3971_);
lean_dec_ref(v_requestStream_3946_);
v___y_3965_ = v_sentMessage_3957_;
goto v___jp_3964_;
}
}
else
{
uint8_t v___x_3984_; 
lean_dec_ref(v_reader_3955_);
lean_dec_ref(v_requestStream_3946_);
v___x_3984_ = 0;
v___y_3965_ = v___x_3984_;
goto v___jp_3964_;
}
v___jp_3964_:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3966_ = lean_box(v___y_3965_);
v___x_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
v___x_3969_ = lean_unsigned_to_nat(0u);
v___x_3970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3969_, v___y_3965_, v___x_3968_, v___f_3963_);
return v___x_3970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3985_, lean_object* v_connectionContext_3986_, lean_object* v_state_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3985_, v_connectionContext_3986_, v_state_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3990_, lean_object* v_00_u03b2_3991_, lean_object* v_inst_3992_, lean_object* v_socket_3993_, lean_object* v_connectionContext_3994_, lean_object* v_state_3995_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3993_, v_connectionContext_3994_, v_state_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_3998_, lean_object* v_00_u03b2_3999_, lean_object* v_inst_4000_, lean_object* v_socket_4001_, lean_object* v_connectionContext_4002_, lean_object* v_state_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_3998_, v_00_u03b2_3999_, v_inst_4000_, v_socket_4001_, v_connectionContext_4002_, v_state_4003_);
lean_dec_ref(v_inst_4000_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4006_){
_start:
{
if (lean_obj_tag(v_x_4006_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4016_; 
v_a_4008_ = lean_ctor_get(v_x_4006_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v_x_4006_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4010_ = v_x_4006_;
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v_x_4006_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4035_; 
v_a_4017_ = lean_ctor_get(v_x_4006_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_x_4006_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4019_ = v_x_4006_;
v_isShared_4020_ = v_isSharedCheck_4035_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v_x_4006_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4035_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v_snd_4021_; uint8_t v___x_4022_; 
v_snd_4021_ = lean_ctor_get(v_a_4017_, 1);
v___x_4022_ = lean_unbox(v_snd_4021_);
if (v___x_4022_ == 0)
{
lean_object* v_fst_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
v_fst_4023_ = lean_ctor_get(v_a_4017_, 0);
lean_inc(v_fst_4023_);
lean_dec(v_a_4017_);
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_fst_4023_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4024_);
v___x_4026_ = v___x_4019_;
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
else
{
lean_object* v_fst_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v_fst_4029_ = lean_ctor_get(v_a_4017_, 0);
lean_inc(v_fst_4029_);
lean_dec(v_a_4017_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v_fst_4029_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4030_);
v___x_4032_ = v___x_4019_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4039_){
_start:
{
if (lean_obj_tag(v_x_4039_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4049_; 
v_a_4041_ = lean_ctor_get(v_x_4039_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_x_4039_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4043_ = v_x_4039_;
v_isShared_4044_ = v_isSharedCheck_4049_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v_x_4039_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4049_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4059_; 
v_a_4050_ = lean_ctor_get(v_x_4039_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_x_4039_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4052_ = v_x_4039_;
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v_x_4039_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4056_; 
v___x_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_a_4050_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4054_);
v___x_4056_ = v___x_4052_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
return v___x_4057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4067_){
_start:
{
if (lean_obj_tag(v_x_4067_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4077_; 
v_a_4069_ = lean_ctor_get(v_x_4067_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_x_4067_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4071_ = v_x_4067_;
v_isShared_4072_ = v_isSharedCheck_4077_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v_x_4067_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4077_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4069_);
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
else
{
lean_object* v___x_4078_; 
lean_dec_ref_known(v_x_4067_, 1);
v___x_4078_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4082_, lean_object* v_handler_4083_, lean_object* v___f_4084_, lean_object* v_x_4085_){
_start:
{
if (lean_obj_tag(v_x_4085_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; 
v_a_4087_ = lean_ctor_get(v_x_4085_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v_x_4085_, 1);
v___x_4088_ = lean_apply_3(v_onFailure_4082_, v_handler_4083_, v_a_4087_, lean_box(0));
v___x_4089_ = lean_unsigned_to_nat(0u);
v___x_4090_ = 0;
v___x_4091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4089_, v___x_4090_, v___x_4088_, v___f_4084_);
return v___x_4091_;
}
else
{
lean_object* v___x_4092_; 
lean_dec_ref(v___f_4084_);
lean_dec(v_handler_4083_);
lean_dec_ref(v_onFailure_4082_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v_x_4085_);
return v___x_4092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4093_, lean_object* v_handler_4094_, lean_object* v___f_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4093_, v_handler_4094_, v___f_4095_, v_x_4096_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4099_, lean_object* v_socket_4100_, lean_object* v_____r_4101_){
_start:
{
lean_object* v_val_4104_; lean_object* v_close_4106_; lean_object* v___x_4107_; 
v_close_4106_ = lean_ctor_get(v_inst_4099_, 3);
lean_inc_ref(v_close_4106_);
lean_dec_ref(v_inst_4099_);
v___x_4107_ = lean_apply_2(v_close_4106_, v_socket_4100_, lean_box(0));
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set_tag(v___x_4110_, 1);
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
v_val_4104_ = v___x_4113_;
goto v___jp_4103_;
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
v_a_4116_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4107_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4107_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
lean_ctor_set_tag(v___x_4118_, 0);
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
v_val_4104_ = v___x_4121_;
goto v___jp_4103_;
}
}
}
v___jp_4103_:
{
lean_object* v___x_4105_; 
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v_val_4104_);
return v___x_4105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4124_, lean_object* v_socket_4125_, lean_object* v_____r_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4124_, v_socket_4125_, v_____r_4126_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4129_, lean_object* v_x_4130_){
_start:
{
if (lean_obj_tag(v_x_4130_) == 0)
{
lean_object* v___x_4132_; 
lean_dec_ref(v___f_4129_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_x_4130_);
return v___x_4132_;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4134_; 
v_a_4133_ = lean_ctor_get(v_x_4130_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v_x_4130_, 1);
v___x_4134_ = lean_apply_2(v___f_4129_, v_a_4133_, lean_box(0));
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4135_, lean_object* v_x_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4135_, v_x_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4139_, lean_object* v_val_4140_, lean_object* v___f_4141_, lean_object* v___f_4142_, lean_object* v_x_4143_){
_start:
{
if (lean_obj_tag(v_x_4143_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v___f_4142_);
lean_dec_ref(v___f_4141_);
lean_dec(v_val_4140_);
lean_dec_ref(v_close_4139_);
v_a_4145_ = lean_ctor_get(v_x_4143_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_x_4143_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4147_ = v_x_4143_;
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v_x_4143_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
}
else
{
lean_object* v_a_4154_; uint8_t v___x_4155_; 
v_a_4154_ = lean_ctor_get(v_x_4143_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v_x_4143_, 1);
v___x_4155_ = lean_unbox(v_a_4154_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; 
lean_dec_ref(v___f_4142_);
v___x_4156_ = lean_apply_2(v_close_4139_, v_val_4140_, lean_box(0));
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4158_ = lean_unbox(v_a_4154_);
lean_dec(v_a_4154_);
v___x_4159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4157_, v___x_4158_, v___x_4156_, v___f_4141_);
return v___x_4159_;
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec(v_a_4154_);
lean_dec_ref(v___f_4141_);
lean_dec(v_val_4140_);
lean_dec_ref(v_close_4139_);
v___x_4160_ = lean_box(0);
v___x_4161_ = lean_apply_2(v___f_4142_, v___x_4160_, lean_box(0));
return v___x_4161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4162_, lean_object* v_val_4163_, lean_object* v___f_4164_, lean_object* v___f_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4162_, v_val_4163_, v___f_4164_, v___f_4165_, v_x_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4169_, lean_object* v_responseBodyInstance_4170_, lean_object* v___f_4171_, lean_object* v___f_4172_, lean_object* v_____r_4173_){
_start:
{
if (lean_obj_tag(v_respStream_4169_) == 1)
{
lean_object* v_val_4175_; lean_object* v_close_4176_; lean_object* v_isClosed_4177_; lean_object* v___x_4178_; lean_object* v___f_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; 
v_val_4175_ = lean_ctor_get(v_respStream_4169_, 0);
lean_inc_n(v_val_4175_, 2);
lean_dec_ref_known(v_respStream_4169_, 1);
v_close_4176_ = lean_ctor_get(v_responseBodyInstance_4170_, 1);
lean_inc_ref(v_close_4176_);
v_isClosed_4177_ = lean_ctor_get(v_responseBodyInstance_4170_, 2);
lean_inc_ref(v_isClosed_4177_);
lean_dec_ref(v_responseBodyInstance_4170_);
v___x_4178_ = lean_apply_2(v_isClosed_4177_, v_val_4175_, lean_box(0));
v___f_4179_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4179_, 0, v_close_4176_);
lean_closure_set(v___f_4179_, 1, v_val_4175_);
lean_closure_set(v___f_4179_, 2, v___f_4171_);
lean_closure_set(v___f_4179_, 3, v___f_4172_);
v___x_4180_ = lean_unsigned_to_nat(0u);
v___x_4181_ = 0;
v___x_4182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4180_, v___x_4181_, v___x_4178_, v___f_4179_);
return v___x_4182_;
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_dec_ref(v___f_4171_);
lean_dec_ref(v_responseBodyInstance_4170_);
lean_dec(v_respStream_4169_);
v___x_4183_ = lean_box(0);
v___x_4184_ = lean_apply_2(v___f_4172_, v___x_4183_, lean_box(0));
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4185_, lean_object* v_responseBodyInstance_4186_, lean_object* v___f_4187_, lean_object* v___f_4188_, lean_object* v_____r_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4185_, v_responseBodyInstance_4186_, v___f_4187_, v___f_4188_, v_____r_4189_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4192_, lean_object* v___f_4193_, lean_object* v___f_4194_, lean_object* v_x_4195_){
_start:
{
if (lean_obj_tag(v_x_4195_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4205_; 
lean_dec_ref(v___f_4194_);
lean_dec_ref(v___f_4193_);
lean_dec_ref(v_requestStream_4192_);
v_a_4197_ = lean_ctor_get(v_x_4195_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_x_4195_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4199_ = v_x_4195_;
v_isShared_4200_ = v_isSharedCheck_4205_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v_x_4195_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4205_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
return v___x_4203_;
}
}
}
else
{
lean_object* v_a_4206_; uint8_t v___x_4207_; 
v_a_4206_ = lean_ctor_get(v_x_4195_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v_x_4195_, 1);
v___x_4207_ = lean_unbox(v_a_4206_);
if (v___x_4207_ == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; 
lean_dec_ref(v___f_4194_);
v___x_4208_ = l_Std_Http_Body_Stream_close(v_requestStream_4192_);
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = lean_unbox(v_a_4206_);
lean_dec(v_a_4206_);
v___x_4211_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4209_, v___x_4210_, v___x_4208_, v___f_4193_);
return v___x_4211_;
}
else
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_dec(v_a_4206_);
lean_dec_ref(v___f_4193_);
lean_dec_ref(v_requestStream_4192_);
v___x_4212_ = lean_box(0);
v___x_4213_ = lean_apply_2(v___f_4194_, v___x_4212_, lean_box(0));
return v___x_4213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4214_, lean_object* v___f_4215_, lean_object* v___f_4216_, lean_object* v_x_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4214_, v___f_4215_, v___f_4216_, v_x_4217_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4220_, lean_object* v_responseBodyInstance_4221_, lean_object* v___f_4222_, lean_object* v___f_4223_, lean_object* v_x_4224_){
_start:
{
if (lean_obj_tag(v_x_4224_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v___f_4223_);
lean_dec_ref(v___f_4222_);
lean_dec_ref(v_responseBodyInstance_4221_);
lean_dec_ref(v___f_4220_);
v_a_4226_ = lean_ctor_get(v_x_4224_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_x_4224_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4228_ = v_x_4224_;
v_isShared_4229_ = v_isSharedCheck_4234_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v_x_4224_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4234_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
return v___x_4232_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v_requestStream_4236_; lean_object* v_respStream_4237_; lean_object* v___x_4238_; lean_object* v___f_4239_; lean_object* v___f_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_5017__overap_4243_; lean_object* v___x_4244_; lean_object* v___f_4245_; lean_object* v___f_4246_; lean_object* v___f_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; lean_object* v___x_4250_; 
v_a_4235_ = lean_ctor_get(v_x_4224_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v_x_4224_, 1);
v_requestStream_4236_ = lean_ctor_get(v_a_4235_, 1);
lean_inc_ref_n(v_requestStream_4236_, 2);
v_respStream_4237_ = lean_ctor_get(v_a_4235_, 6);
lean_inc(v_respStream_4237_);
lean_dec(v_a_4235_);
v___x_4238_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4239_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4240_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4241_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4242_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_4242_, 0, lean_box(0));
lean_closure_set(v___x_4242_, 1, lean_box(0));
lean_closure_set(v___x_4242_, 2, lean_box(0));
lean_closure_set(v___x_4242_, 3, v___x_4238_);
lean_closure_set(v___x_4242_, 4, lean_box(0));
lean_closure_set(v___x_4242_, 5, lean_box(0));
lean_closure_set(v___x_4242_, 6, v___x_4241_);
lean_closure_set(v___x_4242_, 7, v___f_4220_);
v___x_5017__overap_4243_ = l_Std_Mutex_atomically___redArg(v___x_4238_, v___f_4239_, v___f_4240_, v_requestStream_4236_, v___x_4242_);
v___x_4244_ = lean_apply_1(v___x_5017__overap_4243_, lean_box(0));
v___f_4245_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4245_, 0, v_respStream_4237_);
lean_closure_set(v___f_4245_, 1, v_responseBodyInstance_4221_);
lean_closure_set(v___f_4245_, 2, v___f_4222_);
lean_closure_set(v___f_4245_, 3, v___f_4223_);
lean_inc_ref(v___f_4245_);
v___f_4246_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4246_, 0, v___f_4245_);
v___f_4247_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4247_, 0, v_requestStream_4236_);
lean_closure_set(v___f_4247_, 1, v___f_4246_);
lean_closure_set(v___f_4247_, 2, v___f_4245_);
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = 0;
v___x_4250_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4248_, v___x_4249_, v___x_4244_, v___f_4247_);
return v___x_4250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4251_, lean_object* v_responseBodyInstance_4252_, lean_object* v___f_4253_, lean_object* v___f_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4251_, v_responseBodyInstance_4252_, v___f_4253_, v___f_4254_, v_x_4255_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4258_, lean_object* v_responseBodyInstance_4259_, lean_object* v_handler_4260_, lean_object* v_config_4261_, lean_object* v___x_4262_, uint8_t v___x_4263_, lean_object* v___f_4264_, lean_object* v_x_4265_){
_start:
{
if (lean_obj_tag(v_x_4265_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4275_; 
lean_dec_ref(v___f_4264_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v_config_4261_);
lean_dec(v_handler_4260_);
lean_dec_ref(v_responseBodyInstance_4259_);
lean_dec_ref(v_h_4258_);
v_a_4267_ = lean_ctor_get(v_x_4265_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_x_4265_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4269_ = v_x_4265_;
v_isShared_4270_ = v_isSharedCheck_4275_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v_x_4265_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4275_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v___x_4273_; 
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
return v___x_4273_;
}
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_a_4276_ = lean_ctor_get(v_x_4265_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v_x_4265_, 1);
v___x_4277_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4258_, v_responseBodyInstance_4259_, v_handler_4260_, v_config_4261_, v_a_4276_, v___x_4262_);
v___x_4278_ = lean_unsigned_to_nat(0u);
v___x_4279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4278_, v___x_4263_, v___x_4277_, v___f_4264_);
return v___x_4279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4280_, lean_object* v_responseBodyInstance_4281_, lean_object* v_handler_4282_, lean_object* v_config_4283_, lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v___f_4286_, lean_object* v_x_4287_, lean_object* v___y_4288_){
_start:
{
uint8_t v___x_5688__boxed_4289_; lean_object* v_res_4290_; 
v___x_5688__boxed_4289_ = lean_unbox(v___x_4285_);
v_res_4290_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4280_, v_responseBodyInstance_4281_, v_handler_4282_, v_config_4283_, v___x_4284_, v___x_5688__boxed_4289_, v___f_4286_, v_x_4287_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4291_, lean_object* v_h_4292_, lean_object* v_responseBodyInstance_4293_, lean_object* v_config_4294_, lean_object* v_handler_4295_, uint8_t v___x_4296_, lean_object* v___f_4297_, lean_object* v_x_4298_){
_start:
{
if (lean_obj_tag(v_x_4298_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4308_; 
lean_dec_ref(v___f_4297_);
lean_dec(v_handler_4295_);
lean_dec_ref(v_config_4294_);
lean_dec_ref(v_responseBodyInstance_4293_);
lean_dec_ref(v_h_4292_);
lean_dec_ref(v_inst_4291_);
v_a_4300_ = lean_ctor_get(v_x_4298_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_x_4298_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4302_ = v_x_4298_;
v_isShared_4303_ = v_isSharedCheck_4308_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v_x_4298_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4308_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
return v___x_4306_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_a_4309_ = lean_ctor_get(v_x_4298_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v_x_4298_, 1);
v___x_4310_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4291_, v_h_4292_, v_responseBodyInstance_4293_, v_config_4294_, v_handler_4295_, v_a_4309_);
v___x_4311_ = lean_unsigned_to_nat(0u);
v___x_4312_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4311_, v___x_4296_, v___x_4310_, v___f_4297_);
return v___x_4312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4313_, lean_object* v_h_4314_, lean_object* v_responseBodyInstance_4315_, lean_object* v_config_4316_, lean_object* v_handler_4317_, lean_object* v___x_4318_, lean_object* v___f_4319_, lean_object* v_x_4320_, lean_object* v___y_4321_){
_start:
{
uint8_t v___x_5729__boxed_4322_; lean_object* v_res_4323_; 
v___x_5729__boxed_4322_ = lean_unbox(v___x_4318_);
v_res_4323_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4313_, v_h_4314_, v_responseBodyInstance_4315_, v_config_4316_, v_handler_4317_, v___x_5729__boxed_4322_, v___f_4319_, v_x_4320_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4324_, lean_object* v_socket_4325_, lean_object* v_connectionContext_4326_, lean_object* v_h_4327_, lean_object* v_responseBodyInstance_4328_, lean_object* v_handler_4329_, lean_object* v_config_4330_, lean_object* v___f_4331_, lean_object* v_inst_4332_, lean_object* v_x_4333_){
_start:
{
if (lean_obj_tag(v_x_4333_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4343_; 
lean_dec_ref(v_inst_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_config_4330_);
lean_dec(v_handler_4329_);
lean_dec_ref(v_responseBodyInstance_4328_);
lean_dec_ref(v_h_4327_);
lean_dec_ref(v_connectionContext_4326_);
lean_dec(v_socket_4325_);
v_a_4335_ = lean_ctor_get(v_x_4333_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_x_4333_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4337_ = v_x_4333_;
v_isShared_4338_ = v_isSharedCheck_4343_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v_x_4333_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4343_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; 
v___x_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
return v___x_4341_;
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4378_; 
v_a_4344_ = lean_ctor_get(v_x_4333_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v_x_4333_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4346_ = v_x_4333_;
v_isShared_4347_ = v_isSharedCheck_4378_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v_x_4333_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4378_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v_machine_4354_; lean_object* v_requestStream_4355_; lean_object* v_keepAliveTimeout_4356_; lean_object* v_currentTimeout_4357_; lean_object* v_headerTimeout_4358_; lean_object* v_response_4359_; lean_object* v_respStream_4360_; uint8_t v_requiresData_4361_; lean_object* v_expectData_4362_; uint8_t v_handlerDispatched_4363_; lean_object* v_pendingHead_4364_; 
v_machine_4354_ = lean_ctor_get(v_a_4344_, 0);
v_requestStream_4355_ = lean_ctor_get(v_a_4344_, 1);
v_keepAliveTimeout_4356_ = lean_ctor_get(v_a_4344_, 2);
v_currentTimeout_4357_ = lean_ctor_get(v_a_4344_, 3);
v_headerTimeout_4358_ = lean_ctor_get(v_a_4344_, 4);
v_response_4359_ = lean_ctor_get(v_a_4344_, 5);
v_respStream_4360_ = lean_ctor_get(v_a_4344_, 6);
v_requiresData_4361_ = lean_ctor_get_uint8(v_a_4344_, sizeof(void*)*9);
v_expectData_4362_ = lean_ctor_get(v_a_4344_, 7);
v_handlerDispatched_4363_ = lean_ctor_get_uint8(v_a_4344_, sizeof(void*)*9 + 1);
v_pendingHead_4364_ = lean_ctor_get(v_a_4344_, 8);
if (v_requiresData_4361_ == 0)
{
if (v_handlerDispatched_4363_ == 0)
{
if (lean_obj_tag(v_respStream_4360_) == 0)
{
lean_object* v_writer_4374_; uint8_t v_sentMessage_4375_; 
v_writer_4374_ = lean_ctor_get(v_machine_4354_, 1);
v_sentMessage_4375_ = lean_ctor_get_uint8(v_writer_4374_, sizeof(void*)*6);
if (v_sentMessage_4375_ == 0)
{
lean_object* v_reader_4376_; lean_object* v_state_4377_; 
v_reader_4376_ = lean_ctor_get(v_machine_4354_, 0);
v_state_4377_ = lean_ctor_get(v_reader_4376_, 0);
if (lean_obj_tag(v_state_4377_) == 2)
{
lean_inc(v_respStream_4360_);
lean_inc(v_pendingHead_4364_);
lean_inc(v_expectData_4362_);
lean_inc_ref(v_response_4359_);
lean_inc(v_headerTimeout_4358_);
lean_inc(v_currentTimeout_4357_);
lean_inc(v_keepAliveTimeout_4356_);
lean_inc_ref(v_requestStream_4355_);
lean_inc_ref(v_machine_4354_);
lean_del_object(v___x_4346_);
lean_dec(v_a_4344_);
goto v___jp_4365_;
}
else
{
lean_dec_ref(v_inst_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_config_4330_);
lean_dec(v_handler_4329_);
lean_dec_ref(v_responseBodyInstance_4328_);
lean_dec_ref(v_h_4327_);
lean_dec_ref(v_connectionContext_4326_);
lean_dec(v_socket_4325_);
goto v___jp_4348_;
}
}
else
{
lean_dec_ref(v_inst_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_config_4330_);
lean_dec(v_handler_4329_);
lean_dec_ref(v_responseBodyInstance_4328_);
lean_dec_ref(v_h_4327_);
lean_dec_ref(v_connectionContext_4326_);
lean_dec(v_socket_4325_);
goto v___jp_4348_;
}
}
else
{
lean_inc_ref(v_respStream_4360_);
lean_inc(v_pendingHead_4364_);
lean_inc(v_expectData_4362_);
lean_inc_ref(v_response_4359_);
lean_inc(v_headerTimeout_4358_);
lean_inc(v_currentTimeout_4357_);
lean_inc(v_keepAliveTimeout_4356_);
lean_inc_ref(v_requestStream_4355_);
lean_inc_ref(v_machine_4354_);
lean_del_object(v___x_4346_);
lean_dec(v_a_4344_);
goto v___jp_4365_;
}
}
else
{
lean_inc(v_pendingHead_4364_);
lean_inc(v_expectData_4362_);
lean_inc(v_respStream_4360_);
lean_inc_ref(v_response_4359_);
lean_inc(v_headerTimeout_4358_);
lean_inc(v_currentTimeout_4357_);
lean_inc(v_keepAliveTimeout_4356_);
lean_inc_ref(v_requestStream_4355_);
lean_inc_ref(v_machine_4354_);
lean_del_object(v___x_4346_);
lean_dec(v_a_4344_);
goto v___jp_4365_;
}
}
else
{
lean_inc(v_pendingHead_4364_);
lean_inc(v_expectData_4362_);
lean_inc(v_respStream_4360_);
lean_inc_ref(v_response_4359_);
lean_inc(v_headerTimeout_4358_);
lean_inc(v_currentTimeout_4357_);
lean_inc(v_keepAliveTimeout_4356_);
lean_inc_ref(v_requestStream_4355_);
lean_inc_ref(v_machine_4354_);
lean_del_object(v___x_4346_);
lean_dec(v_a_4344_);
goto v___jp_4365_;
}
v___jp_4348_:
{
lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4349_, 0, v_a_4344_);
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 0, v___x_4349_);
v___x_4351_ = v___x_4346_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
}
v___jp_4365_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___f_4369_; lean_object* v___x_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4366_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4366_, 0, v_machine_4354_);
lean_ctor_set(v___x_4366_, 1, v_requestStream_4355_);
lean_ctor_set(v___x_4366_, 2, v_keepAliveTimeout_4356_);
lean_ctor_set(v___x_4366_, 3, v_currentTimeout_4357_);
lean_ctor_set(v___x_4366_, 4, v_headerTimeout_4358_);
lean_ctor_set(v___x_4366_, 5, v_response_4359_);
lean_ctor_set(v___x_4366_, 6, v_respStream_4360_);
lean_ctor_set(v___x_4366_, 7, v_expectData_4362_);
lean_ctor_set(v___x_4366_, 8, v_pendingHead_4364_);
lean_ctor_set_uint8(v___x_4366_, sizeof(void*)*9, v___x_4324_);
lean_ctor_set_uint8(v___x_4366_, sizeof(void*)*9 + 1, v_handlerDispatched_4363_);
lean_inc_ref(v___x_4366_);
v___x_4367_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4325_, v_connectionContext_4326_, v___x_4366_);
v___x_4368_ = lean_box(v___x_4324_);
lean_inc_ref(v_config_4330_);
lean_inc(v_handler_4329_);
lean_inc_ref(v_responseBodyInstance_4328_);
lean_inc_ref(v_h_4327_);
v___f_4369_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4369_, 0, v_h_4327_);
lean_closure_set(v___f_4369_, 1, v_responseBodyInstance_4328_);
lean_closure_set(v___f_4369_, 2, v_handler_4329_);
lean_closure_set(v___f_4369_, 3, v_config_4330_);
lean_closure_set(v___f_4369_, 4, v___x_4366_);
lean_closure_set(v___f_4369_, 5, v___x_4368_);
lean_closure_set(v___f_4369_, 6, v___f_4331_);
v___x_4370_ = lean_box(v___x_4324_);
v___f_4371_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4371_, 0, v_inst_4332_);
lean_closure_set(v___f_4371_, 1, v_h_4327_);
lean_closure_set(v___f_4371_, 2, v_responseBodyInstance_4328_);
lean_closure_set(v___f_4371_, 3, v_config_4330_);
lean_closure_set(v___f_4371_, 4, v_handler_4329_);
lean_closure_set(v___f_4371_, 5, v___x_4370_);
lean_closure_set(v___f_4371_, 6, v___f_4369_);
v___x_4372_ = lean_unsigned_to_nat(0u);
v___x_4373_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4372_, v___x_4324_, v___x_4367_, v___f_4371_);
return v___x_4373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4379_, lean_object* v_socket_4380_, lean_object* v_connectionContext_4381_, lean_object* v_h_4382_, lean_object* v_responseBodyInstance_4383_, lean_object* v_handler_4384_, lean_object* v_config_4385_, lean_object* v___f_4386_, lean_object* v_inst_4387_, lean_object* v_x_4388_, lean_object* v___y_4389_){
_start:
{
uint8_t v___x_5769__boxed_4390_; lean_object* v_res_4391_; 
v___x_5769__boxed_4390_ = lean_unbox(v___x_4379_);
v_res_4391_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5769__boxed_4390_, v_socket_4380_, v_connectionContext_4381_, v_h_4382_, v_responseBodyInstance_4383_, v_handler_4384_, v_config_4385_, v___f_4386_, v_inst_4387_, v_x_4388_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4392_, lean_object* v_handler_4393_, lean_object* v_extensions_4394_, lean_object* v_connectionContext_4395_, uint8_t v___x_4396_, lean_object* v___f_4397_, lean_object* v_x_4398_){
_start:
{
if (lean_obj_tag(v_x_4398_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4408_; 
lean_dec_ref(v___f_4397_);
lean_dec_ref(v_connectionContext_4395_);
lean_dec(v_extensions_4394_);
lean_dec(v_handler_4393_);
lean_dec_ref(v_h_4392_);
v_a_4400_ = lean_ctor_get(v_x_4398_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_x_4398_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4402_ = v_x_4398_;
v_isShared_4403_ = v_isSharedCheck_4408_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v_x_4398_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4408_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4406_; 
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
return v___x_4406_;
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4409_ = lean_ctor_get(v_x_4398_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v_x_4398_, 1);
v___x_4410_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4392_, v_handler_4393_, v_extensions_4394_, v_connectionContext_4395_, v_a_4409_);
v___x_4411_ = lean_unsigned_to_nat(0u);
v___x_4412_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4411_, v___x_4396_, v___x_4410_, v___f_4397_);
return v___x_4412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4413_, lean_object* v_handler_4414_, lean_object* v_extensions_4415_, lean_object* v_connectionContext_4416_, lean_object* v___x_4417_, lean_object* v___f_4418_, lean_object* v_x_4419_, lean_object* v___y_4420_){
_start:
{
uint8_t v___x_5844__boxed_4421_; lean_object* v_res_4422_; 
v___x_5844__boxed_4421_ = lean_unbox(v___x_4417_);
v_res_4422_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4413_, v_handler_4414_, v_extensions_4415_, v_connectionContext_4416_, v___x_5844__boxed_4421_, v___f_4418_, v_x_4419_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4423_, lean_object* v_responseBodyInstance_4424_, lean_object* v_handler_4425_, lean_object* v_config_4426_, lean_object* v_connectionContext_4427_, lean_object* v_events_4428_, lean_object* v___x_4429_, uint8_t v___x_4430_, lean_object* v___f_4431_, lean_object* v_____r_4432_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4423_, v_responseBodyInstance_4424_, v_handler_4425_, v_config_4426_, v_connectionContext_4427_, v_events_4428_, v___x_4429_);
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4435_, v___x_4430_, v___x_4434_, v___f_4431_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4437_, lean_object* v_responseBodyInstance_4438_, lean_object* v_handler_4439_, lean_object* v_config_4440_, lean_object* v_connectionContext_4441_, lean_object* v_events_4442_, lean_object* v___x_4443_, lean_object* v___x_4444_, lean_object* v___f_4445_, lean_object* v_____r_4446_, lean_object* v___y_4447_){
_start:
{
uint8_t v___x_5883__boxed_4448_; lean_object* v_res_4449_; 
v___x_5883__boxed_4448_ = lean_unbox(v___x_4444_);
v_res_4449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4437_, v_responseBodyInstance_4438_, v_handler_4439_, v_config_4440_, v_connectionContext_4441_, v_events_4442_, v___x_4443_, v___x_5883__boxed_4448_, v___f_4445_, v_____r_4446_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4450_, lean_object* v___f_4451_, lean_object* v_x_4452_){
_start:
{
if (lean_obj_tag(v_x_4452_) == 0)
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4462_; 
lean_dec_ref(v___f_4451_);
lean_dec_ref(v___x_4450_);
v_a_4454_ = lean_ctor_get(v_x_4452_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_x_4452_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4456_ = v_x_4452_;
v_isShared_4457_ = v_isSharedCheck_4462_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v_x_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4462_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
return v___x_4460_;
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4474_; 
v_a_4463_ = lean_ctor_get(v_x_4452_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_x_4452_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4465_ = v_x_4452_;
v_isShared_4466_ = v_isSharedCheck_4474_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v_x_4452_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4474_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
if (lean_obj_tag(v_a_4463_) == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
lean_dec_ref(v___f_4451_);
v___x_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4450_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4467_);
v___x_4469_ = v___x_4465_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4470_; 
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
}
else
{
lean_object* v_val_4472_; lean_object* v___x_4473_; 
lean_del_object(v___x_4465_);
lean_dec_ref(v___x_4450_);
v_val_4472_ = lean_ctor_get(v_a_4463_, 0);
lean_inc(v_val_4472_);
lean_dec_ref_known(v_a_4463_, 1);
v___x_4473_ = lean_apply_2(v___f_4451_, v_val_4472_, lean_box(0));
return v___x_4473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4475_, lean_object* v___f_4476_, lean_object* v_x_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4475_, v___f_4476_, v_x_4477_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4480_, lean_object* v_responseBodyInstance_4481_, lean_object* v_handler_4482_, lean_object* v_config_4483_, lean_object* v_connectionContext_4484_, uint8_t v___x_4485_, lean_object* v___f_4486_, lean_object* v_inst_4487_, lean_object* v_socket_4488_, lean_object* v___f_4489_, lean_object* v___f_4490_, lean_object* v_x_4491_, lean_object* v_____s_4492_){
_start:
{
lean_object* v_machine_4494_; lean_object* v_reader_4495_; lean_object* v_requestStream_4496_; lean_object* v_keepAliveTimeout_4497_; lean_object* v_currentTimeout_4498_; lean_object* v_headerTimeout_4499_; lean_object* v_response_4500_; lean_object* v_respStream_4501_; uint8_t v_requiresData_4502_; lean_object* v_expectData_4503_; uint8_t v_handlerDispatched_4504_; lean_object* v_pendingHead_4505_; lean_object* v_writer_4506_; lean_object* v_state_4507_; uint8_t v___x_4508_; 
v_machine_4494_ = lean_ctor_get(v_____s_4492_, 0);
v_reader_4495_ = lean_ctor_get(v_machine_4494_, 0);
v_requestStream_4496_ = lean_ctor_get(v_____s_4492_, 1);
v_keepAliveTimeout_4497_ = lean_ctor_get(v_____s_4492_, 2);
v_currentTimeout_4498_ = lean_ctor_get(v_____s_4492_, 3);
v_headerTimeout_4499_ = lean_ctor_get(v_____s_4492_, 4);
v_response_4500_ = lean_ctor_get(v_____s_4492_, 5);
v_respStream_4501_ = lean_ctor_get(v_____s_4492_, 6);
v_requiresData_4502_ = lean_ctor_get_uint8(v_____s_4492_, sizeof(void*)*9);
v_expectData_4503_ = lean_ctor_get(v_____s_4492_, 7);
v_handlerDispatched_4504_ = lean_ctor_get_uint8(v_____s_4492_, sizeof(void*)*9 + 1);
v_pendingHead_4505_ = lean_ctor_get(v_____s_4492_, 8);
v_writer_4506_ = lean_ctor_get(v_machine_4494_, 1);
v_state_4507_ = lean_ctor_get(v_reader_4495_, 0);
v___x_4508_ = 0;
if (lean_obj_tag(v_state_4507_) == 6)
{
lean_object* v_state_4530_; 
v_state_4530_ = lean_ctor_get(v_writer_4506_, 2);
if (lean_obj_tag(v_state_4530_) == 7)
{
lean_object* v_outputData_4531_; lean_object* v_size_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; 
v_outputData_4531_ = lean_ctor_get(v_writer_4506_, 1);
v_size_4532_ = lean_ctor_get(v_outputData_4531_, 1);
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = lean_nat_dec_eq(v_size_4532_, v___x_4533_);
if (v___x_4534_ == 0)
{
lean_inc(v_pendingHead_4505_);
lean_inc(v_expectData_4503_);
lean_inc(v_respStream_4501_);
lean_inc_ref(v_response_4500_);
lean_inc(v_headerTimeout_4499_);
lean_inc(v_currentTimeout_4498_);
lean_inc(v_keepAliveTimeout_4497_);
lean_inc_ref(v_requestStream_4496_);
lean_inc_ref(v_machine_4494_);
lean_dec_ref(v_____s_4492_);
goto v___jp_4509_;
}
else
{
if (v___x_4534_ == 0)
{
lean_inc(v_pendingHead_4505_);
lean_inc(v_expectData_4503_);
lean_inc(v_respStream_4501_);
lean_inc_ref(v_response_4500_);
lean_inc(v_headerTimeout_4499_);
lean_inc(v_currentTimeout_4498_);
lean_inc(v_keepAliveTimeout_4497_);
lean_inc_ref(v_requestStream_4496_);
lean_inc_ref(v_machine_4494_);
lean_dec_ref(v_____s_4492_);
goto v___jp_4509_;
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec_ref(v___f_4490_);
lean_dec_ref(v___f_4489_);
lean_dec(v_socket_4488_);
lean_dec_ref(v_inst_4487_);
lean_dec_ref(v___f_4486_);
lean_dec_ref(v_connectionContext_4484_);
lean_dec_ref(v_config_4483_);
lean_dec(v_handler_4482_);
lean_dec_ref(v_responseBodyInstance_4481_);
lean_dec_ref(v_h_4480_);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v_____s_4492_);
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
}
}
else
{
lean_inc(v_pendingHead_4505_);
lean_inc(v_expectData_4503_);
lean_inc(v_respStream_4501_);
lean_inc_ref(v_response_4500_);
lean_inc(v_headerTimeout_4499_);
lean_inc(v_currentTimeout_4498_);
lean_inc(v_keepAliveTimeout_4497_);
lean_inc_ref(v_requestStream_4496_);
lean_inc_ref(v_machine_4494_);
lean_dec_ref(v_____s_4492_);
goto v___jp_4509_;
}
}
else
{
lean_inc(v_pendingHead_4505_);
lean_inc(v_expectData_4503_);
lean_inc(v_respStream_4501_);
lean_inc_ref(v_response_4500_);
lean_inc(v_headerTimeout_4499_);
lean_inc(v_currentTimeout_4498_);
lean_inc(v_keepAliveTimeout_4497_);
lean_inc_ref(v_requestStream_4496_);
lean_inc_ref(v_machine_4494_);
lean_dec_ref(v_____s_4492_);
goto v___jp_4509_;
}
v___jp_4509_:
{
lean_object* v___x_4510_; lean_object* v_snd_4511_; lean_object* v_output_4512_; lean_object* v_fst_4513_; lean_object* v_events_4514_; lean_object* v_data_4515_; lean_object* v_size_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___f_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4510_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4508_, v_machine_4494_);
v_snd_4511_ = lean_ctor_get(v___x_4510_, 1);
lean_inc(v_snd_4511_);
v_output_4512_ = lean_ctor_get(v_snd_4511_, 1);
lean_inc_ref(v_output_4512_);
v_fst_4513_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_fst_4513_);
lean_dec_ref(v___x_4510_);
v_events_4514_ = lean_ctor_get(v_snd_4511_, 0);
lean_inc_ref_n(v_events_4514_, 2);
lean_dec(v_snd_4511_);
v_data_4515_ = lean_ctor_get(v_output_4512_, 0);
lean_inc_ref(v_data_4515_);
v_size_4516_ = lean_ctor_get(v_output_4512_, 1);
lean_inc(v_size_4516_);
lean_dec_ref(v_output_4512_);
v___x_4517_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4517_, 0, v_fst_4513_);
lean_ctor_set(v___x_4517_, 1, v_requestStream_4496_);
lean_ctor_set(v___x_4517_, 2, v_keepAliveTimeout_4497_);
lean_ctor_set(v___x_4517_, 3, v_currentTimeout_4498_);
lean_ctor_set(v___x_4517_, 4, v_headerTimeout_4499_);
lean_ctor_set(v___x_4517_, 5, v_response_4500_);
lean_ctor_set(v___x_4517_, 6, v_respStream_4501_);
lean_ctor_set(v___x_4517_, 7, v_expectData_4503_);
lean_ctor_set(v___x_4517_, 8, v_pendingHead_4505_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*9, v_requiresData_4502_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*9 + 1, v_handlerDispatched_4504_);
v___x_4518_ = lean_box(v___x_4485_);
lean_inc_ref(v___f_4486_);
lean_inc_ref(v___x_4517_);
lean_inc_ref(v_connectionContext_4484_);
lean_inc_ref(v_config_4483_);
lean_inc(v_handler_4482_);
lean_inc_ref(v_responseBodyInstance_4481_);
lean_inc_ref(v_h_4480_);
v___f_4519_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4519_, 0, v_h_4480_);
lean_closure_set(v___f_4519_, 1, v_responseBodyInstance_4481_);
lean_closure_set(v___f_4519_, 2, v_handler_4482_);
lean_closure_set(v___f_4519_, 3, v_config_4483_);
lean_closure_set(v___f_4519_, 4, v_connectionContext_4484_);
lean_closure_set(v___f_4519_, 5, v_events_4514_);
lean_closure_set(v___f_4519_, 6, v___x_4517_);
lean_closure_set(v___f_4519_, 7, v___x_4518_);
lean_closure_set(v___f_4519_, 8, v___f_4486_);
v___x_4520_ = lean_unsigned_to_nat(0u);
v___x_4521_ = lean_nat_dec_lt(v___x_4520_, v_size_4516_);
lean_dec(v_size_4516_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
lean_dec_ref(v___f_4519_);
lean_dec_ref(v_data_4515_);
lean_dec_ref(v___f_4490_);
lean_dec_ref(v___f_4489_);
lean_dec(v_socket_4488_);
lean_dec_ref(v_inst_4487_);
v___x_4522_ = lean_box(0);
v___x_4523_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4480_, v_responseBodyInstance_4481_, v_handler_4482_, v_config_4483_, v_connectionContext_4484_, v_events_4514_, v___x_4517_, v___x_4485_, v___f_4486_, v___x_4522_);
return v___x_4523_;
}
else
{
lean_object* v_sendAll_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___f_4528_; lean_object* v___x_4529_; 
lean_dec_ref(v_events_4514_);
lean_dec_ref(v___f_4486_);
lean_dec_ref(v_connectionContext_4484_);
lean_dec_ref(v_config_4483_);
lean_dec(v_handler_4482_);
lean_dec_ref(v_responseBodyInstance_4481_);
lean_dec_ref(v_h_4480_);
v_sendAll_4524_ = lean_ctor_get(v_inst_4487_, 1);
lean_inc_ref(v_sendAll_4524_);
lean_dec_ref(v_inst_4487_);
v___x_4525_ = lean_apply_3(v_sendAll_4524_, v_socket_4488_, v_data_4515_, lean_box(0));
v___x_4526_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4520_, v___x_4485_, v___x_4525_, v___f_4489_);
v___x_4527_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4520_, v___x_4485_, v___x_4526_, v___f_4490_);
v___f_4528_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4528_, 0, v___x_4517_);
lean_closure_set(v___f_4528_, 1, v___f_4519_);
v___x_4529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4520_, v___x_4485_, v___x_4527_, v___f_4528_);
return v___x_4529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4538_, lean_object* v_responseBodyInstance_4539_, lean_object* v_handler_4540_, lean_object* v_config_4541_, lean_object* v_connectionContext_4542_, lean_object* v___x_4543_, lean_object* v___f_4544_, lean_object* v_inst_4545_, lean_object* v_socket_4546_, lean_object* v___f_4547_, lean_object* v___f_4548_, lean_object* v_x_4549_, lean_object* v_____s_4550_, lean_object* v___y_4551_){
_start:
{
uint8_t v___x_5957__boxed_4552_; lean_object* v_res_4553_; 
v___x_5957__boxed_4552_ = lean_unbox(v___x_4543_);
v_res_4553_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4538_, v_responseBodyInstance_4539_, v_handler_4540_, v_config_4541_, v_connectionContext_4542_, v___x_5957__boxed_4552_, v___f_4544_, v_inst_4545_, v_socket_4546_, v___f_4547_, v___f_4548_, v_x_4549_, v_____s_4550_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4554_, lean_object* v_x_4555_){
_start:
{
if (lean_obj_tag(v_x_4555_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4565_; 
v_a_4557_ = lean_ctor_get(v_x_4555_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v_x_4555_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4559_ = v_x_4555_;
v_isShared_4560_ = v_isSharedCheck_4565_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v_x_4555_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4565_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
lean_object* v___x_4563_; 
v___x_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
return v___x_4563_;
}
}
}
else
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
lean_dec_ref_known(v_x_4555_, 1);
v___x_4566_ = l_IO_Promise_result_x21___redArg(v_a_4554_);
v___x_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4568_, lean_object* v_x_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4568_, v_x_4569_);
lean_dec(v_a_4568_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4572_, lean_object* v___x_4573_, lean_object* v___x_4574_, uint8_t v___x_4575_, lean_object* v_x_4576_){
_start:
{
if (lean_obj_tag(v_x_4576_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v___x_4574_);
lean_dec(v___x_4573_);
lean_dec_ref(v___f_4572_);
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
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4598_; 
v_a_4587_ = lean_ctor_get(v_x_4576_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v_x_4576_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4589_ = v_x_4576_;
v_isShared_4590_ = v_isSharedCheck_4598_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v_x_4576_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4598_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4591_; lean_object* v___f_4592_; lean_object* v___x_4594_; 
lean_inc(v_a_4587_);
lean_inc(v___x_4573_);
v___x_4591_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4572_, v___x_4573_, v_a_4587_, v___x_4574_);
v___f_4592_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4592_, 0, v_a_4587_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v___x_4591_);
v___x_4594_ = v___x_4589_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4591_);
v___x_4594_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
v___x_4596_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4573_, v___x_4575_, v___x_4595_, v___f_4592_);
return v___x_4596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4599_, lean_object* v___x_4600_, lean_object* v___x_4601_, lean_object* v___x_4602_, lean_object* v_x_4603_, lean_object* v___y_4604_){
_start:
{
uint8_t v___x_6060__boxed_4605_; lean_object* v_res_4606_; 
v___x_6060__boxed_4605_ = lean_unbox(v___x_4602_);
v_res_4606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4599_, v___x_4600_, v___x_4601_, v___x_6060__boxed_4605_, v_x_4603_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4607_, lean_object* v_machine_4608_, lean_object* v_a_4609_, lean_object* v___x_4610_, lean_object* v_socket_4611_, lean_object* v_connectionContext_4612_, lean_object* v_h_4613_, lean_object* v_responseBodyInstance_4614_, lean_object* v_handler_4615_, lean_object* v___f_4616_, lean_object* v_inst_4617_, lean_object* v_extensions_4618_, lean_object* v___f_4619_, lean_object* v___f_4620_, lean_object* v___f_4621_, lean_object* v_x_4622_){
_start:
{
if (lean_obj_tag(v_x_4622_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4632_; 
lean_dec_ref(v___f_4621_);
lean_dec_ref(v___f_4620_);
lean_dec_ref(v___f_4619_);
lean_dec(v_extensions_4618_);
lean_dec_ref(v_inst_4617_);
lean_dec_ref(v___f_4616_);
lean_dec(v_handler_4615_);
lean_dec_ref(v_responseBodyInstance_4614_);
lean_dec_ref(v_h_4613_);
lean_dec_ref(v_connectionContext_4612_);
lean_dec(v_socket_4611_);
lean_dec(v___x_4610_);
lean_dec_ref(v_a_4609_);
lean_dec_ref(v_machine_4608_);
lean_dec_ref(v_config_4607_);
v_a_4624_ = lean_ctor_get(v_x_4622_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v_x_4622_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4626_ = v_x_4622_;
v_isShared_4627_ = v_isSharedCheck_4632_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v_x_4622_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4632_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4624_);
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
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4658_; 
v_a_4633_ = lean_ctor_get(v_x_4622_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_x_4622_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4635_ = v_x_4622_;
v_isShared_4636_ = v_isSharedCheck_4658_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v_x_4622_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4658_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v_keepAliveTimeout_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; uint8_t v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___f_4644_; lean_object* v___x_4645_; lean_object* v___f_4646_; lean_object* v___x_4647_; lean_object* v___f_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___f_4651_; lean_object* v___x_4653_; 
v_keepAliveTimeout_4637_ = lean_ctor_get(v_config_4607_, 5);
lean_inc_n(v_keepAliveTimeout_4637_, 2);
v___x_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4638_, 0, v_keepAliveTimeout_4637_);
v___x_4639_ = lean_box(0);
v___x_4640_ = 0;
v___x_4641_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4641_, 0, v_machine_4608_);
lean_ctor_set(v___x_4641_, 1, v_a_4609_);
lean_ctor_set(v___x_4641_, 2, v___x_4638_);
lean_ctor_set(v___x_4641_, 3, v_keepAliveTimeout_4637_);
lean_ctor_set(v___x_4641_, 4, v___x_4639_);
lean_ctor_set(v___x_4641_, 5, v_a_4633_);
lean_ctor_set(v___x_4641_, 6, v___x_4639_);
lean_ctor_set(v___x_4641_, 7, v___x_4610_);
lean_ctor_set(v___x_4641_, 8, v___x_4639_);
lean_ctor_set_uint8(v___x_4641_, sizeof(void*)*9, v___x_4640_);
lean_ctor_set_uint8(v___x_4641_, sizeof(void*)*9 + 1, v___x_4640_);
v___x_4642_ = lean_io_promise_new();
v___x_4643_ = lean_box(v___x_4640_);
lean_inc_ref(v_inst_4617_);
lean_inc_ref(v_config_4607_);
lean_inc_n(v_handler_4615_, 2);
lean_inc_ref(v_responseBodyInstance_4614_);
lean_inc_ref_n(v_h_4613_, 2);
lean_inc_ref_n(v_connectionContext_4612_, 2);
lean_inc(v_socket_4611_);
v___f_4644_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4644_, 0, v___x_4643_);
lean_closure_set(v___f_4644_, 1, v_socket_4611_);
lean_closure_set(v___f_4644_, 2, v_connectionContext_4612_);
lean_closure_set(v___f_4644_, 3, v_h_4613_);
lean_closure_set(v___f_4644_, 4, v_responseBodyInstance_4614_);
lean_closure_set(v___f_4644_, 5, v_handler_4615_);
lean_closure_set(v___f_4644_, 6, v_config_4607_);
lean_closure_set(v___f_4644_, 7, v___f_4616_);
lean_closure_set(v___f_4644_, 8, v_inst_4617_);
v___x_4645_ = lean_box(v___x_4640_);
v___f_4646_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4646_, 0, v_h_4613_);
lean_closure_set(v___f_4646_, 1, v_handler_4615_);
lean_closure_set(v___f_4646_, 2, v_extensions_4618_);
lean_closure_set(v___f_4646_, 3, v_connectionContext_4612_);
lean_closure_set(v___f_4646_, 4, v___x_4645_);
lean_closure_set(v___f_4646_, 5, v___f_4644_);
v___x_4647_ = lean_box(v___x_4640_);
v___f_4648_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4648_, 0, v_h_4613_);
lean_closure_set(v___f_4648_, 1, v_responseBodyInstance_4614_);
lean_closure_set(v___f_4648_, 2, v_handler_4615_);
lean_closure_set(v___f_4648_, 3, v_config_4607_);
lean_closure_set(v___f_4648_, 4, v_connectionContext_4612_);
lean_closure_set(v___f_4648_, 5, v___x_4647_);
lean_closure_set(v___f_4648_, 6, v___f_4646_);
lean_closure_set(v___f_4648_, 7, v_inst_4617_);
lean_closure_set(v___f_4648_, 8, v_socket_4611_);
lean_closure_set(v___f_4648_, 9, v___f_4619_);
lean_closure_set(v___f_4648_, 10, v___f_4620_);
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = lean_box(v___x_4640_);
v___f_4651_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4651_, 0, v___f_4648_);
lean_closure_set(v___f_4651_, 1, v___x_4649_);
lean_closure_set(v___f_4651_, 2, v___x_4641_);
lean_closure_set(v___f_4651_, 3, v___x_4650_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v___x_4642_);
v___x_4653_ = v___x_4635_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4642_);
v___x_4653_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
v___x_4655_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4649_, v___x_4640_, v___x_4654_, v___f_4651_);
v___x_4656_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4649_, v___x_4640_, v___x_4655_, v___f_4621_);
return v___x_4656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4659_ = _args[0];
lean_object* v_machine_4660_ = _args[1];
lean_object* v_a_4661_ = _args[2];
lean_object* v___x_4662_ = _args[3];
lean_object* v_socket_4663_ = _args[4];
lean_object* v_connectionContext_4664_ = _args[5];
lean_object* v_h_4665_ = _args[6];
lean_object* v_responseBodyInstance_4666_ = _args[7];
lean_object* v_handler_4667_ = _args[8];
lean_object* v___f_4668_ = _args[9];
lean_object* v_inst_4669_ = _args[10];
lean_object* v_extensions_4670_ = _args[11];
lean_object* v___f_4671_ = _args[12];
lean_object* v___f_4672_ = _args[13];
lean_object* v___f_4673_ = _args[14];
lean_object* v_x_4674_ = _args[15];
lean_object* v___y_4675_ = _args[16];
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4659_, v_machine_4660_, v_a_4661_, v___x_4662_, v_socket_4663_, v_connectionContext_4664_, v_h_4665_, v_responseBodyInstance_4666_, v_handler_4667_, v___f_4668_, v_inst_4669_, v_extensions_4670_, v___f_4671_, v___f_4672_, v___f_4673_, v_x_4674_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4677_, lean_object* v_machine_4678_, lean_object* v_socket_4679_, lean_object* v_connectionContext_4680_, lean_object* v_h_4681_, lean_object* v_responseBodyInstance_4682_, lean_object* v_handler_4683_, lean_object* v___f_4684_, lean_object* v_inst_4685_, lean_object* v_extensions_4686_, lean_object* v___f_4687_, lean_object* v___f_4688_, lean_object* v___f_4689_, lean_object* v_x_4690_){
_start:
{
if (lean_obj_tag(v_x_4690_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4700_; 
lean_dec_ref(v___f_4689_);
lean_dec_ref(v___f_4688_);
lean_dec_ref(v___f_4687_);
lean_dec(v_extensions_4686_);
lean_dec_ref(v_inst_4685_);
lean_dec_ref(v___f_4684_);
lean_dec(v_handler_4683_);
lean_dec_ref(v_responseBodyInstance_4682_);
lean_dec_ref(v_h_4681_);
lean_dec_ref(v_connectionContext_4680_);
lean_dec(v_socket_4679_);
lean_dec_ref(v_machine_4678_);
lean_dec_ref(v_config_4677_);
v_a_4692_ = lean_ctor_get(v_x_4690_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v_x_4690_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4694_ = v_x_4690_;
v_isShared_4695_ = v_isSharedCheck_4700_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v_x_4690_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4700_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
lean_object* v___x_4698_; 
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
return v___x_4698_;
}
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4715_; 
v_a_4701_ = lean_ctor_get(v_x_4690_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_x_4690_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4703_ = v_x_4690_;
v_isShared_4704_ = v_isSharedCheck_4715_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v_x_4690_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4715_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___f_4707_; lean_object* v___x_4709_; 
v___x_4705_ = lean_box(0);
v___x_4706_ = l_Std_CloseableChannel_new___redArg(v___x_4705_);
v___f_4707_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4707_, 0, v_config_4677_);
lean_closure_set(v___f_4707_, 1, v_machine_4678_);
lean_closure_set(v___f_4707_, 2, v_a_4701_);
lean_closure_set(v___f_4707_, 3, v___x_4705_);
lean_closure_set(v___f_4707_, 4, v_socket_4679_);
lean_closure_set(v___f_4707_, 5, v_connectionContext_4680_);
lean_closure_set(v___f_4707_, 6, v_h_4681_);
lean_closure_set(v___f_4707_, 7, v_responseBodyInstance_4682_);
lean_closure_set(v___f_4707_, 8, v_handler_4683_);
lean_closure_set(v___f_4707_, 9, v___f_4684_);
lean_closure_set(v___f_4707_, 10, v_inst_4685_);
lean_closure_set(v___f_4707_, 11, v_extensions_4686_);
lean_closure_set(v___f_4707_, 12, v___f_4687_);
lean_closure_set(v___f_4707_, 13, v___f_4688_);
lean_closure_set(v___f_4707_, 14, v___f_4689_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 0, v___x_4706_);
v___x_4709_ = v___x_4703_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4706_);
v___x_4709_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; lean_object* v___x_4713_; 
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
v___x_4711_ = lean_unsigned_to_nat(0u);
v___x_4712_ = 0;
v___x_4713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4711_, v___x_4712_, v___x_4710_, v___f_4707_);
return v___x_4713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4716_, lean_object* v_machine_4717_, lean_object* v_socket_4718_, lean_object* v_connectionContext_4719_, lean_object* v_h_4720_, lean_object* v_responseBodyInstance_4721_, lean_object* v_handler_4722_, lean_object* v___f_4723_, lean_object* v_inst_4724_, lean_object* v_extensions_4725_, lean_object* v___f_4726_, lean_object* v___f_4727_, lean_object* v___f_4728_, lean_object* v_x_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4716_, v_machine_4717_, v_socket_4718_, v_connectionContext_4719_, v_h_4720_, v_responseBodyInstance_4721_, v_handler_4722_, v___f_4723_, v_inst_4724_, v_extensions_4725_, v___f_4726_, v___f_4727_, v___f_4728_, v_x_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4735_, lean_object* v_h_4736_, lean_object* v_connection_4737_, lean_object* v_config_4738_, lean_object* v_connectionContext_4739_, lean_object* v_handler_4740_){
_start:
{
lean_object* v_responseBodyInstance_4742_; lean_object* v_onFailure_4743_; lean_object* v___x_4744_; lean_object* v_socket_4745_; lean_object* v_machine_4746_; lean_object* v_extensions_4747_; lean_object* v___f_4748_; lean_object* v___f_4749_; lean_object* v___f_4750_; lean_object* v___f_4751_; lean_object* v___f_4752_; lean_object* v___f_4753_; lean_object* v___f_4754_; lean_object* v___f_4755_; lean_object* v___f_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; lean_object* v___x_4759_; 
v_responseBodyInstance_4742_ = lean_ctor_get(v_h_4736_, 0);
lean_inc_ref_n(v_responseBodyInstance_4742_, 2);
v_onFailure_4743_ = lean_ctor_get(v_h_4736_, 2);
v___x_4744_ = l_Std_Http_Body_mkStream();
v_socket_4745_ = lean_ctor_get(v_connection_4737_, 0);
lean_inc_n(v_socket_4745_, 2);
v_machine_4746_ = lean_ctor_get(v_connection_4737_, 1);
lean_inc_ref(v_machine_4746_);
v_extensions_4747_ = lean_ctor_get(v_connection_4737_, 2);
lean_inc(v_extensions_4747_);
lean_dec_ref(v_connection_4737_);
v___f_4748_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4749_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4750_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4751_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4740_);
lean_inc_ref(v_onFailure_4743_);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4752_, 0, v_onFailure_4743_);
lean_closure_set(v___f_4752_, 1, v_handler_4740_);
lean_closure_set(v___f_4752_, 2, v___f_4751_);
lean_inc_ref(v_inst_4735_);
v___f_4753_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4753_, 0, v_inst_4735_);
lean_closure_set(v___f_4753_, 1, v_socket_4745_);
lean_inc_ref(v___f_4753_);
v___f_4754_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4754_, 0, v___f_4753_);
v___f_4755_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4755_, 0, v___f_4748_);
lean_closure_set(v___f_4755_, 1, v_responseBodyInstance_4742_);
lean_closure_set(v___f_4755_, 2, v___f_4754_);
lean_closure_set(v___f_4755_, 3, v___f_4753_);
v___f_4756_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4756_, 0, v_config_4738_);
lean_closure_set(v___f_4756_, 1, v_machine_4746_);
lean_closure_set(v___f_4756_, 2, v_socket_4745_);
lean_closure_set(v___f_4756_, 3, v_connectionContext_4739_);
lean_closure_set(v___f_4756_, 4, v_h_4736_);
lean_closure_set(v___f_4756_, 5, v_responseBodyInstance_4742_);
lean_closure_set(v___f_4756_, 6, v_handler_4740_);
lean_closure_set(v___f_4756_, 7, v___f_4749_);
lean_closure_set(v___f_4756_, 8, v_inst_4735_);
lean_closure_set(v___f_4756_, 9, v_extensions_4747_);
lean_closure_set(v___f_4756_, 10, v___f_4750_);
lean_closure_set(v___f_4756_, 11, v___f_4752_);
lean_closure_set(v___f_4756_, 12, v___f_4755_);
v___x_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = 0;
v___x_4759_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4757_, v___x_4758_, v___x_4744_, v___f_4756_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4760_, lean_object* v_h_4761_, lean_object* v_connection_4762_, lean_object* v_config_4763_, lean_object* v_connectionContext_4764_, lean_object* v_handler_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4760_, v_h_4761_, v_connection_4762_, v_config_4763_, v_connectionContext_4764_, v_handler_4765_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4768_, lean_object* v_00_u03c3_4769_, lean_object* v_inst_4770_, lean_object* v_h_4771_, lean_object* v_connection_4772_, lean_object* v_config_4773_, lean_object* v_connectionContext_4774_, lean_object* v_handler_4775_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4770_, v_h_4771_, v_connection_4772_, v_config_4773_, v_connectionContext_4774_, v_handler_4775_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4778_, lean_object* v_00_u03c3_4779_, lean_object* v_inst_4780_, lean_object* v_h_4781_, lean_object* v_connection_4782_, lean_object* v_config_4783_, lean_object* v_connectionContext_4784_, lean_object* v_handler_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4778_, v_00_u03c3_4779_, v_inst_4780_, v_h_4781_, v_connection_4782_, v_config_4783_, v_connectionContext_4784_, v_handler_4785_);
return v_res_4787_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = 0;
v___x_4789_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4788_);
return v___x_4789_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4790_ = lean_unsigned_to_nat(4096u);
v___x_4791_ = lean_mk_empty_byte_array(v___x_4790_);
return v___x_4791_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4793_ = l_ByteArray_mkIterator(v___x_4792_);
return v___x_4793_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4794_ = 0;
v___x_4795_ = lean_unsigned_to_nat(0u);
v___x_4796_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4797_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4798_ = lean_box(0);
v___x_4799_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
lean_ctor_set(v___x_4799_, 1, v___x_4797_);
lean_ctor_set(v___x_4799_, 2, v___x_4796_);
lean_ctor_set(v___x_4799_, 3, v___x_4795_);
lean_ctor_set(v___x_4799_, 4, v___x_4795_);
lean_ctor_set(v___x_4799_, 5, v___x_4795_);
lean_ctor_set_uint8(v___x_4799_, sizeof(void*)*6, v___x_4794_);
return v___x_4799_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = 1;
v___x_4808_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4807_);
return v___x_4808_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4809_; uint8_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = 0;
v___x_4811_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4812_ = lean_box(0);
v___x_4813_ = lean_box(0);
v___x_4814_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4815_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4816_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
lean_ctor_set(v___x_4816_, 1, v___x_4814_);
lean_ctor_set(v___x_4816_, 2, v___x_4813_);
lean_ctor_set(v___x_4816_, 3, v___x_4812_);
lean_ctor_set(v___x_4816_, 4, v___x_4811_);
lean_ctor_set(v___x_4816_, 5, v___x_4809_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*6, v___x_4810_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*6 + 1, v___x_4810_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*6 + 2, v___x_4810_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4817_, lean_object* v_client_4818_, lean_object* v_extensions_4819_, lean_object* v_inst_4820_, lean_object* v_inst_4821_, lean_object* v_handler_4822_, lean_object* v_x_4823_){
_start:
{
if (lean_obj_tag(v_x_4823_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4833_; 
lean_dec(v_handler_4822_);
lean_dec_ref(v_inst_4821_);
lean_dec_ref(v_inst_4820_);
lean_dec(v_extensions_4819_);
lean_dec(v_client_4818_);
lean_dec_ref(v_config_4817_);
v_a_4825_ = lean_ctor_get(v_x_4823_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_x_4823_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4827_ = v_x_4823_;
v_isShared_4828_ = v_isSharedCheck_4833_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v_x_4823_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4833_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
}
}
else
{
lean_object* v_a_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v_enableKeepAlive_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v_a_4834_ = lean_ctor_get(v_x_4823_, 0);
lean_inc(v_a_4834_);
lean_dec_ref_known(v_x_4823_, 1);
v___x_4835_ = 0;
v___x_4836_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4837_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4838_ = lean_box(0);
v___x_4839_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4840_ = l_Std_Http_Config_toH1Config(v_config_4817_);
v_enableKeepAlive_4841_ = lean_ctor_get_uint8(v___x_4840_, sizeof(void*)*18);
v___x_4842_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4842_, 0, v___x_4836_);
lean_ctor_set(v___x_4842_, 1, v___x_4839_);
lean_ctor_set(v___x_4842_, 2, v___x_4840_);
lean_ctor_set(v___x_4842_, 3, v___x_4837_);
lean_ctor_set(v___x_4842_, 4, v___x_4838_);
lean_ctor_set(v___x_4842_, 5, v___x_4838_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*6, v_enableKeepAlive_4841_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*6 + 1, v___x_4835_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*6 + 2, v___x_4835_);
v___x_4843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4843_, 0, v_client_4818_);
lean_ctor_set(v___x_4843_, 1, v___x_4842_);
lean_ctor_set(v___x_4843_, 2, v_extensions_4819_);
v___x_4844_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4820_, v_inst_4821_, v___x_4843_, v_config_4817_, v_a_4834_, v_handler_4822_);
return v___x_4844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4845_, lean_object* v_client_4846_, lean_object* v_extensions_4847_, lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_handler_4850_, lean_object* v_x_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4845_, v_client_4846_, v_extensions_4847_, v_inst_4848_, v_inst_4849_, v_handler_4850_, v_x_4851_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_client_4856_, lean_object* v_handler_4857_, lean_object* v_config_4858_, lean_object* v_extensions_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v___f_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; lean_object* v___x_4867_; 
v___f_4862_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4862_, 0, v_config_4858_);
lean_closure_set(v___f_4862_, 1, v_client_4856_);
lean_closure_set(v___f_4862_, 2, v_extensions_4859_);
lean_closure_set(v___f_4862_, 3, v_inst_4854_);
lean_closure_set(v___f_4862_, 4, v_inst_4855_);
lean_closure_set(v___f_4862_, 5, v_handler_4857_);
lean_inc_ref(v_a_4860_);
v___x_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4863_, 0, v_a_4860_);
v___x_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
v___x_4865_ = lean_unsigned_to_nat(0u);
v___x_4866_ = 0;
v___x_4867_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4865_, v___x_4866_, v___x_4864_, v___f_4862_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4868_, lean_object* v_inst_4869_, lean_object* v_client_4870_, lean_object* v_handler_4871_, lean_object* v_config_4872_, lean_object* v_extensions_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4868_, v_inst_4869_, v_client_4870_, v_handler_4871_, v_config_4872_, v_extensions_4873_, v_a_4874_);
lean_dec_ref(v_a_4874_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4877_, lean_object* v_00_u03c3_4878_, lean_object* v_inst_4879_, lean_object* v_inst_4880_, lean_object* v_client_4881_, lean_object* v_handler_4882_, lean_object* v_config_4883_, lean_object* v_extensions_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4879_, v_inst_4880_, v_client_4881_, v_handler_4882_, v_config_4883_, v_extensions_4884_, v_a_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4888_, lean_object* v_00_u03c3_4889_, lean_object* v_inst_4890_, lean_object* v_inst_4891_, lean_object* v_client_4892_, lean_object* v_handler_4893_, lean_object* v_config_4894_, lean_object* v_extensions_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Std_Http_Server_serveConnection(v_t_4888_, v_00_u03c3_4889_, v_inst_4890_, v_inst_4891_, v_client_4892_, v_handler_4893_, v_config_4894_, v_extensions_4895_, v_a_4896_);
lean_dec_ref(v_a_4896_);
return v_res_4898_;
}
}
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
