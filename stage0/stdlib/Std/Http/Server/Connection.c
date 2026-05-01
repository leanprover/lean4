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
extern lean_object* l_Std_Time_TimeZone_UTC;
lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_56_);
v___x_59_ = lean_apply_1(v_k_57_, v_x_58_);
return v___x_59_;
}
case 1:
{
lean_object* v_x_60_; lean_object* v___x_61_; 
v_x_60_ = lean_ctor_get(v_t_56_, 0);
lean_inc(v_x_60_);
lean_dec_ref(v_t_56_);
v___x_61_ = lean_apply_1(v_k_57_, v_x_60_);
return v___x_61_;
}
case 2:
{
uint8_t v_x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_x_62_ = lean_ctor_get_uint8(v_t_56_, 0);
lean_dec_ref(v_t_56_);
v___x_63_ = lean_box(v_x_62_);
v___x_64_ = lean_apply_1(v_k_57_, v___x_63_);
return v___x_64_;
}
case 3:
{
lean_object* v_x_65_; lean_object* v___x_66_; 
v_x_65_ = lean_ctor_get(v_t_56_, 0);
lean_inc_ref(v_x_65_);
lean_dec_ref(v_t_56_);
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
lean_dec_ref(v_x_152_);
if (lean_obj_tag(v_a_165_) == 1)
{
lean_object* v_val_166_; 
v_val_166_ = lean_ctor_get(v_a_165_, 0);
lean_inc(v_val_166_);
lean_dec_ref(v_a_165_);
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
lean_dec_ref(v_x_175_);
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
lean_dec_ref(v_x_193_);
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
lean_dec_ref(v_responseBody_253_);
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
lean_dec_ref(v_response_248_);
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
lean_dec_ref(v_requestBody_251_);
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
lean_dec_ref(v_x_313_);
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
lean_dec_ref(v_x_343_);
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
lean_dec_ref(v_expect_408_);
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
lean_dec_ref(v_socket_407_);
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
lean_dec_ref(v_headerTimeout_414_);
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
lean_dec_ref(v_keepAliveTimeout_413_);
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
lean_dec_ref(v_x_508_);
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
lean_dec_ref(v_x_550_);
v___x_552_ = lean_task_pure(v_a_551_);
return v___x_552_;
}
else
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v_x_550_, 0);
lean_inc_ref(v_a_553_);
lean_dec_ref(v_x_550_);
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
lean_dec_ref(v_x_555_);
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
lean_dec_ref(v_x_555_);
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
lean_dec_ref(v_x_587_);
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
lean_dec_ref(v_x_630_);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Rat_ofInt(v_a_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
return v_x_807_;
}
else
{
lean_object* v_key_809_; lean_object* v_value_810_; lean_object* v_tail_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_834_; 
v_key_809_ = lean_ctor_get(v_x_808_, 0);
v_value_810_ = lean_ctor_get(v_x_808_, 1);
v_tail_811_ = lean_ctor_get(v_x_808_, 2);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_834_ == 0)
{
v___x_813_ = v_x_808_;
v_isShared_814_ = v_isSharedCheck_834_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_tail_811_);
lean_inc(v_value_810_);
lean_inc(v_key_809_);
lean_dec(v_x_808_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_834_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v_fold_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_815_ = lean_array_get_size(v_x_807_);
v___x_816_ = lean_string_hash(v_key_809_);
v___x_817_ = 32ULL;
v___x_818_ = lean_uint64_shift_right(v___x_816_, v___x_817_);
v_fold_819_ = lean_uint64_xor(v___x_816_, v___x_818_);
v___x_820_ = 16ULL;
v___x_821_ = lean_uint64_shift_right(v_fold_819_, v___x_820_);
v___x_822_ = lean_uint64_xor(v_fold_819_, v___x_821_);
v___x_823_ = lean_uint64_to_usize(v___x_822_);
v___x_824_ = lean_usize_of_nat(v___x_815_);
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_sub(v___x_824_, v___x_825_);
v___x_827_ = lean_usize_land(v___x_823_, v___x_826_);
v___x_828_ = lean_array_uget_borrowed(v_x_807_, v___x_827_);
lean_inc(v___x_828_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 2, v___x_828_);
v___x_830_ = v___x_813_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_key_809_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_value_810_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v___x_828_);
v___x_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; 
v___x_831_ = lean_array_uset(v_x_807_, v___x_827_, v___x_830_);
v_x_807_ = v___x_831_;
v_x_808_ = v_tail_811_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object* v_i_835_, lean_object* v_source_836_, lean_object* v_target_837_){
_start:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_array_get_size(v_source_836_);
v___x_839_ = lean_nat_dec_lt(v_i_835_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v_source_836_);
lean_dec(v_i_835_);
return v_target_837_;
}
else
{
lean_object* v_es_840_; lean_object* v___x_841_; lean_object* v_source_842_; lean_object* v_target_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_es_840_ = lean_array_fget(v_source_836_, v_i_835_);
v___x_841_ = lean_box(0);
v_source_842_ = lean_array_fset(v_source_836_, v_i_835_, v___x_841_);
v_target_843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_target_837_, v_es_840_);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_add(v_i_835_, v___x_844_);
lean_dec(v_i_835_);
v_i_835_ = v___x_845_;
v_source_836_ = v_source_842_;
v_target_837_ = v_target_843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object* v_data_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_nbuckets_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_848_ = lean_array_get_size(v_data_847_);
v___x_849_ = lean_unsigned_to_nat(2u);
v_nbuckets_850_ = lean_nat_mul(v___x_848_, v___x_849_);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_box(0);
v___x_853_ = lean_mk_array(v_nbuckets_850_, v___x_852_);
v___x_854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v___x_851_, v_data_847_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = lean_array_push(v___x_858_, v_i_855_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_val_861_ = lean_ctor_get(v_x_856_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v_x_856_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v_x_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_array_push(v_val_861_, v_i_855_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_870_, lean_object* v_a_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_val_875_; lean_object* v___x_876_; 
v___x_873_ = lean_box(0);
v___x_874_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_870_, v___x_873_);
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec(v___x_874_);
v___x_876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_876_, 0, v_a_871_);
lean_ctor_set(v___x_876_, 1, v_val_875_);
lean_ctor_set(v___x_876_, 2, v_x_872_);
return v___x_876_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_894_; 
v_key_877_ = lean_ctor_get(v_x_872_, 0);
v_value_878_ = lean_ctor_get(v_x_872_, 1);
v_tail_879_ = lean_ctor_get(v_x_872_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_894_ == 0)
{
v___x_881_ = v_x_872_;
v_isShared_882_ = v_isSharedCheck_894_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_inc(v_value_878_);
lean_inc(v_key_877_);
lean_dec(v_x_872_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_894_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; 
v___x_883_ = lean_string_dec_eq(v_key_877_, v_a_871_);
if (v___x_883_ == 0)
{
lean_object* v_tail_884_; lean_object* v___x_886_; 
v_tail_884_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_870_, v_a_871_, v_tail_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 2, v_tail_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_key_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_value_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_tail_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_val_890_; lean_object* v___x_892_; 
lean_dec(v_key_877_);
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_value_878_);
v___x_889_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_870_, v___x_888_);
v_val_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_890_);
lean_dec(v___x_889_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_val_890_);
lean_ctor_set(v___x_881_, 0, v_a_871_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_val_890_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_tail_879_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_896_) == 0)
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
else
{
lean_object* v_key_898_; lean_object* v_tail_899_; uint8_t v___x_900_; 
v_key_898_ = lean_ctor_get(v_x_896_, 0);
v_tail_899_ = lean_ctor_get(v_x_896_, 2);
v___x_900_ = lean_string_dec_eq(v_key_898_, v_a_895_);
if (v___x_900_ == 0)
{
v_x_896_ = v_tail_899_;
goto _start;
}
else
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_902_, lean_object* v_x_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec_ref(v_a_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_906_, lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_size_909_; lean_object* v_buckets_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_960_; 
v_size_909_ = lean_ctor_get(v_m_907_, 0);
v_buckets_910_ = lean_ctor_get(v_m_907_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_m_907_);
if (v_isSharedCheck_960_ == 0)
{
v___x_912_ = v_m_907_;
v_isShared_913_ = v_isSharedCheck_960_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_buckets_910_);
lean_inc(v_size_909_);
lean_dec(v_m_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_960_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v_fold_918_; uint64_t v___x_919_; uint64_t v___x_920_; uint64_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v_bkt_927_; uint8_t v___x_928_; 
v___x_914_ = lean_array_get_size(v_buckets_910_);
v___x_915_ = lean_string_hash(v_a_908_);
v___x_916_ = 32ULL;
v___x_917_ = lean_uint64_shift_right(v___x_915_, v___x_916_);
v_fold_918_ = lean_uint64_xor(v___x_915_, v___x_917_);
v___x_919_ = 16ULL;
v___x_920_ = lean_uint64_shift_right(v_fold_918_, v___x_919_);
v___x_921_ = lean_uint64_xor(v_fold_918_, v___x_920_);
v___x_922_ = lean_uint64_to_usize(v___x_921_);
v___x_923_ = lean_usize_of_nat(v___x_914_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_sub(v___x_923_, v___x_924_);
v___x_926_ = lean_usize_land(v___x_922_, v___x_925_);
v_bkt_927_ = lean_array_uget_borrowed(v_buckets_910_, v___x_926_);
v___x_928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_908_, v_bkt_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_size_x27_932_; lean_object* v___x_933_; lean_object* v_buckets_x27_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
v___x_931_ = lean_array_push(v___x_930_, v_i_906_);
v_size_x27_932_ = lean_nat_add(v_size_909_, v___x_929_);
lean_dec(v_size_909_);
lean_inc(v_bkt_927_);
v___x_933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_933_, 0, v_a_908_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
lean_ctor_set(v___x_933_, 2, v_bkt_927_);
v_buckets_x27_934_ = lean_array_uset(v_buckets_910_, v___x_926_, v___x_933_);
v___x_935_ = lean_unsigned_to_nat(4u);
v___x_936_ = lean_nat_mul(v_size_x27_932_, v___x_935_);
v___x_937_ = lean_unsigned_to_nat(3u);
v___x_938_ = lean_nat_div(v___x_936_, v___x_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_array_get_size(v_buckets_x27_934_);
v___x_940_ = lean_nat_dec_le(v___x_938_, v___x_939_);
lean_dec(v___x_938_);
if (v___x_940_ == 0)
{
lean_object* v_val_941_; lean_object* v___x_943_; 
v_val_941_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_934_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_val_941_);
lean_ctor_set(v___x_912_, 0, v_size_x27_932_);
v___x_943_ = v___x_912_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_size_x27_932_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_val_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
lean_object* v___x_946_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_buckets_x27_934_);
lean_ctor_set(v___x_912_, 0, v_size_x27_932_);
v___x_946_ = v___x_912_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_size_x27_932_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_buckets_x27_934_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v___x_948_; lean_object* v_buckets_x27_949_; lean_object* v_bkt_x27_950_; lean_object* v___y_952_; uint8_t v___x_957_; 
lean_inc(v_bkt_927_);
v___x_948_ = lean_box(0);
v_buckets_x27_949_ = lean_array_uset(v_buckets_910_, v___x_926_, v___x_948_);
lean_inc_ref(v_a_908_);
v_bkt_x27_950_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_906_, v_a_908_, v_bkt_927_);
v___x_957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_908_, v_bkt_x27_950_);
lean_dec_ref(v_a_908_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_sub(v_size_909_, v___x_958_);
lean_dec(v_size_909_);
v___y_952_ = v___x_959_;
goto v___jp_951_;
}
else
{
v___y_952_ = v_size_909_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_array_uset(v_buckets_x27_949_, v___x_926_, v_bkt_x27_950_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_953_);
lean_ctor_set(v___x_912_, 0, v___y_952_);
v___x_955_ = v___x_912_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___y_952_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v___x_961_, lean_object* v_entries_962_, lean_object* v_indexes_963_, lean_object* v_status_964_, uint8_t v_version_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_status_964_);
lean_dec_ref(v_indexes_963_);
lean_dec_ref(v_entries_962_);
v_a_968_ = lean_ctor_get(v_x_966_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v_x_966_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v_x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_994_; 
v_a_977_ = lean_ctor_get(v_x_966_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_994_ == 0)
{
v___x_979_ = v_x_966_;
v_isShared_980_ = v_isSharedCheck_994_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v_x_966_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_994_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_i_984_; lean_object* v___x_985_; lean_object* v_entries_986_; lean_object* v_indexes_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_981_ = l_Std_Http_Header_Name_date;
v___x_982_ = l_Std_Time_DateTime_toRFC822String(v___x_961_, v_a_977_);
v___x_983_ = l_Std_Http_Header_Value_ofString_x21(v___x_982_);
v_i_984_ = lean_array_get_size(v_entries_962_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_981_);
lean_ctor_set(v___x_985_, 1, v___x_983_);
v_entries_986_ = lean_array_push(v_entries_962_, v___x_985_);
v_indexes_987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_984_, v_indexes_963_, v___x_981_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_entries_986_);
lean_ctor_set(v___x_988_, 1, v_indexes_987_);
v___x_989_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_989_, 0, v_status_964_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*2, v_version_965_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_989_);
v___x_991_ = v___x_979_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v___x_995_, lean_object* v_entries_996_, lean_object* v_indexes_997_, lean_object* v_status_998_, lean_object* v_version_999_, lean_object* v_x_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_version_boxed_1002_; lean_object* v_res_1003_; 
v_version_boxed_1002_ = lean_unbox(v_version_999_);
v_res_1003_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v___x_995_, v_entries_996_, v_indexes_997_, v_status_998_, v_version_boxed_1002_, v_x_1000_);
lean_dec_ref(v___x_995_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_a_1004_, lean_object* v___x_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_second_1009_; lean_object* v_nano_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_second_1015_; lean_object* v_nano_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1007_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_a_1004_);
v___x_1008_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1007_);
v_second_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_second_1009_);
v_nano_1010_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_nano_1010_);
lean_dec_ref(v___x_1008_);
v___x_1011_ = l_Std_Time_TimeZone_toSeconds(v___x_1005_);
v___x_1012_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_1013_ = lean_int_mul(v___x_1011_, v___x_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = l_Std_Time_Duration_ofNanoseconds(v___x_1013_);
lean_dec(v___x_1013_);
v_second_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_second_1015_);
v_nano_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_nano_1016_);
lean_dec_ref(v___x_1014_);
v___x_1017_ = lean_int_mul(v_second_1009_, v___x_1012_);
lean_dec(v_second_1009_);
v___x_1018_ = lean_int_add(v___x_1017_, v_nano_1010_);
lean_dec(v_nano_1010_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_int_mul(v_second_1015_, v___x_1012_);
lean_dec(v_second_1015_);
v___x_1020_ = lean_int_add(v___x_1019_, v_nano_1016_);
lean_dec(v_nano_1016_);
lean_dec(v___x_1019_);
v___x_1021_ = lean_int_add(v___x_1018_, v___x_1020_);
lean_dec(v___x_1020_);
lean_dec(v___x_1018_);
v___x_1022_ = l_Std_Time_Duration_ofNanoseconds(v___x_1021_);
lean_dec(v___x_1021_);
v___x_1023_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_a_1024_, lean_object* v___x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_a_1024_, v___x_1025_, v_x_1026_);
lean_dec_ref(v___x_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(lean_object* v_m_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_buckets_1030_; lean_object* v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v_fold_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_buckets_1030_ = lean_ctor_get(v_m_1028_, 1);
v___x_1031_ = lean_array_get_size(v_buckets_1030_);
v___x_1032_ = lean_string_hash(v_a_1029_);
v___x_1033_ = 32ULL;
v___x_1034_ = lean_uint64_shift_right(v___x_1032_, v___x_1033_);
v_fold_1035_ = lean_uint64_xor(v___x_1032_, v___x_1034_);
v___x_1036_ = 16ULL;
v___x_1037_ = lean_uint64_shift_right(v_fold_1035_, v___x_1036_);
v___x_1038_ = lean_uint64_xor(v_fold_1035_, v___x_1037_);
v___x_1039_ = lean_uint64_to_usize(v___x_1038_);
v___x_1040_ = lean_usize_of_nat(v___x_1031_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_sub(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_usize_land(v___x_1039_, v___x_1042_);
v___x_1044_ = lean_array_uget_borrowed(v_buckets_1030_, v___x_1043_);
v___x_1045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1029_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg___boxed(lean_object* v_m_1046_, lean_object* v_a_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_m_1046_, v_a_1047_);
lean_dec_ref(v_a_1047_);
lean_dec_ref(v_m_1046_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1050_, lean_object* v_head_1051_){
_start:
{
uint8_t v_generateDate_1056_; 
v_generateDate_1056_ = lean_ctor_get_uint8(v_config_1050_, sizeof(void*)*24 + 1);
if (v_generateDate_1056_ == 0)
{
goto v___jp_1053_;
}
else
{
lean_object* v_headers_1057_; lean_object* v_status_1058_; uint8_t v_version_1059_; lean_object* v_entries_1060_; lean_object* v_indexes_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1097_; 
v_headers_1057_ = lean_ctor_get(v_head_1051_, 1);
lean_inc_ref(v_headers_1057_);
v_status_1058_ = lean_ctor_get(v_head_1051_, 0);
v_version_1059_ = lean_ctor_get_uint8(v_head_1051_, sizeof(void*)*2);
v_entries_1060_ = lean_ctor_get(v_headers_1057_, 0);
v_indexes_1061_ = lean_ctor_get(v_headers_1057_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_headers_1057_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1063_ = v_headers_1057_;
v_isShared_1064_ = v_isSharedCheck_1097_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_indexes_1061_);
lean_inc(v_entries_1060_);
lean_dec(v_headers_1057_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1097_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = l_Std_Http_Header_Name_date;
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_indexes_1061_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v_val_1071_; lean_object* v___x_1075_; 
lean_inc(v_status_1058_);
lean_dec_ref(v_head_1051_);
v___x_1067_ = l_Std_Time_TimeZone_UTC;
v___x_1068_ = lean_box(v_version_1059_);
v___f_1069_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1069_, 0, v___x_1067_);
lean_closure_set(v___f_1069_, 1, v_entries_1060_);
lean_closure_set(v___f_1069_, 2, v_indexes_1061_);
lean_closure_set(v___f_1069_, 3, v_status_1058_);
lean_closure_set(v___f_1069_, 4, v___x_1068_);
v___x_1075_ = lean_get_current_time();
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1088_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1088_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1088_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_inc(v_a_1076_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1080_, 0, v_a_1076_);
lean_closure_set(v___f_1080_, 1, v___x_1067_);
v___x_1081_ = lean_mk_thunk(v___f_1080_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1081_);
lean_ctor_set(v___x_1063_, 0, v_a_1076_);
v___x_1083_ = v___x_1063_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1076_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 1);
lean_ctor_set(v___x_1078_, 0, v___x_1083_);
v___x_1085_ = v___x_1078_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v_val_1071_ = v___x_1085_;
goto v___jp_1070_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1063_);
v_a_1089_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1075_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1075_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 0);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_val_1071_ = v___x_1094_;
goto v___jp_1070_;
}
}
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_val_1071_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1073_, v___x_1066_, v___x_1072_, v___f_1069_);
return v___x_1074_;
}
}
else
{
lean_del_object(v___x_1063_);
lean_dec_ref(v_indexes_1061_);
lean_dec_ref(v_entries_1060_);
goto v___jp_1053_;
}
}
}
v___jp_1053_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_head_1051_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1098_, lean_object* v_head_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1098_, v_head_1099_);
lean_dec_ref(v_config_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_nat_to_int(v_a_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_nat_to_int(v_a_1104_);
v___x_1106_ = l_Rat_ofInt(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_m_1108_, v_a_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_00_u03b2_1111_, v_m_1112_, v_a_1113_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_m_1112_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1116_, lean_object* v_a_1117_, lean_object* v_x_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_a_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1120_, v_a_1121_, v_x_1122_);
lean_dec(v_x_1122_);
lean_dec_ref(v_a_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1125_, lean_object* v_data_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1128_, lean_object* v_i_1129_, lean_object* v_source_1130_, lean_object* v_target_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v_i_1129_, v_source_1130_, v_target_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1137_, lean_object* v_____r_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1137_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1144_, lean_object* v_____r_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1144_, v_____r_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1148_, lean_object* v_x_1149_){
_start:
{
if (lean_obj_tag(v_x_1149_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___f_1148_);
v_a_1151_ = lean_ctor_get(v_x_1149_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_x_1149_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v_x_1149_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v_x_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1161_; 
v_a_1160_ = lean_ctor_get(v_x_1149_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v_x_1149_);
v___x_1161_ = lean_apply_2(v___f_1148_, v_a_1160_, lean_box(0));
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1162_, v_x_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1166_, lean_object* v_body_1167_, lean_object* v___f_1168_, lean_object* v___f_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1170_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___f_1169_);
lean_dec_ref(v___f_1168_);
lean_dec(v_body_1167_);
lean_dec_ref(v_close_1166_);
v_a_1172_ = lean_ctor_get(v_x_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v_x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v_x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; uint8_t v___x_1182_; 
v_a_1181_ = lean_ctor_get(v_x_1170_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v_x_1170_);
v___x_1182_ = lean_unbox(v_a_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref(v___f_1169_);
v___x_1183_ = lean_apply_2(v_close_1166_, v_body_1167_, lean_box(0));
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_unbox(v_a_1181_);
lean_dec(v_a_1181_);
v___x_1186_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1184_, v___x_1185_, v___x_1183_, v___f_1168_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_a_1181_);
lean_dec_ref(v___f_1168_);
lean_dec(v_body_1167_);
lean_dec_ref(v_close_1166_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_apply_2(v___f_1169_, v___x_1187_, lean_box(0));
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1189_, lean_object* v_body_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1189_, v_body_1190_, v___f_1191_, v___f_1192_, v_x_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v___x_1196_, lean_object* v_x1_1197_, lean_object* v_x2_1198_){
_start:
{
lean_object* v_fst_1199_; uint8_t v___x_1200_; 
v_fst_1199_ = lean_ctor_get(v_x2_1198_, 0);
v___x_1200_ = lean_string_dec_eq(v_fst_1199_, v___x_1196_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_array_push(v_x1_1197_, v_x2_1198_);
return v___x_1201_;
}
else
{
lean_dec_ref(v_x2_1198_);
return v_x1_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v___x_1202_, lean_object* v_x1_1203_, lean_object* v_x2_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v___x_1202_, v_x1_1203_, v_x2_1204_);
lean_dec_ref(v___x_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___f_1206_, lean_object* v___f_1207_, lean_object* v_x1_1208_, lean_object* v_x2_1209_){
_start:
{
lean_object* v_fst_1210_; lean_object* v_entries_1211_; lean_object* v_indexes_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1223_; 
v_fst_1210_ = lean_ctor_get(v_x2_1209_, 0);
lean_inc(v_fst_1210_);
v_entries_1211_ = lean_ctor_get(v_x1_1208_, 0);
v_indexes_1212_ = lean_ctor_get(v_x1_1208_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x1_1208_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1214_ = v_x1_1208_;
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_indexes_1212_);
lean_inc(v_entries_1211_);
lean_dec(v_x1_1208_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_i_1216_; lean_object* v_f_1217_; lean_object* v_entries_1218_; lean_object* v_indexes_1219_; lean_object* v___x_1221_; 
v_i_1216_ = lean_array_get_size(v_entries_1211_);
v_f_1217_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1217_, 0, v_i_1216_);
v_entries_1218_ = lean_array_push(v_entries_1211_, v_x2_1209_);
v_indexes_1219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1206_, v___f_1207_, v_indexes_1212_, v_fst_1210_, v_f_1217_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v_indexes_1219_);
lean_ctor_set(v___x_1214_, 0, v_entries_1218_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_entries_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_indexes_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___f_1246_; 
v___x_1245_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1246_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1246_, 0, v___x_1245_);
return v___f_1246_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___f_1253_; 
v___x_1252_ = l_Std_Http_Header_Name_contentLength;
v___f_1253_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1253_, 0, v___x_1252_);
return v___f_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v___y_1254_, lean_object* v_body_1255_, lean_object* v_isClosed_1256_, lean_object* v_close_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___y_1261_; uint8_t v_omitBody_1262_; lean_object* v___y_1275_; lean_object* v___y_1310_; uint8_t v___y_1311_; uint8_t v___y_1312_; 
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_close_1257_);
lean_dec_ref(v_isClosed_1256_);
lean_dec(v_body_1255_);
lean_dec_ref(v___y_1254_);
v_a_1315_ = lean_ctor_get(v_x_1258_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1317_ = v_x_1258_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v_x_1258_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
else
{
lean_object* v_writer_1324_; lean_object* v_a_1325_; lean_object* v_reader_1326_; lean_object* v_config_1327_; lean_object* v_events_1328_; lean_object* v_error_1329_; lean_object* v_instant_1330_; uint8_t v_keepAlive_1331_; uint8_t v_forcedFlush_1332_; uint8_t v_pullBodyStalled_1333_; lean_object* v_userData_1334_; lean_object* v_outputData_1335_; lean_object* v_state_1336_; lean_object* v_knownSize_1337_; lean_object* v_messageHead_1338_; uint8_t v_sentMessage_1339_; uint8_t v_userClosedBody_1340_; uint8_t v_omitBody_1341_; lean_object* v_userDataBytes_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1493_; 
v_writer_1324_ = lean_ctor_get(v___y_1254_, 1);
lean_inc_ref(v_writer_1324_);
v_a_1325_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v_x_1258_);
v_reader_1326_ = lean_ctor_get(v___y_1254_, 0);
v_config_1327_ = lean_ctor_get(v___y_1254_, 2);
v_events_1328_ = lean_ctor_get(v___y_1254_, 3);
v_error_1329_ = lean_ctor_get(v___y_1254_, 4);
v_instant_1330_ = lean_ctor_get(v___y_1254_, 5);
v_keepAlive_1331_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*6);
v_forcedFlush_1332_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1333_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*6 + 2);
v_userData_1334_ = lean_ctor_get(v_writer_1324_, 0);
v_outputData_1335_ = lean_ctor_get(v_writer_1324_, 1);
v_state_1336_ = lean_ctor_get(v_writer_1324_, 2);
v_knownSize_1337_ = lean_ctor_get(v_writer_1324_, 3);
v_messageHead_1338_ = lean_ctor_get(v_writer_1324_, 4);
v_sentMessage_1339_ = lean_ctor_get_uint8(v_writer_1324_, sizeof(void*)*6);
v_userClosedBody_1340_ = lean_ctor_get_uint8(v_writer_1324_, sizeof(void*)*6 + 1);
v_omitBody_1341_ = lean_ctor_get_uint8(v_writer_1324_, sizeof(void*)*6 + 2);
v_userDataBytes_1342_ = lean_ctor_get(v_writer_1324_, 5);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_writer_1324_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1344_ = v_writer_1324_;
v_isShared_1345_ = v_isSharedCheck_1493_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_userDataBytes_1342_);
lean_inc(v_messageHead_1338_);
lean_inc(v_knownSize_1337_);
lean_inc(v_state_1336_);
lean_inc(v_outputData_1335_);
lean_inc(v_userData_1334_);
lean_dec(v_writer_1324_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1493_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1373_; uint8_t v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; uint8_t v___x_1442_; uint8_t v___y_1444_; lean_object* v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1447_; uint8_t v___y_1448_; uint8_t v___y_1449_; uint8_t v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1458_; uint8_t v___y_1471_; uint8_t v___y_1472_; uint8_t v___y_1475_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1442_ = 0;
v___x_1491_ = lean_box(1);
v___x_1492_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1336_, v___x_1491_);
if (v___x_1492_ == 0)
{
v___y_1475_ = v___x_1492_;
goto v___jp_1474_;
}
else
{
if (v_sentMessage_1339_ == 0)
{
v___y_1475_ = v___x_1492_;
goto v___jp_1474_;
}
else
{
lean_del_object(v___x_1344_);
lean_dec(v_userDataBytes_1342_);
lean_dec(v_messageHead_1338_);
lean_dec(v_knownSize_1337_);
lean_dec(v_state_1336_);
lean_dec_ref(v_outputData_1335_);
lean_dec_ref(v_userData_1334_);
lean_dec(v_a_1325_);
v___y_1261_ = v___y_1254_;
v_omitBody_1262_ = v_omitBody_1341_;
goto v___jp_1260_;
}
}
v___jp_1346_:
{
lean_object* v_message_1349_; lean_object* v___x_2280__overap_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v_message_1349_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1347_, v_a_1325_, v___y_1348_);
v___x_2280__overap_1350_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1347_);
v___x_1351_ = lean_apply_2(v___x_2280__overap_1350_, v_outputData_1335_, v_message_1349_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1351_);
v___x_1353_ = v___x_1344_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_userData_1334_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_state_1336_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_knownSize_1337_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_messageHead_1338_);
lean_ctor_set(v_reuseFailAlloc_1355_, 5, v_userDataBytes_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, sizeof(void*)*6, v_sentMessage_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, sizeof(void*)*6 + 1, v_userClosedBody_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, sizeof(void*)*6 + 2, v_omitBody_1341_);
v___x_1353_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1354_, 0, v_reader_1326_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
lean_ctor_set(v___x_1354_, 2, v_config_1327_);
lean_ctor_set(v___x_1354_, 3, v_events_1328_);
lean_ctor_set(v___x_1354_, 4, v_error_1329_);
lean_ctor_set(v___x_1354_, 5, v_instant_1330_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*6, v_keepAlive_1331_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*6 + 1, v_forcedFlush_1332_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*6 + 2, v_pullBodyStalled_1333_);
v___y_1261_ = v___x_1354_;
v_omitBody_1262_ = v_omitBody_1341_;
goto v___jp_1260_;
}
}
v___jp_1356_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_array_get_size(v___y_1361_);
v___x_1363_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1364_ = lean_nat_dec_lt(v___y_1360_, v___x_1362_);
if (v___x_1364_ == 0)
{
lean_dec_ref(v___y_1361_);
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___y_1359_;
goto v___jp_1346_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_le(v___x_1362_, v___x_1362_);
if (v___x_1365_ == 0)
{
if (v___x_1364_ == 0)
{
lean_dec_ref(v___y_1361_);
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___y_1359_;
goto v___jp_1346_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = lean_usize_of_nat(v___x_1362_);
lean_inc_ref(v___y_1358_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___y_1358_, v___y_1361_, v___x_1366_, v___x_1367_, v___y_1359_);
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___x_1368_;
goto v___jp_1346_;
}
}
else
{
size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1362_);
lean_inc_ref(v___y_1358_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___y_1358_, v___y_1361_, v___x_1369_, v___x_1370_, v___y_1359_);
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___x_1371_;
goto v___jp_1346_;
}
}
}
v___jp_1372_:
{
lean_object* v_entries_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_entries_1379_ = lean_ctor_get(v___y_1377_, 0);
lean_inc_ref(v_entries_1379_);
lean_dec_ref(v___y_1377_);
v___x_1380_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1375_, v___y_1378_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1375_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_array_get_size(v_entries_1379_);
v___x_1383_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1384_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1385_ = lean_nat_dec_lt(v___x_1381_, v___x_1382_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_entries_1379_);
v___y_1357_ = v___y_1374_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___x_1380_;
v___y_1360_ = v___x_1381_;
v___y_1361_ = v___x_1383_;
goto v___jp_1356_;
}
else
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_nat_dec_le(v___x_1382_, v___x_1382_);
if (v___x_1386_ == 0)
{
if (v___x_1385_ == 0)
{
lean_dec_ref(v_entries_1379_);
v___y_1357_ = v___y_1374_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___x_1380_;
v___y_1360_ = v___x_1381_;
v___y_1361_ = v___x_1383_;
goto v___jp_1356_;
}
else
{
size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = lean_usize_of_nat(v___x_1382_);
lean_inc_ref(v___y_1373_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1384_, v___y_1373_, v_entries_1379_, v___x_1387_, v___x_1388_, v___x_1383_);
v___y_1357_ = v___y_1374_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___x_1380_;
v___y_1360_ = v___x_1381_;
v___y_1361_ = v___x_1389_;
goto v___jp_1356_;
}
}
else
{
size_t v___x_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = lean_usize_of_nat(v___x_1382_);
lean_inc_ref(v___y_1373_);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1384_, v___y_1373_, v_entries_1379_, v___x_1390_, v___x_1391_, v___x_1383_);
v___y_1357_ = v___y_1374_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___x_1380_;
v___y_1360_ = v___x_1381_;
v___y_1361_ = v___x_1392_;
goto v___jp_1356_;
}
}
}
v___jp_1393_:
{
lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___f_1399_; lean_object* v___f_1400_; lean_object* v___f_1401_; uint8_t v___x_1402_; 
v___x_1397_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1398_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___f_1399_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1400_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1401_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1402_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1399_, v___f_1400_, v___x_1397_, v___y_1396_);
if (v___x_1402_ == 0)
{
if (v___y_1395_ == 0)
{
v___y_1373_ = v___f_1398_;
v___y_1374_ = v___y_1394_;
v___y_1375_ = v___f_1399_;
v___y_1376_ = v___f_1401_;
v___y_1377_ = v___y_1396_;
v___y_1378_ = v___f_1400_;
goto v___jp_1372_;
}
else
{
v___y_1347_ = v___y_1394_;
v___y_1348_ = v___y_1396_;
goto v___jp_1346_;
}
}
else
{
v___y_1373_ = v___f_1398_;
v___y_1374_ = v___y_1394_;
v___y_1375_ = v___f_1399_;
v___y_1376_ = v___f_1401_;
v___y_1377_ = v___y_1396_;
v___y_1378_ = v___f_1400_;
goto v___jp_1372_;
}
}
v___jp_1403_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_array_get_size(v___y_1409_);
v___x_1411_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1412_ = lean_nat_dec_lt(v___y_1405_, v___x_1410_);
if (v___x_1412_ == 0)
{
lean_dec_ref(v___y_1409_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1406_;
goto v___jp_1393_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_le(v___x_1410_, v___x_1410_);
if (v___x_1413_ == 0)
{
if (v___x_1412_ == 0)
{
lean_dec_ref(v___y_1409_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1406_;
goto v___jp_1393_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1410_);
lean_inc_ref(v___y_1408_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___y_1408_, v___y_1409_, v___x_1414_, v___x_1415_, v___y_1406_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___x_1416_;
goto v___jp_1393_;
}
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1410_);
lean_inc_ref(v___y_1408_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___y_1408_, v___y_1409_, v___x_1417_, v___x_1418_, v___y_1406_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___x_1419_;
goto v___jp_1393_;
}
}
}
v___jp_1420_:
{
lean_object* v_entries_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_entries_1428_ = lean_ctor_get(v___y_1424_, 0);
lean_inc_ref(v_entries_1428_);
lean_dec_ref(v___y_1424_);
v___x_1429_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1422_, v___y_1423_);
lean_dec_ref(v___y_1423_);
lean_dec_ref(v___y_1422_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_array_get_size(v_entries_1428_);
v___x_1432_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1433_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1434_ = lean_nat_dec_lt(v___x_1430_, v___x_1431_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v_entries_1428_);
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___x_1430_;
v___y_1406_ = v___x_1429_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___x_1432_;
goto v___jp_1403_;
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_nat_dec_le(v___x_1431_, v___x_1431_);
if (v___x_1435_ == 0)
{
if (v___x_1434_ == 0)
{
lean_dec_ref(v_entries_1428_);
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___x_1430_;
v___y_1406_ = v___x_1429_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___x_1432_;
goto v___jp_1403_;
}
else
{
size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = lean_usize_of_nat(v___x_1431_);
lean_inc_ref(v___y_1425_);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1433_, v___y_1425_, v_entries_1428_, v___x_1436_, v___x_1437_, v___x_1432_);
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___x_1430_;
v___y_1406_ = v___x_1429_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___x_1438_;
goto v___jp_1403_;
}
}
else
{
size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = lean_usize_of_nat(v___x_1431_);
lean_inc_ref(v___y_1425_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1433_, v___y_1425_, v_entries_1428_, v___x_1439_, v___x_1440_, v___x_1432_);
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___x_1430_;
v___y_1406_ = v___x_1429_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___x_1441_;
goto v___jp_1403_;
}
}
}
v___jp_1443_:
{
lean_object* v_headerSize_1450_; lean_object* v_machine_1451_; lean_object* v_machine_1452_; lean_object* v_reader_1453_; lean_object* v_state_1454_; 
v_headerSize_1450_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1447_, v_a_1325_, v___y_1446_);
v_machine_1451_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1442_, v___y_1445_, v_headerSize_1450_, v___y_1449_);
v_machine_1452_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1442_, v_machine_1451_, v_a_1325_);
lean_dec(v_a_1325_);
v_reader_1453_ = lean_ctor_get(v_machine_1452_, 0);
lean_inc_ref(v_reader_1453_);
v_state_1454_ = lean_ctor_get(v_reader_1453_, 0);
lean_inc(v_state_1454_);
lean_dec_ref(v_reader_1453_);
if (lean_obj_tag(v_state_1454_) == 7)
{
lean_dec_ref(v_state_1454_);
v___y_1310_ = v_machine_1452_;
v___y_1311_ = v___y_1448_;
v___y_1312_ = v___y_1444_;
goto v___jp_1309_;
}
else
{
lean_dec(v_state_1454_);
v___y_1310_ = v_machine_1452_;
v___y_1311_ = v___y_1448_;
v___y_1312_ = v___y_1446_;
goto v___jp_1309_;
}
}
v___jp_1455_:
{
uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v_indexes_1461_; lean_object* v___x_1462_; lean_object* v_machine_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; uint8_t v___x_1467_; 
v___x_1459_ = 1;
v___x_1460_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1459_, v_a_1325_);
v_indexes_1461_ = lean_ctor_get(v___x_1460_, 1);
lean_inc_ref(v_indexes_1461_);
lean_dec_ref(v___x_1460_);
lean_inc(v_a_1325_);
v___x_1462_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1462_, 0, v_userData_1334_);
lean_ctor_set(v___x_1462_, 1, v_outputData_1335_);
lean_ctor_set(v___x_1462_, 2, v_state_1336_);
lean_ctor_set(v___x_1462_, 3, v_knownSize_1337_);
lean_ctor_set(v___x_1462_, 4, v_a_1325_);
lean_ctor_set(v___x_1462_, 5, v_userDataBytes_1342_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*6, v___y_1456_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*6 + 1, v_userClosedBody_1340_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*6 + 2, v_omitBody_1341_);
v_machine_1463_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1463_, 0, v_reader_1326_);
lean_ctor_set(v_machine_1463_, 1, v___x_1462_);
lean_ctor_set(v_machine_1463_, 2, v_config_1327_);
lean_ctor_set(v_machine_1463_, 3, v_events_1328_);
lean_ctor_set(v_machine_1463_, 4, v_error_1329_);
lean_ctor_set(v_machine_1463_, 5, v_instant_1330_);
lean_ctor_set_uint8(v_machine_1463_, sizeof(void*)*6, v_keepAlive_1331_);
lean_ctor_set_uint8(v_machine_1463_, sizeof(void*)*6 + 1, v_forcedFlush_1332_);
lean_ctor_set_uint8(v_machine_1463_, sizeof(void*)*6 + 2, v_pullBodyStalled_1333_);
v___x_1464_ = l_Std_Http_Header_Name_contentLength;
v___f_1465_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1466_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1465_, v___f_1466_, v_indexes_1461_, v___x_1464_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1465_, v___f_1466_, v_indexes_1461_, v___x_1468_);
lean_dec_ref(v_indexes_1461_);
v___y_1444_ = v___y_1456_;
v___y_1445_ = v_machine_1463_;
v___y_1446_ = v___y_1457_;
v___y_1447_ = v___x_1459_;
v___y_1448_ = v___y_1458_;
v___y_1449_ = v___x_1469_;
goto v___jp_1443_;
}
else
{
lean_dec_ref(v_indexes_1461_);
v___y_1444_ = v___y_1456_;
v___y_1445_ = v_machine_1463_;
v___y_1446_ = v___y_1457_;
v___y_1447_ = v___x_1459_;
v___y_1448_ = v___y_1458_;
v___y_1449_ = v___x_1467_;
goto v___jp_1443_;
}
}
v___jp_1470_:
{
lean_object* v_state_1473_; 
v_state_1473_ = lean_ctor_get(v_reader_1326_, 0);
if (lean_obj_tag(v_state_1473_) == 7)
{
v___y_1456_ = v___y_1471_;
v___y_1457_ = v___y_1472_;
v___y_1458_ = v___y_1471_;
goto v___jp_1455_;
}
else
{
v___y_1456_ = v___y_1471_;
v___y_1457_ = v___y_1472_;
v___y_1458_ = v___y_1472_;
goto v___jp_1455_;
}
}
v___jp_1474_:
{
if (v___y_1475_ == 0)
{
lean_del_object(v___x_1344_);
lean_dec(v_userDataBytes_1342_);
lean_dec(v_messageHead_1338_);
lean_dec(v_knownSize_1337_);
lean_dec(v_state_1336_);
lean_dec_ref(v_outputData_1335_);
lean_dec_ref(v_userData_1334_);
lean_dec(v_a_1325_);
v___y_1261_ = v___y_1254_;
v_omitBody_1262_ = v_omitBody_1341_;
goto v___jp_1260_;
}
else
{
lean_object* v_status_1476_; uint8_t v___x_1477_; uint16_t v___x_1478_; uint16_t v___x_1479_; uint8_t v___x_1480_; 
lean_inc(v_instant_1330_);
lean_inc(v_error_1329_);
lean_inc_ref(v_events_1328_);
lean_inc_ref(v_config_1327_);
lean_inc_ref(v_reader_1326_);
lean_dec_ref(v___y_1254_);
v_status_1476_ = lean_ctor_get(v_a_1325_, 0);
v___x_1477_ = 0;
v___x_1478_ = 100;
v___x_1479_ = l_Std_Http_Status_toCode(v_status_1476_);
v___x_1480_ = lean_uint16_dec_le(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_del_object(v___x_1344_);
lean_dec(v_messageHead_1338_);
v___y_1471_ = v___y_1475_;
v___y_1472_ = v___x_1477_;
goto v___jp_1470_;
}
else
{
uint16_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = 200;
v___x_1482_ = lean_uint16_dec_lt(v___x_1479_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_del_object(v___x_1344_);
lean_dec(v_messageHead_1338_);
v___y_1471_ = v___y_1475_;
v___y_1472_ = v___x_1477_;
goto v___jp_1470_;
}
else
{
uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___f_1486_; lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; uint8_t v___x_1490_; 
v___x_1483_ = 1;
v___x_1484_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1483_, v_a_1325_);
v___x_1485_ = l_Std_Http_Header_Name_contentLength;
v___f_1486_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15);
v___f_1487_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1488_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1489_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1490_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1487_, v___f_1488_, v___x_1485_, v___x_1484_);
if (v___x_1490_ == 0)
{
if (v___x_1482_ == 0)
{
v___y_1421_ = v___x_1483_;
v___y_1422_ = v___f_1487_;
v___y_1423_ = v___f_1488_;
v___y_1424_ = v___x_1484_;
v___y_1425_ = v___f_1486_;
v___y_1426_ = v___x_1482_;
v___y_1427_ = v___f_1489_;
goto v___jp_1420_;
}
else
{
v___y_1394_ = v___x_1483_;
v___y_1395_ = v___x_1482_;
v___y_1396_ = v___x_1484_;
goto v___jp_1393_;
}
}
else
{
v___y_1421_ = v___x_1483_;
v___y_1422_ = v___f_1487_;
v___y_1423_ = v___f_1488_;
v___y_1424_ = v___x_1484_;
v___y_1425_ = v___f_1486_;
v___y_1426_ = v___x_1482_;
v___y_1427_ = v___f_1489_;
goto v___jp_1420_;
}
}
}
}
}
}
}
v___jp_1260_:
{
if (v_omitBody_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v_close_1257_);
lean_dec_ref(v_isClosed_1256_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_body_1255_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___y_1261_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; 
lean_inc(v_body_1255_);
v___x_1267_ = lean_apply_2(v_isClosed_1256_, v_body_1255_, lean_box(0));
v___f_1268_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1268_, 0, v___y_1261_);
lean_inc_ref(v___f_1268_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1269_, 0, v___f_1268_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1270_, 0, v_close_1257_);
lean_closure_set(v___f_1270_, 1, v_body_1255_);
lean_closure_set(v___f_1270_, 2, v___f_1269_);
lean_closure_set(v___f_1270_, 3, v___f_1268_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = 0;
v___x_1273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1271_, v___x_1272_, v___x_1267_, v___f_1270_);
return v___x_1273_;
}
}
v___jp_1274_:
{
lean_object* v_writer_1276_; lean_object* v_reader_1277_; lean_object* v_config_1278_; lean_object* v_events_1279_; lean_object* v_error_1280_; lean_object* v_instant_1281_; uint8_t v_keepAlive_1282_; uint8_t v_forcedFlush_1283_; uint8_t v_pullBodyStalled_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1308_; 
v_writer_1276_ = lean_ctor_get(v___y_1275_, 1);
v_reader_1277_ = lean_ctor_get(v___y_1275_, 0);
v_config_1278_ = lean_ctor_get(v___y_1275_, 2);
v_events_1279_ = lean_ctor_get(v___y_1275_, 3);
v_error_1280_ = lean_ctor_get(v___y_1275_, 4);
v_instant_1281_ = lean_ctor_get(v___y_1275_, 5);
v_keepAlive_1282_ = lean_ctor_get_uint8(v___y_1275_, sizeof(void*)*6);
v_forcedFlush_1283_ = lean_ctor_get_uint8(v___y_1275_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1284_ = lean_ctor_get_uint8(v___y_1275_, sizeof(void*)*6 + 2);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___y_1275_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1286_ = v___y_1275_;
v_isShared_1287_ = v_isSharedCheck_1308_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_instant_1281_);
lean_inc(v_error_1280_);
lean_inc(v_events_1279_);
lean_inc(v_config_1278_);
lean_inc(v_writer_1276_);
lean_inc(v_reader_1277_);
lean_dec(v___y_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1308_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_userData_1288_; lean_object* v_outputData_1289_; lean_object* v_knownSize_1290_; lean_object* v_messageHead_1291_; uint8_t v_sentMessage_1292_; uint8_t v_userClosedBody_1293_; uint8_t v_omitBody_1294_; lean_object* v_userDataBytes_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1306_; 
v_userData_1288_ = lean_ctor_get(v_writer_1276_, 0);
v_outputData_1289_ = lean_ctor_get(v_writer_1276_, 1);
v_knownSize_1290_ = lean_ctor_get(v_writer_1276_, 3);
v_messageHead_1291_ = lean_ctor_get(v_writer_1276_, 4);
v_sentMessage_1292_ = lean_ctor_get_uint8(v_writer_1276_, sizeof(void*)*6);
v_userClosedBody_1293_ = lean_ctor_get_uint8(v_writer_1276_, sizeof(void*)*6 + 1);
v_omitBody_1294_ = lean_ctor_get_uint8(v_writer_1276_, sizeof(void*)*6 + 2);
v_userDataBytes_1295_ = lean_ctor_get(v_writer_1276_, 5);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_writer_1276_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_writer_1276_, 2);
lean_dec(v_unused_1307_);
v___x_1297_ = v_writer_1276_;
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_userDataBytes_1295_);
lean_inc(v_messageHead_1291_);
lean_inc(v_knownSize_1290_);
lean_inc(v_outputData_1289_);
lean_inc(v_userData_1288_);
lean_dec(v_writer_1276_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_box(2);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 2, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_userData_1288_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_outputData_1289_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_knownSize_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_messageHead_1291_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_userDataBytes_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*6, v_sentMessage_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*6 + 1, v_userClosedBody_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*6 + 2, v_omitBody_1294_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1301_);
v___x_1303_ = v___x_1286_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_reader_1277_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_config_1278_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v_events_1279_);
lean_ctor_set(v_reuseFailAlloc_1304_, 4, v_error_1280_);
lean_ctor_set(v_reuseFailAlloc_1304_, 5, v_instant_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*6, v_keepAlive_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*6 + 1, v_forcedFlush_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*6 + 2, v_pullBodyStalled_1284_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v___y_1261_ = v___x_1303_;
v_omitBody_1262_ = v_omitBody_1294_;
goto v___jp_1260_;
}
}
}
}
}
v___jp_1309_:
{
if (v___y_1312_ == 0)
{
v___y_1275_ = v___y_1310_;
goto v___jp_1274_;
}
else
{
if (v___y_1311_ == 0)
{
lean_object* v_writer_1313_; uint8_t v_omitBody_1314_; 
v_writer_1313_ = lean_ctor_get(v___y_1310_, 1);
v_omitBody_1314_ = lean_ctor_get_uint8(v_writer_1313_, sizeof(void*)*6 + 2);
v___y_1261_ = v___y_1310_;
v_omitBody_1262_ = v_omitBody_1314_;
goto v___jp_1260_;
}
else
{
v___y_1275_ = v___y_1310_;
goto v___jp_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1494_, lean_object* v_body_1495_, lean_object* v_isClosed_1496_, lean_object* v_close_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1494_, v_body_1495_, v_isClosed_1496_, v_close_1497_, v_x_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v_config_1501_, lean_object* v_line_1502_, lean_object* v_body_1503_, lean_object* v_isClosed_1504_, lean_object* v_close_1505_, lean_object* v_machine_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___y_1510_; 
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_machine_1506_);
lean_dec_ref(v_close_1505_);
lean_dec_ref(v_isClosed_1504_);
lean_dec(v_body_1503_);
lean_dec_ref(v_line_1502_);
v_a_1516_ = lean_ctor_get(v_x_1507_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1518_ = v_x_1507_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v_x_1507_);
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
v_a_1525_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v_x_1507_);
if (lean_obj_tag(v_a_1525_) == 1)
{
lean_object* v_writer_1526_; lean_object* v_reader_1527_; lean_object* v_config_1528_; lean_object* v_events_1529_; lean_object* v_error_1530_; lean_object* v_instant_1531_; uint8_t v_keepAlive_1532_; uint8_t v_forcedFlush_1533_; uint8_t v_pullBodyStalled_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1557_; 
v_writer_1526_ = lean_ctor_get(v_machine_1506_, 1);
v_reader_1527_ = lean_ctor_get(v_machine_1506_, 0);
v_config_1528_ = lean_ctor_get(v_machine_1506_, 2);
v_events_1529_ = lean_ctor_get(v_machine_1506_, 3);
v_error_1530_ = lean_ctor_get(v_machine_1506_, 4);
v_instant_1531_ = lean_ctor_get(v_machine_1506_, 5);
v_keepAlive_1532_ = lean_ctor_get_uint8(v_machine_1506_, sizeof(void*)*6);
v_forcedFlush_1533_ = lean_ctor_get_uint8(v_machine_1506_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1534_ = lean_ctor_get_uint8(v_machine_1506_, sizeof(void*)*6 + 2);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_machine_1506_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1536_ = v_machine_1506_;
v_isShared_1537_ = v_isSharedCheck_1557_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_instant_1531_);
lean_inc(v_error_1530_);
lean_inc(v_events_1529_);
lean_inc(v_config_1528_);
lean_inc(v_writer_1526_);
lean_inc(v_reader_1527_);
lean_dec(v_machine_1506_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1557_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_userData_1538_; lean_object* v_outputData_1539_; lean_object* v_state_1540_; lean_object* v_messageHead_1541_; uint8_t v_sentMessage_1542_; uint8_t v_userClosedBody_1543_; uint8_t v_omitBody_1544_; lean_object* v_userDataBytes_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1555_; 
v_userData_1538_ = lean_ctor_get(v_writer_1526_, 0);
v_outputData_1539_ = lean_ctor_get(v_writer_1526_, 1);
v_state_1540_ = lean_ctor_get(v_writer_1526_, 2);
v_messageHead_1541_ = lean_ctor_get(v_writer_1526_, 4);
v_sentMessage_1542_ = lean_ctor_get_uint8(v_writer_1526_, sizeof(void*)*6);
v_userClosedBody_1543_ = lean_ctor_get_uint8(v_writer_1526_, sizeof(void*)*6 + 1);
v_omitBody_1544_ = lean_ctor_get_uint8(v_writer_1526_, sizeof(void*)*6 + 2);
v_userDataBytes_1545_ = lean_ctor_get(v_writer_1526_, 5);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_writer_1526_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_writer_1526_, 3);
lean_dec(v_unused_1556_);
v___x_1547_ = v_writer_1526_;
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_userDataBytes_1545_);
lean_inc(v_messageHead_1541_);
lean_inc(v_state_1540_);
lean_inc(v_outputData_1539_);
lean_inc(v_userData_1538_);
lean_dec(v_writer_1526_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 3, v_a_1525_);
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_userData_1538_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_outputData_1539_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_state_1540_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_a_1525_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_messageHead_1541_);
lean_ctor_set(v_reuseFailAlloc_1554_, 5, v_userDataBytes_1545_);
lean_ctor_set_uint8(v_reuseFailAlloc_1554_, sizeof(void*)*6, v_sentMessage_1542_);
lean_ctor_set_uint8(v_reuseFailAlloc_1554_, sizeof(void*)*6 + 1, v_userClosedBody_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1554_, sizeof(void*)*6 + 2, v_omitBody_1544_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v___x_1550_);
v___x_1552_ = v___x_1536_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_reader_1527_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_config_1528_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_events_1529_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_error_1530_);
lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_instant_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1553_, sizeof(void*)*6, v_keepAlive_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1553_, sizeof(void*)*6 + 1, v_forcedFlush_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1553_, sizeof(void*)*6 + 2, v_pullBodyStalled_1534_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
v___y_1510_ = v___x_1552_;
goto v___jp_1509_;
}
}
}
}
}
else
{
lean_dec(v_a_1525_);
v___y_1510_ = v_machine_1506_;
goto v___jp_1509_;
}
}
v___jp_1509_:
{
lean_object* v___x_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1511_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1501_, v_line_1502_);
v___f_1512_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1512_, 0, v___y_1510_);
lean_closure_set(v___f_1512_, 1, v_body_1503_);
lean_closure_set(v___f_1512_, 2, v_isClosed_1504_);
lean_closure_set(v___f_1512_, 3, v_close_1505_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = 0;
v___x_1515_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1513_, v___x_1514_, v___x_1511_, v___f_1512_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v_config_1558_, lean_object* v_line_1559_, lean_object* v_body_1560_, lean_object* v_isClosed_1561_, lean_object* v_close_1562_, lean_object* v_machine_1563_, lean_object* v_x_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v_config_1558_, v_line_1559_, v_body_1560_, v_isClosed_1561_, v_close_1562_, v_machine_1563_, v_x_1564_);
lean_dec_ref(v_config_1558_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1567_, lean_object* v_config_1568_, lean_object* v_machine_1569_, lean_object* v_res_1570_){
_start:
{
lean_object* v_close_1572_; lean_object* v_isClosed_1573_; lean_object* v_getKnownSize_1574_; lean_object* v_line_1575_; lean_object* v_body_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; 
v_close_1572_ = lean_ctor_get(v_inst_1567_, 1);
lean_inc_ref(v_close_1572_);
v_isClosed_1573_ = lean_ctor_get(v_inst_1567_, 2);
lean_inc_ref(v_isClosed_1573_);
v_getKnownSize_1574_ = lean_ctor_get(v_inst_1567_, 5);
lean_inc_ref(v_getKnownSize_1574_);
lean_dec_ref(v_inst_1567_);
v_line_1575_ = lean_ctor_get(v_res_1570_, 0);
lean_inc_ref(v_line_1575_);
v_body_1576_ = lean_ctor_get(v_res_1570_, 1);
lean_inc_n(v_body_1576_, 2);
lean_dec_ref(v_res_1570_);
v___x_1577_ = lean_apply_2(v_getKnownSize_1574_, v_body_1576_, lean_box(0));
v___f_1578_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_1578_, 0, v_config_1568_);
lean_closure_set(v___f_1578_, 1, v_line_1575_);
lean_closure_set(v___f_1578_, 2, v_body_1576_);
lean_closure_set(v___f_1578_, 3, v_isClosed_1573_);
lean_closure_set(v___f_1578_, 4, v_close_1572_);
lean_closure_set(v___f_1578_, 5, v_machine_1569_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = 0;
v___x_1581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1579_, v___x_1580_, v___x_1577_, v___f_1578_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1582_, lean_object* v_config_1583_, lean_object* v_machine_1584_, lean_object* v_res_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1582_, v_config_1583_, v_machine_1584_, v_res_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1588_, lean_object* v_inst_1589_, lean_object* v_config_1590_, lean_object* v_machine_1591_, lean_object* v_res_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1589_, v_config_1590_, v_machine_1591_, v_res_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1595_, lean_object* v_inst_1596_, lean_object* v_config_1597_, lean_object* v_machine_1598_, lean_object* v_res_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1595_, v_inst_1596_, v_config_1597_, v_machine_1598_, v_res_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v_closed_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_closed_1605_ = lean_ctor_get_uint8(v_____do__lift_1602_, sizeof(void*)*5);
v___x_1606_ = lean_box(v_closed_1605_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v_____do__lift_1609_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v_pendingProducer_1621_; lean_object* v_pendingConsumer_1622_; lean_object* v_interestWaiter_1623_; uint8_t v_closed_1624_; lean_object* v_pendingIncompleteChunk_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1634_; 
v___x_1620_ = lean_st_ref_take(v___y_1618_);
v_pendingProducer_1621_ = lean_ctor_get(v___x_1620_, 0);
v_pendingConsumer_1622_ = lean_ctor_get(v___x_1620_, 1);
v_interestWaiter_1623_ = lean_ctor_get(v___x_1620_, 2);
v_closed_1624_ = lean_ctor_get_uint8(v___x_1620_, sizeof(void*)*5);
v_pendingIncompleteChunk_1625_ = lean_ctor_get(v___x_1620_, 4);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v___x_1620_, 3);
lean_dec(v_unused_1635_);
v___x_1627_ = v___x_1620_;
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1625_);
lean_inc(v_interestWaiter_1623_);
lean_inc(v_pendingConsumer_1622_);
lean_inc(v_pendingProducer_1621_);
lean_dec(v___x_1620_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 3, v___x_1617_);
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_pendingProducer_1621_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_pendingConsumer_1622_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_interestWaiter_1623_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v_pendingIncompleteChunk_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*5, v_closed_1624_);
v___x_1630_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_st_ref_set(v___y_1618_, v___x_1630_);
v___x_1632_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1636_, v___y_1637_);
lean_dec(v___y_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1640_, lean_object* v_x_1641_){
_start:
{
if (lean_obj_tag(v_x_1641_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v___x_1640_);
v_a_1643_ = lean_ctor_get(v_x_1641_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v_x_1641_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v_x_1641_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
}
else
{
lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1641_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_x_1641_, 0);
lean_dec(v_unused_1661_);
v___x_1653_ = v_x_1641_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v_x_1641_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1640_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1662_, v_x_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1666_, lean_object* v_requestStream_1667_, lean_object* v_keepAliveTimeout_1668_, lean_object* v_currentTimeout_1669_, lean_object* v_headerTimeout_1670_, lean_object* v_response_1671_, lean_object* v_respStream_1672_, lean_object* v_expectData_1673_, uint8_t v_handlerDispatched_1674_, lean_object* v_____r_1675_){
_start:
{
uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1677_ = 0;
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1679_, 0, v_machine_1666_);
lean_ctor_set(v___x_1679_, 1, v_requestStream_1667_);
lean_ctor_set(v___x_1679_, 2, v_keepAliveTimeout_1668_);
lean_ctor_set(v___x_1679_, 3, v_currentTimeout_1669_);
lean_ctor_set(v___x_1679_, 4, v_headerTimeout_1670_);
lean_ctor_set(v___x_1679_, 5, v_response_1671_);
lean_ctor_set(v___x_1679_, 6, v_respStream_1672_);
lean_ctor_set(v___x_1679_, 7, v_expectData_1673_);
lean_ctor_set(v___x_1679_, 8, v___x_1678_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*9, v___x_1677_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*9 + 1, v_handlerDispatched_1674_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1683_, lean_object* v_requestStream_1684_, lean_object* v_keepAliveTimeout_1685_, lean_object* v_currentTimeout_1686_, lean_object* v_headerTimeout_1687_, lean_object* v_response_1688_, lean_object* v_respStream_1689_, lean_object* v_expectData_1690_, lean_object* v_handlerDispatched_1691_, lean_object* v_____r_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_handlerDispatched_boxed_1694_; lean_object* v_res_1695_; 
v_handlerDispatched_boxed_1694_ = lean_unbox(v_handlerDispatched_1691_);
v_res_1695_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1683_, v_requestStream_1684_, v_keepAliveTimeout_1685_, v_currentTimeout_1686_, v_headerTimeout_1687_, v_response_1688_, v_respStream_1689_, v_expectData_1690_, v_handlerDispatched_boxed_1694_, v_____r_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1696_, lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v___f_1696_);
v_a_1699_ = lean_ctor_get(v_x_1697_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v_x_1697_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v_x_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v_x_1697_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v_x_1697_);
v___x_1709_ = lean_apply_2(v___f_1696_, v_a_1708_, lean_box(0));
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1710_, v_x_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1714_, lean_object* v___f_1715_, lean_object* v___f_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v___f_1716_);
lean_dec_ref(v___f_1715_);
lean_dec_ref(v_requestStream_1714_);
v_a_1719_ = lean_ctor_get(v_x_1717_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1717_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1721_ = v_x_1717_;
v_isShared_1722_ = v_isSharedCheck_1727_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v_x_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1727_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; uint8_t v___x_1729_; 
v_a_1728_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v_x_1717_);
v___x_1729_ = lean_unbox(v_a_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v___f_1716_);
v___x_1730_ = l_Std_Http_Body_Stream_close(v_requestStream_1714_);
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_unbox(v_a_1728_);
lean_dec(v_a_1728_);
v___x_1733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1731_, v___x_1732_, v___x_1730_, v___f_1715_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v_a_1728_);
lean_dec_ref(v___f_1715_);
lean_dec_ref(v_requestStream_1714_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_apply_2(v___f_1716_, v___x_1734_, lean_box(0));
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1736_, lean_object* v___f_1737_, lean_object* v___f_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1736_, v___f_1737_, v___f_1738_, v_x_1739_);
return v_res_1741_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1742_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1743_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___f_1751_; 
v___x_1749_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1750_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1751_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1751_, 0, v___f_1750_);
lean_closure_set(v___f_1751_, 1, v___x_1749_);
return v___f_1751_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___f_1761_; lean_object* v___f_1762_; 
v___x_1760_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1761_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1762_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1762_, 0, v___f_1761_);
lean_closure_set(v___f_1762_, 1, v___x_1760_);
return v___f_1762_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1763_; lean_object* v___x_1764_; 
v___f_1763_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1764_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1764_, 0, lean_box(0));
lean_closure_set(v___x_1764_, 1, lean_box(0));
lean_closure_set(v___x_1764_, 2, lean_box(0));
lean_closure_set(v___x_1764_, 3, v___f_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1765_, lean_object* v___f_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v___f_1766_);
lean_dec_ref(v___y_1765_);
v_a_1769_ = lean_ctor_get(v_x_1767_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_x_1767_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1771_ = v_x_1767_;
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v_x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
}
else
{
lean_object* v_machine_1778_; lean_object* v_requestStream_1779_; lean_object* v_keepAliveTimeout_1780_; lean_object* v_currentTimeout_1781_; lean_object* v_headerTimeout_1782_; lean_object* v_response_1783_; lean_object* v_respStream_1784_; lean_object* v_expectData_1785_; uint8_t v_handlerDispatched_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___f_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_4928__overap_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___f_1796_; lean_object* v___f_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v_x_1767_);
v_machine_1778_ = lean_ctor_get(v___y_1765_, 0);
lean_inc_ref(v_machine_1778_);
v_requestStream_1779_ = lean_ctor_get(v___y_1765_, 1);
lean_inc_ref_n(v_requestStream_1779_, 3);
v_keepAliveTimeout_1780_ = lean_ctor_get(v___y_1765_, 2);
lean_inc(v_keepAliveTimeout_1780_);
v_currentTimeout_1781_ = lean_ctor_get(v___y_1765_, 3);
lean_inc(v_currentTimeout_1781_);
v_headerTimeout_1782_ = lean_ctor_get(v___y_1765_, 4);
lean_inc(v_headerTimeout_1782_);
v_response_1783_ = lean_ctor_get(v___y_1765_, 5);
lean_inc_ref(v_response_1783_);
v_respStream_1784_ = lean_ctor_get(v___y_1765_, 6);
lean_inc(v_respStream_1784_);
v_expectData_1785_ = lean_ctor_get(v___y_1765_, 7);
lean_inc(v_expectData_1785_);
v_handlerDispatched_1786_ = lean_ctor_get_uint8(v___y_1765_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1765_);
v___x_1787_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1788_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1789_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1790_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1791_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1791_, 0, lean_box(0));
lean_closure_set(v___x_1791_, 1, lean_box(0));
lean_closure_set(v___x_1791_, 2, lean_box(0));
lean_closure_set(v___x_1791_, 3, v___x_1787_);
lean_closure_set(v___x_1791_, 4, lean_box(0));
lean_closure_set(v___x_1791_, 5, lean_box(0));
lean_closure_set(v___x_1791_, 6, v___x_1790_);
lean_closure_set(v___x_1791_, 7, v___f_1766_);
v___x_4928__overap_1792_ = l_Std_Mutex_atomically___redArg(v___x_1787_, v___f_1788_, v___f_1789_, v_requestStream_1779_, v___x_1791_);
v___x_1793_ = lean_apply_1(v___x_4928__overap_1792_, lean_box(0));
v___x_1794_ = lean_box(v_handlerDispatched_1786_);
v___f_1795_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1795_, 0, v_machine_1778_);
lean_closure_set(v___f_1795_, 1, v_requestStream_1779_);
lean_closure_set(v___f_1795_, 2, v_keepAliveTimeout_1780_);
lean_closure_set(v___f_1795_, 3, v_currentTimeout_1781_);
lean_closure_set(v___f_1795_, 4, v_headerTimeout_1782_);
lean_closure_set(v___f_1795_, 5, v_response_1783_);
lean_closure_set(v___f_1795_, 6, v_respStream_1784_);
lean_closure_set(v___f_1795_, 7, v_expectData_1785_);
lean_closure_set(v___f_1795_, 8, v___x_1794_);
lean_inc_ref(v___f_1795_);
v___f_1796_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1796_, 0, v___f_1795_);
v___f_1797_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1797_, 0, v_requestStream_1779_);
lean_closure_set(v___f_1797_, 1, v___f_1796_);
lean_closure_set(v___f_1797_, 2, v___f_1795_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = 0;
v___x_1800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1798_, v___x_1799_, v___x_1793_, v___f_1797_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1801_, lean_object* v___f_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1801_, v___f_1802_, v_x_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1817_; 
lean_dec_ref(v___y_1806_);
v_a_1809_ = lean_ctor_get(v_x_1807_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1811_ = v_x_1807_;
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v_x_1807_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
}
else
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1826_; 
v_isSharedCheck_1826_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v_x_1807_, 0);
lean_dec(v_unused_1827_);
v___x_1819_ = v_x_1807_;
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v_x_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___y_1806_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1821_);
v___x_1823_ = v___x_1819_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1828_, v_x_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1832_, lean_object* v___f_1833_, lean_object* v___y_1834_, lean_object* v_x_1835_){
_start:
{
if (lean_obj_tag(v_x_1835_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___f_1833_);
lean_dec_ref(v_requestStream_1832_);
v_a_1837_ = lean_ctor_get(v_x_1835_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_x_1835_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1839_ = v_x_1835_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v_x_1835_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1860_; 
v_a_1846_ = lean_ctor_get(v_x_1835_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_x_1835_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1848_ = v_x_1835_;
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v_x_1835_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_unbox(v_a_1846_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; 
lean_del_object(v___x_1848_);
lean_dec_ref(v___y_1834_);
v___x_1851_ = l_Std_Http_Body_Stream_close(v_requestStream_1832_);
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_unbox(v_a_1846_);
lean_dec(v_a_1846_);
v___x_1854_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1852_, v___x_1853_, v___x_1851_, v___f_1833_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_a_1846_);
lean_dec_ref(v___f_1833_);
lean_dec_ref(v_requestStream_1832_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___y_1834_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1855_);
v___x_1857_ = v___x_1848_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1861_, lean_object* v___f_1862_, lean_object* v___y_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1861_, v___f_1862_, v___y_1863_, v_x_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1867_, lean_object* v_machine_1868_, lean_object* v_a_1869_, uint8_t v_requiresData_1870_, lean_object* v_expectData_1871_, lean_object* v_pendingHead_1872_, lean_object* v_x_1873_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_pendingHead_1872_);
lean_dec(v_expectData_1871_);
lean_dec_ref(v_a_1869_);
lean_dec_ref(v_machine_1868_);
v_a_1875_ = lean_ctor_get(v_x_1873_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_x_1873_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1877_ = v_x_1873_;
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v_x_1873_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1898_; 
v_a_1884_ = lean_ctor_get(v_x_1873_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_x_1873_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1886_ = v_x_1873_;
v_isShared_1887_ = v_isSharedCheck_1898_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v_x_1873_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1898_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_keepAliveTimeout_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v_keepAliveTimeout_1888_ = lean_ctor_get(v_config_1867_, 5);
lean_inc_n(v_keepAliveTimeout_1888_, 2);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_keepAliveTimeout_1888_);
v___x_1890_ = lean_box(0);
v___x_1891_ = 0;
v___x_1892_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1892_, 0, v_machine_1868_);
lean_ctor_set(v___x_1892_, 1, v_a_1869_);
lean_ctor_set(v___x_1892_, 2, v___x_1889_);
lean_ctor_set(v___x_1892_, 3, v_keepAliveTimeout_1888_);
lean_ctor_set(v___x_1892_, 4, v___x_1890_);
lean_ctor_set(v___x_1892_, 5, v_a_1884_);
lean_ctor_set(v___x_1892_, 6, v___x_1890_);
lean_ctor_set(v___x_1892_, 7, v_expectData_1871_);
lean_ctor_set(v___x_1892_, 8, v_pendingHead_1872_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*9, v_requiresData_1870_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*9 + 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1893_);
v___x_1895_ = v___x_1886_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1899_, lean_object* v_machine_1900_, lean_object* v_a_1901_, lean_object* v_requiresData_1902_, lean_object* v_expectData_1903_, lean_object* v_pendingHead_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v_requiresData_boxed_1907_; lean_object* v_res_1908_; 
v_requiresData_boxed_1907_ = lean_unbox(v_requiresData_1902_);
v_res_1908_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1899_, v_machine_1900_, v_a_1901_, v_requiresData_boxed_1907_, v_expectData_1903_, v_pendingHead_1904_, v_x_1905_);
lean_dec_ref(v_config_1899_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1909_, lean_object* v_machine_1910_, uint8_t v_requiresData_1911_, lean_object* v_expectData_1912_, lean_object* v_pendingHead_1913_, lean_object* v_x_1914_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_pendingHead_1913_);
lean_dec(v_expectData_1912_);
lean_dec_ref(v_machine_1910_);
lean_dec_ref(v_config_1909_);
v_a_1916_ = lean_ctor_get(v_x_1914_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1914_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v_x_1914_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v_x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1940_; 
v_a_1925_ = lean_ctor_get(v_x_1914_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_x_1914_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1927_ = v_x_1914_;
v_isShared_1928_ = v_isSharedCheck_1940_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v_x_1914_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1940_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1934_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = l_Std_CloseableChannel_new___redArg(v___x_1929_);
v___x_1931_ = lean_box(v_requiresData_1911_);
v___f_1932_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1932_, 0, v_config_1909_);
lean_closure_set(v___f_1932_, 1, v_machine_1910_);
lean_closure_set(v___f_1932_, 2, v_a_1925_);
lean_closure_set(v___f_1932_, 3, v___x_1931_);
lean_closure_set(v___f_1932_, 4, v_expectData_1912_);
lean_closure_set(v___f_1932_, 5, v_pendingHead_1913_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1930_);
v___x_1934_ = v___x_1927_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1930_);
v___x_1934_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = 0;
v___x_1938_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1936_, v___x_1937_, v___x_1935_, v___f_1932_);
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1941_, lean_object* v_machine_1942_, lean_object* v_requiresData_1943_, lean_object* v_expectData_1944_, lean_object* v_pendingHead_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v_requiresData_boxed_1948_; lean_object* v_res_1949_; 
v_requiresData_boxed_1948_ = lean_unbox(v_requiresData_1943_);
v_res_1949_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1941_, v_machine_1942_, v_requiresData_boxed_1948_, v_expectData_1944_, v_pendingHead_1945_, v_x_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1950_, lean_object* v_____r_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1953_ = l_Std_Http_Body_mkStream();
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = 0;
v___x_1956_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1954_, v___x_1955_, v___x_1953_, v___f_1950_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1957_, lean_object* v_____r_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1957_, v_____r_1958_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1961_, lean_object* v_val_1962_, lean_object* v___f_1963_, lean_object* v___f_1964_, lean_object* v_x_1965_){
_start:
{
if (lean_obj_tag(v_x_1965_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v___f_1964_);
lean_dec_ref(v___f_1963_);
lean_dec(v_val_1962_);
lean_dec_ref(v_close_1961_);
v_a_1967_ = lean_ctor_get(v_x_1965_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_x_1965_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1969_ = v_x_1965_;
v_isShared_1970_ = v_isSharedCheck_1975_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v_x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1975_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
}
else
{
lean_object* v_a_1976_; uint8_t v___x_1977_; 
v_a_1976_ = lean_ctor_get(v_x_1965_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v_x_1965_);
v___x_1977_ = lean_unbox(v_a_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; 
lean_dec_ref(v___f_1964_);
v___x_1978_ = lean_apply_2(v_close_1961_, v_val_1962_, lean_box(0));
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_unbox(v_a_1976_);
lean_dec(v_a_1976_);
v___x_1981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1979_, v___x_1980_, v___x_1978_, v___f_1963_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v_a_1976_);
lean_dec_ref(v___f_1963_);
lean_dec(v_val_1962_);
lean_dec_ref(v_close_1961_);
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_apply_2(v___f_1964_, v___x_1982_, lean_box(0));
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1984_, lean_object* v_val_1985_, lean_object* v___f_1986_, lean_object* v___f_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1984_, v_val_1985_, v___f_1986_, v___f_1987_, v_x_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1991_, lean_object* v_inst_1992_, lean_object* v___f_1993_, lean_object* v___f_1994_, lean_object* v_____r_1995_){
_start:
{
if (lean_obj_tag(v_respStream_1991_) == 1)
{
lean_object* v_val_1997_; lean_object* v_close_1998_; lean_object* v_isClosed_1999_; lean_object* v___x_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; 
v_val_1997_ = lean_ctor_get(v_respStream_1991_, 0);
lean_inc_n(v_val_1997_, 2);
lean_dec_ref(v_respStream_1991_);
v_close_1998_ = lean_ctor_get(v_inst_1992_, 1);
lean_inc_ref(v_close_1998_);
v_isClosed_1999_ = lean_ctor_get(v_inst_1992_, 2);
lean_inc_ref(v_isClosed_1999_);
lean_dec_ref(v_inst_1992_);
v___x_2000_ = lean_apply_2(v_isClosed_1999_, v_val_1997_, lean_box(0));
v___f_2001_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_2001_, 0, v_close_1998_);
lean_closure_set(v___f_2001_, 1, v_val_1997_);
lean_closure_set(v___f_2001_, 2, v___f_1993_);
lean_closure_set(v___f_2001_, 3, v___f_1994_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = 0;
v___x_2004_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2002_, v___x_2003_, v___x_2000_, v___f_2001_);
return v___x_2004_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref(v___f_1993_);
lean_dec_ref(v_inst_1992_);
lean_dec(v_respStream_1991_);
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_apply_2(v___f_1994_, v___x_2005_, lean_box(0));
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_2007_, lean_object* v_inst_2008_, lean_object* v___f_2009_, lean_object* v___f_2010_, lean_object* v_____r_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_2007_, v_inst_2008_, v___f_2009_, v___f_2010_, v_____r_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2014_, lean_object* v_keepAliveTimeout_2015_, lean_object* v_currentTimeout_2016_, lean_object* v_headerTimeout_2017_, lean_object* v_response_2018_, lean_object* v_respStream_2019_, uint8_t v_requiresData_2020_, lean_object* v_expectData_2021_, uint8_t v_handlerDispatched_2022_, lean_object* v_pendingHead_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_pendingHead_2023_);
lean_dec(v_expectData_2021_);
lean_dec(v_respStream_2019_);
lean_dec_ref(v_response_2018_);
lean_dec(v_headerTimeout_2017_);
lean_dec(v_currentTimeout_2016_);
lean_dec(v_keepAliveTimeout_2015_);
lean_dec_ref(v_requestStream_2014_);
v_a_2026_ = lean_ctor_get(v_x_2024_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2028_ = v_x_2024_;
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v_x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2056_; 
v_a_2035_ = lean_ctor_get(v_x_2024_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2037_ = v_x_2024_;
v_isShared_2038_ = v_isSharedCheck_2056_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v_x_2024_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2056_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_snd_2039_; uint8_t v___x_2040_; 
v_snd_2039_ = lean_ctor_get(v_a_2035_, 1);
v___x_2040_ = lean_unbox(v_snd_2039_);
if (v___x_2040_ == 0)
{
lean_object* v_fst_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v_fst_2041_ = lean_ctor_get(v_a_2035_, 0);
lean_inc(v_fst_2041_);
lean_dec(v_a_2035_);
v___x_2042_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2042_, 0, v_fst_2041_);
lean_ctor_set(v___x_2042_, 1, v_requestStream_2014_);
lean_ctor_set(v___x_2042_, 2, v_keepAliveTimeout_2015_);
lean_ctor_set(v___x_2042_, 3, v_currentTimeout_2016_);
lean_ctor_set(v___x_2042_, 4, v_headerTimeout_2017_);
lean_ctor_set(v___x_2042_, 5, v_response_2018_);
lean_ctor_set(v___x_2042_, 6, v_respStream_2019_);
lean_ctor_set(v___x_2042_, 7, v_expectData_2021_);
lean_ctor_set(v___x_2042_, 8, v_pendingHead_2023_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*9, v_requiresData_2020_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*9 + 1, v_handlerDispatched_2022_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2043_);
v___x_2045_ = v___x_2037_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
else
{
lean_object* v_fst_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_dec(v_pendingHead_2023_);
v_fst_2048_ = lean_ctor_get(v_a_2035_, 0);
lean_inc(v_fst_2048_);
lean_dec(v_a_2035_);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2050_, 0, v_fst_2048_);
lean_ctor_set(v___x_2050_, 1, v_requestStream_2014_);
lean_ctor_set(v___x_2050_, 2, v_keepAliveTimeout_2015_);
lean_ctor_set(v___x_2050_, 3, v_currentTimeout_2016_);
lean_ctor_set(v___x_2050_, 4, v_headerTimeout_2017_);
lean_ctor_set(v___x_2050_, 5, v_response_2018_);
lean_ctor_set(v___x_2050_, 6, v_respStream_2019_);
lean_ctor_set(v___x_2050_, 7, v_expectData_2021_);
lean_ctor_set(v___x_2050_, 8, v___x_2049_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*9, v_requiresData_2020_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*9 + 1, v_handlerDispatched_2022_);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2051_);
v___x_2053_ = v___x_2037_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2057_, lean_object* v_keepAliveTimeout_2058_, lean_object* v_currentTimeout_2059_, lean_object* v_headerTimeout_2060_, lean_object* v_response_2061_, lean_object* v_respStream_2062_, lean_object* v_requiresData_2063_, lean_object* v_expectData_2064_, lean_object* v_handlerDispatched_2065_, lean_object* v_pendingHead_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v_requiresData_boxed_2069_; uint8_t v_handlerDispatched_boxed_2070_; lean_object* v_res_2071_; 
v_requiresData_boxed_2069_ = lean_unbox(v_requiresData_2063_);
v_handlerDispatched_boxed_2070_ = lean_unbox(v_handlerDispatched_2065_);
v_res_2071_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2057_, v_keepAliveTimeout_2058_, v_currentTimeout_2059_, v_headerTimeout_2060_, v_response_2061_, v_respStream_2062_, v_requiresData_boxed_2069_, v_expectData_2064_, v_handlerDispatched_boxed_2070_, v_pendingHead_2066_, v_x_2067_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2084_, lean_object* v_inst_2085_, lean_object* v___f_2086_, lean_object* v_handler_2087_, lean_object* v___f_2088_, lean_object* v___f_2089_, lean_object* v_inst_2090_, lean_object* v_connectionContext_2091_, lean_object* v_a_2092_, lean_object* v_x_2093_, lean_object* v___y_2094_){
_start:
{
switch(lean_obj_tag(v_a_2092_))
{
case 0:
{
lean_object* v_head_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_connectionContext_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v___f_2089_);
lean_dec_ref(v___f_2088_);
lean_dec(v_handler_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v_inst_2085_);
v_head_2096_ = lean_ctor_get(v_a_2092_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2098_ = v_a_2092_;
v_isShared_2099_ = v_isSharedCheck_2139_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_head_2096_);
lean_dec(v_a_2092_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2139_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_machine_2100_; lean_object* v_requestStream_2101_; lean_object* v_response_2102_; lean_object* v_respStream_2103_; uint8_t v_requiresData_2104_; lean_object* v_expectData_2105_; uint8_t v_handlerDispatched_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2134_; 
v_machine_2100_ = lean_ctor_get(v___y_2094_, 0);
v_requestStream_2101_ = lean_ctor_get(v___y_2094_, 1);
v_response_2102_ = lean_ctor_get(v___y_2094_, 5);
v_respStream_2103_ = lean_ctor_get(v___y_2094_, 6);
v_requiresData_2104_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*9);
v_expectData_2105_ = lean_ctor_get(v___y_2094_, 7);
v_handlerDispatched_2106_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*9 + 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___y_2094_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; lean_object* v_unused_2136_; lean_object* v_unused_2137_; lean_object* v_unused_2138_; 
v_unused_2135_ = lean_ctor_get(v___y_2094_, 8);
lean_dec(v_unused_2135_);
v_unused_2136_ = lean_ctor_get(v___y_2094_, 4);
lean_dec(v_unused_2136_);
v_unused_2137_ = lean_ctor_get(v___y_2094_, 3);
lean_dec(v_unused_2137_);
v_unused_2138_ = lean_ctor_get(v___y_2094_, 2);
lean_dec(v_unused_2138_);
v___x_2108_ = v___y_2094_;
v_isShared_2109_ = v_isSharedCheck_2134_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_expectData_2105_);
lean_inc(v_respStream_2103_);
lean_inc(v_response_2102_);
lean_inc(v_requestStream_2101_);
lean_inc(v_machine_2100_);
lean_dec(v___y_2094_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2134_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_lingeringTimeout_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v_lingeringTimeout_2110_ = lean_ctor_get(v_config_2084_, 4);
lean_inc(v_lingeringTimeout_2110_);
lean_dec_ref(v_config_2084_);
v___x_2111_ = lean_box(0);
lean_inc(v_head_2096_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 1);
v___x_2113_ = v___x_2098_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_head_2096_);
v___x_2113_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
lean_inc_ref(v_requestStream_2101_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 8, v___x_2113_);
lean_ctor_set(v___x_2108_, 4, v___x_2111_);
lean_ctor_set(v___x_2108_, 3, v_lingeringTimeout_2110_);
lean_ctor_set(v___x_2108_, 2, v___x_2111_);
v___x_2115_ = v___x_2108_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_machine_2100_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_requestStream_2101_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_lingeringTimeout_2110_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2132_, 5, v_response_2102_);
lean_ctor_set(v_reuseFailAlloc_2132_, 6, v_respStream_2103_);
lean_ctor_set(v_reuseFailAlloc_2132_, 7, v_expectData_2105_);
lean_ctor_set(v_reuseFailAlloc_2132_, 8, v___x_2113_);
lean_ctor_set_uint8(v_reuseFailAlloc_2132_, sizeof(void*)*9, v_requiresData_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2132_, sizeof(void*)*9 + 1, v_handlerDispatched_2106_);
v___x_2115_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
uint8_t v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = 0;
v___x_2117_ = 1;
v___x_2118_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2116_, v_head_2096_, v___x_2117_);
lean_dec(v_head_2096_);
if (lean_obj_tag(v___x_2118_) == 1)
{
lean_object* v___f_2119_; lean_object* v___x_2120_; lean_object* v___f_2121_; lean_object* v___f_2122_; lean_object* v___x_5121__overap_2123_; lean_object* v___x_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v___f_2119_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2119_, 0, v___x_2118_);
v___x_2120_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2121_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2122_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5121__overap_2123_ = l_Std_Mutex_atomically___redArg(v___x_2120_, v___f_2121_, v___f_2122_, v_requestStream_2101_, v___f_2119_);
v___x_2124_ = lean_apply_1(v___x_5121__overap_2123_, lean_box(0));
v___f_2125_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2125_, 0, v___x_2115_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = 0;
v___x_2128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2126_, v___x_2127_, v___x_2124_, v___f_2125_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec(v___x_2118_);
lean_dec_ref(v_requestStream_2101_);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2115_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_connectionContext_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v___f_2089_);
lean_dec_ref(v___f_2088_);
lean_dec(v_handler_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_config_2084_);
v_size_2140_ = lean_ctor_get(v_a_2092_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2142_ = v_a_2092_;
v_isShared_2143_ = v_isSharedCheck_2167_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_size_2140_);
lean_dec(v_a_2092_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2167_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_machine_2144_; lean_object* v_requestStream_2145_; lean_object* v_keepAliveTimeout_2146_; lean_object* v_currentTimeout_2147_; lean_object* v_headerTimeout_2148_; lean_object* v_response_2149_; lean_object* v_respStream_2150_; uint8_t v_handlerDispatched_2151_; lean_object* v_pendingHead_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2165_; 
v_machine_2144_ = lean_ctor_get(v___y_2094_, 0);
v_requestStream_2145_ = lean_ctor_get(v___y_2094_, 1);
v_keepAliveTimeout_2146_ = lean_ctor_get(v___y_2094_, 2);
v_currentTimeout_2147_ = lean_ctor_get(v___y_2094_, 3);
v_headerTimeout_2148_ = lean_ctor_get(v___y_2094_, 4);
v_response_2149_ = lean_ctor_get(v___y_2094_, 5);
v_respStream_2150_ = lean_ctor_get(v___y_2094_, 6);
v_handlerDispatched_2151_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*9 + 1);
v_pendingHead_2152_ = lean_ctor_get(v___y_2094_, 8);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___y_2094_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___y_2094_, 7);
lean_dec(v_unused_2166_);
v___x_2154_ = v___y_2094_;
v_isShared_2155_ = v_isSharedCheck_2165_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_pendingHead_2152_);
lean_inc(v_respStream_2150_);
lean_inc(v_response_2149_);
lean_inc(v_headerTimeout_2148_);
lean_inc(v_currentTimeout_2147_);
lean_inc(v_keepAliveTimeout_2146_);
lean_inc(v_requestStream_2145_);
lean_inc(v_machine_2144_);
lean_dec(v___y_2094_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2165_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
uint8_t v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = 1;
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 7, v_size_2140_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_machine_2144_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_requestStream_2145_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_keepAliveTimeout_2146_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_currentTimeout_2147_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_headerTimeout_2148_);
lean_ctor_set(v_reuseFailAlloc_2164_, 5, v_response_2149_);
lean_ctor_set(v_reuseFailAlloc_2164_, 6, v_respStream_2150_);
lean_ctor_set(v_reuseFailAlloc_2164_, 7, v_size_2140_);
lean_ctor_set(v_reuseFailAlloc_2164_, 8, v_pendingHead_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2164_, sizeof(void*)*9 + 1, v_handlerDispatched_2151_);
v___x_2158_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*9, v___x_2156_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2158_);
v___x_2160_ = v___x_2142_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2168_; lean_object* v_onFailure_2169_; lean_object* v___f_2170_; lean_object* v___y_2172_; 
lean_dec_ref(v_connectionContext_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v___f_2089_);
lean_dec_ref(v___f_2088_);
lean_dec_ref(v_config_2084_);
v_err_2168_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_err_2168_);
lean_dec_ref(v_a_2092_);
v_onFailure_2169_ = lean_ctor_get(v_inst_2085_, 2);
lean_inc_ref(v_onFailure_2169_);
lean_dec_ref(v_inst_2085_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2170_, 0, v___y_2094_);
lean_closure_set(v___f_2170_, 1, v___f_2086_);
switch(lean_obj_tag(v_err_2168_))
{
case 0:
{
lean_object* v___x_2178_; 
v___x_2178_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2172_ = v___x_2178_;
goto v___jp_2171_;
}
case 1:
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2172_ = v___x_2179_;
goto v___jp_2171_;
}
case 2:
{
lean_object* v___x_2180_; 
v___x_2180_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2172_ = v___x_2180_;
goto v___jp_2171_;
}
case 3:
{
lean_object* v___x_2181_; 
v___x_2181_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2172_ = v___x_2181_;
goto v___jp_2171_;
}
case 4:
{
lean_object* v___x_2182_; 
v___x_2182_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2172_ = v___x_2182_;
goto v___jp_2171_;
}
case 5:
{
lean_object* v___x_2183_; 
v___x_2183_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2172_ = v___x_2183_;
goto v___jp_2171_;
}
case 6:
{
lean_object* v___x_2184_; 
v___x_2184_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2172_ = v___x_2184_;
goto v___jp_2171_;
}
case 7:
{
lean_object* v___x_2185_; 
v___x_2185_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2172_ = v___x_2185_;
goto v___jp_2171_;
}
case 8:
{
lean_object* v___x_2186_; 
v___x_2186_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2172_ = v___x_2186_;
goto v___jp_2171_;
}
case 9:
{
lean_object* v___x_2187_; 
v___x_2187_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2172_ = v___x_2187_;
goto v___jp_2171_;
}
case 10:
{
lean_object* v___x_2188_; 
v___x_2188_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2172_ = v___x_2188_;
goto v___jp_2171_;
}
default: 
{
lean_object* v_message_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_message_2189_ = lean_ctor_get(v_err_2168_, 0);
lean_inc_ref(v_message_2189_);
lean_dec_ref(v_err_2168_);
v___x_2190_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2191_ = lean_string_append(v___x_2190_, v_message_2189_);
lean_dec_ref(v_message_2189_);
v___y_2172_ = v___x_2191_;
goto v___jp_2171_;
}
}
v___jp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2173_ = lean_mk_io_user_error(v___y_2172_);
v___x_2174_ = lean_apply_3(v_onFailure_2169_, v_handler_2087_, v___x_2173_, lean_box(0));
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = 0;
v___x_2177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2175_, v___x_2176_, v___x_2174_, v___f_2170_);
return v___x_2177_;
}
}
case 4:
{
lean_object* v_requestStream_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_5177__overap_2198_; lean_object* v___x_2199_; lean_object* v___f_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v_connectionContext_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v___f_2089_);
lean_dec(v_handler_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_config_2084_);
v_requestStream_2192_ = lean_ctor_get(v___y_2094_, 1);
lean_inc_ref_n(v_requestStream_2192_, 2);
v___x_2193_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2194_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2195_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2196_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2197_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2197_, 0, lean_box(0));
lean_closure_set(v___x_2197_, 1, lean_box(0));
lean_closure_set(v___x_2197_, 2, lean_box(0));
lean_closure_set(v___x_2197_, 3, v___x_2193_);
lean_closure_set(v___x_2197_, 4, lean_box(0));
lean_closure_set(v___x_2197_, 5, lean_box(0));
lean_closure_set(v___x_2197_, 6, v___x_2196_);
lean_closure_set(v___x_2197_, 7, v___f_2088_);
v___x_5177__overap_2198_ = l_Std_Mutex_atomically___redArg(v___x_2193_, v___f_2194_, v___f_2195_, v_requestStream_2192_, v___x_2197_);
v___x_2199_ = lean_apply_1(v___x_5177__overap_2198_, lean_box(0));
lean_inc_ref(v___y_2094_);
v___f_2200_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2200_, 0, v___y_2094_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2201_, 0, v_requestStream_2192_);
lean_closure_set(v___f_2201_, 1, v___f_2200_);
lean_closure_set(v___f_2201_, 2, v___y_2094_);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = 0;
v___x_2204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2202_, v___x_2203_, v___x_2199_, v___f_2201_);
return v___x_2204_;
}
case 6:
{
lean_object* v_machine_2205_; lean_object* v_requestStream_2206_; lean_object* v_respStream_2207_; uint8_t v_requiresData_2208_; lean_object* v_expectData_2209_; lean_object* v_pendingHead_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_5198__overap_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___f_2219_; lean_object* v___f_2220_; lean_object* v___f_2221_; lean_object* v___f_2222_; lean_object* v___f_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_connectionContext_2091_);
lean_dec_ref(v___f_2088_);
lean_dec(v_handler_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v_inst_2085_);
v_machine_2205_ = lean_ctor_get(v___y_2094_, 0);
lean_inc_ref(v_machine_2205_);
v_requestStream_2206_ = lean_ctor_get(v___y_2094_, 1);
lean_inc_ref_n(v_requestStream_2206_, 2);
v_respStream_2207_ = lean_ctor_get(v___y_2094_, 6);
lean_inc(v_respStream_2207_);
v_requiresData_2208_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*9);
v_expectData_2209_ = lean_ctor_get(v___y_2094_, 7);
lean_inc(v_expectData_2209_);
v_pendingHead_2210_ = lean_ctor_get(v___y_2094_, 8);
lean_inc(v_pendingHead_2210_);
lean_dec_ref(v___y_2094_);
v___x_2211_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2212_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2213_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2214_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2215_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2215_, 0, lean_box(0));
lean_closure_set(v___x_2215_, 1, lean_box(0));
lean_closure_set(v___x_2215_, 2, lean_box(0));
lean_closure_set(v___x_2215_, 3, v___x_2211_);
lean_closure_set(v___x_2215_, 4, lean_box(0));
lean_closure_set(v___x_2215_, 5, lean_box(0));
lean_closure_set(v___x_2215_, 6, v___x_2214_);
lean_closure_set(v___x_2215_, 7, v___f_2089_);
v___x_5198__overap_2216_ = l_Std_Mutex_atomically___redArg(v___x_2211_, v___f_2212_, v___f_2213_, v_requestStream_2206_, v___x_2215_);
v___x_2217_ = lean_apply_1(v___x_5198__overap_2216_, lean_box(0));
v___x_2218_ = lean_box(v_requiresData_2208_);
v___f_2219_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2219_, 0, v_config_2084_);
lean_closure_set(v___f_2219_, 1, v_machine_2205_);
lean_closure_set(v___f_2219_, 2, v___x_2218_);
lean_closure_set(v___f_2219_, 3, v_expectData_2209_);
lean_closure_set(v___f_2219_, 4, v_pendingHead_2210_);
v___f_2220_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2220_, 0, v___f_2219_);
lean_inc_ref(v___f_2220_);
v___f_2221_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2221_, 0, v___f_2220_);
v___f_2222_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2222_, 0, v_respStream_2207_);
lean_closure_set(v___f_2222_, 1, v_inst_2090_);
lean_closure_set(v___f_2222_, 2, v___f_2221_);
lean_closure_set(v___f_2222_, 3, v___f_2220_);
lean_inc_ref(v___f_2222_);
v___f_2223_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2223_, 0, v___f_2222_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2224_, 0, v_requestStream_2206_);
lean_closure_set(v___f_2224_, 1, v___f_2223_);
lean_closure_set(v___f_2224_, 2, v___f_2222_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = 0;
v___x_2227_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2225_, v___x_2226_, v___x_2217_, v___f_2224_);
return v___x_2227_;
}
case 7:
{
lean_object* v_pendingHead_2228_; 
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v___f_2089_);
lean_dec_ref(v___f_2088_);
lean_dec_ref(v___f_2086_);
v_pendingHead_2228_ = lean_ctor_get(v___y_2094_, 8);
if (lean_obj_tag(v_pendingHead_2228_) == 1)
{
lean_object* v_machine_2229_; lean_object* v_requestStream_2230_; lean_object* v_keepAliveTimeout_2231_; lean_object* v_currentTimeout_2232_; lean_object* v_headerTimeout_2233_; lean_object* v_response_2234_; lean_object* v_respStream_2235_; uint8_t v_requiresData_2236_; lean_object* v_expectData_2237_; uint8_t v_handlerDispatched_2238_; lean_object* v_val_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; 
lean_inc_ref(v_pendingHead_2228_);
v_machine_2229_ = lean_ctor_get(v___y_2094_, 0);
lean_inc_ref(v_machine_2229_);
v_requestStream_2230_ = lean_ctor_get(v___y_2094_, 1);
lean_inc_ref(v_requestStream_2230_);
v_keepAliveTimeout_2231_ = lean_ctor_get(v___y_2094_, 2);
lean_inc(v_keepAliveTimeout_2231_);
v_currentTimeout_2232_ = lean_ctor_get(v___y_2094_, 3);
lean_inc(v_currentTimeout_2232_);
v_headerTimeout_2233_ = lean_ctor_get(v___y_2094_, 4);
lean_inc(v_headerTimeout_2233_);
v_response_2234_ = lean_ctor_get(v___y_2094_, 5);
lean_inc_ref(v_response_2234_);
v_respStream_2235_ = lean_ctor_get(v___y_2094_, 6);
lean_inc(v_respStream_2235_);
v_requiresData_2236_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*9);
v_expectData_2237_ = lean_ctor_get(v___y_2094_, 7);
lean_inc(v_expectData_2237_);
v_handlerDispatched_2238_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2094_);
v_val_2239_ = lean_ctor_get(v_pendingHead_2228_, 0);
lean_inc(v_val_2239_);
v___x_2240_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2085_, v_handler_2087_, v_machine_2229_, v_val_2239_, v_config_2084_, v_connectionContext_2091_);
v___x_2241_ = lean_box(v_requiresData_2236_);
v___x_2242_ = lean_box(v_handlerDispatched_2238_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2243_, 0, v_requestStream_2230_);
lean_closure_set(v___f_2243_, 1, v_keepAliveTimeout_2231_);
lean_closure_set(v___f_2243_, 2, v_currentTimeout_2232_);
lean_closure_set(v___f_2243_, 3, v_headerTimeout_2233_);
lean_closure_set(v___f_2243_, 4, v_response_2234_);
lean_closure_set(v___f_2243_, 5, v_respStream_2235_);
lean_closure_set(v___f_2243_, 6, v___x_2241_);
lean_closure_set(v___f_2243_, 7, v_expectData_2237_);
lean_closure_set(v___f_2243_, 8, v___x_2242_);
lean_closure_set(v___f_2243_, 9, v_pendingHead_2228_);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = 0;
v___x_2246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2244_, v___x_2245_, v___x_2240_, v___f_2243_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v_connectionContext_2091_);
lean_dec(v_handler_2087_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_config_2084_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___y_2094_);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
default: 
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec(v_a_2092_);
lean_dec_ref(v_connectionContext_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v___f_2089_);
lean_dec_ref(v___f_2088_);
lean_dec(v_handler_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_config_2084_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___y_2094_);
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2253_, lean_object* v_inst_2254_, lean_object* v___f_2255_, lean_object* v_handler_2256_, lean_object* v___f_2257_, lean_object* v___f_2258_, lean_object* v_inst_2259_, lean_object* v_connectionContext_2260_, lean_object* v_a_2261_, lean_object* v_x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2253_, v_inst_2254_, v___f_2255_, v_handler_2256_, v___f_2257_, v___f_2258_, v_inst_2259_, v_connectionContext_2260_, v_a_2261_, v_x_2262_, v___y_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_x_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_handler_2276_, lean_object* v_config_2277_, lean_object* v_connectionContext_2278_, lean_object* v_events_2279_, lean_object* v_state_2280_){
_start:
{
lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; size_t v_sz_2285_; size_t v___x_2286_; lean_object* v___x_4110__overap_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; 
v___f_2282_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2283_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2283_, 0, v_config_2277_);
lean_closure_set(v___f_2283_, 1, v_inst_2274_);
lean_closure_set(v___f_2283_, 2, v___f_2282_);
lean_closure_set(v___f_2283_, 3, v_handler_2276_);
lean_closure_set(v___f_2283_, 4, v___f_2282_);
lean_closure_set(v___f_2283_, 5, v___f_2282_);
lean_closure_set(v___f_2283_, 6, v_inst_2275_);
lean_closure_set(v___f_2283_, 7, v_connectionContext_2278_);
v___x_2284_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2285_ = lean_array_size(v_events_2279_);
v___x_2286_ = ((size_t)0ULL);
v___x_4110__overap_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2284_, v_events_2279_, v___f_2283_, v_sz_2285_, v___x_2286_, v_state_2280_);
v___x_2288_ = lean_apply_1(v___x_4110__overap_2287_, lean_box(0));
v___f_2289_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = 0;
v___x_2292_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2290_, v___x_2291_, v___x_2288_, v___f_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_handler_2295_, lean_object* v_config_2296_, lean_object* v_connectionContext_2297_, lean_object* v_events_2298_, lean_object* v_state_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2293_, v_inst_2294_, v_handler_2295_, v_config_2296_, v_connectionContext_2297_, v_events_2298_, v_state_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2302_, lean_object* v_00_u03b2_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_handler_2306_, lean_object* v_config_2307_, lean_object* v_connectionContext_2308_, lean_object* v_events_2309_, lean_object* v_state_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2304_, v_inst_2305_, v_handler_2306_, v_config_2307_, v_connectionContext_2308_, v_events_2309_, v_state_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2313_, lean_object* v_00_u03b2_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_handler_2317_, lean_object* v_config_2318_, lean_object* v_connectionContext_2319_, lean_object* v_events_2320_, lean_object* v_state_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2313_, v_00_u03b2_2314_, v_inst_2315_, v_inst_2316_, v_handler_2317_, v_config_2318_, v_connectionContext_2319_, v_events_2320_, v_state_2321_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2324_){
_start:
{
if (lean_obj_tag(v_x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_ctor_get(v_x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v_x_2324_);
v___x_2326_ = lean_task_pure(v_a_2325_);
return v___x_2326_;
}
else
{
lean_object* v_a_2327_; 
v_a_2327_ = lean_ctor_get(v_x_2324_, 0);
lean_inc_ref(v_a_2327_);
lean_dec_ref(v_x_2324_);
return v_a_2327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2328_, lean_object* v_requestStream_2329_, lean_object* v_keepAliveTimeout_2330_, lean_object* v_currentTimeout_2331_, lean_object* v_headerTimeout_2332_, lean_object* v_response_2333_, lean_object* v_respStream_2334_, uint8_t v_requiresData_2335_, lean_object* v_expectData_2336_, lean_object* v_x_2337_){
_start:
{
if (lean_obj_tag(v_x_2337_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_expectData_2336_);
lean_dec(v_respStream_2334_);
lean_dec_ref(v_response_2333_);
lean_dec(v_headerTimeout_2332_);
lean_dec(v_currentTimeout_2331_);
lean_dec(v_keepAliveTimeout_2330_);
lean_dec_ref(v_requestStream_2329_);
lean_dec_ref(v_machine_2328_);
v_a_2339_ = lean_ctor_get(v_x_2337_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_x_2337_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2341_ = v_x_2337_;
v_isShared_2342_ = v_isSharedCheck_2347_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v_x_2337_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2347_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
}
else
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v_x_2337_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v_x_2337_, 0);
lean_dec(v_unused_2359_);
v___x_2349_ = v_x_2337_;
v_isShared_2350_ = v_isSharedCheck_2358_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v_x_2337_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2358_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2351_ = 1;
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2353_, 0, v_machine_2328_);
lean_ctor_set(v___x_2353_, 1, v_requestStream_2329_);
lean_ctor_set(v___x_2353_, 2, v_keepAliveTimeout_2330_);
lean_ctor_set(v___x_2353_, 3, v_currentTimeout_2331_);
lean_ctor_set(v___x_2353_, 4, v_headerTimeout_2332_);
lean_ctor_set(v___x_2353_, 5, v_response_2333_);
lean_ctor_set(v___x_2353_, 6, v_respStream_2334_);
lean_ctor_set(v___x_2353_, 7, v_expectData_2336_);
lean_ctor_set(v___x_2353_, 8, v___x_2352_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*9, v_requiresData_2335_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*9 + 1, v___x_2351_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2353_);
v___x_2355_ = v___x_2349_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2360_, lean_object* v_requestStream_2361_, lean_object* v_keepAliveTimeout_2362_, lean_object* v_currentTimeout_2363_, lean_object* v_headerTimeout_2364_, lean_object* v_response_2365_, lean_object* v_respStream_2366_, lean_object* v_requiresData_2367_, lean_object* v_expectData_2368_, lean_object* v_x_2369_, lean_object* v___y_2370_){
_start:
{
uint8_t v_requiresData_boxed_2371_; lean_object* v_res_2372_; 
v_requiresData_boxed_2371_ = lean_unbox(v_requiresData_2367_);
v_res_2372_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2360_, v_requestStream_2361_, v_keepAliveTimeout_2362_, v_currentTimeout_2363_, v_headerTimeout_2364_, v_response_2365_, v_respStream_2366_, v_requiresData_boxed_2371_, v_expectData_2368_, v_x_2369_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2373_, lean_object* v_response_2374_, lean_object* v___x_2375_, lean_object* v___f_2376_, lean_object* v_x_2377_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v___f_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v_response_2374_);
lean_dec_ref(v_toFunctor_2373_);
v_a_2379_ = lean_ctor_get(v_x_2377_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2381_ = v_x_2377_;
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v_x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2402_; 
v_a_2388_ = lean_ctor_get(v_x_2377_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2390_ = v_x_2377_;
v_isShared_2391_ = v_isSharedCheck_2402_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v_x_2377_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2402_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2392_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2392_, 0, lean_box(0));
lean_closure_set(v___x_2392_, 1, lean_box(0));
lean_closure_set(v___x_2392_, 2, v_toFunctor_2373_);
v___x_2393_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2393_, 0, lean_box(0));
lean_closure_set(v___x_2393_, 1, v_response_2374_);
v___x_2394_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2394_, 0, lean_box(0));
lean_closure_set(v___x_2394_, 1, lean_box(0));
lean_closure_set(v___x_2394_, 2, lean_box(0));
lean_closure_set(v___x_2394_, 3, v___x_2392_);
lean_closure_set(v___x_2394_, 4, v___x_2393_);
v___x_2395_ = 0;
lean_inc(v___x_2375_);
v___x_2396_ = l_BaseIO_chainTask___redArg(v_a_2388_, v___x_2394_, v___x_2375_, v___x_2395_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2396_);
v___x_2398_ = v___x_2390_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
v___x_2400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2375_, v___x_2395_, v___x_2399_, v___f_2376_);
return v___x_2400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2403_, lean_object* v_response_2404_, lean_object* v___x_2405_, lean_object* v___f_2406_, lean_object* v_x_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2403_, v_response_2404_, v___x_2405_, v___f_2406_, v_x_2407_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2411_, lean_object* v_handler_2412_, lean_object* v_extensions_2413_, lean_object* v_connectionContext_2414_, lean_object* v_state_2415_){
_start:
{
lean_object* v___x_2417_; lean_object* v_toApplicative_2418_; lean_object* v_pendingHead_2419_; 
v___x_2417_ = l_instMonadBaseIO;
v_toApplicative_2418_ = lean_ctor_get(v___x_2417_, 0);
v_pendingHead_2419_ = lean_ctor_get(v_state_2415_, 8);
lean_inc(v_pendingHead_2419_);
if (lean_obj_tag(v_pendingHead_2419_) == 1)
{
lean_object* v_toFunctor_2420_; lean_object* v_machine_2421_; lean_object* v_requestStream_2422_; lean_object* v_keepAliveTimeout_2423_; lean_object* v_currentTimeout_2424_; lean_object* v_headerTimeout_2425_; lean_object* v_response_2426_; lean_object* v_respStream_2427_; uint8_t v_requiresData_2428_; lean_object* v_expectData_2429_; lean_object* v_val_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2452_; 
v_toFunctor_2420_ = lean_ctor_get(v_toApplicative_2418_, 0);
v_machine_2421_ = lean_ctor_get(v_state_2415_, 0);
lean_inc_ref(v_machine_2421_);
v_requestStream_2422_ = lean_ctor_get(v_state_2415_, 1);
lean_inc_ref(v_requestStream_2422_);
v_keepAliveTimeout_2423_ = lean_ctor_get(v_state_2415_, 2);
lean_inc(v_keepAliveTimeout_2423_);
v_currentTimeout_2424_ = lean_ctor_get(v_state_2415_, 3);
lean_inc(v_currentTimeout_2424_);
v_headerTimeout_2425_ = lean_ctor_get(v_state_2415_, 4);
lean_inc(v_headerTimeout_2425_);
v_response_2426_ = lean_ctor_get(v_state_2415_, 5);
lean_inc_ref(v_response_2426_);
v_respStream_2427_ = lean_ctor_get(v_state_2415_, 6);
lean_inc(v_respStream_2427_);
v_requiresData_2428_ = lean_ctor_get_uint8(v_state_2415_, sizeof(void*)*9);
v_expectData_2429_ = lean_ctor_get(v_state_2415_, 7);
lean_inc(v_expectData_2429_);
lean_dec_ref(v_state_2415_);
v_val_2430_ = lean_ctor_get(v_pendingHead_2419_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_pendingHead_2419_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2432_ = v_pendingHead_2419_;
v_isShared_2433_ = v_isSharedCheck_2452_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_val_2430_);
lean_dec(v_pendingHead_2419_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2452_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_onRequest_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v_onRequest_2434_ = lean_ctor_get(v_inst_2411_, 1);
lean_inc_ref(v_onRequest_2434_);
lean_dec_ref(v_inst_2411_);
lean_inc_ref(v_requestStream_2422_);
v___x_2435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2435_, 0, v_val_2430_);
lean_ctor_set(v___x_2435_, 1, v_requestStream_2422_);
lean_ctor_set(v___x_2435_, 2, v_extensions_2413_);
v___x_2436_ = lean_apply_3(v_onRequest_2434_, v_handler_2412_, v___x_2435_, v_connectionContext_2414_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2438_, 0, lean_box(0));
lean_closure_set(v___x_2438_, 1, v___x_2436_);
v___x_2439_ = lean_io_as_task(v___x_2438_, v___x_2437_);
v___f_2440_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2441_ = lean_box(v_requiresData_2428_);
lean_inc_ref(v_response_2426_);
v___f_2442_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2442_, 0, v_machine_2421_);
lean_closure_set(v___f_2442_, 1, v_requestStream_2422_);
lean_closure_set(v___f_2442_, 2, v_keepAliveTimeout_2423_);
lean_closure_set(v___f_2442_, 3, v_currentTimeout_2424_);
lean_closure_set(v___f_2442_, 4, v_headerTimeout_2425_);
lean_closure_set(v___f_2442_, 5, v_response_2426_);
lean_closure_set(v___f_2442_, 6, v_respStream_2427_);
lean_closure_set(v___f_2442_, 7, v___x_2441_);
lean_closure_set(v___f_2442_, 8, v_expectData_2429_);
lean_inc_ref(v_toFunctor_2420_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2443_, 0, v_toFunctor_2420_);
lean_closure_set(v___f_2443_, 1, v_response_2426_);
lean_closure_set(v___f_2443_, 2, v___x_2437_);
lean_closure_set(v___f_2443_, 3, v___f_2442_);
v___x_2444_ = 1;
v___x_2445_ = lean_task_bind(v___x_2439_, v___f_2440_, v___x_2437_, v___x_2444_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2445_);
v___x_2447_ = v___x_2432_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
v___x_2449_ = 0;
v___x_2450_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2437_, v___x_2449_, v___x_2448_, v___f_2443_);
return v___x_2450_;
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_dec(v_pendingHead_2419_);
lean_dec_ref(v_connectionContext_2414_);
lean_dec(v_extensions_2413_);
lean_dec(v_handler_2412_);
lean_dec_ref(v_inst_2411_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_state_2415_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2455_, lean_object* v_handler_2456_, lean_object* v_extensions_2457_, lean_object* v_connectionContext_2458_, lean_object* v_state_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2455_, v_handler_2456_, v_extensions_2457_, v_connectionContext_2458_, v_state_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2462_, lean_object* v_inst_2463_, lean_object* v_handler_2464_, lean_object* v_extensions_2465_, lean_object* v_connectionContext_2466_, lean_object* v_state_2467_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2463_, v_handler_2464_, v_extensions_2465_, v_connectionContext_2466_, v_state_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2470_, lean_object* v_inst_2471_, lean_object* v_handler_2472_, lean_object* v_extensions_2473_, lean_object* v_connectionContext_2474_, lean_object* v_state_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2470_, v_inst_2471_, v_handler_2472_, v_extensions_2473_, v_connectionContext_2474_, v_state_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2478_, lean_object* v_____r_2479_){
_start:
{
lean_object* v_writer_2481_; lean_object* v_reader_2482_; lean_object* v_config_2483_; lean_object* v_events_2484_; lean_object* v_error_2485_; lean_object* v_instant_2486_; uint8_t v_keepAlive_2487_; uint8_t v_forcedFlush_2488_; uint8_t v_pullBodyStalled_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2516_; 
v_writer_2481_ = lean_ctor_get(v_machine_2478_, 1);
v_reader_2482_ = lean_ctor_get(v_machine_2478_, 0);
v_config_2483_ = lean_ctor_get(v_machine_2478_, 2);
v_events_2484_ = lean_ctor_get(v_machine_2478_, 3);
v_error_2485_ = lean_ctor_get(v_machine_2478_, 4);
v_instant_2486_ = lean_ctor_get(v_machine_2478_, 5);
v_keepAlive_2487_ = lean_ctor_get_uint8(v_machine_2478_, sizeof(void*)*6);
v_forcedFlush_2488_ = lean_ctor_get_uint8(v_machine_2478_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2489_ = lean_ctor_get_uint8(v_machine_2478_, sizeof(void*)*6 + 2);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_machine_2478_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2491_ = v_machine_2478_;
v_isShared_2492_ = v_isSharedCheck_2516_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_instant_2486_);
lean_inc(v_error_2485_);
lean_inc(v_events_2484_);
lean_inc(v_config_2483_);
lean_inc(v_writer_2481_);
lean_inc(v_reader_2482_);
lean_dec(v_machine_2478_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2516_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_userData_2493_; lean_object* v_outputData_2494_; lean_object* v_state_2495_; lean_object* v_knownSize_2496_; lean_object* v_messageHead_2497_; uint8_t v_sentMessage_2498_; uint8_t v_omitBody_2499_; lean_object* v_userDataBytes_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2515_; 
v_userData_2493_ = lean_ctor_get(v_writer_2481_, 0);
v_outputData_2494_ = lean_ctor_get(v_writer_2481_, 1);
v_state_2495_ = lean_ctor_get(v_writer_2481_, 2);
v_knownSize_2496_ = lean_ctor_get(v_writer_2481_, 3);
v_messageHead_2497_ = lean_ctor_get(v_writer_2481_, 4);
v_sentMessage_2498_ = lean_ctor_get_uint8(v_writer_2481_, sizeof(void*)*6);
v_omitBody_2499_ = lean_ctor_get_uint8(v_writer_2481_, sizeof(void*)*6 + 2);
v_userDataBytes_2500_ = lean_ctor_get(v_writer_2481_, 5);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_writer_2481_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2502_ = v_writer_2481_;
v_isShared_2503_ = v_isSharedCheck_2515_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_userDataBytes_2500_);
lean_inc(v_messageHead_2497_);
lean_inc(v_knownSize_2496_);
lean_inc(v_state_2495_);
lean_inc(v_outputData_2494_);
lean_inc(v_userData_2493_);
lean_dec(v_writer_2481_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2515_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
uint8_t v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = 1;
if (v_isShared_2503_ == 0)
{
v___x_2506_ = v___x_2502_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_userData_2493_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_outputData_2494_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_state_2495_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_knownSize_2496_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_messageHead_2497_);
lean_ctor_set(v_reuseFailAlloc_2514_, 5, v_userDataBytes_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2514_, sizeof(void*)*6, v_sentMessage_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2514_, sizeof(void*)*6 + 2, v_omitBody_2499_);
v___x_2506_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2508_; 
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*6 + 1, v___x_2504_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v___x_2506_);
v___x_2508_ = v___x_2491_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_reader_2482_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_config_2483_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_events_2484_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v_error_2485_);
lean_ctor_set(v_reuseFailAlloc_2513_, 5, v_instant_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*6, v_keepAlive_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*6 + 1, v_forcedFlush_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*6 + 2, v_pullBodyStalled_2489_);
v___x_2508_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2517_, lean_object* v_____r_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2517_, v_____r_2518_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2521_, lean_object* v_x2_2522_){
_start:
{
lean_object* v_data_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_data_2523_ = lean_ctor_get(v_x2_2522_, 0);
v___x_2524_ = lean_byte_array_size(v_data_2523_);
v___x_2525_ = lean_nat_add(v_x1_2521_, v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2526_, lean_object* v_x2_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2526_, v_x2_2527_);
lean_dec_ref(v_x2_2527_);
lean_dec(v_x1_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2529_, lean_object* v_machine_2530_, lean_object* v_isClosed_2531_, lean_object* v___f_2532_, lean_object* v___f_2533_, lean_object* v_x_2534_){
_start:
{
lean_object* v___y_2537_; 
if (lean_obj_tag(v_x_2534_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v___f_2533_);
lean_dec_ref(v___f_2532_);
lean_dec_ref(v_isClosed_2531_);
lean_dec_ref(v_machine_2530_);
lean_dec(v_body_2529_);
v_a_2542_ = lean_ctor_get(v_x_2534_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2534_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2544_ = v_x_2534_;
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v_x_2534_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2618_; 
v_a_2551_ = lean_ctor_get(v_x_2534_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_x_2534_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2553_ = v_x_2534_;
v_isShared_2554_ = v_isSharedCheck_2618_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v_x_2534_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2618_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
if (lean_obj_tag(v_a_2551_) == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_dec_ref(v___f_2533_);
lean_dec_ref(v___f_2532_);
lean_dec_ref(v_isClosed_2531_);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_body_2529_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v_machine_2530_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2556_);
v___x_2558_ = v___x_2553_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
else
{
lean_object* v_val_2561_; 
lean_del_object(v___x_2553_);
v_val_2561_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_val_2561_);
lean_dec_ref(v_a_2551_);
if (lean_obj_tag(v_val_2561_) == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v___f_2533_);
lean_dec_ref(v_machine_2530_);
v___x_2562_ = lean_apply_2(v_isClosed_2531_, v_body_2529_, lean_box(0));
v___x_2563_ = lean_unsigned_to_nat(0u);
v___x_2564_ = 0;
v___x_2565_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2563_, v___x_2564_, v___x_2562_, v___f_2532_);
return v___x_2565_;
}
else
{
lean_object* v_val_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
lean_dec_ref(v___f_2532_);
lean_dec_ref(v_isClosed_2531_);
v_val_2566_ = lean_ctor_get(v_val_2561_, 0);
lean_inc(v_val_2566_);
lean_dec_ref(v_val_2561_);
v___x_2567_ = lean_unsigned_to_nat(1u);
v___x_2568_ = lean_mk_empty_array_with_capacity(v___x_2567_);
v___x_2569_ = lean_array_push(v___x_2568_, v_val_2566_);
v___x_2570_ = lean_array_get_size(v___x_2569_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_nat_dec_eq(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v_reader_2573_; lean_object* v_writer_2574_; lean_object* v_config_2575_; lean_object* v_events_2576_; lean_object* v_error_2577_; lean_object* v_instant_2578_; uint8_t v_keepAlive_2579_; uint8_t v_forcedFlush_2580_; uint8_t v_pullBodyStalled_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2617_; 
v_reader_2573_ = lean_ctor_get(v_machine_2530_, 0);
v_writer_2574_ = lean_ctor_get(v_machine_2530_, 1);
v_config_2575_ = lean_ctor_get(v_machine_2530_, 2);
v_events_2576_ = lean_ctor_get(v_machine_2530_, 3);
v_error_2577_ = lean_ctor_get(v_machine_2530_, 4);
v_instant_2578_ = lean_ctor_get(v_machine_2530_, 5);
v_keepAlive_2579_ = lean_ctor_get_uint8(v_machine_2530_, sizeof(void*)*6);
v_forcedFlush_2580_ = lean_ctor_get_uint8(v_machine_2530_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2581_ = lean_ctor_get_uint8(v_machine_2530_, sizeof(void*)*6 + 2);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_machine_2530_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2583_ = v_machine_2530_;
v_isShared_2584_ = v_isSharedCheck_2617_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_instant_2578_);
lean_inc(v_error_2577_);
lean_inc(v_events_2576_);
lean_inc(v_config_2575_);
lean_inc(v_writer_2574_);
lean_inc(v_reader_2573_);
lean_dec(v_machine_2530_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2617_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___y_2586_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2609_ = lean_nat_dec_lt(v___x_2571_, v___x_2570_);
if (v___x_2609_ == 0)
{
lean_dec_ref(v___f_2533_);
v___y_2586_ = v___x_2571_;
goto v___jp_2585_;
}
else
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_nat_dec_le(v___x_2570_, v___x_2570_);
if (v___x_2610_ == 0)
{
if (v___x_2609_ == 0)
{
lean_dec_ref(v___f_2533_);
v___y_2586_ = v___x_2571_;
goto v___jp_2585_;
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = lean_usize_of_nat(v___x_2570_);
lean_inc_ref(v___x_2569_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2608_, v___f_2533_, v___x_2569_, v___x_2611_, v___x_2612_, v___x_2571_);
v___y_2586_ = v___x_2613_;
goto v___jp_2585_;
}
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2570_);
lean_inc_ref(v___x_2569_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2608_, v___f_2533_, v___x_2569_, v___x_2614_, v___x_2615_, v___x_2571_);
v___y_2586_ = v___x_2616_;
goto v___jp_2585_;
}
}
v___jp_2585_:
{
lean_object* v_userData_2587_; lean_object* v_outputData_2588_; lean_object* v_state_2589_; lean_object* v_knownSize_2590_; lean_object* v_messageHead_2591_; uint8_t v_sentMessage_2592_; uint8_t v_userClosedBody_2593_; uint8_t v_omitBody_2594_; lean_object* v_userDataBytes_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2607_; 
v_userData_2587_ = lean_ctor_get(v_writer_2574_, 0);
v_outputData_2588_ = lean_ctor_get(v_writer_2574_, 1);
v_state_2589_ = lean_ctor_get(v_writer_2574_, 2);
v_knownSize_2590_ = lean_ctor_get(v_writer_2574_, 3);
v_messageHead_2591_ = lean_ctor_get(v_writer_2574_, 4);
v_sentMessage_2592_ = lean_ctor_get_uint8(v_writer_2574_, sizeof(void*)*6);
v_userClosedBody_2593_ = lean_ctor_get_uint8(v_writer_2574_, sizeof(void*)*6 + 1);
v_omitBody_2594_ = lean_ctor_get_uint8(v_writer_2574_, sizeof(void*)*6 + 2);
v_userDataBytes_2595_ = lean_ctor_get(v_writer_2574_, 5);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_writer_2574_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2597_ = v_writer_2574_;
v_isShared_2598_ = v_isSharedCheck_2607_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_userDataBytes_2595_);
lean_inc(v_messageHead_2591_);
lean_inc(v_knownSize_2590_);
lean_inc(v_state_2589_);
lean_inc(v_outputData_2588_);
lean_inc(v_userData_2587_);
lean_dec(v_writer_2574_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2607_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2599_ = l_Array_append___redArg(v_userData_2587_, v___x_2569_);
lean_dec_ref(v___x_2569_);
v___x_2600_ = lean_nat_add(v_userDataBytes_2595_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec(v_userDataBytes_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 5, v___x_2600_);
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_outputData_2588_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_state_2589_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_knownSize_2590_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_messageHead_2591_);
lean_ctor_set(v_reuseFailAlloc_2606_, 5, v___x_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*6, v_sentMessage_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*6 + 1, v_userClosedBody_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*6 + 2, v_omitBody_2594_);
v___x_2602_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 1, v___x_2602_);
v___x_2604_ = v___x_2583_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_reader_2573_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_config_2575_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_events_2576_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_error_2577_);
lean_ctor_set(v_reuseFailAlloc_2605_, 5, v_instant_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2605_, sizeof(void*)*6, v_keepAlive_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2605_, sizeof(void*)*6 + 1, v_forcedFlush_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2605_, sizeof(void*)*6 + 2, v_pullBodyStalled_2581_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
v___y_2537_ = v___x_2604_;
goto v___jp_2536_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2569_);
lean_dec_ref(v___f_2533_);
v___y_2537_ = v_machine_2530_;
goto v___jp_2536_;
}
}
}
}
}
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_body_2529_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___y_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2619_, lean_object* v_machine_2620_, lean_object* v_isClosed_2621_, lean_object* v___f_2622_, lean_object* v___f_2623_, lean_object* v_x_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2619_, v_machine_2620_, v_isClosed_2621_, v___f_2622_, v___f_2623_, v_x_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2628_, lean_object* v_machine_2629_, lean_object* v_body_2630_){
_start:
{
lean_object* v_close_2632_; lean_object* v_isClosed_2633_; lean_object* v_tryRecv_2634_; lean_object* v___x_2635_; lean_object* v___f_2636_; lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; 
v_close_2632_ = lean_ctor_get(v_inst_2628_, 1);
lean_inc_ref(v_close_2632_);
v_isClosed_2633_ = lean_ctor_get(v_inst_2628_, 2);
lean_inc_ref(v_isClosed_2633_);
v_tryRecv_2634_ = lean_ctor_get(v_inst_2628_, 4);
lean_inc_ref(v_tryRecv_2634_);
lean_dec_ref(v_inst_2628_);
lean_inc_n(v_body_2630_, 2);
v___x_2635_ = lean_apply_2(v_tryRecv_2634_, v_body_2630_, lean_box(0));
lean_inc_ref(v_machine_2629_);
v___f_2636_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2636_, 0, v_machine_2629_);
lean_inc_ref(v___f_2636_);
v___f_2637_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2637_, 0, v___f_2636_);
v___f_2638_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2638_, 0, v_close_2632_);
lean_closure_set(v___f_2638_, 1, v_body_2630_);
lean_closure_set(v___f_2638_, 2, v___f_2637_);
lean_closure_set(v___f_2638_, 3, v___f_2636_);
v___f_2639_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2640_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2640_, 0, v_body_2630_);
lean_closure_set(v___f_2640_, 1, v_machine_2629_);
lean_closure_set(v___f_2640_, 2, v_isClosed_2633_);
lean_closure_set(v___f_2640_, 3, v___f_2638_);
lean_closure_set(v___f_2640_, 4, v___f_2639_);
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = 0;
v___x_2643_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2641_, v___x_2642_, v___x_2635_, v___f_2640_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2644_, lean_object* v_machine_2645_, lean_object* v_body_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2644_, v_machine_2645_, v_body_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2649_, lean_object* v_inst_2650_, lean_object* v_machine_2651_, lean_object* v_body_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2650_, v_machine_2651_, v_body_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2655_, lean_object* v_inst_2656_, lean_object* v_machine_2657_, lean_object* v_body_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2655_, v_inst_2656_, v_machine_2657_, v_body_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2667_, lean_object* v_____r_2668_, lean_object* v_st_2669_){
_start:
{
lean_object* v_machine_2671_; lean_object* v_requestStream_2672_; lean_object* v_keepAliveTimeout_2673_; lean_object* v_currentTimeout_2674_; lean_object* v_headerTimeout_2675_; lean_object* v_response_2676_; lean_object* v_respStream_2677_; uint8_t v_requiresData_2678_; lean_object* v_expectData_2679_; uint8_t v_handlerDispatched_2680_; lean_object* v_pendingHead_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2763_; 
v_machine_2671_ = lean_ctor_get(v_st_2669_, 0);
v_requestStream_2672_ = lean_ctor_get(v_st_2669_, 1);
v_keepAliveTimeout_2673_ = lean_ctor_get(v_st_2669_, 2);
v_currentTimeout_2674_ = lean_ctor_get(v_st_2669_, 3);
v_headerTimeout_2675_ = lean_ctor_get(v_st_2669_, 4);
v_response_2676_ = lean_ctor_get(v_st_2669_, 5);
v_respStream_2677_ = lean_ctor_get(v_st_2669_, 6);
v_requiresData_2678_ = lean_ctor_get_uint8(v_st_2669_, sizeof(void*)*9);
v_expectData_2679_ = lean_ctor_get(v_st_2669_, 7);
v_handlerDispatched_2680_ = lean_ctor_get_uint8(v_st_2669_, sizeof(void*)*9 + 1);
v_pendingHead_2681_ = lean_ctor_get(v_st_2669_, 8);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_st_2669_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2683_ = v_st_2669_;
v_isShared_2684_ = v_isSharedCheck_2763_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_pendingHead_2681_);
lean_inc(v_expectData_2679_);
lean_inc(v_respStream_2677_);
lean_inc(v_response_2676_);
lean_inc(v_headerTimeout_2675_);
lean_inc(v_currentTimeout_2674_);
lean_inc(v_keepAliveTimeout_2673_);
lean_inc(v_requestStream_2672_);
lean_inc(v_machine_2671_);
lean_dec(v_st_2669_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2763_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___y_2686_; lean_object* v_reader_2695_; lean_object* v_state_2696_; 
v_reader_2695_ = lean_ctor_get(v_machine_2671_, 0);
lean_inc_ref(v_reader_2695_);
v_state_2696_ = lean_ctor_get(v_reader_2695_, 0);
lean_inc(v_state_2696_);
if (lean_obj_tag(v_state_2696_) == 6)
{
lean_dec_ref(v_reader_2695_);
lean_dec_ref(v_val_2667_);
v___y_2686_ = v_machine_2671_;
goto v___jp_2685_;
}
else
{
if (lean_obj_tag(v_state_2696_) == 7)
{
lean_dec_ref(v_state_2696_);
lean_dec_ref(v_reader_2695_);
lean_dec_ref(v_val_2667_);
v___y_2686_ = v_machine_2671_;
goto v___jp_2685_;
}
else
{
lean_object* v_input_2697_; lean_object* v_writer_2698_; lean_object* v_config_2699_; lean_object* v_events_2700_; lean_object* v_error_2701_; lean_object* v_instant_2702_; uint8_t v_keepAlive_2703_; uint8_t v_forcedFlush_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2761_; 
v_input_2697_ = lean_ctor_get(v_reader_2695_, 1);
lean_inc_ref(v_input_2697_);
v_writer_2698_ = lean_ctor_get(v_machine_2671_, 1);
v_config_2699_ = lean_ctor_get(v_machine_2671_, 2);
v_events_2700_ = lean_ctor_get(v_machine_2671_, 3);
v_error_2701_ = lean_ctor_get(v_machine_2671_, 4);
v_instant_2702_ = lean_ctor_get(v_machine_2671_, 5);
v_keepAlive_2703_ = lean_ctor_get_uint8(v_machine_2671_, sizeof(void*)*6);
v_forcedFlush_2704_ = lean_ctor_get_uint8(v_machine_2671_, sizeof(void*)*6 + 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_machine_2671_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; 
v_unused_2762_ = lean_ctor_get(v_machine_2671_, 0);
lean_dec(v_unused_2762_);
v___x_2706_ = v_machine_2671_;
v_isShared_2707_ = v_isSharedCheck_2761_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_instant_2702_);
lean_inc(v_error_2701_);
lean_inc(v_events_2700_);
lean_inc(v_config_2699_);
lean_inc(v_writer_2698_);
lean_dec(v_machine_2671_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2761_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_messageHead_2708_; lean_object* v_messageCount_2709_; lean_object* v_bodyBytesRead_2710_; lean_object* v_headerBytesRead_2711_; uint8_t v_noMoreInput_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2758_; 
v_messageHead_2708_ = lean_ctor_get(v_reader_2695_, 2);
v_messageCount_2709_ = lean_ctor_get(v_reader_2695_, 3);
v_bodyBytesRead_2710_ = lean_ctor_get(v_reader_2695_, 4);
v_headerBytesRead_2711_ = lean_ctor_get(v_reader_2695_, 5);
v_noMoreInput_2712_ = lean_ctor_get_uint8(v_reader_2695_, sizeof(void*)*6);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_reader_2695_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; lean_object* v_unused_2760_; 
v_unused_2759_ = lean_ctor_get(v_reader_2695_, 1);
lean_dec(v_unused_2759_);
v_unused_2760_ = lean_ctor_get(v_reader_2695_, 0);
lean_dec(v_unused_2760_);
v___x_2714_ = v_reader_2695_;
v_isShared_2715_ = v_isSharedCheck_2758_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_headerBytesRead_2711_);
lean_inc(v_bodyBytesRead_2710_);
lean_inc(v_messageCount_2709_);
lean_inc(v_messageHead_2708_);
lean_dec(v_reader_2695_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2758_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_array_2716_; lean_object* v_idx_2717_; uint8_t v___x_2718_; lean_object* v___y_2720_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_array_2716_ = lean_ctor_get(v_input_2697_, 0);
lean_inc_ref(v_array_2716_);
v_idx_2717_ = lean_ctor_get(v_input_2697_, 1);
lean_inc(v_idx_2717_);
lean_dec_ref(v_input_2697_);
v___x_2718_ = 0;
v___x_2749_ = lean_byte_array_size(v_array_2716_);
v___x_2750_ = lean_nat_dec_le(v___x_2749_, v_idx_2717_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2751_ = l_ByteArray_extract(v_array_2716_, v_idx_2717_, v___x_2749_);
lean_dec_ref(v_array_2716_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_byte_array_size(v___x_2751_);
v___x_2754_ = lean_byte_array_size(v_val_2667_);
v___x_2755_ = lean_byte_array_copy_slice(v_val_2667_, v___x_2752_, v___x_2751_, v___x_2753_, v___x_2754_, v___x_2750_);
lean_dec_ref(v_val_2667_);
v___x_2756_ = l_ByteArray_mkIterator(v___x_2755_);
v___y_2720_ = v___x_2756_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2757_; 
lean_dec(v_idx_2717_);
lean_dec_ref(v_array_2716_);
v___x_2757_ = l_ByteArray_mkIterator(v_val_2667_);
v___y_2720_ = v___x_2757_;
goto v___jp_2719_;
}
v___jp_2719_:
{
lean_object* v_maxHeaderBytes_2721_; lean_object* v_maxStartLineLength_2722_; lean_object* v_maxChunkLineLength_2723_; lean_object* v_maxBodySize_2724_; lean_object* v_array_2725_; lean_object* v_idx_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_maxHeaderBytes_2721_ = lean_ctor_get(v_config_2699_, 2);
v_maxStartLineLength_2722_ = lean_ctor_get(v_config_2699_, 5);
v_maxChunkLineLength_2723_ = lean_ctor_get(v_config_2699_, 13);
v_maxBodySize_2724_ = lean_ctor_get(v_config_2699_, 15);
v_array_2725_ = lean_ctor_get(v___y_2720_, 0);
v_idx_2726_ = lean_ctor_get(v___y_2720_, 1);
v___x_2727_ = lean_nat_add(v_maxBodySize_2724_, v_maxHeaderBytes_2721_);
v___x_2728_ = lean_nat_add(v___x_2727_, v_maxStartLineLength_2722_);
lean_dec(v___x_2727_);
v___x_2729_ = lean_nat_add(v___x_2728_, v_maxChunkLineLength_2723_);
lean_dec(v___x_2728_);
v___x_2730_ = lean_byte_array_size(v_array_2725_);
v___x_2731_ = lean_nat_sub(v___x_2730_, v_idx_2726_);
v___x_2732_ = lean_nat_dec_lt(v___x_2729_, v___x_2731_);
lean_dec(v___x_2731_);
lean_dec(v___x_2729_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2734_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v___y_2720_);
v___x_2734_ = v___x_2714_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_state_2696_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v___y_2720_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_messageHead_2708_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_messageCount_2709_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v_bodyBytesRead_2710_);
lean_ctor_set(v_reuseFailAlloc_2738_, 5, v_headerBytesRead_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, sizeof(void*)*6, v_noMoreInput_2712_);
v___x_2734_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v_machine_2736_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2734_);
v_machine_2736_ = v___x_2706_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_writer_2698_);
lean_ctor_set(v_reuseFailAlloc_2737_, 2, v_config_2699_);
lean_ctor_set(v_reuseFailAlloc_2737_, 3, v_events_2700_);
lean_ctor_set(v_reuseFailAlloc_2737_, 4, v_error_2701_);
lean_ctor_set(v_reuseFailAlloc_2737_, 5, v_instant_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, sizeof(void*)*6, v_keepAlive_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, sizeof(void*)*6 + 1, v_forcedFlush_2704_);
v_machine_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_ctor_set_uint8(v_machine_2736_, sizeof(void*)*6 + 2, v___x_2718_);
v___y_2686_ = v_machine_2736_;
goto v___jp_2685_;
}
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec(v_error_2701_);
lean_dec(v_state_2696_);
v___x_2739_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2740_ = lean_array_push(v_events_2700_, v___x_2739_);
v___x_2741_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v___y_2720_);
lean_ctor_set(v___x_2714_, 0, v___x_2741_);
v___x_2743_ = v___x_2714_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v___y_2720_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_messageHead_2708_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_messageCount_2709_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_bodyBytesRead_2710_);
lean_ctor_set(v_reuseFailAlloc_2748_, 5, v_headerBytesRead_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*6, v_noMoreInput_2712_);
v___x_2743_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2744_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 4, v___x_2744_);
lean_ctor_set(v___x_2706_, 3, v___x_2740_);
lean_ctor_set(v___x_2706_, 0, v___x_2743_);
v___x_2746_ = v___x_2706_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_writer_2698_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_config_2699_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 5, v_instant_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6, v_keepAlive_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6 + 1, v_forcedFlush_2704_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*6 + 2, v___x_2718_);
v___y_2686_ = v___x_2746_;
goto v___jp_2685_;
}
}
}
}
}
}
}
}
v___jp_2685_:
{
lean_object* v___x_2688_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___y_2686_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___y_2686_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_requestStream_2672_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_keepAliveTimeout_2673_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_currentTimeout_2674_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v_headerTimeout_2675_);
lean_ctor_set(v_reuseFailAlloc_2694_, 5, v_response_2676_);
lean_ctor_set(v_reuseFailAlloc_2694_, 6, v_respStream_2677_);
lean_ctor_set(v_reuseFailAlloc_2694_, 7, v_expectData_2679_);
lean_ctor_set(v_reuseFailAlloc_2694_, 8, v_pendingHead_2681_);
lean_ctor_set_uint8(v_reuseFailAlloc_2694_, sizeof(void*)*9, v_requiresData_2678_);
lean_ctor_set_uint8(v_reuseFailAlloc_2694_, sizeof(void*)*9 + 1, v_handlerDispatched_2680_);
v___x_2688_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
uint8_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2689_ = 0;
v___x_2690_ = lean_box(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2688_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2764_, lean_object* v_____r_2765_, lean_object* v_st_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2764_, v_____r_2765_, v_st_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2769_, lean_object* v_machine_2770_, lean_object* v_requestStream_2771_, lean_object* v_currentTimeout_2772_, lean_object* v_response_2773_, lean_object* v_respStream_2774_, uint8_t v_requiresData_2775_, lean_object* v_expectData_2776_, uint8_t v_handlerDispatched_2777_, lean_object* v_pendingHead_2778_, lean_object* v___f_2779_, lean_object* v_x_2780_){
_start:
{
if (lean_obj_tag(v_x_2780_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref(v___f_2779_);
lean_dec(v_pendingHead_2778_);
lean_dec(v_expectData_2776_);
lean_dec(v_respStream_2774_);
lean_dec_ref(v_response_2773_);
lean_dec(v_currentTimeout_2772_);
lean_dec_ref(v_requestStream_2771_);
lean_dec_ref(v_machine_2770_);
v_a_2782_ = lean_ctor_get(v_x_2780_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2780_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2784_ = v_x_2780_;
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v_x_2780_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
return v___x_2788_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v_headerTimeout_2792_; lean_object* v_second_2793_; lean_object* v_nano_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v_second_2798_; lean_object* v_nano_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2791_ = lean_ctor_get(v_x_2780_, 0);
lean_inc(v_a_2791_);
lean_dec_ref(v_x_2780_);
v_headerTimeout_2792_ = lean_ctor_get(v_config_2769_, 6);
v_second_2793_ = lean_ctor_get(v_a_2791_, 0);
lean_inc(v_second_2793_);
v_nano_2794_ = lean_ctor_get(v_a_2791_, 1);
lean_inc(v_nano_2794_);
lean_dec(v_a_2791_);
v___x_2795_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2796_ = lean_int_mul(v_headerTimeout_2792_, v___x_2795_);
v___x_2797_ = l_Std_Time_Duration_ofNanoseconds(v___x_2796_);
lean_dec(v___x_2796_);
v_second_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_second_2798_);
v_nano_2799_ = lean_ctor_get(v___x_2797_, 1);
lean_inc(v_nano_2799_);
lean_dec_ref(v___x_2797_);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2802_ = lean_int_mul(v_second_2793_, v___x_2801_);
lean_dec(v_second_2793_);
v___x_2803_ = lean_int_add(v___x_2802_, v_nano_2794_);
lean_dec(v_nano_2794_);
lean_dec(v___x_2802_);
v___x_2804_ = lean_int_mul(v_second_2798_, v___x_2801_);
lean_dec(v_second_2798_);
v___x_2805_ = lean_int_add(v___x_2804_, v_nano_2799_);
lean_dec(v_nano_2799_);
lean_dec(v___x_2804_);
v___x_2806_ = lean_int_add(v___x_2803_, v___x_2805_);
lean_dec(v___x_2805_);
lean_dec(v___x_2803_);
v___x_2807_ = l_Std_Time_Duration_ofNanoseconds(v___x_2806_);
lean_dec(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2809_, 0, v_machine_2770_);
lean_ctor_set(v___x_2809_, 1, v_requestStream_2771_);
lean_ctor_set(v___x_2809_, 2, v___x_2800_);
lean_ctor_set(v___x_2809_, 3, v_currentTimeout_2772_);
lean_ctor_set(v___x_2809_, 4, v___x_2808_);
lean_ctor_set(v___x_2809_, 5, v_response_2773_);
lean_ctor_set(v___x_2809_, 6, v_respStream_2774_);
lean_ctor_set(v___x_2809_, 7, v_expectData_2776_);
lean_ctor_set(v___x_2809_, 8, v_pendingHead_2778_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*9, v_requiresData_2775_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*9 + 1, v_handlerDispatched_2777_);
v___x_2810_ = lean_box(0);
v___x_2811_ = lean_apply_3(v___f_2779_, v___x_2810_, v___x_2809_, lean_box(0));
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2812_, lean_object* v_machine_2813_, lean_object* v_requestStream_2814_, lean_object* v_currentTimeout_2815_, lean_object* v_response_2816_, lean_object* v_respStream_2817_, lean_object* v_requiresData_2818_, lean_object* v_expectData_2819_, lean_object* v_handlerDispatched_2820_, lean_object* v_pendingHead_2821_, lean_object* v___f_2822_, lean_object* v_x_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v_requiresData_boxed_2825_; uint8_t v_handlerDispatched_boxed_2826_; lean_object* v_res_2827_; 
v_requiresData_boxed_2825_ = lean_unbox(v_requiresData_2818_);
v_handlerDispatched_boxed_2826_ = lean_unbox(v_handlerDispatched_2820_);
v_res_2827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2812_, v_machine_2813_, v_requestStream_2814_, v_currentTimeout_2815_, v_response_2816_, v_respStream_2817_, v_requiresData_boxed_2825_, v_expectData_2819_, v_handlerDispatched_boxed_2826_, v_pendingHead_2821_, v___f_2822_, v_x_2823_);
lean_dec_ref(v_config_2812_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2828_, lean_object* v_requestStream_2829_, lean_object* v_keepAliveTimeout_2830_, lean_object* v_currentTimeout_2831_, lean_object* v_headerTimeout_2832_, lean_object* v_response_2833_, uint8_t v_requiresData_2834_, lean_object* v_expectData_2835_, uint8_t v_handlerDispatched_2836_, lean_object* v_pendingHead_2837_, lean_object* v_____r_2838_){
_start:
{
lean_object* v_writer_2840_; lean_object* v_reader_2841_; lean_object* v_config_2842_; lean_object* v_events_2843_; lean_object* v_error_2844_; lean_object* v_instant_2845_; uint8_t v_keepAlive_2846_; uint8_t v_forcedFlush_2847_; uint8_t v_pullBodyStalled_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2878_; 
v_writer_2840_ = lean_ctor_get(v_machine_2828_, 1);
v_reader_2841_ = lean_ctor_get(v_machine_2828_, 0);
v_config_2842_ = lean_ctor_get(v_machine_2828_, 2);
v_events_2843_ = lean_ctor_get(v_machine_2828_, 3);
v_error_2844_ = lean_ctor_get(v_machine_2828_, 4);
v_instant_2845_ = lean_ctor_get(v_machine_2828_, 5);
v_keepAlive_2846_ = lean_ctor_get_uint8(v_machine_2828_, sizeof(void*)*6);
v_forcedFlush_2847_ = lean_ctor_get_uint8(v_machine_2828_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2848_ = lean_ctor_get_uint8(v_machine_2828_, sizeof(void*)*6 + 2);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_machine_2828_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2850_ = v_machine_2828_;
v_isShared_2851_ = v_isSharedCheck_2878_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_instant_2845_);
lean_inc(v_error_2844_);
lean_inc(v_events_2843_);
lean_inc(v_config_2842_);
lean_inc(v_writer_2840_);
lean_inc(v_reader_2841_);
lean_dec(v_machine_2828_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2878_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_userData_2852_; lean_object* v_outputData_2853_; lean_object* v_state_2854_; lean_object* v_knownSize_2855_; lean_object* v_messageHead_2856_; uint8_t v_sentMessage_2857_; uint8_t v_omitBody_2858_; lean_object* v_userDataBytes_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2877_; 
v_userData_2852_ = lean_ctor_get(v_writer_2840_, 0);
v_outputData_2853_ = lean_ctor_get(v_writer_2840_, 1);
v_state_2854_ = lean_ctor_get(v_writer_2840_, 2);
v_knownSize_2855_ = lean_ctor_get(v_writer_2840_, 3);
v_messageHead_2856_ = lean_ctor_get(v_writer_2840_, 4);
v_sentMessage_2857_ = lean_ctor_get_uint8(v_writer_2840_, sizeof(void*)*6);
v_omitBody_2858_ = lean_ctor_get_uint8(v_writer_2840_, sizeof(void*)*6 + 2);
v_userDataBytes_2859_ = lean_ctor_get(v_writer_2840_, 5);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_writer_2840_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2861_ = v_writer_2840_;
v_isShared_2862_ = v_isSharedCheck_2877_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_userDataBytes_2859_);
lean_inc(v_messageHead_2856_);
lean_inc(v_knownSize_2855_);
lean_inc(v_state_2854_);
lean_inc(v_outputData_2853_);
lean_inc(v_userData_2852_);
lean_dec(v_writer_2840_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2877_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
uint8_t v___x_2863_; lean_object* v___x_2865_; 
v___x_2863_ = 1;
if (v_isShared_2862_ == 0)
{
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_userData_2852_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_outputData_2853_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_state_2854_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_knownSize_2855_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_messageHead_2856_);
lean_ctor_set(v_reuseFailAlloc_2876_, 5, v_userDataBytes_2859_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*6, v_sentMessage_2857_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*6 + 2, v_omitBody_2858_);
v___x_2865_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2867_; 
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*6 + 1, v___x_2863_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 1, v___x_2865_);
v___x_2867_ = v___x_2850_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_reader_2841_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_config_2842_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v_events_2843_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v_error_2844_);
lean_ctor_set(v_reuseFailAlloc_2875_, 5, v_instant_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2875_, sizeof(void*)*6, v_keepAlive_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2875_, sizeof(void*)*6 + 1, v_forcedFlush_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2875_, sizeof(void*)*6 + 2, v_pullBodyStalled_2848_);
v___x_2867_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v_requestStream_2829_);
lean_ctor_set(v___x_2869_, 2, v_keepAliveTimeout_2830_);
lean_ctor_set(v___x_2869_, 3, v_currentTimeout_2831_);
lean_ctor_set(v___x_2869_, 4, v_headerTimeout_2832_);
lean_ctor_set(v___x_2869_, 5, v_response_2833_);
lean_ctor_set(v___x_2869_, 6, v___x_2868_);
lean_ctor_set(v___x_2869_, 7, v_expectData_2835_);
lean_ctor_set(v___x_2869_, 8, v_pendingHead_2837_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*9, v_requiresData_2834_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*9 + 1, v_handlerDispatched_2836_);
v___x_2870_ = 0;
v___x_2871_ = lean_box(v___x_2870_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2879_, lean_object* v_requestStream_2880_, lean_object* v_keepAliveTimeout_2881_, lean_object* v_currentTimeout_2882_, lean_object* v_headerTimeout_2883_, lean_object* v_response_2884_, lean_object* v_requiresData_2885_, lean_object* v_expectData_2886_, lean_object* v_handlerDispatched_2887_, lean_object* v_pendingHead_2888_, lean_object* v_____r_2889_, lean_object* v___y_2890_){
_start:
{
uint8_t v_requiresData_boxed_2891_; uint8_t v_handlerDispatched_boxed_2892_; lean_object* v_res_2893_; 
v_requiresData_boxed_2891_ = lean_unbox(v_requiresData_2885_);
v_handlerDispatched_boxed_2892_ = lean_unbox(v_handlerDispatched_2887_);
v_res_2893_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2879_, v_requestStream_2880_, v_keepAliveTimeout_2881_, v_currentTimeout_2882_, v_headerTimeout_2883_, v_response_2884_, v_requiresData_boxed_2891_, v_expectData_2886_, v_handlerDispatched_boxed_2892_, v_pendingHead_2888_, v_____r_2889_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2894_, lean_object* v_x_2895_){
_start:
{
if (lean_obj_tag(v_x_2895_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v___f_2894_);
v_a_2897_ = lean_ctor_get(v_x_2895_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_x_2895_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2899_ = v_x_2895_;
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v_x_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v_x_2895_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v_x_2895_);
v___x_2907_ = lean_apply_2(v___f_2894_, v_a_2906_, lean_box(0));
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2908_, lean_object* v_x_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2908_, v_x_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2912_, lean_object* v_val_2913_, lean_object* v___f_2914_, lean_object* v___f_2915_, lean_object* v_x_2916_){
_start:
{
if (lean_obj_tag(v_x_2916_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v___f_2915_);
lean_dec_ref(v___f_2914_);
lean_dec(v_val_2913_);
lean_dec_ref(v_close_2912_);
v_a_2918_ = lean_ctor_get(v_x_2916_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_x_2916_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2920_ = v_x_2916_;
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v_x_2916_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
}
else
{
lean_object* v_a_2927_; uint8_t v___x_2928_; 
v_a_2927_ = lean_ctor_get(v_x_2916_, 0);
lean_inc(v_a_2927_);
lean_dec_ref(v_x_2916_);
v___x_2928_ = lean_unbox(v_a_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; 
lean_dec_ref(v___f_2915_);
v___x_2929_ = lean_apply_2(v_close_2912_, v_val_2913_, lean_box(0));
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_unbox(v_a_2927_);
lean_dec(v_a_2927_);
v___x_2932_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2930_, v___x_2931_, v___x_2929_, v___f_2914_);
return v___x_2932_;
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_a_2927_);
lean_dec_ref(v___f_2914_);
lean_dec(v_val_2913_);
lean_dec_ref(v_close_2912_);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_apply_2(v___f_2915_, v___x_2933_, lean_box(0));
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2935_, lean_object* v_val_2936_, lean_object* v___f_2937_, lean_object* v___f_2938_, lean_object* v_x_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2935_, v_val_2936_, v___f_2937_, v___f_2938_, v_x_2939_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2942_, lean_object* v_handler_2943_, lean_object* v_x_2944_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
lean_object* v_a_2946_; lean_object* v_onFailure_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v_x_2944_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v_x_2944_);
v_onFailure_2947_ = lean_ctor_get(v_inst_2942_, 2);
lean_inc_ref(v_onFailure_2947_);
lean_dec_ref(v_inst_2942_);
v___x_2948_ = lean_apply_3(v_onFailure_2947_, v_handler_2943_, v_a_2946_, lean_box(0));
return v___x_2948_;
}
else
{
lean_object* v___x_2949_; 
lean_dec(v_handler_2943_);
lean_dec_ref(v_inst_2942_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_x_2944_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2950_, lean_object* v_handler_2951_, lean_object* v_x_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2950_, v_handler_2951_, v_x_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2955_, lean_object* v_____r_2956_){
_start:
{
uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2958_ = 0;
v___x_2959_ = lean_box(v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_st_2955_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2963_, lean_object* v_____r_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2963_, v_____r_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2967_, lean_object* v___f_2968_, lean_object* v___f_2969_, lean_object* v_x_2970_){
_start:
{
if (lean_obj_tag(v_x_2970_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v___f_2969_);
lean_dec_ref(v___f_2968_);
lean_dec_ref(v_requestStream_2967_);
v_a_2972_ = lean_ctor_get(v_x_2970_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_x_2970_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v_x_2970_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v_x_2970_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
}
else
{
lean_object* v_a_2981_; uint8_t v___x_2982_; 
v_a_2981_ = lean_ctor_get(v_x_2970_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v_x_2970_);
v___x_2982_ = lean_unbox(v_a_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; lean_object* v___x_2986_; 
lean_dec_ref(v___f_2969_);
v___x_2983_ = l_Std_Http_Body_Stream_close(v_requestStream_2967_);
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_unbox(v_a_2981_);
lean_dec(v_a_2981_);
v___x_2986_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2984_, v___x_2985_, v___x_2983_, v___f_2968_);
return v___x_2986_;
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_dec(v_a_2981_);
lean_dec_ref(v___f_2968_);
lean_dec_ref(v_requestStream_2967_);
v___x_2987_ = lean_box(0);
v___x_2988_ = lean_apply_2(v___f_2969_, v___x_2987_, lean_box(0));
return v___x_2988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2989_, lean_object* v___f_2990_, lean_object* v___f_2991_, lean_object* v_x_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2989_, v___f_2990_, v___f_2991_, v_x_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2995_, lean_object* v___f_2996_, lean_object* v___f_2997_, lean_object* v_requestStream_2998_, lean_object* v___f_2999_, lean_object* v_x_3000_){
_start:
{
if (lean_obj_tag(v_x_3000_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v___f_2999_);
lean_dec_ref(v_requestStream_2998_);
lean_dec_ref(v___f_2997_);
lean_dec_ref(v___f_2996_);
v_a_3002_ = lean_ctor_get(v_x_3000_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_x_3000_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3004_ = v_x_3000_;
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v_x_3000_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
}
else
{
lean_dec_ref(v_x_3000_);
if (v_final_2995_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___f_2999_);
lean_dec_ref(v_requestStream_2998_);
lean_dec_ref(v___f_2997_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_apply_2(v___f_2996_, v___x_3011_, lean_box(0));
return v___x_3012_;
}
else
{
lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_7012__overap_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref(v___f_2996_);
v___x_3013_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3014_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3015_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3016_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3017_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3017_, 0, lean_box(0));
lean_closure_set(v___x_3017_, 1, lean_box(0));
lean_closure_set(v___x_3017_, 2, lean_box(0));
lean_closure_set(v___x_3017_, 3, v___x_3013_);
lean_closure_set(v___x_3017_, 4, lean_box(0));
lean_closure_set(v___x_3017_, 5, lean_box(0));
lean_closure_set(v___x_3017_, 6, v___x_3016_);
lean_closure_set(v___x_3017_, 7, v___f_2997_);
v___x_7012__overap_3018_ = l_Std_Mutex_atomically___redArg(v___x_3013_, v___f_3014_, v___f_3015_, v_requestStream_2998_, v___x_3017_);
v___x_3019_ = lean_apply_1(v___x_7012__overap_3018_, lean_box(0));
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = 0;
v___x_3022_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3020_, v___x_3021_, v___x_3019_, v___f_2999_);
return v___x_3022_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3023_, lean_object* v___f_3024_, lean_object* v___f_3025_, lean_object* v_requestStream_3026_, lean_object* v___f_3027_, lean_object* v_x_3028_, lean_object* v___y_3029_){
_start:
{
uint8_t v_final_boxed_3030_; lean_object* v_res_3031_; 
v_final_boxed_3030_ = lean_unbox(v_final_3023_);
v_res_3031_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3030_, v___f_3024_, v___f_3025_, v_requestStream_3026_, v___f_3027_, v_x_3028_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3032_, lean_object* v_x_3033_){
_start:
{
if (lean_obj_tag(v_x_3033_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v_state_3032_);
v_a_3035_ = lean_ctor_get(v_x_3033_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_x_3033_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3037_ = v_x_3033_;
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v_x_3033_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
}
}
else
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3073_; 
v_isSharedCheck_3073_ = !lean_is_exclusive(v_x_3033_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v_x_3033_, 0);
lean_dec(v_unused_3074_);
v___x_3045_ = v_x_3033_;
v_isShared_3046_ = v_isSharedCheck_3073_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v_x_3033_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3073_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_machine_3047_; lean_object* v_requestStream_3048_; lean_object* v_keepAliveTimeout_3049_; lean_object* v_currentTimeout_3050_; lean_object* v_headerTimeout_3051_; lean_object* v_response_3052_; lean_object* v_respStream_3053_; uint8_t v_requiresData_3054_; lean_object* v_expectData_3055_; lean_object* v_pendingHead_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3072_; 
v_machine_3047_ = lean_ctor_get(v_state_3032_, 0);
v_requestStream_3048_ = lean_ctor_get(v_state_3032_, 1);
v_keepAliveTimeout_3049_ = lean_ctor_get(v_state_3032_, 2);
v_currentTimeout_3050_ = lean_ctor_get(v_state_3032_, 3);
v_headerTimeout_3051_ = lean_ctor_get(v_state_3032_, 4);
v_response_3052_ = lean_ctor_get(v_state_3032_, 5);
v_respStream_3053_ = lean_ctor_get(v_state_3032_, 6);
v_requiresData_3054_ = lean_ctor_get_uint8(v_state_3032_, sizeof(void*)*9);
v_expectData_3055_ = lean_ctor_get(v_state_3032_, 7);
v_pendingHead_3056_ = lean_ctor_get(v_state_3032_, 8);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_state_3032_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3058_ = v_state_3032_;
v_isShared_3059_ = v_isSharedCheck_3072_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_pendingHead_3056_);
lean_inc(v_expectData_3055_);
lean_inc(v_respStream_3053_);
lean_inc(v_response_3052_);
lean_inc(v_headerTimeout_3051_);
lean_inc(v_currentTimeout_3050_);
lean_inc(v_keepAliveTimeout_3049_);
lean_inc(v_requestStream_3048_);
lean_inc(v_machine_3047_);
lean_dec(v_state_3032_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3072_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3064_; 
v___x_3060_ = lean_box(52);
v___x_3061_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3047_, v___x_3060_);
v___x_3062_ = 0;
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3061_);
v___x_3064_ = v___x_3058_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_requestStream_3048_);
lean_ctor_set(v_reuseFailAlloc_3071_, 2, v_keepAliveTimeout_3049_);
lean_ctor_set(v_reuseFailAlloc_3071_, 3, v_currentTimeout_3050_);
lean_ctor_set(v_reuseFailAlloc_3071_, 4, v_headerTimeout_3051_);
lean_ctor_set(v_reuseFailAlloc_3071_, 5, v_response_3052_);
lean_ctor_set(v_reuseFailAlloc_3071_, 6, v_respStream_3053_);
lean_ctor_set(v_reuseFailAlloc_3071_, 7, v_expectData_3055_);
lean_ctor_set(v_reuseFailAlloc_3071_, 8, v_pendingHead_3056_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*9, v_requiresData_3054_);
v___x_3064_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_ctor_set_uint8(v___x_3064_, sizeof(void*)*9 + 1, v___x_3062_);
v___x_3065_ = lean_box(v___x_3062_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3066_);
v___x_3068_ = v___x_3045_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3075_, lean_object* v_x_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3075_, v_x_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3079_, lean_object* v_requestStream_3080_, lean_object* v_keepAliveTimeout_3081_, lean_object* v_currentTimeout_3082_, lean_object* v_headerTimeout_3083_, lean_object* v_response_3084_, lean_object* v_respStream_3085_, uint8_t v_requiresData_3086_, lean_object* v_expectData_3087_, lean_object* v_pendingHead_3088_, lean_object* v_____r_3089_){
_start:
{
uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3091_ = 0;
v___x_3092_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3092_, 0, v_machine_3079_);
lean_ctor_set(v___x_3092_, 1, v_requestStream_3080_);
lean_ctor_set(v___x_3092_, 2, v_keepAliveTimeout_3081_);
lean_ctor_set(v___x_3092_, 3, v_currentTimeout_3082_);
lean_ctor_set(v___x_3092_, 4, v_headerTimeout_3083_);
lean_ctor_set(v___x_3092_, 5, v_response_3084_);
lean_ctor_set(v___x_3092_, 6, v_respStream_3085_);
lean_ctor_set(v___x_3092_, 7, v_expectData_3087_);
lean_ctor_set(v___x_3092_, 8, v_pendingHead_3088_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*9, v_requiresData_3086_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*9 + 1, v___x_3091_);
v___x_3093_ = lean_box(v___x_3091_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3097_, lean_object* v_requestStream_3098_, lean_object* v_keepAliveTimeout_3099_, lean_object* v_currentTimeout_3100_, lean_object* v_headerTimeout_3101_, lean_object* v_response_3102_, lean_object* v_respStream_3103_, lean_object* v_requiresData_3104_, lean_object* v_expectData_3105_, lean_object* v_pendingHead_3106_, lean_object* v_____r_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v_requiresData_boxed_3109_; lean_object* v_res_3110_; 
v_requiresData_boxed_3109_ = lean_unbox(v_requiresData_3104_);
v_res_3110_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3097_, v_requestStream_3098_, v_keepAliveTimeout_3099_, v_currentTimeout_3100_, v_headerTimeout_3101_, v_response_3102_, v_respStream_3103_, v_requiresData_boxed_3109_, v_expectData_3105_, v_pendingHead_3106_, v_____r_3107_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3111_, lean_object* v_body_3112_, lean_object* v___f_3113_, lean_object* v___f_3114_, lean_object* v_x_3115_){
_start:
{
if (lean_obj_tag(v_x_3115_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v___f_3114_);
lean_dec_ref(v___f_3113_);
lean_dec(v_body_3112_);
lean_dec_ref(v_close_3111_);
v_a_3117_ = lean_ctor_get(v_x_3115_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_x_3115_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3119_ = v_x_3115_;
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v_x_3115_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
return v___x_3123_;
}
}
}
else
{
lean_object* v_a_3126_; uint8_t v___x_3127_; 
v_a_3126_ = lean_ctor_get(v_x_3115_, 0);
lean_inc(v_a_3126_);
lean_dec_ref(v_x_3115_);
v___x_3127_ = lean_unbox(v_a_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; lean_object* v___x_3131_; 
lean_dec_ref(v___f_3114_);
v___x_3128_ = lean_apply_2(v_close_3111_, v_body_3112_, lean_box(0));
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_unbox(v_a_3126_);
lean_dec(v_a_3126_);
v___x_3131_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3129_, v___x_3130_, v___x_3128_, v___f_3113_);
return v___x_3131_;
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v_a_3126_);
lean_dec_ref(v___f_3113_);
lean_dec(v_body_3112_);
lean_dec_ref(v_close_3111_);
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_apply_2(v___f_3114_, v___x_3132_, lean_box(0));
return v___x_3133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3134_, lean_object* v_body_3135_, lean_object* v___f_3136_, lean_object* v___f_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3134_, v_body_3135_, v___f_3136_, v___f_3137_, v_x_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3141_, lean_object* v_keepAliveTimeout_3142_, lean_object* v_currentTimeout_3143_, lean_object* v_headerTimeout_3144_, lean_object* v_response_3145_, uint8_t v_requiresData_3146_, lean_object* v_expectData_3147_, uint8_t v___x_3148_, lean_object* v_pendingHead_3149_, lean_object* v_____x_3150_){
_start:
{
lean_object* v_fst_3152_; lean_object* v_snd_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3164_; 
v_fst_3152_ = lean_ctor_get(v_____x_3150_, 0);
v_snd_3153_ = lean_ctor_get(v_____x_3150_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_____x_3150_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3155_ = v_____x_3150_;
v_isShared_3156_ = v_isSharedCheck_3164_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_snd_3153_);
lean_inc(v_fst_3152_);
lean_dec(v_____x_3150_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3164_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3157_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3157_, 0, v_fst_3152_);
lean_ctor_set(v___x_3157_, 1, v_requestStream_3141_);
lean_ctor_set(v___x_3157_, 2, v_keepAliveTimeout_3142_);
lean_ctor_set(v___x_3157_, 3, v_currentTimeout_3143_);
lean_ctor_set(v___x_3157_, 4, v_headerTimeout_3144_);
lean_ctor_set(v___x_3157_, 5, v_response_3145_);
lean_ctor_set(v___x_3157_, 6, v_snd_3153_);
lean_ctor_set(v___x_3157_, 7, v_expectData_3147_);
lean_ctor_set(v___x_3157_, 8, v_pendingHead_3149_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*9, v_requiresData_3146_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*9 + 1, v___x_3148_);
v___x_3158_ = lean_box(v___x_3148_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v___x_3158_);
lean_ctor_set(v___x_3155_, 0, v___x_3157_);
v___x_3160_ = v___x_3155_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3158_);
v___x_3160_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3165_, lean_object* v_keepAliveTimeout_3166_, lean_object* v_currentTimeout_3167_, lean_object* v_headerTimeout_3168_, lean_object* v_response_3169_, lean_object* v_requiresData_3170_, lean_object* v_expectData_3171_, lean_object* v___x_3172_, lean_object* v_pendingHead_3173_, lean_object* v_____x_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v_requiresData_boxed_3176_; uint8_t v___x_7768__boxed_3177_; lean_object* v_res_3178_; 
v_requiresData_boxed_3176_ = lean_unbox(v_requiresData_3170_);
v___x_7768__boxed_3177_ = lean_unbox(v___x_3172_);
v_res_3178_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3165_, v_keepAliveTimeout_3166_, v_currentTimeout_3167_, v_headerTimeout_3168_, v_response_3169_, v_requiresData_boxed_3176_, v_expectData_3171_, v___x_7768__boxed_3177_, v_pendingHead_3173_, v_____x_3174_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3179_, lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v___f_3179_);
v_a_3182_ = lean_ctor_get(v_x_3180_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_x_3180_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3184_ = v_x_3180_;
v_isShared_3185_ = v_isSharedCheck_3190_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v_x_3180_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3190_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3182_);
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
else
{
lean_object* v_a_3191_; lean_object* v___x_3192_; 
v_a_3191_ = lean_ctor_get(v_x_3180_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v_x_3180_);
v___x_3192_ = lean_apply_2(v___f_3179_, v_a_3191_, lean_box(0));
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3193_, lean_object* v_x_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3193_, v_x_3194_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3197_, lean_object* v___f_3198_, lean_object* v_inst_3199_, lean_object* v___f_3200_, lean_object* v_x_3201_){
_start:
{
if (lean_obj_tag(v_x_3201_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___f_3200_);
lean_dec_ref(v_inst_3199_);
lean_dec_ref(v___f_3198_);
v_a_3203_ = lean_ctor_get(v_x_3201_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_x_3201_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3205_ = v_x_3201_;
v_isShared_3206_ = v_isSharedCheck_3211_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v_x_3201_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3211_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; 
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
return v___x_3209_;
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v_snd_3213_; 
v_a_3212_ = lean_ctor_get(v_x_3201_, 0);
v_snd_3213_ = lean_ctor_get(v_a_3212_, 1);
if (lean_obj_tag(v_snd_3213_) == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec_ref(v___f_3200_);
lean_dec_ref(v_inst_3199_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_x_3201_);
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3215_, v___x_3197_, v___x_3214_, v___f_3198_);
return v___x_3216_;
}
else
{
lean_object* v_fst_3217_; lean_object* v_val_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_inc_ref(v_snd_3213_);
lean_inc(v_a_3212_);
lean_dec_ref(v_x_3201_);
lean_dec_ref(v___f_3198_);
v_fst_3217_ = lean_ctor_get(v_a_3212_, 0);
lean_inc(v_fst_3217_);
lean_dec(v_a_3212_);
v_val_3218_ = lean_ctor_get(v_snd_3213_, 0);
lean_inc(v_val_3218_);
lean_dec_ref(v_snd_3213_);
v___x_3219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3199_, v_fst_3217_, v_val_3218_);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3220_, v___x_3197_, v___x_3219_, v___f_3200_);
return v___x_3221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3222_, lean_object* v___f_3223_, lean_object* v_inst_3224_, lean_object* v___f_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_){
_start:
{
uint8_t v___x_7834__boxed_3228_; lean_object* v_res_3229_; 
v___x_7834__boxed_3228_ = lean_unbox(v___x_3222_);
v_res_3229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7834__boxed_3228_, v___f_3223_, v_inst_3224_, v___f_3225_, v_x_3226_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_state_3230_, lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_state_3230_);
v_a_3233_ = lean_ctor_get(v_x_3231_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_x_3231_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3235_ = v_x_3231_;
v_isShared_3236_ = v_isSharedCheck_3241_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v_x_3231_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3241_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
}
else
{
lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3271_; 
v_isSharedCheck_3271_ = !lean_is_exclusive(v_x_3231_);
if (v_isSharedCheck_3271_ == 0)
{
lean_object* v_unused_3272_; 
v_unused_3272_ = lean_ctor_get(v_x_3231_, 0);
lean_dec(v_unused_3272_);
v___x_3243_ = v_x_3231_;
v_isShared_3244_ = v_isSharedCheck_3271_;
goto v_resetjp_3242_;
}
else
{
lean_dec(v_x_3231_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3271_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v_machine_3245_; lean_object* v_requestStream_3246_; lean_object* v_keepAliveTimeout_3247_; lean_object* v_currentTimeout_3248_; lean_object* v_headerTimeout_3249_; lean_object* v_response_3250_; lean_object* v_respStream_3251_; uint8_t v_requiresData_3252_; lean_object* v_expectData_3253_; lean_object* v_pendingHead_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3270_; 
v_machine_3245_ = lean_ctor_get(v_state_3230_, 0);
v_requestStream_3246_ = lean_ctor_get(v_state_3230_, 1);
v_keepAliveTimeout_3247_ = lean_ctor_get(v_state_3230_, 2);
v_currentTimeout_3248_ = lean_ctor_get(v_state_3230_, 3);
v_headerTimeout_3249_ = lean_ctor_get(v_state_3230_, 4);
v_response_3250_ = lean_ctor_get(v_state_3230_, 5);
v_respStream_3251_ = lean_ctor_get(v_state_3230_, 6);
v_requiresData_3252_ = lean_ctor_get_uint8(v_state_3230_, sizeof(void*)*9);
v_expectData_3253_ = lean_ctor_get(v_state_3230_, 7);
v_pendingHead_3254_ = lean_ctor_get(v_state_3230_, 8);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_state_3230_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3256_ = v_state_3230_;
v_isShared_3257_ = v_isSharedCheck_3270_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_pendingHead_3254_);
lean_inc(v_expectData_3253_);
lean_inc(v_respStream_3251_);
lean_inc(v_response_3250_);
lean_inc(v_headerTimeout_3249_);
lean_inc(v_currentTimeout_3248_);
lean_inc(v_keepAliveTimeout_3247_);
lean_inc(v_requestStream_3246_);
lean_inc(v_machine_3245_);
lean_dec(v_state_3230_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3270_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; lean_object* v___x_3262_; 
v___x_3258_ = lean_box(31);
v___x_3259_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3245_, v___x_3258_);
v___x_3260_ = 0;
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3259_);
v___x_3262_ = v___x_3256_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v_requestStream_3246_);
lean_ctor_set(v_reuseFailAlloc_3269_, 2, v_keepAliveTimeout_3247_);
lean_ctor_set(v_reuseFailAlloc_3269_, 3, v_currentTimeout_3248_);
lean_ctor_set(v_reuseFailAlloc_3269_, 4, v_headerTimeout_3249_);
lean_ctor_set(v_reuseFailAlloc_3269_, 5, v_response_3250_);
lean_ctor_set(v_reuseFailAlloc_3269_, 6, v_respStream_3251_);
lean_ctor_set(v_reuseFailAlloc_3269_, 7, v_expectData_3253_);
lean_ctor_set(v_reuseFailAlloc_3269_, 8, v_pendingHead_3254_);
lean_ctor_set_uint8(v_reuseFailAlloc_3269_, sizeof(void*)*9, v_requiresData_3252_);
v___x_3262_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*9 + 1, v___x_3260_);
v___x_3263_ = lean_box(v___x_3260_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3264_);
v___x_3266_ = v___x_3243_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_state_3273_, lean_object* v_x_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_state_3273_, v_x_3274_);
return v_res_3276_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3279_ = lean_mk_io_user_error(v___x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_handler_3282_, lean_object* v_config_3283_, lean_object* v_event_3284_, lean_object* v_state_3285_){
_start:
{
switch(lean_obj_tag(v_event_3284_))
{
case 0:
{
lean_object* v_x_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_handler_3282_);
lean_dec_ref(v_inst_3281_);
lean_dec_ref(v_inst_3280_);
v_x_3287_ = lean_ctor_get(v_event_3284_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_event_3284_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3289_ = v_event_3284_;
v_isShared_3290_ = v_isSharedCheck_3394_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_x_3287_);
lean_dec(v_event_3284_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3394_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
if (lean_obj_tag(v_x_3287_) == 0)
{
lean_object* v_machine_3291_; lean_object* v_reader_3292_; lean_object* v_requestStream_3293_; lean_object* v_keepAliveTimeout_3294_; lean_object* v_currentTimeout_3295_; lean_object* v_headerTimeout_3296_; lean_object* v_response_3297_; lean_object* v_respStream_3298_; uint8_t v_requiresData_3299_; lean_object* v_expectData_3300_; uint8_t v_handlerDispatched_3301_; lean_object* v_pendingHead_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v_config_3283_);
v_machine_3291_ = lean_ctor_get(v_state_3285_, 0);
lean_inc_ref(v_machine_3291_);
v_reader_3292_ = lean_ctor_get(v_machine_3291_, 0);
lean_inc_ref(v_reader_3292_);
v_requestStream_3293_ = lean_ctor_get(v_state_3285_, 1);
v_keepAliveTimeout_3294_ = lean_ctor_get(v_state_3285_, 2);
v_currentTimeout_3295_ = lean_ctor_get(v_state_3285_, 3);
v_headerTimeout_3296_ = lean_ctor_get(v_state_3285_, 4);
v_response_3297_ = lean_ctor_get(v_state_3285_, 5);
v_respStream_3298_ = lean_ctor_get(v_state_3285_, 6);
v_requiresData_3299_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3300_ = lean_ctor_get(v_state_3285_, 7);
v_handlerDispatched_3301_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9 + 1);
v_pendingHead_3302_ = lean_ctor_get(v_state_3285_, 8);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_state_3285_);
if (v_isSharedCheck_3345_ == 0)
{
lean_object* v_unused_3346_; 
v_unused_3346_ = lean_ctor_get(v_state_3285_, 0);
lean_dec(v_unused_3346_);
v___x_3304_ = v_state_3285_;
v_isShared_3305_ = v_isSharedCheck_3345_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_pendingHead_3302_);
lean_inc(v_expectData_3300_);
lean_inc(v_respStream_3298_);
lean_inc(v_response_3297_);
lean_inc(v_headerTimeout_3296_);
lean_inc(v_currentTimeout_3295_);
lean_inc(v_keepAliveTimeout_3294_);
lean_inc(v_requestStream_3293_);
lean_dec(v_state_3285_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3345_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_writer_3306_; lean_object* v_config_3307_; lean_object* v_events_3308_; lean_object* v_error_3309_; lean_object* v_instant_3310_; uint8_t v_keepAlive_3311_; uint8_t v_forcedFlush_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3343_; 
v_writer_3306_ = lean_ctor_get(v_machine_3291_, 1);
v_config_3307_ = lean_ctor_get(v_machine_3291_, 2);
v_events_3308_ = lean_ctor_get(v_machine_3291_, 3);
v_error_3309_ = lean_ctor_get(v_machine_3291_, 4);
v_instant_3310_ = lean_ctor_get(v_machine_3291_, 5);
v_keepAlive_3311_ = lean_ctor_get_uint8(v_machine_3291_, sizeof(void*)*6);
v_forcedFlush_3312_ = lean_ctor_get_uint8(v_machine_3291_, sizeof(void*)*6 + 1);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_machine_3291_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; 
v_unused_3344_ = lean_ctor_get(v_machine_3291_, 0);
lean_dec(v_unused_3344_);
v___x_3314_ = v_machine_3291_;
v_isShared_3315_ = v_isSharedCheck_3343_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_instant_3310_);
lean_inc(v_error_3309_);
lean_inc(v_events_3308_);
lean_inc(v_config_3307_);
lean_inc(v_writer_3306_);
lean_dec(v_machine_3291_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3343_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_state_3316_; lean_object* v_input_3317_; lean_object* v_messageHead_3318_; lean_object* v_messageCount_3319_; lean_object* v_bodyBytesRead_3320_; lean_object* v_headerBytesRead_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3342_; 
v_state_3316_ = lean_ctor_get(v_reader_3292_, 0);
v_input_3317_ = lean_ctor_get(v_reader_3292_, 1);
v_messageHead_3318_ = lean_ctor_get(v_reader_3292_, 2);
v_messageCount_3319_ = lean_ctor_get(v_reader_3292_, 3);
v_bodyBytesRead_3320_ = lean_ctor_get(v_reader_3292_, 4);
v_headerBytesRead_3321_ = lean_ctor_get(v_reader_3292_, 5);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_reader_3292_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3323_ = v_reader_3292_;
v_isShared_3324_ = v_isSharedCheck_3342_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_headerBytesRead_3321_);
lean_inc(v_bodyBytesRead_3320_);
lean_inc(v_messageCount_3319_);
lean_inc(v_messageHead_3318_);
lean_inc(v_input_3317_);
lean_inc(v_state_3316_);
lean_dec(v_reader_3292_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3342_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
uint8_t v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = 1;
if (v_isShared_3324_ == 0)
{
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_state_3316_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_input_3317_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_messageHead_3318_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_messageCount_3319_);
lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_bodyBytesRead_3320_);
lean_ctor_set(v_reuseFailAlloc_3341_, 5, v_headerBytesRead_3321_);
v___x_3327_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
uint8_t v___x_3328_; lean_object* v___x_3330_; 
lean_ctor_set_uint8(v___x_3327_, sizeof(void*)*6, v___x_3325_);
v___x_3328_ = 0;
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3327_);
v___x_3330_ = v___x_3314_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_writer_3306_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_config_3307_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_events_3308_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_error_3309_);
lean_ctor_set(v_reuseFailAlloc_3340_, 5, v_instant_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3340_, sizeof(void*)*6, v_keepAlive_3311_);
lean_ctor_set_uint8(v_reuseFailAlloc_3340_, sizeof(void*)*6 + 1, v_forcedFlush_3312_);
v___x_3330_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
lean_ctor_set_uint8(v___x_3330_, sizeof(void*)*6 + 2, v___x_3328_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3330_);
v___x_3332_ = v___x_3304_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_requestStream_3293_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_keepAliveTimeout_3294_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_currentTimeout_3295_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v_headerTimeout_3296_);
lean_ctor_set(v_reuseFailAlloc_3339_, 5, v_response_3297_);
lean_ctor_set(v_reuseFailAlloc_3339_, 6, v_respStream_3298_);
lean_ctor_set(v_reuseFailAlloc_3339_, 7, v_expectData_3300_);
lean_ctor_set(v_reuseFailAlloc_3339_, 8, v_pendingHead_3302_);
lean_ctor_set_uint8(v_reuseFailAlloc_3339_, sizeof(void*)*9, v_requiresData_3299_);
lean_ctor_set_uint8(v_reuseFailAlloc_3339_, sizeof(void*)*9 + 1, v_handlerDispatched_3301_);
v___x_3332_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3333_ = lean_box(v___x_3328_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 1);
lean_ctor_set(v___x_3289_, 0, v___x_3334_);
v___x_3336_ = v___x_3289_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3337_; 
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
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
lean_object* v_val_3347_; lean_object* v_machine_3348_; lean_object* v_requestStream_3349_; lean_object* v_keepAliveTimeout_3350_; lean_object* v_currentTimeout_3351_; lean_object* v_response_3352_; lean_object* v_respStream_3353_; uint8_t v_requiresData_3354_; lean_object* v_expectData_3355_; uint8_t v_handlerDispatched_3356_; lean_object* v_pendingHead_3357_; lean_object* v___f_3358_; 
lean_del_object(v___x_3289_);
v_val_3347_ = lean_ctor_get(v_x_3287_, 0);
lean_inc_n(v_val_3347_, 2);
lean_dec_ref(v_x_3287_);
v_machine_3348_ = lean_ctor_get(v_state_3285_, 0);
v_requestStream_3349_ = lean_ctor_get(v_state_3285_, 1);
v_keepAliveTimeout_3350_ = lean_ctor_get(v_state_3285_, 2);
lean_inc(v_keepAliveTimeout_3350_);
v_currentTimeout_3351_ = lean_ctor_get(v_state_3285_, 3);
v_response_3352_ = lean_ctor_get(v_state_3285_, 5);
v_respStream_3353_ = lean_ctor_get(v_state_3285_, 6);
v_requiresData_3354_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3355_ = lean_ctor_get(v_state_3285_, 7);
v_handlerDispatched_3356_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9 + 1);
v_pendingHead_3357_ = lean_ctor_get(v_state_3285_, 8);
v___f_3358_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3358_, 0, v_val_3347_);
if (lean_obj_tag(v_keepAliveTimeout_3350_) == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec_ref(v___f_3358_);
lean_dec_ref(v_config_3283_);
v___x_3359_ = lean_box(0);
v___x_3360_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3347_, v___x_3359_, v_state_3285_);
return v___x_3360_;
}
else
{
lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3392_; 
lean_inc(v_pendingHead_3357_);
lean_inc(v_expectData_3355_);
lean_inc(v_respStream_3353_);
lean_inc_ref(v_response_3352_);
lean_inc(v_currentTimeout_3351_);
lean_inc_ref(v_requestStream_3349_);
lean_inc_ref(v_machine_3348_);
lean_dec(v_val_3347_);
lean_dec_ref(v_state_3285_);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_keepAliveTimeout_3350_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v_keepAliveTimeout_3350_, 0);
lean_dec(v_unused_3393_);
v___x_3362_ = v_keepAliveTimeout_3350_;
v_isShared_3363_ = v_isSharedCheck_3392_;
goto v_resetjp_3361_;
}
else
{
lean_dec(v_keepAliveTimeout_3350_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3392_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___f_3366_; lean_object* v_val_3368_; lean_object* v___x_3375_; 
v___x_3364_ = lean_box(v_requiresData_3354_);
v___x_3365_ = lean_box(v_handlerDispatched_3356_);
v___f_3366_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3366_, 0, v_config_3283_);
lean_closure_set(v___f_3366_, 1, v_machine_3348_);
lean_closure_set(v___f_3366_, 2, v_requestStream_3349_);
lean_closure_set(v___f_3366_, 3, v_currentTimeout_3351_);
lean_closure_set(v___f_3366_, 4, v_response_3352_);
lean_closure_set(v___f_3366_, 5, v_respStream_3353_);
lean_closure_set(v___f_3366_, 6, v___x_3364_);
lean_closure_set(v___f_3366_, 7, v_expectData_3355_);
lean_closure_set(v___f_3366_, 8, v___x_3365_);
lean_closure_set(v___f_3366_, 9, v_pendingHead_3357_);
lean_closure_set(v___f_3366_, 10, v___f_3358_);
v___x_3375_ = lean_get_current_time();
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 1);
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
v_val_3368_ = v___x_3381_;
goto v___jp_3367_;
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
v_a_3384_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3375_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3375_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 0);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
v_val_3368_ = v___x_3389_;
goto v___jp_3367_;
}
}
}
v___jp_3367_:
{
lean_object* v___x_3370_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 0);
lean_ctor_set(v___x_3362_, 0, v_val_3368_);
v___x_3370_ = v___x_3362_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_val_3368_);
v___x_3370_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = 0;
v___x_3373_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3371_, v___x_3372_, v___x_3370_, v___f_3366_);
return v___x_3373_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v_config_3283_);
lean_dec(v_handler_3282_);
lean_dec_ref(v_inst_3280_);
v_x_3395_ = lean_ctor_get(v_event_3284_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_event_3284_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3397_ = v_event_3284_;
v_isShared_3398_ = v_isSharedCheck_3510_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_x_3395_);
lean_dec(v_event_3284_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3510_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
if (lean_obj_tag(v_x_3395_) == 0)
{
lean_object* v_machine_3399_; lean_object* v_requestStream_3400_; lean_object* v_keepAliveTimeout_3401_; lean_object* v_currentTimeout_3402_; lean_object* v_headerTimeout_3403_; lean_object* v_response_3404_; lean_object* v_respStream_3405_; uint8_t v_requiresData_3406_; lean_object* v_expectData_3407_; uint8_t v_handlerDispatched_3408_; lean_object* v_pendingHead_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___f_3412_; 
lean_del_object(v___x_3397_);
v_machine_3399_ = lean_ctor_get(v_state_3285_, 0);
lean_inc_ref_n(v_machine_3399_, 2);
v_requestStream_3400_ = lean_ctor_get(v_state_3285_, 1);
lean_inc_ref_n(v_requestStream_3400_, 2);
v_keepAliveTimeout_3401_ = lean_ctor_get(v_state_3285_, 2);
lean_inc_n(v_keepAliveTimeout_3401_, 2);
v_currentTimeout_3402_ = lean_ctor_get(v_state_3285_, 3);
lean_inc_n(v_currentTimeout_3402_, 2);
v_headerTimeout_3403_ = lean_ctor_get(v_state_3285_, 4);
lean_inc_n(v_headerTimeout_3403_, 2);
v_response_3404_ = lean_ctor_get(v_state_3285_, 5);
lean_inc_ref_n(v_response_3404_, 2);
v_respStream_3405_ = lean_ctor_get(v_state_3285_, 6);
lean_inc(v_respStream_3405_);
v_requiresData_3406_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3407_ = lean_ctor_get(v_state_3285_, 7);
lean_inc_n(v_expectData_3407_, 2);
v_handlerDispatched_3408_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9 + 1);
v_pendingHead_3409_ = lean_ctor_get(v_state_3285_, 8);
lean_inc_n(v_pendingHead_3409_, 2);
lean_dec_ref(v_state_3285_);
v___x_3410_ = lean_box(v_requiresData_3406_);
v___x_3411_ = lean_box(v_handlerDispatched_3408_);
v___f_3412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3412_, 0, v_machine_3399_);
lean_closure_set(v___f_3412_, 1, v_requestStream_3400_);
lean_closure_set(v___f_3412_, 2, v_keepAliveTimeout_3401_);
lean_closure_set(v___f_3412_, 3, v_currentTimeout_3402_);
lean_closure_set(v___f_3412_, 4, v_headerTimeout_3403_);
lean_closure_set(v___f_3412_, 5, v_response_3404_);
lean_closure_set(v___f_3412_, 6, v___x_3410_);
lean_closure_set(v___f_3412_, 7, v_expectData_3407_);
lean_closure_set(v___f_3412_, 8, v___x_3411_);
lean_closure_set(v___f_3412_, 9, v_pendingHead_3409_);
if (lean_obj_tag(v_respStream_3405_) == 1)
{
lean_object* v_val_3413_; lean_object* v_close_3414_; lean_object* v_isClosed_3415_; lean_object* v___x_3416_; lean_object* v___f_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; 
lean_dec(v_pendingHead_3409_);
lean_dec(v_expectData_3407_);
lean_dec_ref(v_response_3404_);
lean_dec(v_headerTimeout_3403_);
lean_dec(v_currentTimeout_3402_);
lean_dec(v_keepAliveTimeout_3401_);
lean_dec_ref(v_requestStream_3400_);
lean_dec_ref(v_machine_3399_);
v_val_3413_ = lean_ctor_get(v_respStream_3405_, 0);
lean_inc_n(v_val_3413_, 2);
lean_dec_ref(v_respStream_3405_);
v_close_3414_ = lean_ctor_get(v_inst_3281_, 1);
lean_inc_ref(v_close_3414_);
v_isClosed_3415_ = lean_ctor_get(v_inst_3281_, 2);
lean_inc_ref(v_isClosed_3415_);
lean_dec_ref(v_inst_3281_);
v___x_3416_ = lean_apply_2(v_isClosed_3415_, v_val_3413_, lean_box(0));
lean_inc_ref(v___f_3412_);
v___f_3417_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3417_, 0, v___f_3412_);
v___f_3418_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3418_, 0, v_close_3414_);
lean_closure_set(v___f_3418_, 1, v_val_3413_);
lean_closure_set(v___f_3418_, 2, v___f_3417_);
lean_closure_set(v___f_3418_, 3, v___f_3412_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = 0;
v___x_3421_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3419_, v___x_3420_, v___x_3416_, v___f_3418_);
return v___x_3421_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v___f_3412_);
lean_dec(v_respStream_3405_);
lean_dec_ref(v_inst_3281_);
v___x_3422_ = lean_box(0);
v___x_3423_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3399_, v_requestStream_3400_, v_keepAliveTimeout_3401_, v_currentTimeout_3402_, v_headerTimeout_3403_, v_response_3404_, v_requiresData_3406_, v_expectData_3407_, v_handlerDispatched_3408_, v_pendingHead_3409_, v___x_3422_);
return v___x_3423_;
}
}
else
{
lean_object* v_val_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_inst_3281_);
v_val_3424_ = lean_ctor_get(v_x_3395_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_x_3395_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3426_ = v_x_3395_;
v_isShared_3427_ = v_isSharedCheck_3509_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_val_3424_);
lean_dec(v_x_3395_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3509_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_machine_3428_; lean_object* v_requestStream_3429_; lean_object* v_keepAliveTimeout_3430_; lean_object* v_currentTimeout_3431_; lean_object* v_headerTimeout_3432_; lean_object* v_response_3433_; lean_object* v_respStream_3434_; uint8_t v_requiresData_3435_; lean_object* v_expectData_3436_; uint8_t v_handlerDispatched_3437_; lean_object* v_pendingHead_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3508_; 
v_machine_3428_ = lean_ctor_get(v_state_3285_, 0);
v_requestStream_3429_ = lean_ctor_get(v_state_3285_, 1);
v_keepAliveTimeout_3430_ = lean_ctor_get(v_state_3285_, 2);
v_currentTimeout_3431_ = lean_ctor_get(v_state_3285_, 3);
v_headerTimeout_3432_ = lean_ctor_get(v_state_3285_, 4);
v_response_3433_ = lean_ctor_get(v_state_3285_, 5);
v_respStream_3434_ = lean_ctor_get(v_state_3285_, 6);
v_requiresData_3435_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3436_ = lean_ctor_get(v_state_3285_, 7);
v_handlerDispatched_3437_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9 + 1);
v_pendingHead_3438_ = lean_ctor_get(v_state_3285_, 8);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_state_3285_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3440_ = v_state_3285_;
v_isShared_3441_ = v_isSharedCheck_3508_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_pendingHead_3438_);
lean_inc(v_expectData_3436_);
lean_inc(v_respStream_3434_);
lean_inc(v_response_3433_);
lean_inc(v_headerTimeout_3432_);
lean_inc(v_currentTimeout_3431_);
lean_inc(v_keepAliveTimeout_3430_);
lean_inc(v_requestStream_3429_);
lean_inc(v_machine_3428_);
lean_dec(v_state_3285_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3508_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___y_3443_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3456_ = lean_unsigned_to_nat(1u);
v___x_3457_ = lean_mk_empty_array_with_capacity(v___x_3456_);
v___x_3458_ = lean_array_push(v___x_3457_, v_val_3424_);
v___x_3459_ = lean_array_get_size(v___x_3458_);
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = lean_nat_dec_eq(v___x_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v_reader_3462_; lean_object* v_writer_3463_; lean_object* v_config_3464_; lean_object* v_events_3465_; lean_object* v_error_3466_; lean_object* v_instant_3467_; uint8_t v_keepAlive_3468_; uint8_t v_forcedFlush_3469_; uint8_t v_pullBodyStalled_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3507_; 
v_reader_3462_ = lean_ctor_get(v_machine_3428_, 0);
v_writer_3463_ = lean_ctor_get(v_machine_3428_, 1);
v_config_3464_ = lean_ctor_get(v_machine_3428_, 2);
v_events_3465_ = lean_ctor_get(v_machine_3428_, 3);
v_error_3466_ = lean_ctor_get(v_machine_3428_, 4);
v_instant_3467_ = lean_ctor_get(v_machine_3428_, 5);
v_keepAlive_3468_ = lean_ctor_get_uint8(v_machine_3428_, sizeof(void*)*6);
v_forcedFlush_3469_ = lean_ctor_get_uint8(v_machine_3428_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3470_ = lean_ctor_get_uint8(v_machine_3428_, sizeof(void*)*6 + 2);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_machine_3428_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3472_ = v_machine_3428_;
v_isShared_3473_ = v_isSharedCheck_3507_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_instant_3467_);
lean_inc(v_error_3466_);
lean_inc(v_events_3465_);
lean_inc(v_config_3464_);
lean_inc(v_writer_3463_);
lean_inc(v_reader_3462_);
lean_dec(v_machine_3428_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3507_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___y_3475_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3497_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3498_ = lean_nat_dec_lt(v___x_3460_, v___x_3459_);
if (v___x_3498_ == 0)
{
v___y_3475_ = v___x_3460_;
goto v___jp_3474_;
}
else
{
lean_object* v___f_3499_; uint8_t v___x_3500_; 
v___f_3499_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3500_ = lean_nat_dec_le(v___x_3459_, v___x_3459_);
if (v___x_3500_ == 0)
{
if (v___x_3498_ == 0)
{
v___y_3475_ = v___x_3460_;
goto v___jp_3474_;
}
else
{
size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = lean_usize_of_nat(v___x_3459_);
lean_inc_ref(v___x_3458_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3497_, v___f_3499_, v___x_3458_, v___x_3501_, v___x_3502_, v___x_3460_);
v___y_3475_ = v___x_3503_;
goto v___jp_3474_;
}
}
else
{
size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((size_t)0ULL);
v___x_3505_ = lean_usize_of_nat(v___x_3459_);
lean_inc_ref(v___x_3458_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3497_, v___f_3499_, v___x_3458_, v___x_3504_, v___x_3505_, v___x_3460_);
v___y_3475_ = v___x_3506_;
goto v___jp_3474_;
}
}
v___jp_3474_:
{
lean_object* v_userData_3476_; lean_object* v_outputData_3477_; lean_object* v_state_3478_; lean_object* v_knownSize_3479_; lean_object* v_messageHead_3480_; uint8_t v_sentMessage_3481_; uint8_t v_userClosedBody_3482_; uint8_t v_omitBody_3483_; lean_object* v_userDataBytes_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3496_; 
v_userData_3476_ = lean_ctor_get(v_writer_3463_, 0);
v_outputData_3477_ = lean_ctor_get(v_writer_3463_, 1);
v_state_3478_ = lean_ctor_get(v_writer_3463_, 2);
v_knownSize_3479_ = lean_ctor_get(v_writer_3463_, 3);
v_messageHead_3480_ = lean_ctor_get(v_writer_3463_, 4);
v_sentMessage_3481_ = lean_ctor_get_uint8(v_writer_3463_, sizeof(void*)*6);
v_userClosedBody_3482_ = lean_ctor_get_uint8(v_writer_3463_, sizeof(void*)*6 + 1);
v_omitBody_3483_ = lean_ctor_get_uint8(v_writer_3463_, sizeof(void*)*6 + 2);
v_userDataBytes_3484_ = lean_ctor_get(v_writer_3463_, 5);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_writer_3463_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3486_ = v_writer_3463_;
v_isShared_3487_ = v_isSharedCheck_3496_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_userDataBytes_3484_);
lean_inc(v_messageHead_3480_);
lean_inc(v_knownSize_3479_);
lean_inc(v_state_3478_);
lean_inc(v_outputData_3477_);
lean_inc(v_userData_3476_);
lean_dec(v_writer_3463_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3496_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3488_ = l_Array_append___redArg(v_userData_3476_, v___x_3458_);
lean_dec_ref(v___x_3458_);
v___x_3489_ = lean_nat_add(v_userDataBytes_3484_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec(v_userDataBytes_3484_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 5, v___x_3489_);
lean_ctor_set(v___x_3486_, 0, v___x_3488_);
v___x_3491_ = v___x_3486_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_outputData_3477_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_state_3478_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_knownSize_3479_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_messageHead_3480_);
lean_ctor_set(v_reuseFailAlloc_3495_, 5, v___x_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3495_, sizeof(void*)*6, v_sentMessage_3481_);
lean_ctor_set_uint8(v_reuseFailAlloc_3495_, sizeof(void*)*6 + 1, v_userClosedBody_3482_);
lean_ctor_set_uint8(v_reuseFailAlloc_3495_, sizeof(void*)*6 + 2, v_omitBody_3483_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v___x_3491_);
v___x_3493_ = v___x_3472_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_reader_3462_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_config_3464_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_events_3465_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v_error_3466_);
lean_ctor_set(v_reuseFailAlloc_3494_, 5, v_instant_3467_);
lean_ctor_set_uint8(v_reuseFailAlloc_3494_, sizeof(void*)*6, v_keepAlive_3468_);
lean_ctor_set_uint8(v_reuseFailAlloc_3494_, sizeof(void*)*6 + 1, v_forcedFlush_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3494_, sizeof(void*)*6 + 2, v_pullBodyStalled_3470_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
v___y_3443_ = v___x_3493_;
goto v___jp_3442_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3458_);
v___y_3443_ = v_machine_3428_;
goto v___jp_3442_;
}
v___jp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___y_3443_);
v___x_3445_ = v___x_3440_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___y_3443_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_requestStream_3429_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_keepAliveTimeout_3430_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_currentTimeout_3431_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v_headerTimeout_3432_);
lean_ctor_set(v_reuseFailAlloc_3455_, 5, v_response_3433_);
lean_ctor_set(v_reuseFailAlloc_3455_, 6, v_respStream_3434_);
lean_ctor_set(v_reuseFailAlloc_3455_, 7, v_expectData_3436_);
lean_ctor_set(v_reuseFailAlloc_3455_, 8, v_pendingHead_3438_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*9, v_requiresData_3435_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*9 + 1, v_handlerDispatched_3437_);
v___x_3445_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3446_ = 0;
v___x_3447_ = lean_box(v___x_3446_);
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3445_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3448_);
v___x_3450_ = v___x_3426_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3450_);
v___x_3452_ = v___x_3397_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
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
uint8_t v_x_3511_; 
lean_dec_ref(v_config_3283_);
lean_dec_ref(v_inst_3281_);
v_x_3511_ = lean_ctor_get_uint8(v_event_3284_, 0);
lean_dec_ref(v_event_3284_);
if (v_x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_dec(v_handler_3282_);
lean_dec_ref(v_inst_3280_);
v___x_3512_ = lean_box(v_x_3511_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v_state_3285_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
v___x_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
return v___x_3515_;
}
else
{
lean_object* v_machine_3516_; lean_object* v_requestStream_3517_; lean_object* v_keepAliveTimeout_3518_; lean_object* v_currentTimeout_3519_; lean_object* v_headerTimeout_3520_; lean_object* v_response_3521_; lean_object* v_respStream_3522_; uint8_t v_requiresData_3523_; lean_object* v_expectData_3524_; uint8_t v_handlerDispatched_3525_; lean_object* v_pendingHead_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3576_; 
v_machine_3516_ = lean_ctor_get(v_state_3285_, 0);
v_requestStream_3517_ = lean_ctor_get(v_state_3285_, 1);
v_keepAliveTimeout_3518_ = lean_ctor_get(v_state_3285_, 2);
v_currentTimeout_3519_ = lean_ctor_get(v_state_3285_, 3);
v_headerTimeout_3520_ = lean_ctor_get(v_state_3285_, 4);
v_response_3521_ = lean_ctor_get(v_state_3285_, 5);
v_respStream_3522_ = lean_ctor_get(v_state_3285_, 6);
v_requiresData_3523_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3524_ = lean_ctor_get(v_state_3285_, 7);
v_handlerDispatched_3525_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9 + 1);
v_pendingHead_3526_ = lean_ctor_get(v_state_3285_, 8);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_state_3285_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3528_ = v_state_3285_;
v_isShared_3529_ = v_isSharedCheck_3576_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_pendingHead_3526_);
lean_inc(v_expectData_3524_);
lean_inc(v_respStream_3522_);
lean_inc(v_response_3521_);
lean_inc(v_headerTimeout_3520_);
lean_inc(v_currentTimeout_3519_);
lean_inc(v_keepAliveTimeout_3518_);
lean_inc(v_requestStream_3517_);
lean_inc(v_machine_3516_);
lean_dec(v_state_3285_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3576_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
uint8_t v___x_3530_; lean_object* v___x_3531_; lean_object* v_fst_3532_; lean_object* v_snd_3533_; lean_object* v_reader_3534_; lean_object* v_writer_3535_; lean_object* v_config_3536_; lean_object* v_events_3537_; lean_object* v_error_3538_; lean_object* v_instant_3539_; uint8_t v_keepAlive_3540_; uint8_t v_forcedFlush_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3575_; 
v___x_3530_ = 0;
v___x_3531_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3530_, v_machine_3516_);
v_fst_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_fst_3532_);
v_snd_3533_ = lean_ctor_get(v___x_3531_, 1);
lean_inc(v_snd_3533_);
lean_dec_ref(v___x_3531_);
v_reader_3534_ = lean_ctor_get(v_fst_3532_, 0);
v_writer_3535_ = lean_ctor_get(v_fst_3532_, 1);
v_config_3536_ = lean_ctor_get(v_fst_3532_, 2);
v_events_3537_ = lean_ctor_get(v_fst_3532_, 3);
v_error_3538_ = lean_ctor_get(v_fst_3532_, 4);
v_instant_3539_ = lean_ctor_get(v_fst_3532_, 5);
v_keepAlive_3540_ = lean_ctor_get_uint8(v_fst_3532_, sizeof(void*)*6);
v_forcedFlush_3541_ = lean_ctor_get_uint8(v_fst_3532_, sizeof(void*)*6 + 1);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_fst_3532_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3543_ = v_fst_3532_;
v_isShared_3544_ = v_isSharedCheck_3575_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_instant_3539_);
lean_inc(v_error_3538_);
lean_inc(v_events_3537_);
lean_inc(v_config_3536_);
lean_inc(v_writer_3535_);
lean_inc(v_reader_3534_);
lean_dec(v_fst_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3575_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___f_3545_; lean_object* v___f_3546_; uint8_t v___y_3548_; 
v___f_3545_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3545_, 0, v_inst_3280_);
lean_closure_set(v___f_3545_, 1, v_handler_3282_);
v___f_3546_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3533_) == 0)
{
uint8_t v_sentMessage_3571_; 
v_sentMessage_3571_ = lean_ctor_get_uint8(v_writer_3535_, sizeof(void*)*6);
if (v_sentMessage_3571_ == 0)
{
lean_object* v_state_3572_; 
v_state_3572_ = lean_ctor_get(v_reader_3534_, 0);
if (lean_obj_tag(v_state_3572_) == 2)
{
v___y_3548_ = v_x_3511_;
goto v___jp_3547_;
}
else
{
v___y_3548_ = v_sentMessage_3571_;
goto v___jp_3547_;
}
}
else
{
uint8_t v___x_3573_; 
v___x_3573_ = 0;
v___y_3548_ = v___x_3573_;
goto v___jp_3547_;
}
}
else
{
uint8_t v___x_3574_; 
v___x_3574_ = 0;
v___y_3548_ = v___x_3574_;
goto v___jp_3547_;
}
v___jp_3547_:
{
lean_object* v___x_3550_; 
if (v_isShared_3544_ == 0)
{
v___x_3550_ = v___x_3543_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_reader_3534_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_writer_3535_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_config_3536_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_events_3537_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_error_3538_);
lean_ctor_set(v_reuseFailAlloc_3570_, 5, v_instant_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*6, v_keepAlive_3540_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*6 + 1, v_forcedFlush_3541_);
v___x_3550_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v_st_3552_; 
lean_ctor_set_uint8(v___x_3550_, sizeof(void*)*6 + 2, v___y_3548_);
lean_inc_ref(v_requestStream_3517_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3550_);
v_st_3552_ = v___x_3528_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_requestStream_3517_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_keepAliveTimeout_3518_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_currentTimeout_3519_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_headerTimeout_3520_);
lean_ctor_set(v_reuseFailAlloc_3569_, 5, v_response_3521_);
lean_ctor_set(v_reuseFailAlloc_3569_, 6, v_respStream_3522_);
lean_ctor_set(v_reuseFailAlloc_3569_, 7, v_expectData_3524_);
lean_ctor_set(v_reuseFailAlloc_3569_, 8, v_pendingHead_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*9, v_requiresData_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*9 + 1, v_handlerDispatched_3525_);
v_st_3552_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___f_3553_; 
lean_inc_ref(v_st_3552_);
v___f_3553_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3553_, 0, v_st_3552_);
if (lean_obj_tag(v_snd_3533_) == 1)
{
lean_object* v_val_3554_; uint8_t v_final_3555_; uint8_t v_incomplete_3556_; lean_object* v_chunk_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___x_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; 
lean_dec_ref(v_st_3552_);
v_val_3554_ = lean_ctor_get(v_snd_3533_, 0);
lean_inc(v_val_3554_);
lean_dec_ref(v_snd_3533_);
v_final_3555_ = lean_ctor_get_uint8(v_val_3554_, sizeof(void*)*1);
v_incomplete_3556_ = lean_ctor_get_uint8(v_val_3554_, sizeof(void*)*1 + 1);
v_chunk_3557_ = lean_ctor_get(v_val_3554_, 0);
lean_inc_ref(v_chunk_3557_);
lean_dec(v_val_3554_);
lean_inc_ref_n(v_requestStream_3517_, 2);
v___x_3558_ = l_Std_Http_Body_Stream_send(v_requestStream_3517_, v_chunk_3557_, v_incomplete_3556_);
v___x_3559_ = lean_unsigned_to_nat(0u);
v___x_3560_ = 0;
v___x_3561_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3559_, v___x_3560_, v___x_3558_, v___f_3545_);
lean_inc_ref_n(v___f_3553_, 2);
v___f_3562_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3562_, 0, v___f_3553_);
v___f_3563_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3563_, 0, v_requestStream_3517_);
lean_closure_set(v___f_3563_, 1, v___f_3562_);
lean_closure_set(v___f_3563_, 2, v___f_3553_);
v___x_3564_ = lean_box(v_final_3555_);
v___f_3565_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3565_, 0, v___x_3564_);
lean_closure_set(v___f_3565_, 1, v___f_3553_);
lean_closure_set(v___f_3565_, 2, v___f_3546_);
lean_closure_set(v___f_3565_, 3, v_requestStream_3517_);
lean_closure_set(v___f_3565_, 4, v___f_3563_);
v___x_3566_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3559_, v___x_3560_, v___x_3561_, v___f_3565_);
return v___x_3566_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec_ref(v___f_3553_);
lean_dec_ref(v___f_3545_);
lean_dec(v_snd_3533_);
lean_dec_ref(v_requestStream_3517_);
v___x_3567_ = lean_box(0);
v___x_3568_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3552_, v___x_3567_);
return v___x_3568_;
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
lean_object* v_x_3577_; 
v_x_3577_ = lean_ctor_get(v_event_3284_, 0);
lean_inc_ref(v_x_3577_);
lean_dec_ref(v_event_3284_);
if (lean_obj_tag(v_x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v_onFailure_3579_; lean_object* v___x_3580_; lean_object* v___f_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; lean_object* v___x_3584_; 
lean_dec_ref(v_config_3283_);
lean_dec_ref(v_inst_3281_);
v_a_3578_ = lean_ctor_get(v_x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref(v_x_3577_);
v_onFailure_3579_ = lean_ctor_get(v_inst_3280_, 2);
lean_inc_ref(v_onFailure_3579_);
lean_dec_ref(v_inst_3280_);
v___x_3580_ = lean_apply_3(v_onFailure_3579_, v_handler_3282_, v_a_3578_, lean_box(0));
v___f_3581_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3581_, 0, v_state_3285_);
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = 0;
v___x_3584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3582_, v___x_3583_, v___x_3580_, v___f_3581_);
return v___x_3584_;
}
else
{
lean_object* v_machine_3585_; lean_object* v_reader_3586_; lean_object* v_state_3587_; 
lean_dec(v_handler_3282_);
lean_dec_ref(v_inst_3280_);
v_machine_3585_ = lean_ctor_get(v_state_3285_, 0);
lean_inc_ref(v_machine_3585_);
v_reader_3586_ = lean_ctor_get(v_machine_3585_, 0);
v_state_3587_ = lean_ctor_get(v_reader_3586_, 0);
if (lean_obj_tag(v_state_3587_) == 7)
{
lean_object* v_a_3588_; lean_object* v_requestStream_3589_; lean_object* v_keepAliveTimeout_3590_; lean_object* v_currentTimeout_3591_; lean_object* v_headerTimeout_3592_; lean_object* v_response_3593_; lean_object* v_respStream_3594_; uint8_t v_requiresData_3595_; lean_object* v_expectData_3596_; lean_object* v_pendingHead_3597_; lean_object* v_close_3598_; lean_object* v_isClosed_3599_; lean_object* v_body_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; 
lean_dec_ref(v_config_3283_);
v_a_3588_ = lean_ctor_get(v_x_3577_, 0);
lean_inc(v_a_3588_);
lean_dec_ref(v_x_3577_);
v_requestStream_3589_ = lean_ctor_get(v_state_3285_, 1);
lean_inc_ref(v_requestStream_3589_);
v_keepAliveTimeout_3590_ = lean_ctor_get(v_state_3285_, 2);
lean_inc(v_keepAliveTimeout_3590_);
v_currentTimeout_3591_ = lean_ctor_get(v_state_3285_, 3);
lean_inc(v_currentTimeout_3591_);
v_headerTimeout_3592_ = lean_ctor_get(v_state_3285_, 4);
lean_inc(v_headerTimeout_3592_);
v_response_3593_ = lean_ctor_get(v_state_3285_, 5);
lean_inc_ref(v_response_3593_);
v_respStream_3594_ = lean_ctor_get(v_state_3285_, 6);
lean_inc(v_respStream_3594_);
v_requiresData_3595_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3596_ = lean_ctor_get(v_state_3285_, 7);
lean_inc(v_expectData_3596_);
v_pendingHead_3597_ = lean_ctor_get(v_state_3285_, 8);
lean_inc(v_pendingHead_3597_);
lean_dec_ref(v_state_3285_);
v_close_3598_ = lean_ctor_get(v_inst_3281_, 1);
lean_inc_ref(v_close_3598_);
v_isClosed_3599_ = lean_ctor_get(v_inst_3281_, 2);
lean_inc_ref(v_isClosed_3599_);
lean_dec_ref(v_inst_3281_);
v_body_3600_ = lean_ctor_get(v_a_3588_, 1);
lean_inc_n(v_body_3600_, 2);
lean_dec(v_a_3588_);
v___x_3601_ = lean_apply_2(v_isClosed_3599_, v_body_3600_, lean_box(0));
v___x_3602_ = lean_box(v_requiresData_3595_);
v___f_3603_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3603_, 0, v_machine_3585_);
lean_closure_set(v___f_3603_, 1, v_requestStream_3589_);
lean_closure_set(v___f_3603_, 2, v_keepAliveTimeout_3590_);
lean_closure_set(v___f_3603_, 3, v_currentTimeout_3591_);
lean_closure_set(v___f_3603_, 4, v_headerTimeout_3592_);
lean_closure_set(v___f_3603_, 5, v_response_3593_);
lean_closure_set(v___f_3603_, 6, v_respStream_3594_);
lean_closure_set(v___f_3603_, 7, v___x_3602_);
lean_closure_set(v___f_3603_, 8, v_expectData_3596_);
lean_closure_set(v___f_3603_, 9, v_pendingHead_3597_);
lean_inc_ref(v___f_3603_);
v___f_3604_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3604_, 0, v___f_3603_);
v___f_3605_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3605_, 0, v_close_3598_);
lean_closure_set(v___f_3605_, 1, v_body_3600_);
lean_closure_set(v___f_3605_, 2, v___f_3604_);
lean_closure_set(v___f_3605_, 3, v___f_3603_);
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = 0;
v___x_3608_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3606_, v___x_3607_, v___x_3601_, v___f_3605_);
return v___x_3608_;
}
else
{
lean_object* v_a_3609_; lean_object* v_requestStream_3610_; lean_object* v_keepAliveTimeout_3611_; lean_object* v_currentTimeout_3612_; lean_object* v_headerTimeout_3613_; lean_object* v_response_3614_; uint8_t v_requiresData_3615_; lean_object* v_expectData_3616_; lean_object* v_pendingHead_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___f_3622_; lean_object* v___f_3623_; lean_object* v___x_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3609_ = lean_ctor_get(v_x_3577_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v_x_3577_);
v_requestStream_3610_ = lean_ctor_get(v_state_3285_, 1);
lean_inc_ref(v_requestStream_3610_);
v_keepAliveTimeout_3611_ = lean_ctor_get(v_state_3285_, 2);
lean_inc(v_keepAliveTimeout_3611_);
v_currentTimeout_3612_ = lean_ctor_get(v_state_3285_, 3);
lean_inc(v_currentTimeout_3612_);
v_headerTimeout_3613_ = lean_ctor_get(v_state_3285_, 4);
lean_inc(v_headerTimeout_3613_);
v_response_3614_ = lean_ctor_get(v_state_3285_, 5);
lean_inc_ref(v_response_3614_);
v_requiresData_3615_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3616_ = lean_ctor_get(v_state_3285_, 7);
lean_inc(v_expectData_3616_);
v_pendingHead_3617_ = lean_ctor_get(v_state_3285_, 8);
lean_inc(v_pendingHead_3617_);
lean_dec_ref(v_state_3285_);
lean_inc_ref(v_inst_3281_);
v___x_3618_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3281_, v_config_3283_, v_machine_3585_, v_a_3609_);
v___x_3619_ = 0;
v___x_3620_ = lean_box(v_requiresData_3615_);
v___x_3621_ = lean_box(v___x_3619_);
v___f_3622_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3622_, 0, v_requestStream_3610_);
lean_closure_set(v___f_3622_, 1, v_keepAliveTimeout_3611_);
lean_closure_set(v___f_3622_, 2, v_currentTimeout_3612_);
lean_closure_set(v___f_3622_, 3, v_headerTimeout_3613_);
lean_closure_set(v___f_3622_, 4, v_response_3614_);
lean_closure_set(v___f_3622_, 5, v___x_3620_);
lean_closure_set(v___f_3622_, 6, v_expectData_3616_);
lean_closure_set(v___f_3622_, 7, v___x_3621_);
lean_closure_set(v___f_3622_, 8, v_pendingHead_3617_);
v___f_3623_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3623_, 0, v___f_3622_);
v___x_3624_ = lean_box(v___x_3619_);
lean_inc_ref(v___f_3623_);
v___f_3625_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 6, 4);
lean_closure_set(v___f_3625_, 0, v___x_3624_);
lean_closure_set(v___f_3625_, 1, v___f_3623_);
lean_closure_set(v___f_3625_, 2, v_inst_3281_);
lean_closure_set(v___f_3625_, 3, v___f_3623_);
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3626_, v___x_3619_, v___x_3618_, v___f_3625_);
return v___x_3627_;
}
}
}
case 4:
{
lean_object* v_onFailure_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; 
lean_dec_ref(v_config_3283_);
lean_dec_ref(v_inst_3281_);
v_onFailure_3628_ = lean_ctor_get(v_inst_3280_, 2);
lean_inc_ref(v_onFailure_3628_);
lean_dec_ref(v_inst_3280_);
v___x_3629_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_3630_ = lean_apply_3(v_onFailure_3628_, v_handler_3282_, v___x_3629_, lean_box(0));
v___f_3631_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 3, 1);
lean_closure_set(v___f_3631_, 0, v_state_3285_);
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = 0;
v___x_3634_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3632_, v___x_3633_, v___x_3630_, v___f_3631_);
return v___x_3634_;
}
case 5:
{
lean_object* v_machine_3635_; lean_object* v_requestStream_3636_; lean_object* v_keepAliveTimeout_3637_; lean_object* v_currentTimeout_3638_; lean_object* v_headerTimeout_3639_; lean_object* v_response_3640_; lean_object* v_respStream_3641_; uint8_t v_requiresData_3642_; lean_object* v_expectData_3643_; lean_object* v_pendingHead_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v_config_3283_);
lean_dec(v_handler_3282_);
lean_dec_ref(v_inst_3281_);
lean_dec_ref(v_inst_3280_);
v_machine_3635_ = lean_ctor_get(v_state_3285_, 0);
v_requestStream_3636_ = lean_ctor_get(v_state_3285_, 1);
v_keepAliveTimeout_3637_ = lean_ctor_get(v_state_3285_, 2);
v_currentTimeout_3638_ = lean_ctor_get(v_state_3285_, 3);
v_headerTimeout_3639_ = lean_ctor_get(v_state_3285_, 4);
v_response_3640_ = lean_ctor_get(v_state_3285_, 5);
v_respStream_3641_ = lean_ctor_get(v_state_3285_, 6);
v_requiresData_3642_ = lean_ctor_get_uint8(v_state_3285_, sizeof(void*)*9);
v_expectData_3643_ = lean_ctor_get(v_state_3285_, 7);
v_pendingHead_3644_ = lean_ctor_get(v_state_3285_, 8);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_state_3285_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3646_ = v_state_3285_;
v_isShared_3647_ = v_isSharedCheck_3658_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_pendingHead_3644_);
lean_inc(v_expectData_3643_);
lean_inc(v_respStream_3641_);
lean_inc(v_response_3640_);
lean_inc(v_headerTimeout_3639_);
lean_inc(v_currentTimeout_3638_);
lean_inc(v_keepAliveTimeout_3637_);
lean_inc(v_requestStream_3636_);
lean_inc(v_machine_3635_);
lean_dec(v_state_3285_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3658_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3652_; 
v___x_3648_ = lean_box(55);
v___x_3649_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3635_, v___x_3648_);
v___x_3650_ = 0;
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3649_);
v___x_3652_ = v___x_3646_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_requestStream_3636_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_keepAliveTimeout_3637_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_currentTimeout_3638_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v_headerTimeout_3639_);
lean_ctor_set(v_reuseFailAlloc_3657_, 5, v_response_3640_);
lean_ctor_set(v_reuseFailAlloc_3657_, 6, v_respStream_3641_);
lean_ctor_set(v_reuseFailAlloc_3657_, 7, v_expectData_3643_);
lean_ctor_set(v_reuseFailAlloc_3657_, 8, v_pendingHead_3644_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*9, v_requiresData_3642_);
v___x_3652_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*9 + 1, v___x_3650_);
v___x_3653_ = lean_box(v___x_3650_);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
}
}
default: 
{
uint8_t v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_dec_ref(v_config_3283_);
lean_dec(v_handler_3282_);
lean_dec_ref(v_inst_3281_);
lean_dec_ref(v_inst_3280_);
v___x_3659_ = 1;
v___x_3660_ = lean_box(v___x_3659_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v_state_3285_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_handler_3666_, lean_object* v_config_3667_, lean_object* v_event_3668_, lean_object* v_state_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3664_, v_inst_3665_, v_handler_3666_, v_config_3667_, v_event_3668_, v_state_3669_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3672_, lean_object* v_00_u03b2_3673_, lean_object* v_inst_3674_, lean_object* v_inst_3675_, lean_object* v_handler_3676_, lean_object* v_config_3677_, lean_object* v_event_3678_, lean_object* v_state_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3674_, v_inst_3675_, v_handler_3676_, v_config_3677_, v_event_3678_, v_state_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3682_, lean_object* v_00_u03b2_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_handler_3686_, lean_object* v_config_3687_, lean_object* v_event_3688_, lean_object* v_state_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3682_, v_00_u03b2_3683_, v_inst_3684_, v_inst_3685_, v_handler_3686_, v_config_3687_, v_event_3688_, v_state_3689_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3692_, uint8_t v_handlerDispatched_3693_, lean_object* v_respStream_3694_, lean_object* v_currentTimeout_3695_, lean_object* v_keepAliveTimeout_3696_, lean_object* v_headerTimeout_3697_, lean_object* v_expectData_3698_, lean_object* v_response_3699_, lean_object* v_socket_3700_, uint8_t v_requiresData_3701_, uint8_t v_sentMessage_3702_, lean_object* v_reader_3703_, uint8_t v_requestBodyInterested_3704_, lean_object* v_requestBody_3705_){
_start:
{
lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3719_; 
if (v_requiresData_3701_ == 0)
{
if (v_handlerDispatched_3693_ == 0)
{
goto v___jp_3722_;
}
else
{
if (lean_obj_tag(v_respStream_3694_) == 0)
{
if (v_sentMessage_3702_ == 0)
{
lean_object* v_state_3726_; 
v_state_3726_ = lean_ctor_get(v_reader_3703_, 0);
if (lean_obj_tag(v_state_3726_) == 2)
{
if (v_requestBodyInterested_3704_ == 0)
{
lean_dec(v_socket_3700_);
goto v___jp_3724_;
}
else
{
goto v___jp_3722_;
}
}
else
{
lean_dec(v_socket_3700_);
goto v___jp_3724_;
}
}
else
{
goto v___jp_3722_;
}
}
else
{
goto v___jp_3722_;
}
}
}
else
{
goto v___jp_3722_;
}
v___jp_3707_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3715_, 0, v___y_3710_);
lean_ctor_set(v___x_3715_, 1, v___y_3713_);
lean_ctor_set(v___x_3715_, 2, v___y_3714_);
lean_ctor_set(v___x_3715_, 3, v___y_3708_);
lean_ctor_set(v___x_3715_, 4, v_requestBody_3705_);
lean_ctor_set(v___x_3715_, 5, v___y_3709_);
lean_ctor_set(v___x_3715_, 6, v___y_3711_);
lean_ctor_set(v___x_3715_, 7, v___y_3712_);
lean_ctor_set(v___x_3715_, 8, v_connectionContext_3692_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
v___jp_3718_:
{
if (v_handlerDispatched_3693_ == 0)
{
lean_object* v___x_3720_; 
lean_dec_ref(v_response_3699_);
v___x_3720_ = lean_box(0);
v___y_3708_ = v_respStream_3694_;
v___y_3709_ = v_currentTimeout_3695_;
v___y_3710_ = v___y_3719_;
v___y_3711_ = v_keepAliveTimeout_3696_;
v___y_3712_ = v_headerTimeout_3697_;
v___y_3713_ = v_expectData_3698_;
v___y_3714_ = v___x_3720_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3721_, 0, v_response_3699_);
v___y_3708_ = v_respStream_3694_;
v___y_3709_ = v_currentTimeout_3695_;
v___y_3710_ = v___y_3719_;
v___y_3711_ = v_keepAliveTimeout_3696_;
v___y_3712_ = v_headerTimeout_3697_;
v___y_3713_ = v_expectData_3698_;
v___y_3714_ = v___x_3721_;
goto v___jp_3707_;
}
}
v___jp_3722_:
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3723_, 0, v_socket_3700_);
v___y_3719_ = v___x_3723_;
goto v___jp_3718_;
}
v___jp_3724_:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_box(0);
v___y_3719_ = v___x_3725_;
goto v___jp_3718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3727_, lean_object* v_handlerDispatched_3728_, lean_object* v_respStream_3729_, lean_object* v_currentTimeout_3730_, lean_object* v_keepAliveTimeout_3731_, lean_object* v_headerTimeout_3732_, lean_object* v_expectData_3733_, lean_object* v_response_3734_, lean_object* v_socket_3735_, lean_object* v_requiresData_3736_, lean_object* v_sentMessage_3737_, lean_object* v_reader_3738_, lean_object* v_requestBodyInterested_3739_, lean_object* v_requestBody_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v_handlerDispatched_boxed_3742_; uint8_t v_requiresData_boxed_3743_; uint8_t v_sentMessage_boxed_3744_; uint8_t v_requestBodyInterested_boxed_3745_; lean_object* v_res_3746_; 
v_handlerDispatched_boxed_3742_ = lean_unbox(v_handlerDispatched_3728_);
v_requiresData_boxed_3743_ = lean_unbox(v_requiresData_3736_);
v_sentMessage_boxed_3744_ = lean_unbox(v_sentMessage_3737_);
v_requestBodyInterested_boxed_3745_ = lean_unbox(v_requestBodyInterested_3739_);
v_res_3746_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3727_, v_handlerDispatched_boxed_3742_, v_respStream_3729_, v_currentTimeout_3730_, v_keepAliveTimeout_3731_, v_headerTimeout_3732_, v_expectData_3733_, v_response_3734_, v_socket_3735_, v_requiresData_boxed_3743_, v_sentMessage_boxed_3744_, v_reader_3738_, v_requestBodyInterested_boxed_3745_, v_requestBody_3740_);
lean_dec_ref(v_reader_3738_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3747_, lean_object* v_x_3748_){
_start:
{
if (lean_obj_tag(v_x_3748_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v___f_3747_);
v_a_3750_ = lean_ctor_get(v_x_3748_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_x_3748_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3752_ = v_x_3748_;
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v_x_3748_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
return v___x_3756_;
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3760_; 
v_a_3759_ = lean_ctor_get(v_x_3748_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v_x_3748_);
v___x_3760_ = lean_apply_2(v___f_3747_, v_a_3759_, lean_box(0));
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3761_, lean_object* v_x_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3761_, v_x_3762_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3769_, uint8_t v_handlerDispatched_3770_, lean_object* v_respStream_3771_, lean_object* v_currentTimeout_3772_, lean_object* v_keepAliveTimeout_3773_, lean_object* v_headerTimeout_3774_, lean_object* v_expectData_3775_, lean_object* v_response_3776_, lean_object* v_socket_3777_, uint8_t v_requiresData_3778_, uint8_t v_sentMessage_3779_, lean_object* v_reader_3780_, uint8_t v_pullBodyStalled_3781_, uint8_t v_requestBodyOpen_3782_, lean_object* v_requestStream_3783_, uint8_t v_requestBodyInterested_3784_){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___f_3790_; lean_object* v___f_3791_; 
v___x_3786_ = lean_box(v_handlerDispatched_3770_);
v___x_3787_ = lean_box(v_requiresData_3778_);
v___x_3788_ = lean_box(v_sentMessage_3779_);
v___x_3789_ = lean_box(v_requestBodyInterested_3784_);
lean_inc_ref(v_reader_3780_);
v___f_3790_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3790_, 0, v_connectionContext_3769_);
lean_closure_set(v___f_3790_, 1, v___x_3786_);
lean_closure_set(v___f_3790_, 2, v_respStream_3771_);
lean_closure_set(v___f_3790_, 3, v_currentTimeout_3772_);
lean_closure_set(v___f_3790_, 4, v_keepAliveTimeout_3773_);
lean_closure_set(v___f_3790_, 5, v_headerTimeout_3774_);
lean_closure_set(v___f_3790_, 6, v_expectData_3775_);
lean_closure_set(v___f_3790_, 7, v_response_3776_);
lean_closure_set(v___f_3790_, 8, v_socket_3777_);
lean_closure_set(v___f_3790_, 9, v___x_3787_);
lean_closure_set(v___f_3790_, 10, v___x_3788_);
lean_closure_set(v___f_3790_, 11, v_reader_3780_);
lean_closure_set(v___f_3790_, 12, v___x_3789_);
v___f_3791_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3791_, 0, v___f_3790_);
if (v_sentMessage_3779_ == 0)
{
lean_object* v_state_3797_; 
v_state_3797_ = lean_ctor_get(v_reader_3780_, 0);
lean_inc(v_state_3797_);
lean_dec_ref(v_reader_3780_);
if (lean_obj_tag(v_state_3797_) == 2)
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3808_; 
v_isSharedCheck_3808_ = !lean_is_exclusive(v_state_3797_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v_state_3797_, 0);
lean_dec(v_unused_3809_);
v___x_3799_ = v_state_3797_;
v_isShared_3800_ = v_isSharedCheck_3808_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v_state_3797_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3808_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
if (v_pullBodyStalled_3781_ == 0)
{
if (v_requestBodyOpen_3782_ == 0)
{
lean_del_object(v___x_3799_);
lean_dec_ref(v_requestStream_3783_);
goto v___jp_3792_;
}
else
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set_tag(v___x_3799_, 1);
lean_ctor_set(v___x_3799_, 0, v_requestStream_3783_);
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_requestStream_3783_);
v___x_3802_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3805_, v_pullBodyStalled_3781_, v___x_3804_, v___f_3791_);
return v___x_3806_;
}
}
}
else
{
lean_del_object(v___x_3799_);
lean_dec_ref(v_requestStream_3783_);
goto v___jp_3792_;
}
}
}
else
{
lean_dec(v_state_3797_);
lean_dec_ref(v_requestStream_3783_);
goto v___jp_3792_;
}
}
else
{
lean_dec_ref(v_requestStream_3783_);
lean_dec_ref(v_reader_3780_);
goto v___jp_3792_;
}
v___jp_3792_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3793_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = 0;
v___x_3796_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3794_, v___x_3795_, v___x_3793_, v___f_3791_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3810_ = _args[0];
lean_object* v_handlerDispatched_3811_ = _args[1];
lean_object* v_respStream_3812_ = _args[2];
lean_object* v_currentTimeout_3813_ = _args[3];
lean_object* v_keepAliveTimeout_3814_ = _args[4];
lean_object* v_headerTimeout_3815_ = _args[5];
lean_object* v_expectData_3816_ = _args[6];
lean_object* v_response_3817_ = _args[7];
lean_object* v_socket_3818_ = _args[8];
lean_object* v_requiresData_3819_ = _args[9];
lean_object* v_sentMessage_3820_ = _args[10];
lean_object* v_reader_3821_ = _args[11];
lean_object* v_pullBodyStalled_3822_ = _args[12];
lean_object* v_requestBodyOpen_3823_ = _args[13];
lean_object* v_requestStream_3824_ = _args[14];
lean_object* v_requestBodyInterested_3825_ = _args[15];
lean_object* v___y_3826_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3827_; uint8_t v_requiresData_boxed_3828_; uint8_t v_sentMessage_boxed_3829_; uint8_t v_pullBodyStalled_boxed_3830_; uint8_t v_requestBodyOpen_boxed_3831_; uint8_t v_requestBodyInterested_boxed_3832_; lean_object* v_res_3833_; 
v_handlerDispatched_boxed_3827_ = lean_unbox(v_handlerDispatched_3811_);
v_requiresData_boxed_3828_ = lean_unbox(v_requiresData_3819_);
v_sentMessage_boxed_3829_ = lean_unbox(v_sentMessage_3820_);
v_pullBodyStalled_boxed_3830_ = lean_unbox(v_pullBodyStalled_3822_);
v_requestBodyOpen_boxed_3831_ = lean_unbox(v_requestBodyOpen_3823_);
v_requestBodyInterested_boxed_3832_ = lean_unbox(v_requestBodyInterested_3825_);
v_res_3833_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3810_, v_handlerDispatched_boxed_3827_, v_respStream_3812_, v_currentTimeout_3813_, v_keepAliveTimeout_3814_, v_headerTimeout_3815_, v_expectData_3816_, v_response_3817_, v_socket_3818_, v_requiresData_boxed_3828_, v_sentMessage_boxed_3829_, v_reader_3821_, v_pullBodyStalled_boxed_3830_, v_requestBodyOpen_boxed_3831_, v_requestStream_3824_, v_requestBodyInterested_boxed_3832_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3834_, lean_object* v_x_3835_){
_start:
{
if (lean_obj_tag(v_x_3835_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v___f_3834_);
v_a_3837_ = lean_ctor_get(v_x_3835_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_x_3835_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3839_ = v_x_3835_;
v_isShared_3840_ = v_isSharedCheck_3845_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v_x_3835_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3845_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3847_; 
v_a_3846_ = lean_ctor_get(v_x_3835_, 0);
lean_inc(v_a_3846_);
lean_dec_ref(v_x_3835_);
v___x_3847_ = lean_apply_2(v___f_3834_, v_a_3846_, lean_box(0));
return v___x_3847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3848_, lean_object* v_x_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3848_, v_x_3849_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3857_, uint8_t v_handlerDispatched_3858_, lean_object* v_respStream_3859_, lean_object* v_currentTimeout_3860_, lean_object* v_keepAliveTimeout_3861_, lean_object* v_headerTimeout_3862_, lean_object* v_expectData_3863_, lean_object* v_response_3864_, lean_object* v_socket_3865_, uint8_t v_requiresData_3866_, uint8_t v_sentMessage_3867_, lean_object* v_reader_3868_, uint8_t v_pullBodyStalled_3869_, lean_object* v_requestStream_3870_, uint8_t v_requestBodyOpen_3871_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___f_3878_; lean_object* v___f_3879_; 
v___x_3873_ = lean_box(v_handlerDispatched_3858_);
v___x_3874_ = lean_box(v_requiresData_3866_);
v___x_3875_ = lean_box(v_sentMessage_3867_);
v___x_3876_ = lean_box(v_pullBodyStalled_3869_);
v___x_3877_ = lean_box(v_requestBodyOpen_3871_);
lean_inc_ref(v_requestStream_3870_);
lean_inc_ref(v_reader_3868_);
v___f_3878_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3878_, 0, v_connectionContext_3857_);
lean_closure_set(v___f_3878_, 1, v___x_3873_);
lean_closure_set(v___f_3878_, 2, v_respStream_3859_);
lean_closure_set(v___f_3878_, 3, v_currentTimeout_3860_);
lean_closure_set(v___f_3878_, 4, v_keepAliveTimeout_3861_);
lean_closure_set(v___f_3878_, 5, v_headerTimeout_3862_);
lean_closure_set(v___f_3878_, 6, v_expectData_3863_);
lean_closure_set(v___f_3878_, 7, v_response_3864_);
lean_closure_set(v___f_3878_, 8, v_socket_3865_);
lean_closure_set(v___f_3878_, 9, v___x_3874_);
lean_closure_set(v___f_3878_, 10, v___x_3875_);
lean_closure_set(v___f_3878_, 11, v_reader_3868_);
lean_closure_set(v___f_3878_, 12, v___x_3876_);
lean_closure_set(v___f_3878_, 13, v___x_3877_);
lean_closure_set(v___f_3878_, 14, v_requestStream_3870_);
v___f_3879_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3879_, 0, v___f_3878_);
if (v_sentMessage_3867_ == 0)
{
lean_object* v_state_3885_; 
v_state_3885_ = lean_ctor_get(v_reader_3868_, 0);
lean_inc(v_state_3885_);
lean_dec_ref(v_reader_3868_);
if (lean_obj_tag(v_state_3885_) == 2)
{
lean_dec_ref(v_state_3885_);
if (v_requestBodyOpen_3871_ == 0)
{
lean_dec_ref(v_requestStream_3870_);
goto v___jp_3880_;
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3870_);
v___x_3887_ = lean_unsigned_to_nat(0u);
v___x_3888_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3887_, v_sentMessage_3867_, v___x_3886_, v___f_3879_);
return v___x_3888_;
}
}
else
{
lean_dec(v_state_3885_);
lean_dec_ref(v_requestStream_3870_);
goto v___jp_3880_;
}
}
else
{
lean_dec_ref(v_requestStream_3870_);
lean_dec_ref(v_reader_3868_);
goto v___jp_3880_;
}
v___jp_3880_:
{
uint8_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3881_ = 0;
v___x_3882_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3883_, v___x_3881_, v___x_3882_, v___f_3879_);
return v___x_3884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3889_, lean_object* v_handlerDispatched_3890_, lean_object* v_respStream_3891_, lean_object* v_currentTimeout_3892_, lean_object* v_keepAliveTimeout_3893_, lean_object* v_headerTimeout_3894_, lean_object* v_expectData_3895_, lean_object* v_response_3896_, lean_object* v_socket_3897_, lean_object* v_requiresData_3898_, lean_object* v_sentMessage_3899_, lean_object* v_reader_3900_, lean_object* v_pullBodyStalled_3901_, lean_object* v_requestStream_3902_, lean_object* v_requestBodyOpen_3903_, lean_object* v___y_3904_){
_start:
{
uint8_t v_handlerDispatched_boxed_3905_; uint8_t v_requiresData_boxed_3906_; uint8_t v_sentMessage_boxed_3907_; uint8_t v_pullBodyStalled_boxed_3908_; uint8_t v_requestBodyOpen_boxed_3909_; lean_object* v_res_3910_; 
v_handlerDispatched_boxed_3905_ = lean_unbox(v_handlerDispatched_3890_);
v_requiresData_boxed_3906_ = lean_unbox(v_requiresData_3898_);
v_sentMessage_boxed_3907_ = lean_unbox(v_sentMessage_3899_);
v_pullBodyStalled_boxed_3908_ = lean_unbox(v_pullBodyStalled_3901_);
v_requestBodyOpen_boxed_3909_ = lean_unbox(v_requestBodyOpen_3903_);
v_res_3910_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3889_, v_handlerDispatched_boxed_3905_, v_respStream_3891_, v_currentTimeout_3892_, v_keepAliveTimeout_3893_, v_headerTimeout_3894_, v_expectData_3895_, v_response_3896_, v_socket_3897_, v_requiresData_boxed_3906_, v_sentMessage_boxed_3907_, v_reader_3900_, v_pullBodyStalled_boxed_3908_, v_requestStream_3902_, v_requestBodyOpen_boxed_3909_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3911_, lean_object* v___f_3912_, uint8_t v___x_3913_, lean_object* v_x_3914_){
_start:
{
uint8_t v___y_3917_; 
if (lean_obj_tag(v_x_3914_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v___f_3912_);
v_a_3923_ = lean_ctor_get(v_x_3914_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_x_3914_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3925_ = v_x_3914_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v_x_3914_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
}
}
else
{
lean_object* v_a_3932_; uint8_t v___x_3933_; 
v_a_3932_ = lean_ctor_get(v_x_3914_, 0);
lean_inc(v_a_3932_);
lean_dec_ref(v_x_3914_);
v___x_3933_ = lean_unbox(v_a_3932_);
lean_dec(v_a_3932_);
if (v___x_3933_ == 0)
{
v___y_3917_ = v___x_3913_;
goto v___jp_3916_;
}
else
{
v___y_3917_ = v_sentMessage_3911_;
goto v___jp_3916_;
}
}
v___jp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3918_ = lean_box(v___y_3917_);
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___x_3921_ = lean_unsigned_to_nat(0u);
v___x_3922_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3921_, v_sentMessage_3911_, v___x_3920_, v___f_3912_);
return v___x_3922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3934_, lean_object* v___f_3935_, lean_object* v___x_3936_, lean_object* v_x_3937_, lean_object* v___y_3938_){
_start:
{
uint8_t v_sentMessage_boxed_3939_; uint8_t v___x_3791__boxed_3940_; lean_object* v_res_3941_; 
v_sentMessage_boxed_3939_ = lean_unbox(v_sentMessage_3934_);
v___x_3791__boxed_3940_ = lean_unbox(v___x_3936_);
v_res_3941_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3939_, v___f_3935_, v___x_3791__boxed_3940_, v_x_3937_);
return v_res_3941_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___f_3942_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3943_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3944_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3945_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3945_, 0, lean_box(0));
lean_closure_set(v___x_3945_, 1, lean_box(0));
lean_closure_set(v___x_3945_, 2, lean_box(0));
lean_closure_set(v___x_3945_, 3, v___x_3944_);
lean_closure_set(v___x_3945_, 4, lean_box(0));
lean_closure_set(v___x_3945_, 5, lean_box(0));
lean_closure_set(v___x_3945_, 6, v___x_3943_);
lean_closure_set(v___x_3945_, 7, v___f_3942_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3946_, lean_object* v_connectionContext_3947_, lean_object* v_state_3948_){
_start:
{
lean_object* v_machine_3950_; lean_object* v_writer_3951_; lean_object* v_requestStream_3952_; lean_object* v_keepAliveTimeout_3953_; lean_object* v_currentTimeout_3954_; lean_object* v_headerTimeout_3955_; lean_object* v_response_3956_; lean_object* v_respStream_3957_; uint8_t v_requiresData_3958_; lean_object* v_expectData_3959_; uint8_t v_handlerDispatched_3960_; lean_object* v_reader_3961_; uint8_t v_pullBodyStalled_3962_; uint8_t v_sentMessage_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; lean_object* v___f_3969_; uint8_t v___y_3971_; 
v_machine_3950_ = lean_ctor_get(v_state_3948_, 0);
lean_inc_ref(v_machine_3950_);
v_writer_3951_ = lean_ctor_get(v_machine_3950_, 1);
lean_inc_ref(v_writer_3951_);
v_requestStream_3952_ = lean_ctor_get(v_state_3948_, 1);
lean_inc_ref_n(v_requestStream_3952_, 2);
v_keepAliveTimeout_3953_ = lean_ctor_get(v_state_3948_, 2);
lean_inc(v_keepAliveTimeout_3953_);
v_currentTimeout_3954_ = lean_ctor_get(v_state_3948_, 3);
lean_inc(v_currentTimeout_3954_);
v_headerTimeout_3955_ = lean_ctor_get(v_state_3948_, 4);
lean_inc(v_headerTimeout_3955_);
v_response_3956_ = lean_ctor_get(v_state_3948_, 5);
lean_inc_ref(v_response_3956_);
v_respStream_3957_ = lean_ctor_get(v_state_3948_, 6);
lean_inc(v_respStream_3957_);
v_requiresData_3958_ = lean_ctor_get_uint8(v_state_3948_, sizeof(void*)*9);
v_expectData_3959_ = lean_ctor_get(v_state_3948_, 7);
lean_inc(v_expectData_3959_);
v_handlerDispatched_3960_ = lean_ctor_get_uint8(v_state_3948_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3948_);
v_reader_3961_ = lean_ctor_get(v_machine_3950_, 0);
lean_inc_ref_n(v_reader_3961_, 2);
v_pullBodyStalled_3962_ = lean_ctor_get_uint8(v_machine_3950_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3950_);
v_sentMessage_3963_ = lean_ctor_get_uint8(v_writer_3951_, sizeof(void*)*6);
lean_dec_ref(v_writer_3951_);
v___x_3964_ = lean_box(v_handlerDispatched_3960_);
v___x_3965_ = lean_box(v_requiresData_3958_);
v___x_3966_ = lean_box(v_sentMessage_3963_);
v___x_3967_ = lean_box(v_pullBodyStalled_3962_);
v___f_3968_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3968_, 0, v_connectionContext_3947_);
lean_closure_set(v___f_3968_, 1, v___x_3964_);
lean_closure_set(v___f_3968_, 2, v_respStream_3957_);
lean_closure_set(v___f_3968_, 3, v_currentTimeout_3954_);
lean_closure_set(v___f_3968_, 4, v_keepAliveTimeout_3953_);
lean_closure_set(v___f_3968_, 5, v_headerTimeout_3955_);
lean_closure_set(v___f_3968_, 6, v_expectData_3959_);
lean_closure_set(v___f_3968_, 7, v_response_3956_);
lean_closure_set(v___f_3968_, 8, v_socket_3946_);
lean_closure_set(v___f_3968_, 9, v___x_3965_);
lean_closure_set(v___f_3968_, 10, v___x_3966_);
lean_closure_set(v___f_3968_, 11, v_reader_3961_);
lean_closure_set(v___f_3968_, 12, v___x_3967_);
lean_closure_set(v___f_3968_, 13, v_requestStream_3952_);
v___f_3969_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3969_, 0, v___f_3968_);
if (v_sentMessage_3963_ == 0)
{
lean_object* v_state_3977_; 
v_state_3977_ = lean_ctor_get(v_reader_3961_, 0);
lean_inc(v_state_3977_);
lean_dec_ref(v_reader_3961_);
if (lean_obj_tag(v_state_3977_) == 2)
{
lean_object* v___x_3978_; lean_object* v___f_3979_; lean_object* v___f_3980_; lean_object* v___x_3981_; lean_object* v___x_3305__overap_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___f_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_dec_ref(v_state_3977_);
v___x_3978_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3979_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3980_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3981_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3305__overap_3982_ = l_Std_Mutex_atomically___redArg(v___x_3978_, v___f_3979_, v___f_3980_, v_requestStream_3952_, v___x_3981_);
v___x_3983_ = lean_apply_1(v___x_3305__overap_3982_, lean_box(0));
v___x_3984_ = 1;
v___x_3985_ = lean_box(v_sentMessage_3963_);
v___x_3986_ = lean_box(v___x_3984_);
v___f_3987_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3987_, 0, v___x_3985_);
lean_closure_set(v___f_3987_, 1, v___f_3969_);
lean_closure_set(v___f_3987_, 2, v___x_3986_);
v___x_3988_ = lean_unsigned_to_nat(0u);
v___x_3989_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3988_, v_sentMessage_3963_, v___x_3983_, v___f_3987_);
return v___x_3989_;
}
else
{
lean_dec(v_state_3977_);
lean_dec_ref(v_requestStream_3952_);
v___y_3971_ = v_sentMessage_3963_;
goto v___jp_3970_;
}
}
else
{
uint8_t v___x_3990_; 
lean_dec_ref(v_reader_3961_);
lean_dec_ref(v_requestStream_3952_);
v___x_3990_ = 0;
v___y_3971_ = v___x_3990_;
goto v___jp_3970_;
}
v___jp_3970_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3972_ = lean_box(v___y_3971_);
v___x_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
v___x_3975_ = lean_unsigned_to_nat(0u);
v___x_3976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3975_, v___y_3971_, v___x_3974_, v___f_3969_);
return v___x_3976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3991_, lean_object* v_connectionContext_3992_, lean_object* v_state_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3991_, v_connectionContext_3992_, v_state_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3996_, lean_object* v_00_u03b2_3997_, lean_object* v_inst_3998_, lean_object* v_socket_3999_, lean_object* v_connectionContext_4000_, lean_object* v_state_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3999_, v_connectionContext_4000_, v_state_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4004_, lean_object* v_00_u03b2_4005_, lean_object* v_inst_4006_, lean_object* v_socket_4007_, lean_object* v_connectionContext_4008_, lean_object* v_state_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4004_, v_00_u03b2_4005_, v_inst_4006_, v_socket_4007_, v_connectionContext_4008_, v_state_4009_);
lean_dec_ref(v_inst_4006_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4012_){
_start:
{
if (lean_obj_tag(v_x_4012_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4022_; 
v_a_4014_ = lean_ctor_get(v_x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4016_ = v_x_4012_;
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v_x_4012_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
return v___x_4020_;
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4041_; 
v_a_4023_ = lean_ctor_get(v_x_4012_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4025_ = v_x_4012_;
v_isShared_4026_ = v_isSharedCheck_4041_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v_x_4012_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4041_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v_snd_4027_; uint8_t v___x_4028_; 
v_snd_4027_ = lean_ctor_get(v_a_4023_, 1);
v___x_4028_ = lean_unbox(v_snd_4027_);
if (v___x_4028_ == 0)
{
lean_object* v_fst_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v_fst_4029_ = lean_ctor_get(v_a_4023_, 0);
lean_inc(v_fst_4029_);
lean_dec(v_a_4023_);
v___x_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4030_, 0, v_fst_4029_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4030_);
v___x_4032_ = v___x_4025_;
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
else
{
lean_object* v_fst_4035_; lean_object* v___x_4036_; lean_object* v___x_4038_; 
v_fst_4035_ = lean_ctor_get(v_a_4023_, 0);
lean_inc(v_fst_4035_);
lean_dec(v_a_4023_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_fst_4035_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4036_);
v___x_4038_ = v___x_4025_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
return v___x_4039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4045_){
_start:
{
if (lean_obj_tag(v_x_4045_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4055_; 
v_a_4047_ = lean_ctor_get(v_x_4045_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_x_4045_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4049_ = v_x_4045_;
v_isShared_4050_ = v_isSharedCheck_4055_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v_x_4045_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4055_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
return v___x_4053_;
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4065_; 
v_a_4056_ = lean_ctor_get(v_x_4045_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_x_4045_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4058_ = v_x_4045_;
v_isShared_4059_ = v_isSharedCheck_4065_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v_x_4045_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4065_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_a_4056_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4060_);
v___x_4062_ = v___x_4058_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; 
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
return v___x_4063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4073_){
_start:
{
if (lean_obj_tag(v_x_4073_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4083_; 
v_a_4075_ = lean_ctor_get(v_x_4073_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_x_4073_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4077_ = v_x_4073_;
v_isShared_4078_ = v_isSharedCheck_4083_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v_x_4073_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4083_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
}
}
else
{
lean_object* v___x_4084_; 
lean_dec_ref(v_x_4073_);
v___x_4084_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4085_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4088_, lean_object* v_handler_4089_, lean_object* v___f_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; 
v_a_4093_ = lean_ctor_get(v_x_4091_, 0);
lean_inc(v_a_4093_);
lean_dec_ref(v_x_4091_);
v___x_4094_ = lean_apply_3(v_onFailure_4088_, v_handler_4089_, v_a_4093_, lean_box(0));
v___x_4095_ = lean_unsigned_to_nat(0u);
v___x_4096_ = 0;
v___x_4097_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4095_, v___x_4096_, v___x_4094_, v___f_4090_);
return v___x_4097_;
}
else
{
lean_object* v___x_4098_; 
lean_dec_ref(v___f_4090_);
lean_dec(v_handler_4089_);
lean_dec_ref(v_onFailure_4088_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_x_4091_);
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4099_, lean_object* v_handler_4100_, lean_object* v___f_4101_, lean_object* v_x_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4099_, v_handler_4100_, v___f_4101_, v_x_4102_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4105_, lean_object* v_socket_4106_, lean_object* v_____r_4107_){
_start:
{
lean_object* v_val_4110_; lean_object* v_close_4112_; lean_object* v___x_4113_; 
v_close_4112_ = lean_ctor_get(v_inst_4105_, 3);
lean_inc_ref(v_close_4112_);
lean_dec_ref(v_inst_4105_);
v___x_4113_ = lean_apply_2(v_close_4112_, v_socket_4106_, lean_box(0));
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 1);
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
v_val_4110_ = v___x_4119_;
goto v___jp_4109_;
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
v_a_4122_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4113_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4113_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
lean_ctor_set_tag(v___x_4124_, 0);
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
v_val_4110_ = v___x_4127_;
goto v___jp_4109_;
}
}
}
v___jp_4109_:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_val_4110_);
return v___x_4111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4130_, lean_object* v_socket_4131_, lean_object* v_____r_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4130_, v_socket_4131_, v_____r_4132_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4135_, lean_object* v_x_4136_){
_start:
{
if (lean_obj_tag(v_x_4136_) == 0)
{
lean_object* v___x_4138_; 
lean_dec_ref(v___f_4135_);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v_x_4136_);
return v___x_4138_;
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4140_; 
v_a_4139_ = lean_ctor_get(v_x_4136_, 0);
lean_inc(v_a_4139_);
lean_dec_ref(v_x_4136_);
v___x_4140_ = lean_apply_2(v___f_4135_, v_a_4139_, lean_box(0));
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4141_, lean_object* v_x_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4141_, v_x_4142_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4145_, lean_object* v_val_4146_, lean_object* v___f_4147_, lean_object* v___f_4148_, lean_object* v_x_4149_){
_start:
{
if (lean_obj_tag(v_x_4149_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4159_; 
lean_dec_ref(v___f_4148_);
lean_dec_ref(v___f_4147_);
lean_dec(v_val_4146_);
lean_dec_ref(v_close_4145_);
v_a_4151_ = lean_ctor_get(v_x_4149_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_x_4149_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4153_ = v_x_4149_;
v_isShared_4154_ = v_isSharedCheck_4159_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v_x_4149_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4159_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
return v___x_4157_;
}
}
}
else
{
lean_object* v_a_4160_; uint8_t v___x_4161_; 
v_a_4160_ = lean_ctor_get(v_x_4149_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v_x_4149_);
v___x_4161_ = lean_unbox(v_a_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; lean_object* v___x_4165_; 
lean_dec_ref(v___f_4148_);
v___x_4162_ = lean_apply_2(v_close_4145_, v_val_4146_, lean_box(0));
v___x_4163_ = lean_unsigned_to_nat(0u);
v___x_4164_ = lean_unbox(v_a_4160_);
lean_dec(v_a_4160_);
v___x_4165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4163_, v___x_4164_, v___x_4162_, v___f_4147_);
return v___x_4165_;
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_dec(v_a_4160_);
lean_dec_ref(v___f_4147_);
lean_dec(v_val_4146_);
lean_dec_ref(v_close_4145_);
v___x_4166_ = lean_box(0);
v___x_4167_ = lean_apply_2(v___f_4148_, v___x_4166_, lean_box(0));
return v___x_4167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4168_, lean_object* v_val_4169_, lean_object* v___f_4170_, lean_object* v___f_4171_, lean_object* v_x_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4168_, v_val_4169_, v___f_4170_, v___f_4171_, v_x_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4175_, lean_object* v_responseBodyInstance_4176_, lean_object* v___f_4177_, lean_object* v___f_4178_, lean_object* v_____r_4179_){
_start:
{
if (lean_obj_tag(v_respStream_4175_) == 1)
{
lean_object* v_val_4181_; lean_object* v_close_4182_; lean_object* v_isClosed_4183_; lean_object* v___x_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; lean_object* v___x_4188_; 
v_val_4181_ = lean_ctor_get(v_respStream_4175_, 0);
lean_inc_n(v_val_4181_, 2);
lean_dec_ref(v_respStream_4175_);
v_close_4182_ = lean_ctor_get(v_responseBodyInstance_4176_, 1);
lean_inc_ref(v_close_4182_);
v_isClosed_4183_ = lean_ctor_get(v_responseBodyInstance_4176_, 2);
lean_inc_ref(v_isClosed_4183_);
lean_dec_ref(v_responseBodyInstance_4176_);
v___x_4184_ = lean_apply_2(v_isClosed_4183_, v_val_4181_, lean_box(0));
v___f_4185_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4185_, 0, v_close_4182_);
lean_closure_set(v___f_4185_, 1, v_val_4181_);
lean_closure_set(v___f_4185_, 2, v___f_4177_);
lean_closure_set(v___f_4185_, 3, v___f_4178_);
v___x_4186_ = lean_unsigned_to_nat(0u);
v___x_4187_ = 0;
v___x_4188_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4186_, v___x_4187_, v___x_4184_, v___f_4185_);
return v___x_4188_;
}
else
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
lean_dec_ref(v___f_4177_);
lean_dec_ref(v_responseBodyInstance_4176_);
lean_dec(v_respStream_4175_);
v___x_4189_ = lean_box(0);
v___x_4190_ = lean_apply_2(v___f_4178_, v___x_4189_, lean_box(0));
return v___x_4190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4191_, lean_object* v_responseBodyInstance_4192_, lean_object* v___f_4193_, lean_object* v___f_4194_, lean_object* v_____r_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4191_, v_responseBodyInstance_4192_, v___f_4193_, v___f_4194_, v_____r_4195_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4198_, lean_object* v___f_4199_, lean_object* v___f_4200_, lean_object* v_x_4201_){
_start:
{
if (lean_obj_tag(v_x_4201_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4211_; 
lean_dec_ref(v___f_4200_);
lean_dec_ref(v___f_4199_);
lean_dec_ref(v_requestStream_4198_);
v_a_4203_ = lean_ctor_get(v_x_4201_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_x_4201_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4205_ = v_x_4201_;
v_isShared_4206_ = v_isSharedCheck_4211_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v_x_4201_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4211_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
lean_object* v___x_4209_; 
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
}
}
else
{
lean_object* v_a_4212_; uint8_t v___x_4213_; 
v_a_4212_ = lean_ctor_get(v_x_4201_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v_x_4201_);
v___x_4213_ = lean_unbox(v_a_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; lean_object* v___x_4217_; 
lean_dec_ref(v___f_4200_);
v___x_4214_ = l_Std_Http_Body_Stream_close(v_requestStream_4198_);
v___x_4215_ = lean_unsigned_to_nat(0u);
v___x_4216_ = lean_unbox(v_a_4212_);
lean_dec(v_a_4212_);
v___x_4217_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4215_, v___x_4216_, v___x_4214_, v___f_4199_);
return v___x_4217_;
}
else
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
lean_dec(v_a_4212_);
lean_dec_ref(v___f_4199_);
lean_dec_ref(v_requestStream_4198_);
v___x_4218_ = lean_box(0);
v___x_4219_ = lean_apply_2(v___f_4200_, v___x_4218_, lean_box(0));
return v___x_4219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4220_, lean_object* v___f_4221_, lean_object* v___f_4222_, lean_object* v_x_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4220_, v___f_4221_, v___f_4222_, v_x_4223_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4226_, lean_object* v_responseBodyInstance_4227_, lean_object* v___f_4228_, lean_object* v___f_4229_, lean_object* v_x_4230_){
_start:
{
if (lean_obj_tag(v_x_4230_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4240_; 
lean_dec_ref(v___f_4229_);
lean_dec_ref(v___f_4228_);
lean_dec_ref(v_responseBodyInstance_4227_);
lean_dec_ref(v___f_4226_);
v_a_4232_ = lean_ctor_get(v_x_4230_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v_x_4230_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4234_ = v_x_4230_;
v_isShared_4235_ = v_isSharedCheck_4240_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v_x_4230_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4240_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v_requestStream_4242_; lean_object* v_respStream_4243_; lean_object* v___x_4244_; lean_object* v___f_4245_; lean_object* v___f_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_5017__overap_4249_; lean_object* v___x_4250_; lean_object* v___f_4251_; lean_object* v___f_4252_; lean_object* v___f_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; lean_object* v___x_4256_; 
v_a_4241_ = lean_ctor_get(v_x_4230_, 0);
lean_inc(v_a_4241_);
lean_dec_ref(v_x_4230_);
v_requestStream_4242_ = lean_ctor_get(v_a_4241_, 1);
lean_inc_ref_n(v_requestStream_4242_, 2);
v_respStream_4243_ = lean_ctor_get(v_a_4241_, 6);
lean_inc(v_respStream_4243_);
lean_dec(v_a_4241_);
v___x_4244_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4245_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4246_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4247_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4248_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_4248_, 0, lean_box(0));
lean_closure_set(v___x_4248_, 1, lean_box(0));
lean_closure_set(v___x_4248_, 2, lean_box(0));
lean_closure_set(v___x_4248_, 3, v___x_4244_);
lean_closure_set(v___x_4248_, 4, lean_box(0));
lean_closure_set(v___x_4248_, 5, lean_box(0));
lean_closure_set(v___x_4248_, 6, v___x_4247_);
lean_closure_set(v___x_4248_, 7, v___f_4226_);
v___x_5017__overap_4249_ = l_Std_Mutex_atomically___redArg(v___x_4244_, v___f_4245_, v___f_4246_, v_requestStream_4242_, v___x_4248_);
v___x_4250_ = lean_apply_1(v___x_5017__overap_4249_, lean_box(0));
v___f_4251_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4251_, 0, v_respStream_4243_);
lean_closure_set(v___f_4251_, 1, v_responseBodyInstance_4227_);
lean_closure_set(v___f_4251_, 2, v___f_4228_);
lean_closure_set(v___f_4251_, 3, v___f_4229_);
lean_inc_ref(v___f_4251_);
v___f_4252_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4252_, 0, v___f_4251_);
v___f_4253_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4253_, 0, v_requestStream_4242_);
lean_closure_set(v___f_4253_, 1, v___f_4252_);
lean_closure_set(v___f_4253_, 2, v___f_4251_);
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = 0;
v___x_4256_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4254_, v___x_4255_, v___x_4250_, v___f_4253_);
return v___x_4256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4257_, lean_object* v_responseBodyInstance_4258_, lean_object* v___f_4259_, lean_object* v___f_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4257_, v_responseBodyInstance_4258_, v___f_4259_, v___f_4260_, v_x_4261_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4264_, lean_object* v_responseBodyInstance_4265_, lean_object* v_handler_4266_, lean_object* v_config_4267_, lean_object* v___x_4268_, uint8_t v___x_4269_, lean_object* v___f_4270_, lean_object* v_x_4271_){
_start:
{
if (lean_obj_tag(v_x_4271_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4281_; 
lean_dec_ref(v___f_4270_);
lean_dec_ref(v___x_4268_);
lean_dec_ref(v_config_4267_);
lean_dec(v_handler_4266_);
lean_dec_ref(v_responseBodyInstance_4265_);
lean_dec_ref(v_h_4264_);
v_a_4273_ = lean_ctor_get(v_x_4271_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v_x_4271_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4275_ = v_x_4271_;
v_isShared_4276_ = v_isSharedCheck_4281_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v_x_4271_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4281_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4279_; 
v___x_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
return v___x_4279_;
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v_a_4282_ = lean_ctor_get(v_x_4271_, 0);
lean_inc(v_a_4282_);
lean_dec_ref(v_x_4271_);
v___x_4283_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4264_, v_responseBodyInstance_4265_, v_handler_4266_, v_config_4267_, v_a_4282_, v___x_4268_);
v___x_4284_ = lean_unsigned_to_nat(0u);
v___x_4285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4284_, v___x_4269_, v___x_4283_, v___f_4270_);
return v___x_4285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4286_, lean_object* v_responseBodyInstance_4287_, lean_object* v_handler_4288_, lean_object* v_config_4289_, lean_object* v___x_4290_, lean_object* v___x_4291_, lean_object* v___f_4292_, lean_object* v_x_4293_, lean_object* v___y_4294_){
_start:
{
uint8_t v___x_5688__boxed_4295_; lean_object* v_res_4296_; 
v___x_5688__boxed_4295_ = lean_unbox(v___x_4291_);
v_res_4296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4286_, v_responseBodyInstance_4287_, v_handler_4288_, v_config_4289_, v___x_4290_, v___x_5688__boxed_4295_, v___f_4292_, v_x_4293_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4297_, lean_object* v_h_4298_, lean_object* v_responseBodyInstance_4299_, lean_object* v_config_4300_, lean_object* v_handler_4301_, uint8_t v___x_4302_, lean_object* v___f_4303_, lean_object* v_x_4304_){
_start:
{
if (lean_obj_tag(v_x_4304_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4314_; 
lean_dec_ref(v___f_4303_);
lean_dec(v_handler_4301_);
lean_dec_ref(v_config_4300_);
lean_dec_ref(v_responseBodyInstance_4299_);
lean_dec_ref(v_h_4298_);
lean_dec_ref(v_inst_4297_);
v_a_4306_ = lean_ctor_get(v_x_4304_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v_x_4304_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4308_ = v_x_4304_;
v_isShared_4309_ = v_isSharedCheck_4314_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v_x_4304_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4314_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4312_; 
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
return v___x_4312_;
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_a_4315_ = lean_ctor_get(v_x_4304_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v_x_4304_);
v___x_4316_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4297_, v_h_4298_, v_responseBodyInstance_4299_, v_config_4300_, v_handler_4301_, v_a_4315_);
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4317_, v___x_4302_, v___x_4316_, v___f_4303_);
return v___x_4318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4319_, lean_object* v_h_4320_, lean_object* v_responseBodyInstance_4321_, lean_object* v_config_4322_, lean_object* v_handler_4323_, lean_object* v___x_4324_, lean_object* v___f_4325_, lean_object* v_x_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v___x_5729__boxed_4328_; lean_object* v_res_4329_; 
v___x_5729__boxed_4328_ = lean_unbox(v___x_4324_);
v_res_4329_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4319_, v_h_4320_, v_responseBodyInstance_4321_, v_config_4322_, v_handler_4323_, v___x_5729__boxed_4328_, v___f_4325_, v_x_4326_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4330_, lean_object* v_socket_4331_, lean_object* v_connectionContext_4332_, lean_object* v_h_4333_, lean_object* v_responseBodyInstance_4334_, lean_object* v_handler_4335_, lean_object* v_config_4336_, lean_object* v___f_4337_, lean_object* v_inst_4338_, lean_object* v_x_4339_){
_start:
{
if (lean_obj_tag(v_x_4339_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4349_; 
lean_dec_ref(v_inst_4338_);
lean_dec_ref(v___f_4337_);
lean_dec_ref(v_config_4336_);
lean_dec(v_handler_4335_);
lean_dec_ref(v_responseBodyInstance_4334_);
lean_dec_ref(v_h_4333_);
lean_dec_ref(v_connectionContext_4332_);
lean_dec(v_socket_4331_);
v_a_4341_ = lean_ctor_get(v_x_4339_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_x_4339_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4343_ = v_x_4339_;
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v_x_4339_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
return v___x_4347_;
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4384_; 
v_a_4350_ = lean_ctor_get(v_x_4339_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v_x_4339_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4352_ = v_x_4339_;
v_isShared_4353_ = v_isSharedCheck_4384_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v_x_4339_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4384_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v_machine_4360_; lean_object* v_requestStream_4361_; lean_object* v_keepAliveTimeout_4362_; lean_object* v_currentTimeout_4363_; lean_object* v_headerTimeout_4364_; lean_object* v_response_4365_; lean_object* v_respStream_4366_; uint8_t v_requiresData_4367_; lean_object* v_expectData_4368_; uint8_t v_handlerDispatched_4369_; lean_object* v_pendingHead_4370_; 
v_machine_4360_ = lean_ctor_get(v_a_4350_, 0);
v_requestStream_4361_ = lean_ctor_get(v_a_4350_, 1);
v_keepAliveTimeout_4362_ = lean_ctor_get(v_a_4350_, 2);
v_currentTimeout_4363_ = lean_ctor_get(v_a_4350_, 3);
v_headerTimeout_4364_ = lean_ctor_get(v_a_4350_, 4);
v_response_4365_ = lean_ctor_get(v_a_4350_, 5);
v_respStream_4366_ = lean_ctor_get(v_a_4350_, 6);
v_requiresData_4367_ = lean_ctor_get_uint8(v_a_4350_, sizeof(void*)*9);
v_expectData_4368_ = lean_ctor_get(v_a_4350_, 7);
v_handlerDispatched_4369_ = lean_ctor_get_uint8(v_a_4350_, sizeof(void*)*9 + 1);
v_pendingHead_4370_ = lean_ctor_get(v_a_4350_, 8);
if (v_requiresData_4367_ == 0)
{
if (v_handlerDispatched_4369_ == 0)
{
if (lean_obj_tag(v_respStream_4366_) == 0)
{
lean_object* v_writer_4380_; uint8_t v_sentMessage_4381_; 
v_writer_4380_ = lean_ctor_get(v_machine_4360_, 1);
v_sentMessage_4381_ = lean_ctor_get_uint8(v_writer_4380_, sizeof(void*)*6);
if (v_sentMessage_4381_ == 0)
{
lean_object* v_reader_4382_; lean_object* v_state_4383_; 
v_reader_4382_ = lean_ctor_get(v_machine_4360_, 0);
v_state_4383_ = lean_ctor_get(v_reader_4382_, 0);
if (lean_obj_tag(v_state_4383_) == 2)
{
lean_inc(v_respStream_4366_);
lean_inc(v_pendingHead_4370_);
lean_inc(v_expectData_4368_);
lean_inc_ref(v_response_4365_);
lean_inc(v_headerTimeout_4364_);
lean_inc(v_currentTimeout_4363_);
lean_inc(v_keepAliveTimeout_4362_);
lean_inc_ref(v_requestStream_4361_);
lean_inc_ref(v_machine_4360_);
lean_del_object(v___x_4352_);
lean_dec(v_a_4350_);
goto v___jp_4371_;
}
else
{
lean_dec_ref(v_inst_4338_);
lean_dec_ref(v___f_4337_);
lean_dec_ref(v_config_4336_);
lean_dec(v_handler_4335_);
lean_dec_ref(v_responseBodyInstance_4334_);
lean_dec_ref(v_h_4333_);
lean_dec_ref(v_connectionContext_4332_);
lean_dec(v_socket_4331_);
goto v___jp_4354_;
}
}
else
{
lean_dec_ref(v_inst_4338_);
lean_dec_ref(v___f_4337_);
lean_dec_ref(v_config_4336_);
lean_dec(v_handler_4335_);
lean_dec_ref(v_responseBodyInstance_4334_);
lean_dec_ref(v_h_4333_);
lean_dec_ref(v_connectionContext_4332_);
lean_dec(v_socket_4331_);
goto v___jp_4354_;
}
}
else
{
lean_inc_ref(v_respStream_4366_);
lean_inc(v_pendingHead_4370_);
lean_inc(v_expectData_4368_);
lean_inc_ref(v_response_4365_);
lean_inc(v_headerTimeout_4364_);
lean_inc(v_currentTimeout_4363_);
lean_inc(v_keepAliveTimeout_4362_);
lean_inc_ref(v_requestStream_4361_);
lean_inc_ref(v_machine_4360_);
lean_del_object(v___x_4352_);
lean_dec(v_a_4350_);
goto v___jp_4371_;
}
}
else
{
lean_inc(v_pendingHead_4370_);
lean_inc(v_expectData_4368_);
lean_inc(v_respStream_4366_);
lean_inc_ref(v_response_4365_);
lean_inc(v_headerTimeout_4364_);
lean_inc(v_currentTimeout_4363_);
lean_inc(v_keepAliveTimeout_4362_);
lean_inc_ref(v_requestStream_4361_);
lean_inc_ref(v_machine_4360_);
lean_del_object(v___x_4352_);
lean_dec(v_a_4350_);
goto v___jp_4371_;
}
}
else
{
lean_inc(v_pendingHead_4370_);
lean_inc(v_expectData_4368_);
lean_inc(v_respStream_4366_);
lean_inc_ref(v_response_4365_);
lean_inc(v_headerTimeout_4364_);
lean_inc(v_currentTimeout_4363_);
lean_inc(v_keepAliveTimeout_4362_);
lean_inc_ref(v_requestStream_4361_);
lean_inc_ref(v_machine_4360_);
lean_del_object(v___x_4352_);
lean_dec(v_a_4350_);
goto v___jp_4371_;
}
v___jp_4354_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4355_, 0, v_a_4350_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4355_);
v___x_4357_ = v___x_4352_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4355_);
v___x_4357_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; 
v___x_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
return v___x_4358_;
}
}
v___jp_4371_:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___f_4375_; lean_object* v___x_4376_; lean_object* v___f_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4372_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4372_, 0, v_machine_4360_);
lean_ctor_set(v___x_4372_, 1, v_requestStream_4361_);
lean_ctor_set(v___x_4372_, 2, v_keepAliveTimeout_4362_);
lean_ctor_set(v___x_4372_, 3, v_currentTimeout_4363_);
lean_ctor_set(v___x_4372_, 4, v_headerTimeout_4364_);
lean_ctor_set(v___x_4372_, 5, v_response_4365_);
lean_ctor_set(v___x_4372_, 6, v_respStream_4366_);
lean_ctor_set(v___x_4372_, 7, v_expectData_4368_);
lean_ctor_set(v___x_4372_, 8, v_pendingHead_4370_);
lean_ctor_set_uint8(v___x_4372_, sizeof(void*)*9, v___x_4330_);
lean_ctor_set_uint8(v___x_4372_, sizeof(void*)*9 + 1, v_handlerDispatched_4369_);
lean_inc_ref(v___x_4372_);
v___x_4373_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4331_, v_connectionContext_4332_, v___x_4372_);
v___x_4374_ = lean_box(v___x_4330_);
lean_inc_ref(v_config_4336_);
lean_inc(v_handler_4335_);
lean_inc_ref(v_responseBodyInstance_4334_);
lean_inc_ref(v_h_4333_);
v___f_4375_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4375_, 0, v_h_4333_);
lean_closure_set(v___f_4375_, 1, v_responseBodyInstance_4334_);
lean_closure_set(v___f_4375_, 2, v_handler_4335_);
lean_closure_set(v___f_4375_, 3, v_config_4336_);
lean_closure_set(v___f_4375_, 4, v___x_4372_);
lean_closure_set(v___f_4375_, 5, v___x_4374_);
lean_closure_set(v___f_4375_, 6, v___f_4337_);
v___x_4376_ = lean_box(v___x_4330_);
v___f_4377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4377_, 0, v_inst_4338_);
lean_closure_set(v___f_4377_, 1, v_h_4333_);
lean_closure_set(v___f_4377_, 2, v_responseBodyInstance_4334_);
lean_closure_set(v___f_4377_, 3, v_config_4336_);
lean_closure_set(v___f_4377_, 4, v_handler_4335_);
lean_closure_set(v___f_4377_, 5, v___x_4376_);
lean_closure_set(v___f_4377_, 6, v___f_4375_);
v___x_4378_ = lean_unsigned_to_nat(0u);
v___x_4379_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4378_, v___x_4330_, v___x_4373_, v___f_4377_);
return v___x_4379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4385_, lean_object* v_socket_4386_, lean_object* v_connectionContext_4387_, lean_object* v_h_4388_, lean_object* v_responseBodyInstance_4389_, lean_object* v_handler_4390_, lean_object* v_config_4391_, lean_object* v___f_4392_, lean_object* v_inst_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_){
_start:
{
uint8_t v___x_5769__boxed_4396_; lean_object* v_res_4397_; 
v___x_5769__boxed_4396_ = lean_unbox(v___x_4385_);
v_res_4397_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5769__boxed_4396_, v_socket_4386_, v_connectionContext_4387_, v_h_4388_, v_responseBodyInstance_4389_, v_handler_4390_, v_config_4391_, v___f_4392_, v_inst_4393_, v_x_4394_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4398_, lean_object* v_handler_4399_, lean_object* v_extensions_4400_, lean_object* v_connectionContext_4401_, uint8_t v___x_4402_, lean_object* v___f_4403_, lean_object* v_x_4404_){
_start:
{
if (lean_obj_tag(v_x_4404_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4414_; 
lean_dec_ref(v___f_4403_);
lean_dec_ref(v_connectionContext_4401_);
lean_dec(v_extensions_4400_);
lean_dec(v_handler_4399_);
lean_dec_ref(v_h_4398_);
v_a_4406_ = lean_ctor_get(v_x_4404_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v_x_4404_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4408_ = v_x_4404_;
v_isShared_4409_ = v_isSharedCheck_4414_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v_x_4404_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4414_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; 
v___x_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
return v___x_4412_;
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v_a_4415_ = lean_ctor_get(v_x_4404_, 0);
lean_inc(v_a_4415_);
lean_dec_ref(v_x_4404_);
v___x_4416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4398_, v_handler_4399_, v_extensions_4400_, v_connectionContext_4401_, v_a_4415_);
v___x_4417_ = lean_unsigned_to_nat(0u);
v___x_4418_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4417_, v___x_4402_, v___x_4416_, v___f_4403_);
return v___x_4418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4419_, lean_object* v_handler_4420_, lean_object* v_extensions_4421_, lean_object* v_connectionContext_4422_, lean_object* v___x_4423_, lean_object* v___f_4424_, lean_object* v_x_4425_, lean_object* v___y_4426_){
_start:
{
uint8_t v___x_5844__boxed_4427_; lean_object* v_res_4428_; 
v___x_5844__boxed_4427_ = lean_unbox(v___x_4423_);
v_res_4428_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4419_, v_handler_4420_, v_extensions_4421_, v_connectionContext_4422_, v___x_5844__boxed_4427_, v___f_4424_, v_x_4425_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4429_, lean_object* v_responseBodyInstance_4430_, lean_object* v_handler_4431_, lean_object* v_config_4432_, lean_object* v_connectionContext_4433_, lean_object* v_events_4434_, lean_object* v___x_4435_, uint8_t v___x_4436_, lean_object* v___f_4437_, lean_object* v_____r_4438_){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4429_, v_responseBodyInstance_4430_, v_handler_4431_, v_config_4432_, v_connectionContext_4433_, v_events_4434_, v___x_4435_);
v___x_4441_ = lean_unsigned_to_nat(0u);
v___x_4442_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4441_, v___x_4436_, v___x_4440_, v___f_4437_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4443_, lean_object* v_responseBodyInstance_4444_, lean_object* v_handler_4445_, lean_object* v_config_4446_, lean_object* v_connectionContext_4447_, lean_object* v_events_4448_, lean_object* v___x_4449_, lean_object* v___x_4450_, lean_object* v___f_4451_, lean_object* v_____r_4452_, lean_object* v___y_4453_){
_start:
{
uint8_t v___x_5883__boxed_4454_; lean_object* v_res_4455_; 
v___x_5883__boxed_4454_ = lean_unbox(v___x_4450_);
v_res_4455_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4443_, v_responseBodyInstance_4444_, v_handler_4445_, v_config_4446_, v_connectionContext_4447_, v_events_4448_, v___x_4449_, v___x_5883__boxed_4454_, v___f_4451_, v_____r_4452_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4456_, lean_object* v___f_4457_, lean_object* v_x_4458_){
_start:
{
if (lean_obj_tag(v_x_4458_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4468_; 
lean_dec_ref(v___f_4457_);
lean_dec_ref(v___x_4456_);
v_a_4460_ = lean_ctor_get(v_x_4458_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_x_4458_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4462_ = v_x_4458_;
v_isShared_4463_ = v_isSharedCheck_4468_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v_x_4458_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4468_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4466_; 
v___x_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
return v___x_4466_;
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4480_; 
v_a_4469_ = lean_ctor_get(v_x_4458_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v_x_4458_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4471_ = v_x_4458_;
v_isShared_4472_ = v_isSharedCheck_4480_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v_x_4458_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4480_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
if (lean_obj_tag(v_a_4469_) == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
lean_dec_ref(v___f_4457_);
v___x_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4456_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4473_);
v___x_4475_ = v___x_4471_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; 
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
}
else
{
lean_object* v_val_4478_; lean_object* v___x_4479_; 
lean_del_object(v___x_4471_);
lean_dec_ref(v___x_4456_);
v_val_4478_ = lean_ctor_get(v_a_4469_, 0);
lean_inc(v_val_4478_);
lean_dec_ref(v_a_4469_);
v___x_4479_ = lean_apply_2(v___f_4457_, v_val_4478_, lean_box(0));
return v___x_4479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4481_, lean_object* v___f_4482_, lean_object* v_x_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4481_, v___f_4482_, v_x_4483_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4486_, lean_object* v_responseBodyInstance_4487_, lean_object* v_handler_4488_, lean_object* v_config_4489_, lean_object* v_connectionContext_4490_, uint8_t v___x_4491_, lean_object* v___f_4492_, lean_object* v_inst_4493_, lean_object* v_socket_4494_, lean_object* v___f_4495_, lean_object* v___f_4496_, lean_object* v_x_4497_, lean_object* v_____s_4498_){
_start:
{
lean_object* v_machine_4500_; lean_object* v_reader_4501_; lean_object* v_requestStream_4502_; lean_object* v_keepAliveTimeout_4503_; lean_object* v_currentTimeout_4504_; lean_object* v_headerTimeout_4505_; lean_object* v_response_4506_; lean_object* v_respStream_4507_; uint8_t v_requiresData_4508_; lean_object* v_expectData_4509_; uint8_t v_handlerDispatched_4510_; lean_object* v_pendingHead_4511_; lean_object* v_writer_4512_; lean_object* v_state_4513_; uint8_t v___x_4514_; 
v_machine_4500_ = lean_ctor_get(v_____s_4498_, 0);
v_reader_4501_ = lean_ctor_get(v_machine_4500_, 0);
v_requestStream_4502_ = lean_ctor_get(v_____s_4498_, 1);
v_keepAliveTimeout_4503_ = lean_ctor_get(v_____s_4498_, 2);
v_currentTimeout_4504_ = lean_ctor_get(v_____s_4498_, 3);
v_headerTimeout_4505_ = lean_ctor_get(v_____s_4498_, 4);
v_response_4506_ = lean_ctor_get(v_____s_4498_, 5);
v_respStream_4507_ = lean_ctor_get(v_____s_4498_, 6);
v_requiresData_4508_ = lean_ctor_get_uint8(v_____s_4498_, sizeof(void*)*9);
v_expectData_4509_ = lean_ctor_get(v_____s_4498_, 7);
v_handlerDispatched_4510_ = lean_ctor_get_uint8(v_____s_4498_, sizeof(void*)*9 + 1);
v_pendingHead_4511_ = lean_ctor_get(v_____s_4498_, 8);
v_writer_4512_ = lean_ctor_get(v_machine_4500_, 1);
v_state_4513_ = lean_ctor_get(v_reader_4501_, 0);
v___x_4514_ = 0;
if (lean_obj_tag(v_state_4513_) == 6)
{
lean_object* v_state_4536_; 
v_state_4536_ = lean_ctor_get(v_writer_4512_, 2);
if (lean_obj_tag(v_state_4536_) == 7)
{
lean_object* v_outputData_4537_; lean_object* v_size_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v_outputData_4537_ = lean_ctor_get(v_writer_4512_, 1);
v_size_4538_ = lean_ctor_get(v_outputData_4537_, 1);
v___x_4539_ = lean_unsigned_to_nat(0u);
v___x_4540_ = lean_nat_dec_eq(v_size_4538_, v___x_4539_);
if (v___x_4540_ == 0)
{
lean_inc(v_pendingHead_4511_);
lean_inc(v_expectData_4509_);
lean_inc(v_respStream_4507_);
lean_inc_ref(v_response_4506_);
lean_inc(v_headerTimeout_4505_);
lean_inc(v_currentTimeout_4504_);
lean_inc(v_keepAliveTimeout_4503_);
lean_inc_ref(v_requestStream_4502_);
lean_inc_ref(v_machine_4500_);
lean_dec_ref(v_____s_4498_);
goto v___jp_4515_;
}
else
{
if (v___x_4540_ == 0)
{
lean_inc(v_pendingHead_4511_);
lean_inc(v_expectData_4509_);
lean_inc(v_respStream_4507_);
lean_inc_ref(v_response_4506_);
lean_inc(v_headerTimeout_4505_);
lean_inc(v_currentTimeout_4504_);
lean_inc(v_keepAliveTimeout_4503_);
lean_inc_ref(v_requestStream_4502_);
lean_inc_ref(v_machine_4500_);
lean_dec_ref(v_____s_4498_);
goto v___jp_4515_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec_ref(v___f_4496_);
lean_dec_ref(v___f_4495_);
lean_dec(v_socket_4494_);
lean_dec_ref(v_inst_4493_);
lean_dec_ref(v___f_4492_);
lean_dec_ref(v_connectionContext_4490_);
lean_dec_ref(v_config_4489_);
lean_dec(v_handler_4488_);
lean_dec_ref(v_responseBodyInstance_4487_);
lean_dec_ref(v_h_4486_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v_____s_4498_);
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
else
{
lean_inc(v_pendingHead_4511_);
lean_inc(v_expectData_4509_);
lean_inc(v_respStream_4507_);
lean_inc_ref(v_response_4506_);
lean_inc(v_headerTimeout_4505_);
lean_inc(v_currentTimeout_4504_);
lean_inc(v_keepAliveTimeout_4503_);
lean_inc_ref(v_requestStream_4502_);
lean_inc_ref(v_machine_4500_);
lean_dec_ref(v_____s_4498_);
goto v___jp_4515_;
}
}
else
{
lean_inc(v_pendingHead_4511_);
lean_inc(v_expectData_4509_);
lean_inc(v_respStream_4507_);
lean_inc_ref(v_response_4506_);
lean_inc(v_headerTimeout_4505_);
lean_inc(v_currentTimeout_4504_);
lean_inc(v_keepAliveTimeout_4503_);
lean_inc_ref(v_requestStream_4502_);
lean_inc_ref(v_machine_4500_);
lean_dec_ref(v_____s_4498_);
goto v___jp_4515_;
}
v___jp_4515_:
{
lean_object* v___x_4516_; lean_object* v_snd_4517_; lean_object* v_output_4518_; lean_object* v_fst_4519_; lean_object* v_events_4520_; lean_object* v_data_4521_; lean_object* v_size_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___f_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4516_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4514_, v_machine_4500_);
v_snd_4517_ = lean_ctor_get(v___x_4516_, 1);
lean_inc(v_snd_4517_);
v_output_4518_ = lean_ctor_get(v_snd_4517_, 1);
lean_inc_ref(v_output_4518_);
v_fst_4519_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_fst_4519_);
lean_dec_ref(v___x_4516_);
v_events_4520_ = lean_ctor_get(v_snd_4517_, 0);
lean_inc_ref_n(v_events_4520_, 2);
lean_dec(v_snd_4517_);
v_data_4521_ = lean_ctor_get(v_output_4518_, 0);
lean_inc_ref(v_data_4521_);
v_size_4522_ = lean_ctor_get(v_output_4518_, 1);
lean_inc(v_size_4522_);
lean_dec_ref(v_output_4518_);
v___x_4523_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4523_, 0, v_fst_4519_);
lean_ctor_set(v___x_4523_, 1, v_requestStream_4502_);
lean_ctor_set(v___x_4523_, 2, v_keepAliveTimeout_4503_);
lean_ctor_set(v___x_4523_, 3, v_currentTimeout_4504_);
lean_ctor_set(v___x_4523_, 4, v_headerTimeout_4505_);
lean_ctor_set(v___x_4523_, 5, v_response_4506_);
lean_ctor_set(v___x_4523_, 6, v_respStream_4507_);
lean_ctor_set(v___x_4523_, 7, v_expectData_4509_);
lean_ctor_set(v___x_4523_, 8, v_pendingHead_4511_);
lean_ctor_set_uint8(v___x_4523_, sizeof(void*)*9, v_requiresData_4508_);
lean_ctor_set_uint8(v___x_4523_, sizeof(void*)*9 + 1, v_handlerDispatched_4510_);
v___x_4524_ = lean_box(v___x_4491_);
lean_inc_ref(v___f_4492_);
lean_inc_ref(v___x_4523_);
lean_inc_ref(v_connectionContext_4490_);
lean_inc_ref(v_config_4489_);
lean_inc(v_handler_4488_);
lean_inc_ref(v_responseBodyInstance_4487_);
lean_inc_ref(v_h_4486_);
v___f_4525_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4525_, 0, v_h_4486_);
lean_closure_set(v___f_4525_, 1, v_responseBodyInstance_4487_);
lean_closure_set(v___f_4525_, 2, v_handler_4488_);
lean_closure_set(v___f_4525_, 3, v_config_4489_);
lean_closure_set(v___f_4525_, 4, v_connectionContext_4490_);
lean_closure_set(v___f_4525_, 5, v_events_4520_);
lean_closure_set(v___f_4525_, 6, v___x_4523_);
lean_closure_set(v___f_4525_, 7, v___x_4524_);
lean_closure_set(v___f_4525_, 8, v___f_4492_);
v___x_4526_ = lean_unsigned_to_nat(0u);
v___x_4527_ = lean_nat_dec_lt(v___x_4526_, v_size_4522_);
lean_dec(v_size_4522_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_dec_ref(v___f_4525_);
lean_dec_ref(v_data_4521_);
lean_dec_ref(v___f_4496_);
lean_dec_ref(v___f_4495_);
lean_dec(v_socket_4494_);
lean_dec_ref(v_inst_4493_);
v___x_4528_ = lean_box(0);
v___x_4529_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4486_, v_responseBodyInstance_4487_, v_handler_4488_, v_config_4489_, v_connectionContext_4490_, v_events_4520_, v___x_4523_, v___x_4491_, v___f_4492_, v___x_4528_);
return v___x_4529_;
}
else
{
lean_object* v_sendAll_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___f_4534_; lean_object* v___x_4535_; 
lean_dec_ref(v_events_4520_);
lean_dec_ref(v___f_4492_);
lean_dec_ref(v_connectionContext_4490_);
lean_dec_ref(v_config_4489_);
lean_dec(v_handler_4488_);
lean_dec_ref(v_responseBodyInstance_4487_);
lean_dec_ref(v_h_4486_);
v_sendAll_4530_ = lean_ctor_get(v_inst_4493_, 1);
lean_inc_ref(v_sendAll_4530_);
lean_dec_ref(v_inst_4493_);
v___x_4531_ = lean_apply_3(v_sendAll_4530_, v_socket_4494_, v_data_4521_, lean_box(0));
v___x_4532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4526_, v___x_4491_, v___x_4531_, v___f_4495_);
v___x_4533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4526_, v___x_4491_, v___x_4532_, v___f_4496_);
v___f_4534_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4534_, 0, v___x_4523_);
lean_closure_set(v___f_4534_, 1, v___f_4525_);
v___x_4535_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4526_, v___x_4491_, v___x_4533_, v___f_4534_);
return v___x_4535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4544_, lean_object* v_responseBodyInstance_4545_, lean_object* v_handler_4546_, lean_object* v_config_4547_, lean_object* v_connectionContext_4548_, lean_object* v___x_4549_, lean_object* v___f_4550_, lean_object* v_inst_4551_, lean_object* v_socket_4552_, lean_object* v___f_4553_, lean_object* v___f_4554_, lean_object* v_x_4555_, lean_object* v_____s_4556_, lean_object* v___y_4557_){
_start:
{
uint8_t v___x_5957__boxed_4558_; lean_object* v_res_4559_; 
v___x_5957__boxed_4558_ = lean_unbox(v___x_4549_);
v_res_4559_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4544_, v_responseBodyInstance_4545_, v_handler_4546_, v_config_4547_, v_connectionContext_4548_, v___x_5957__boxed_4558_, v___f_4550_, v_inst_4551_, v_socket_4552_, v___f_4553_, v___f_4554_, v_x_4555_, v_____s_4556_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4560_, lean_object* v_x_4561_){
_start:
{
if (lean_obj_tag(v_x_4561_) == 0)
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4571_; 
v_a_4563_ = lean_ctor_get(v_x_4561_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_x_4561_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4565_ = v_x_4561_;
v_isShared_4566_ = v_isSharedCheck_4571_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v_x_4561_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4571_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4569_; 
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
return v___x_4569_;
}
}
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_dec_ref(v_x_4561_);
v___x_4572_ = l_IO_Promise_result_x21___redArg(v_a_4560_);
v___x_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4574_, lean_object* v_x_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4574_, v_x_4575_);
lean_dec(v_a_4574_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4578_, lean_object* v___x_4579_, lean_object* v___x_4580_, uint8_t v___x_4581_, lean_object* v_x_4582_){
_start:
{
if (lean_obj_tag(v_x_4582_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v___x_4580_);
lean_dec(v___x_4579_);
lean_dec_ref(v___f_4578_);
v_a_4584_ = lean_ctor_get(v_x_4582_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_x_4582_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4586_ = v_x_4582_;
v_isShared_4587_ = v_isSharedCheck_4592_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v_x_4582_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4592_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
lean_object* v___x_4590_; 
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
return v___x_4590_;
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4604_; 
v_a_4593_ = lean_ctor_get(v_x_4582_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v_x_4582_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4595_ = v_x_4582_;
v_isShared_4596_ = v_isSharedCheck_4604_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v_x_4582_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4604_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4597_; lean_object* v___f_4598_; lean_object* v___x_4600_; 
lean_inc(v_a_4593_);
lean_inc(v___x_4579_);
v___x_4597_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4578_, v___x_4579_, v_a_4593_, v___x_4580_);
v___f_4598_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4598_, 0, v_a_4593_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v___x_4597_);
v___x_4600_ = v___x_4595_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4597_);
v___x_4600_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
v___x_4602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4579_, v___x_4581_, v___x_4601_, v___f_4598_);
return v___x_4602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4605_, lean_object* v___x_4606_, lean_object* v___x_4607_, lean_object* v___x_4608_, lean_object* v_x_4609_, lean_object* v___y_4610_){
_start:
{
uint8_t v___x_6060__boxed_4611_; lean_object* v_res_4612_; 
v___x_6060__boxed_4611_ = lean_unbox(v___x_4608_);
v_res_4612_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4605_, v___x_4606_, v___x_4607_, v___x_6060__boxed_4611_, v_x_4609_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4613_, lean_object* v_machine_4614_, lean_object* v_a_4615_, lean_object* v___x_4616_, lean_object* v_socket_4617_, lean_object* v_connectionContext_4618_, lean_object* v_h_4619_, lean_object* v_responseBodyInstance_4620_, lean_object* v_handler_4621_, lean_object* v___f_4622_, lean_object* v_inst_4623_, lean_object* v_extensions_4624_, lean_object* v___f_4625_, lean_object* v___f_4626_, lean_object* v___f_4627_, lean_object* v_x_4628_){
_start:
{
if (lean_obj_tag(v_x_4628_) == 0)
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref(v___f_4627_);
lean_dec_ref(v___f_4626_);
lean_dec_ref(v___f_4625_);
lean_dec(v_extensions_4624_);
lean_dec_ref(v_inst_4623_);
lean_dec_ref(v___f_4622_);
lean_dec(v_handler_4621_);
lean_dec_ref(v_responseBodyInstance_4620_);
lean_dec_ref(v_h_4619_);
lean_dec_ref(v_connectionContext_4618_);
lean_dec(v_socket_4617_);
lean_dec(v___x_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_machine_4614_);
lean_dec_ref(v_config_4613_);
v_a_4630_ = lean_ctor_get(v_x_4628_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v_x_4628_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4632_ = v_x_4628_;
v_isShared_4633_ = v_isSharedCheck_4638_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v_x_4628_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4638_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4636_; 
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
return v___x_4636_;
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4664_; 
v_a_4639_ = lean_ctor_get(v_x_4628_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v_x_4628_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4641_ = v_x_4628_;
v_isShared_4642_ = v_isSharedCheck_4664_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v_x_4628_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4664_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_keepAliveTimeout_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; uint8_t v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___f_4650_; lean_object* v___x_4651_; lean_object* v___f_4652_; lean_object* v___x_4653_; lean_object* v___f_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___f_4657_; lean_object* v___x_4659_; 
v_keepAliveTimeout_4643_ = lean_ctor_get(v_config_4613_, 5);
lean_inc_n(v_keepAliveTimeout_4643_, 2);
v___x_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_keepAliveTimeout_4643_);
v___x_4645_ = lean_box(0);
v___x_4646_ = 0;
v___x_4647_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4647_, 0, v_machine_4614_);
lean_ctor_set(v___x_4647_, 1, v_a_4615_);
lean_ctor_set(v___x_4647_, 2, v___x_4644_);
lean_ctor_set(v___x_4647_, 3, v_keepAliveTimeout_4643_);
lean_ctor_set(v___x_4647_, 4, v___x_4645_);
lean_ctor_set(v___x_4647_, 5, v_a_4639_);
lean_ctor_set(v___x_4647_, 6, v___x_4645_);
lean_ctor_set(v___x_4647_, 7, v___x_4616_);
lean_ctor_set(v___x_4647_, 8, v___x_4645_);
lean_ctor_set_uint8(v___x_4647_, sizeof(void*)*9, v___x_4646_);
lean_ctor_set_uint8(v___x_4647_, sizeof(void*)*9 + 1, v___x_4646_);
v___x_4648_ = lean_io_promise_new();
v___x_4649_ = lean_box(v___x_4646_);
lean_inc_ref(v_inst_4623_);
lean_inc_ref(v_config_4613_);
lean_inc_n(v_handler_4621_, 2);
lean_inc_ref(v_responseBodyInstance_4620_);
lean_inc_ref_n(v_h_4619_, 2);
lean_inc_ref_n(v_connectionContext_4618_, 2);
lean_inc(v_socket_4617_);
v___f_4650_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4650_, 0, v___x_4649_);
lean_closure_set(v___f_4650_, 1, v_socket_4617_);
lean_closure_set(v___f_4650_, 2, v_connectionContext_4618_);
lean_closure_set(v___f_4650_, 3, v_h_4619_);
lean_closure_set(v___f_4650_, 4, v_responseBodyInstance_4620_);
lean_closure_set(v___f_4650_, 5, v_handler_4621_);
lean_closure_set(v___f_4650_, 6, v_config_4613_);
lean_closure_set(v___f_4650_, 7, v___f_4622_);
lean_closure_set(v___f_4650_, 8, v_inst_4623_);
v___x_4651_ = lean_box(v___x_4646_);
v___f_4652_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4652_, 0, v_h_4619_);
lean_closure_set(v___f_4652_, 1, v_handler_4621_);
lean_closure_set(v___f_4652_, 2, v_extensions_4624_);
lean_closure_set(v___f_4652_, 3, v_connectionContext_4618_);
lean_closure_set(v___f_4652_, 4, v___x_4651_);
lean_closure_set(v___f_4652_, 5, v___f_4650_);
v___x_4653_ = lean_box(v___x_4646_);
v___f_4654_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4654_, 0, v_h_4619_);
lean_closure_set(v___f_4654_, 1, v_responseBodyInstance_4620_);
lean_closure_set(v___f_4654_, 2, v_handler_4621_);
lean_closure_set(v___f_4654_, 3, v_config_4613_);
lean_closure_set(v___f_4654_, 4, v_connectionContext_4618_);
lean_closure_set(v___f_4654_, 5, v___x_4653_);
lean_closure_set(v___f_4654_, 6, v___f_4652_);
lean_closure_set(v___f_4654_, 7, v_inst_4623_);
lean_closure_set(v___f_4654_, 8, v_socket_4617_);
lean_closure_set(v___f_4654_, 9, v___f_4625_);
lean_closure_set(v___f_4654_, 10, v___f_4626_);
v___x_4655_ = lean_unsigned_to_nat(0u);
v___x_4656_ = lean_box(v___x_4646_);
v___f_4657_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4657_, 0, v___f_4654_);
lean_closure_set(v___f_4657_, 1, v___x_4655_);
lean_closure_set(v___f_4657_, 2, v___x_4647_);
lean_closure_set(v___f_4657_, 3, v___x_4656_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v___x_4648_);
v___x_4659_ = v___x_4641_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4648_);
v___x_4659_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
v___x_4661_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4655_, v___x_4646_, v___x_4660_, v___f_4657_);
v___x_4662_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4655_, v___x_4646_, v___x_4661_, v___f_4627_);
return v___x_4662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4665_ = _args[0];
lean_object* v_machine_4666_ = _args[1];
lean_object* v_a_4667_ = _args[2];
lean_object* v___x_4668_ = _args[3];
lean_object* v_socket_4669_ = _args[4];
lean_object* v_connectionContext_4670_ = _args[5];
lean_object* v_h_4671_ = _args[6];
lean_object* v_responseBodyInstance_4672_ = _args[7];
lean_object* v_handler_4673_ = _args[8];
lean_object* v___f_4674_ = _args[9];
lean_object* v_inst_4675_ = _args[10];
lean_object* v_extensions_4676_ = _args[11];
lean_object* v___f_4677_ = _args[12];
lean_object* v___f_4678_ = _args[13];
lean_object* v___f_4679_ = _args[14];
lean_object* v_x_4680_ = _args[15];
lean_object* v___y_4681_ = _args[16];
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4665_, v_machine_4666_, v_a_4667_, v___x_4668_, v_socket_4669_, v_connectionContext_4670_, v_h_4671_, v_responseBodyInstance_4672_, v_handler_4673_, v___f_4674_, v_inst_4675_, v_extensions_4676_, v___f_4677_, v___f_4678_, v___f_4679_, v_x_4680_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4683_, lean_object* v_machine_4684_, lean_object* v_socket_4685_, lean_object* v_connectionContext_4686_, lean_object* v_h_4687_, lean_object* v_responseBodyInstance_4688_, lean_object* v_handler_4689_, lean_object* v___f_4690_, lean_object* v_inst_4691_, lean_object* v_extensions_4692_, lean_object* v___f_4693_, lean_object* v___f_4694_, lean_object* v___f_4695_, lean_object* v_x_4696_){
_start:
{
if (lean_obj_tag(v_x_4696_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4706_; 
lean_dec_ref(v___f_4695_);
lean_dec_ref(v___f_4694_);
lean_dec_ref(v___f_4693_);
lean_dec(v_extensions_4692_);
lean_dec_ref(v_inst_4691_);
lean_dec_ref(v___f_4690_);
lean_dec(v_handler_4689_);
lean_dec_ref(v_responseBodyInstance_4688_);
lean_dec_ref(v_h_4687_);
lean_dec_ref(v_connectionContext_4686_);
lean_dec(v_socket_4685_);
lean_dec_ref(v_machine_4684_);
lean_dec_ref(v_config_4683_);
v_a_4698_ = lean_ctor_get(v_x_4696_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v_x_4696_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4700_ = v_x_4696_;
v_isShared_4701_ = v_isSharedCheck_4706_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v_x_4696_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4706_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; 
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
}
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4721_; 
v_a_4707_ = lean_ctor_get(v_x_4696_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v_x_4696_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4709_ = v_x_4696_;
v_isShared_4710_ = v_isSharedCheck_4721_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v_x_4696_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4721_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___f_4713_; lean_object* v___x_4715_; 
v___x_4711_ = lean_box(0);
v___x_4712_ = l_Std_CloseableChannel_new___redArg(v___x_4711_);
v___f_4713_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4713_, 0, v_config_4683_);
lean_closure_set(v___f_4713_, 1, v_machine_4684_);
lean_closure_set(v___f_4713_, 2, v_a_4707_);
lean_closure_set(v___f_4713_, 3, v___x_4711_);
lean_closure_set(v___f_4713_, 4, v_socket_4685_);
lean_closure_set(v___f_4713_, 5, v_connectionContext_4686_);
lean_closure_set(v___f_4713_, 6, v_h_4687_);
lean_closure_set(v___f_4713_, 7, v_responseBodyInstance_4688_);
lean_closure_set(v___f_4713_, 8, v_handler_4689_);
lean_closure_set(v___f_4713_, 9, v___f_4690_);
lean_closure_set(v___f_4713_, 10, v_inst_4691_);
lean_closure_set(v___f_4713_, 11, v_extensions_4692_);
lean_closure_set(v___f_4713_, 12, v___f_4693_);
lean_closure_set(v___f_4713_, 13, v___f_4694_);
lean_closure_set(v___f_4713_, 14, v___f_4695_);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4712_);
v___x_4715_ = v___x_4709_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4712_);
v___x_4715_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; 
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = 0;
v___x_4719_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4717_, v___x_4718_, v___x_4716_, v___f_4713_);
return v___x_4719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4722_, lean_object* v_machine_4723_, lean_object* v_socket_4724_, lean_object* v_connectionContext_4725_, lean_object* v_h_4726_, lean_object* v_responseBodyInstance_4727_, lean_object* v_handler_4728_, lean_object* v___f_4729_, lean_object* v_inst_4730_, lean_object* v_extensions_4731_, lean_object* v___f_4732_, lean_object* v___f_4733_, lean_object* v___f_4734_, lean_object* v_x_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4722_, v_machine_4723_, v_socket_4724_, v_connectionContext_4725_, v_h_4726_, v_responseBodyInstance_4727_, v_handler_4728_, v___f_4729_, v_inst_4730_, v_extensions_4731_, v___f_4732_, v___f_4733_, v___f_4734_, v_x_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4741_, lean_object* v_h_4742_, lean_object* v_connection_4743_, lean_object* v_config_4744_, lean_object* v_connectionContext_4745_, lean_object* v_handler_4746_){
_start:
{
lean_object* v_responseBodyInstance_4748_; lean_object* v_onFailure_4749_; lean_object* v___x_4750_; lean_object* v_socket_4751_; lean_object* v_machine_4752_; lean_object* v_extensions_4753_; lean_object* v___f_4754_; lean_object* v___f_4755_; lean_object* v___f_4756_; lean_object* v___f_4757_; lean_object* v___f_4758_; lean_object* v___f_4759_; lean_object* v___f_4760_; lean_object* v___f_4761_; lean_object* v___f_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; lean_object* v___x_4765_; 
v_responseBodyInstance_4748_ = lean_ctor_get(v_h_4742_, 0);
lean_inc_ref_n(v_responseBodyInstance_4748_, 2);
v_onFailure_4749_ = lean_ctor_get(v_h_4742_, 2);
v___x_4750_ = l_Std_Http_Body_mkStream();
v_socket_4751_ = lean_ctor_get(v_connection_4743_, 0);
lean_inc_n(v_socket_4751_, 2);
v_machine_4752_ = lean_ctor_get(v_connection_4743_, 1);
lean_inc_ref(v_machine_4752_);
v_extensions_4753_ = lean_ctor_get(v_connection_4743_, 2);
lean_inc(v_extensions_4753_);
lean_dec_ref(v_connection_4743_);
v___f_4754_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4755_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4756_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4757_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4746_);
lean_inc_ref(v_onFailure_4749_);
v___f_4758_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4758_, 0, v_onFailure_4749_);
lean_closure_set(v___f_4758_, 1, v_handler_4746_);
lean_closure_set(v___f_4758_, 2, v___f_4757_);
lean_inc_ref(v_inst_4741_);
v___f_4759_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4759_, 0, v_inst_4741_);
lean_closure_set(v___f_4759_, 1, v_socket_4751_);
lean_inc_ref(v___f_4759_);
v___f_4760_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4760_, 0, v___f_4759_);
v___f_4761_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4761_, 0, v___f_4754_);
lean_closure_set(v___f_4761_, 1, v_responseBodyInstance_4748_);
lean_closure_set(v___f_4761_, 2, v___f_4760_);
lean_closure_set(v___f_4761_, 3, v___f_4759_);
v___f_4762_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4762_, 0, v_config_4744_);
lean_closure_set(v___f_4762_, 1, v_machine_4752_);
lean_closure_set(v___f_4762_, 2, v_socket_4751_);
lean_closure_set(v___f_4762_, 3, v_connectionContext_4745_);
lean_closure_set(v___f_4762_, 4, v_h_4742_);
lean_closure_set(v___f_4762_, 5, v_responseBodyInstance_4748_);
lean_closure_set(v___f_4762_, 6, v_handler_4746_);
lean_closure_set(v___f_4762_, 7, v___f_4755_);
lean_closure_set(v___f_4762_, 8, v_inst_4741_);
lean_closure_set(v___f_4762_, 9, v_extensions_4753_);
lean_closure_set(v___f_4762_, 10, v___f_4756_);
lean_closure_set(v___f_4762_, 11, v___f_4758_);
lean_closure_set(v___f_4762_, 12, v___f_4761_);
v___x_4763_ = lean_unsigned_to_nat(0u);
v___x_4764_ = 0;
v___x_4765_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4763_, v___x_4764_, v___x_4750_, v___f_4762_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4766_, lean_object* v_h_4767_, lean_object* v_connection_4768_, lean_object* v_config_4769_, lean_object* v_connectionContext_4770_, lean_object* v_handler_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4766_, v_h_4767_, v_connection_4768_, v_config_4769_, v_connectionContext_4770_, v_handler_4771_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4774_, lean_object* v_00_u03c3_4775_, lean_object* v_inst_4776_, lean_object* v_h_4777_, lean_object* v_connection_4778_, lean_object* v_config_4779_, lean_object* v_connectionContext_4780_, lean_object* v_handler_4781_){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4776_, v_h_4777_, v_connection_4778_, v_config_4779_, v_connectionContext_4780_, v_handler_4781_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4784_, lean_object* v_00_u03c3_4785_, lean_object* v_inst_4786_, lean_object* v_h_4787_, lean_object* v_connection_4788_, lean_object* v_config_4789_, lean_object* v_connectionContext_4790_, lean_object* v_handler_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4784_, v_00_u03c3_4785_, v_inst_4786_, v_h_4787_, v_connection_4788_, v_config_4789_, v_connectionContext_4790_, v_handler_4791_);
return v_res_4793_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = 0;
v___x_4795_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_unsigned_to_nat(4096u);
v___x_4797_ = lean_mk_empty_byte_array(v___x_4796_);
return v___x_4797_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4798_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4799_ = l_ByteArray_mkIterator(v___x_4798_);
return v___x_4799_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4800_ = 0;
v___x_4801_ = lean_unsigned_to_nat(0u);
v___x_4802_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4803_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4804_ = lean_box(0);
v___x_4805_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
lean_ctor_set(v___x_4805_, 1, v___x_4803_);
lean_ctor_set(v___x_4805_, 2, v___x_4802_);
lean_ctor_set(v___x_4805_, 3, v___x_4801_);
lean_ctor_set(v___x_4805_, 4, v___x_4801_);
lean_ctor_set(v___x_4805_, 5, v___x_4801_);
lean_ctor_set_uint8(v___x_4805_, sizeof(void*)*6, v___x_4800_);
return v___x_4805_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4813_; lean_object* v___x_4814_; 
v___x_4813_ = 1;
v___x_4814_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4813_);
return v___x_4814_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4815_ = lean_unsigned_to_nat(0u);
v___x_4816_ = 0;
v___x_4817_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4818_ = lean_box(0);
v___x_4819_ = lean_box(0);
v___x_4820_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4821_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4822_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
lean_ctor_set(v___x_4822_, 1, v___x_4820_);
lean_ctor_set(v___x_4822_, 2, v___x_4819_);
lean_ctor_set(v___x_4822_, 3, v___x_4818_);
lean_ctor_set(v___x_4822_, 4, v___x_4817_);
lean_ctor_set(v___x_4822_, 5, v___x_4815_);
lean_ctor_set_uint8(v___x_4822_, sizeof(void*)*6, v___x_4816_);
lean_ctor_set_uint8(v___x_4822_, sizeof(void*)*6 + 1, v___x_4816_);
lean_ctor_set_uint8(v___x_4822_, sizeof(void*)*6 + 2, v___x_4816_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4823_, lean_object* v_client_4824_, lean_object* v_extensions_4825_, lean_object* v_inst_4826_, lean_object* v_inst_4827_, lean_object* v_handler_4828_, lean_object* v_x_4829_){
_start:
{
if (lean_obj_tag(v_x_4829_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4839_; 
lean_dec(v_handler_4828_);
lean_dec_ref(v_inst_4827_);
lean_dec_ref(v_inst_4826_);
lean_dec(v_extensions_4825_);
lean_dec(v_client_4824_);
lean_dec_ref(v_config_4823_);
v_a_4831_ = lean_ctor_get(v_x_4829_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v_x_4829_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4833_ = v_x_4829_;
v_isShared_4834_ = v_isSharedCheck_4839_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v_x_4829_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4839_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
lean_object* v___x_4837_; 
v___x_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
return v___x_4837_;
}
}
}
else
{
lean_object* v_a_4840_; uint8_t v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; uint8_t v_enableKeepAlive_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v_a_4840_ = lean_ctor_get(v_x_4829_, 0);
lean_inc(v_a_4840_);
lean_dec_ref(v_x_4829_);
v___x_4841_ = 0;
v___x_4842_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4843_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4844_ = lean_box(0);
v___x_4845_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4846_ = l_Std_Http_Config_toH1Config(v_config_4823_);
v_enableKeepAlive_4847_ = lean_ctor_get_uint8(v___x_4846_, sizeof(void*)*18);
v___x_4848_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4848_, 0, v___x_4842_);
lean_ctor_set(v___x_4848_, 1, v___x_4845_);
lean_ctor_set(v___x_4848_, 2, v___x_4846_);
lean_ctor_set(v___x_4848_, 3, v___x_4843_);
lean_ctor_set(v___x_4848_, 4, v___x_4844_);
lean_ctor_set(v___x_4848_, 5, v___x_4844_);
lean_ctor_set_uint8(v___x_4848_, sizeof(void*)*6, v_enableKeepAlive_4847_);
lean_ctor_set_uint8(v___x_4848_, sizeof(void*)*6 + 1, v___x_4841_);
lean_ctor_set_uint8(v___x_4848_, sizeof(void*)*6 + 2, v___x_4841_);
v___x_4849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4849_, 0, v_client_4824_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
lean_ctor_set(v___x_4849_, 2, v_extensions_4825_);
v___x_4850_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4826_, v_inst_4827_, v___x_4849_, v_config_4823_, v_a_4840_, v_handler_4828_);
return v___x_4850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4851_, lean_object* v_client_4852_, lean_object* v_extensions_4853_, lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_handler_4856_, lean_object* v_x_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4851_, v_client_4852_, v_extensions_4853_, v_inst_4854_, v_inst_4855_, v_handler_4856_, v_x_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4860_, lean_object* v_inst_4861_, lean_object* v_client_4862_, lean_object* v_handler_4863_, lean_object* v_config_4864_, lean_object* v_extensions_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v___f_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; lean_object* v___x_4873_; 
v___f_4868_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4868_, 0, v_config_4864_);
lean_closure_set(v___f_4868_, 1, v_client_4862_);
lean_closure_set(v___f_4868_, 2, v_extensions_4865_);
lean_closure_set(v___f_4868_, 3, v_inst_4860_);
lean_closure_set(v___f_4868_, 4, v_inst_4861_);
lean_closure_set(v___f_4868_, 5, v_handler_4863_);
lean_inc_ref(v_a_4866_);
v___x_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_a_4866_);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
v___x_4871_ = lean_unsigned_to_nat(0u);
v___x_4872_ = 0;
v___x_4873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4871_, v___x_4872_, v___x_4870_, v___f_4868_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4874_, lean_object* v_inst_4875_, lean_object* v_client_4876_, lean_object* v_handler_4877_, lean_object* v_config_4878_, lean_object* v_extensions_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4874_, v_inst_4875_, v_client_4876_, v_handler_4877_, v_config_4878_, v_extensions_4879_, v_a_4880_);
lean_dec_ref(v_a_4880_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4883_, lean_object* v_00_u03c3_4884_, lean_object* v_inst_4885_, lean_object* v_inst_4886_, lean_object* v_client_4887_, lean_object* v_handler_4888_, lean_object* v_config_4889_, lean_object* v_extensions_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v___x_4893_; 
v___x_4893_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4885_, v_inst_4886_, v_client_4887_, v_handler_4888_, v_config_4889_, v_extensions_4890_, v_a_4891_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4894_, lean_object* v_00_u03c3_4895_, lean_object* v_inst_4896_, lean_object* v_inst_4897_, lean_object* v_client_4898_, lean_object* v_handler_4899_, lean_object* v_config_4900_, lean_object* v_extensions_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Std_Http_Server_serveConnection(v_t_4894_, v_00_u03c3_4895_, v_inst_4896_, v_inst_4897_, v_client_4898_, v_handler_4899_, v_config_4900_, v_extensions_4901_, v_a_4902_);
lean_dec_ref(v_a_4902_);
return v_res_4904_;
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
