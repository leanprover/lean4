// Lean compiler output
// Module: Std.Internal.Http.Server.Connection
// Imports: public import Std.Internal.Async.TCP public import Std.Internal.Async.ContextAsync public import Std.Internal.Http.Transport public import Std.Internal.Http.Protocol.H1 public import Std.Internal.Http.Server.Config public import Std.Internal.Http.Server.Handler
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_close(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Http_Body_mkStream();
lean_object* l_Std_Http_Protocol_H1_Machine_canContinue(uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Internal_IO_Async_Selector_sleep(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_instInhabitedError;
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_get_current_time();
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Functor_discard(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Channel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
extern lean_object* l_Std_Http_Header_Name_date;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Time_TimeZone_UTC;
lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Internal_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_ByteArray_mkIterator(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(uint8_t, lean_object*);
lean_object* l_Std_Http_Body_Stream_send(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
lean_object* lean_io_promise_new();
extern lean_object* l_instMonadBaseIO;
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Http"};
static const lean_object* l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "RemoteAddr"};
static const lean_object* l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(62, 74, 245, 198, 196, 207, 141, 173)}};
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(3, 137, 82, 156, 27, 230, 60, 168)}};
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_2),((lean_object*)&l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(136, 13, 149, 223, 202, 48, 50, 45)}};
static const lean_object* l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Std_Http_Server_instImpl_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Std_Http_Server_instTypeNameRemoteAddr = (const lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Internal_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_value;
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_value;
static const lean_array_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value;
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value)} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value;
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_value)} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_EAsync_instMonadFinally___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_value)} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_value)} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get___boxed, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7_value)} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid status line"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid header"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Timeout"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Entity too large"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "URI too long"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unsupported version"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid chunk"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Connection closed"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad message"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Too many headers"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Headers too large"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10_value;
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Other error: "};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 7}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "request header timeout"};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(lean_object* v_x_40_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg___boxed(lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(v_x_48_);
lean_dec(v_x_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx(lean_object* v_00_u03b2_50_, lean_object* v_x_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___redArg(v_x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___boxed(lean_object* v_00_u03b2_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx(v_00_u03b2_53_, v_x_54_);
lean_dec(v_x_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(lean_object* v_t_56_, lean_object* v_k_57_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(lean_object* v_00_u03b2_67_, lean_object* v_motive_68_, lean_object* v_ctorIdx_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_k_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_70_, v_k_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___boxed(lean_object* v_00_u03b2_74_, lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(v_00_u03b2_74_, v_motive_75_, v_ctorIdx_76_, v_t_77_, v_h_78_, v_k_79_);
lean_dec(v_ctorIdx_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim___redArg(lean_object* v_t_81_, lean_object* v_bytes_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_81_, v_bytes_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim(lean_object* v_00_u03b2_84_, lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_bytes_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_86_, v_bytes_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim___redArg(lean_object* v_t_90_, lean_object* v_responseBody_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_90_, v_responseBody_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim(lean_object* v_00_u03b2_93_, lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_responseBody_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_95_, v_responseBody_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim___redArg(lean_object* v_t_99_, lean_object* v_bodyInterest_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_99_, v_bodyInterest_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim(lean_object* v_00_u03b2_102_, lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_bodyInterest_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_104_, v_bodyInterest_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim___redArg(lean_object* v_t_108_, lean_object* v_response_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_108_, v_response_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim(lean_object* v_00_u03b2_111_, lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_response_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_113_, v_response_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object* v_t_117_, lean_object* v_timeout_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_117_, v_timeout_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object* v_00_u03b2_120_, lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_timeout_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_122_, v_timeout_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object* v_t_126_, lean_object* v_shutdown_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_126_, v_shutdown_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object* v_00_u03b2_129_, lean_object* v_motive_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_shutdown_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_131_, v_shutdown_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object* v_t_135_, lean_object* v_close_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_135_, v_close_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object* v_00_u03b2_138_, lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_close_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_140_, v_close_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_152_){
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
v___x_167_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
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
v___x_155_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1));
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_175_){
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
v___x_186_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_190_, lean_object* v_handler_191_, lean_object* v___f_192_, lean_object* v_x_193_){
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
v___x_200_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_198_, v___x_199_, v___x_197_, v___f_192_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_202_, lean_object* v_handler_203_, lean_object* v___f_204_, lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_202_, v_handler_203_, v___f_204_, v_x_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_208_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_216_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_x_3604__boxed_223_; lean_object* v_res_224_; 
v_x_3604__boxed_223_ = lean_unbox(v_x_221_);
v_res_224_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3604__boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_225_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_233_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v___f_247_, lean_object* v_response_248_, lean_object* v___x_249_, lean_object* v___f_250_, lean_object* v_requestBody_251_, lean_object* v___f_252_, lean_object* v_responseBody_253_, lean_object* v_inst_254_, lean_object* v___f_255_, lean_object* v_____r_256_, lean_object* v_selectables_257_){
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
v___x_261_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = 0;
v___x_264_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_262_, v___x_263_, v___x_261_, v___f_247_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v___f_282_, lean_object* v_response_283_, lean_object* v___x_284_, lean_object* v___f_285_, lean_object* v_requestBody_286_, lean_object* v___f_287_, lean_object* v_responseBody_288_, lean_object* v_inst_289_, lean_object* v___f_290_, lean_object* v_____r_291_, lean_object* v_selectables_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_282_, v_response_283_, v___x_284_, v___f_285_, v_requestBody_286_, v___f_287_, v_responseBody_288_, v_inst_289_, v___f_290_, v_____r_291_, v_selectables_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v_token_295_, lean_object* v___f_296_, lean_object* v_x_297_){
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
v___x_304_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_302_, v___x_303_, v___x_301_, v___f_296_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v_token_305_, lean_object* v___f_306_, lean_object* v_x_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v_token_305_, v___f_306_, v_x_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v___f_310_, lean_object* v_selectables_311_, lean_object* v___f_312_, lean_object* v_x_313_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v___f_329_, lean_object* v_selectables_330_, lean_object* v___f_331_, lean_object* v_x_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v___f_329_, v_selectables_330_, v___f_331_, v_x_332_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1000000000u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1000u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1000000u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v_val_341_, lean_object* v___f_342_, lean_object* v_x_343_){
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
v___x_361_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
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
v___x_370_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1);
v___x_371_ = lean_int_mul(v_second_368_, v___x_370_);
lean_dec(v_second_368_);
v___x_372_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_373_ = lean_int_ediv(v_nano_369_, v___x_372_);
lean_dec(v_nano_369_);
v_millis_374_ = lean_int_add(v___x_371_, v___x_373_);
lean_dec(v___x_373_);
lean_dec(v___x_371_);
v___x_375_ = l_Std_Internal_IO_Async_Selector_sleep(v_millis_374_);
lean_dec(v_millis_374_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = 0;
v___x_378_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_376_, v___x_377_, v___x_375_, v___f_342_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v_val_379_, lean_object* v___f_380_, lean_object* v_x_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v_val_379_, v___f_380_, v_x_381_);
lean_dec_ref(v_val_379_);
return v_res_383_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_instInhabitedError;
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_config_396_, lean_object* v_handler_397_, lean_object* v_sources_398_){
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
v___f_416_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_417_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_418_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_418_, 0, v_inst_394_);
lean_closure_set(v___f_418_, 1, v_handler_397_);
lean_closure_set(v___f_418_, 2, v___f_417_);
v___f_419_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_420_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_421_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_422_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_423_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___x_424_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7);
lean_inc_ref(v_inst_395_);
lean_inc_ref(v___f_418_);
v___f_425_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed), 12, 9);
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
v___x_406_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_404_, v___x_405_, v___x_403_, v___y_401_);
return v___x_406_;
}
v___jp_426_:
{
lean_object* v_token_428_; lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_selectables_434_; 
v_token_428_ = lean_ctor_get(v_connectionContext_415_, 1);
lean_inc_ref_n(v_token_428_, 2);
lean_dec_ref(v_connectionContext_415_);
v___f_429_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 4, 2);
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
v___f_443_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_443_, 0, v___f_423_);
lean_closure_set(v___f_443_, 1, v_selectables_441_);
lean_closure_set(v___f_443_, 2, v___f_425_);
v___f_444_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 4, 2);
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
v___x_462_ = l_Std_Internal_IO_Async_Selector_sleep(v_timeout_412_);
lean_dec(v_timeout_412_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_463_, 0, v___f_423_);
lean_closure_set(v___f_463_, 1, v_selectables_441_);
lean_closure_set(v___f_463_, 2, v___f_425_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = 0;
v___x_466_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_464_, v___x_465_, v___x_462_, v___f_463_);
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
v___x_468_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_418_, v_response_409_, v___x_424_, v___f_419_, v_requestBody_411_, v___f_420_, v_responseBody_410_, v_inst_395_, v___f_421_, v___x_467_, v_selectables_441_);
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
v___x_470_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_418_, v_response_409_, v___x_424_, v___f_419_, v_requestBody_411_, v___f_420_, v_responseBody_410_, v_inst_395_, v___f_421_, v___x_469_, v_selectables_434_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_config_480_, lean_object* v_handler_481_, lean_object* v_sources_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_477_, v_inst_478_, v_inst_479_, v_config_480_, v_handler_481_, v_sources_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_485_, lean_object* v_00_u03c3_486_, lean_object* v_00_u03b2_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_config_491_, lean_object* v_handler_492_, lean_object* v_sources_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_config_491_, v_handler_492_, v_sources_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_496_, lean_object* v_00_u03c3_497_, lean_object* v_00_u03b2_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_config_502_, lean_object* v_handler_503_, lean_object* v_sources_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_496_, v_00_u03c3_497_, v_00_u03b2_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_config_502_, v_handler_503_, v_sources_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_507_, lean_object* v_x_508_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_537_, lean_object* v_x_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_537_, v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_541_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___y_1326__boxed_548_; lean_object* v_res_549_; 
v___y_1326__boxed_548_ = lean_unbox(v___y_546_);
v_res_549_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1326__boxed_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_550_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_554_, lean_object* v_x_555_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_564_, lean_object* v_x_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_564_, v_x_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_568_, lean_object* v_x_569_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_574_, lean_object* v_x_575_, lean_object* v___y_576_){
_start:
{
uint8_t v___x_1370__boxed_577_; lean_object* v_res_578_; 
v___x_1370__boxed_577_ = lean_unbox(v___x_574_);
v_res_578_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1370__boxed_577_, v_x_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_579_, uint8_t v___x_580_, lean_object* v_a_581_, lean_object* v___f_582_, lean_object* v___f_583_, lean_object* v___x_584_, uint8_t v___x_585_, lean_object* v___f_586_, lean_object* v_x_587_){
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
v___x_611_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v___x_610_);
v___x_612_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_584_, v___x_585_, v___x_611_, v___f_586_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_613_, lean_object* v___x_614_, lean_object* v_a_615_, lean_object* v___f_616_, lean_object* v___f_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___f_620_, lean_object* v_x_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_1385__boxed_623_; uint8_t v___x_1390__boxed_624_; lean_object* v_res_625_; 
v___x_1385__boxed_623_ = lean_unbox(v___x_614_);
v___x_1390__boxed_624_ = lean_unbox(v___x_619_);
v_res_625_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_613_, v___x_1385__boxed_623_, v_a_615_, v___f_616_, v___f_617_, v___x_618_, v___x_1390__boxed_624_, v___f_620_, v_x_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_626_, lean_object* v___x_627_, uint8_t v___x_628_, lean_object* v___f_629_, lean_object* v_x_630_){
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
v___x_642_ = l_Std_Internal_IO_Async_Selector_sleep(v_lingeringTimeout_641_);
v___x_643_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_627_, v___x_628_, v___x_642_, v___f_629_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___f_647_, lean_object* v_x_648_, lean_object* v___y_649_){
_start:
{
uint8_t v___x_1459__boxed_650_; lean_object* v_res_651_; 
v___x_1459__boxed_650_ = lean_unbox(v___x_646_);
v_res_651_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_644_, v___x_645_, v___x_1459__boxed_650_, v___f_647_, v_x_648_);
lean_dec_ref(v_config_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v___f_655_, lean_object* v___x_656_, lean_object* v_connectionContext_657_, uint8_t v___x_658_, lean_object* v_a_659_, lean_object* v___f_660_, lean_object* v___f_661_, lean_object* v_config_662_, lean_object* v_x_663_){
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
v___f_680_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_681_ = lean_box(v___x_658_);
v___x_682_ = lean_box(v___x_678_);
v___f_683_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_683_, 0, v_connectionContext_657_);
lean_closure_set(v___f_683_, 1, v___x_681_);
lean_closure_set(v___f_683_, 2, v_a_659_);
lean_closure_set(v___f_683_, 3, v___f_660_);
lean_closure_set(v___f_683_, 4, v___f_680_);
lean_closure_set(v___f_683_, 5, v___x_656_);
lean_closure_set(v___f_683_, 6, v___x_682_);
lean_closure_set(v___f_683_, 7, v___f_661_);
v___x_684_ = lean_box(v___x_678_);
v___f_685_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
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
v___x_689_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_656_, v___x_678_, v___x_688_, v___f_685_);
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v___f_692_, lean_object* v___x_693_, lean_object* v_connectionContext_694_, lean_object* v___x_695_, lean_object* v_a_696_, lean_object* v___f_697_, lean_object* v___f_698_, lean_object* v_config_699_, lean_object* v_x_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_1501__boxed_702_; lean_object* v_res_703_; 
v___x_1501__boxed_702_ = lean_unbox(v___x_695_);
v_res_703_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v___f_692_, v___x_693_, v_connectionContext_694_, v___x_1501__boxed_702_, v_a_696_, v___f_697_, v___f_698_, v_config_699_, v_x_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_704_, lean_object* v_handler_705_, lean_object* v_head_706_, lean_object* v_connectionContext_707_, uint8_t v___x_708_, lean_object* v___f_709_, lean_object* v___f_710_, lean_object* v_config_711_, lean_object* v___f_712_, lean_object* v_x_713_){
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
v___x_731_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_731_, 0, lean_box(0));
lean_closure_set(v___x_731_, 1, v___x_729_);
v___x_732_ = lean_io_as_task(v___x_731_, v___x_730_);
lean_inc(v_a_724_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v_a_724_);
v___x_734_ = lean_box(v___x_708_);
v___f_735_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
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
v___x_742_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_730_, v___x_741_, v___x_740_, v___f_735_);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_745_, lean_object* v_handler_746_, lean_object* v_head_747_, lean_object* v_connectionContext_748_, lean_object* v___x_749_, lean_object* v___f_750_, lean_object* v___f_751_, lean_object* v_config_752_, lean_object* v___f_753_, lean_object* v_x_754_, lean_object* v___y_755_){
_start:
{
uint8_t v___x_1582__boxed_756_; lean_object* v_res_757_; 
v___x_1582__boxed_756_ = lean_unbox(v___x_749_);
v_res_757_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_745_, v_handler_746_, v_head_747_, v_connectionContext_748_, v___x_1582__boxed_756_, v___f_750_, v___f_751_, v_config_752_, v___f_753_, v_x_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_760_, lean_object* v_handler_761_, lean_object* v_machine_762_, lean_object* v_head_763_, lean_object* v_config_764_, lean_object* v_connectionContext_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_767_ = lean_box(0);
v___x_768_ = l_Std_CloseableChannel_new___redArg(v___x_767_);
v___f_769_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_769_, 0, v_machine_762_);
v___f_770_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_771_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_772_ = 0;
v___x_773_ = lean_box(v___x_772_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
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
v___x_778_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_777_, v___x_772_, v___x_776_, v___f_774_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_779_, lean_object* v_handler_780_, lean_object* v_machine_781_, lean_object* v_head_782_, lean_object* v_config_783_, lean_object* v_connectionContext_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_779_, v_handler_780_, v_machine_781_, v_head_782_, v_config_783_, v_connectionContext_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_787_, lean_object* v_inst_788_, lean_object* v_handler_789_, lean_object* v_machine_790_, lean_object* v_head_791_, lean_object* v_config_792_, lean_object* v_connectionContext_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_788_, v_handler_789_, v_machine_790_, v_head_791_, v_config_792_, v_connectionContext_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_796_, lean_object* v_inst_797_, lean_object* v_handler_798_, lean_object* v_machine_799_, lean_object* v_head_800_, lean_object* v_config_801_, lean_object* v_connectionContext_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_796_, v_inst_797_, v_handler_798_, v_machine_799_, v_head_800_, v_config_801_, v_connectionContext_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Rat_ofInt(v_a_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_807_, lean_object* v_x_808_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object* v_i_835_, lean_object* v_source_836_, lean_object* v_target_837_){
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
v_target_843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_target_837_, v_es_840_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object* v_data_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_nbuckets_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_848_ = lean_array_get_size(v_data_847_);
v___x_849_ = lean_unsigned_to_nat(2u);
v_nbuckets_850_ = lean_nat_mul(v___x_848_, v___x_849_);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_box(0);
v___x_853_ = lean_mk_array(v_nbuckets_850_, v___x_852_);
v___x_854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v___x_851_, v_data_847_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_855_, lean_object* v_x_856_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_870_, lean_object* v_a_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_val_875_; lean_object* v___x_876_; 
v___x_873_ = lean_box(0);
v___x_874_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_870_, v___x_873_);
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
v_tail_884_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_870_, v_a_871_, v_tail_879_);
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
v___x_889_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_870_, v___x_888_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_895_, lean_object* v_x_896_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_902_, lean_object* v_x_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec_ref(v_a_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_906_, lean_object* v_m_907_, lean_object* v_a_908_){
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
v___x_928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_908_, v_bkt_927_);
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
v_val_941_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_934_);
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
v_bkt_x27_950_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_906_, v_a_908_, v_bkt_927_);
v___x_957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_908_, v_bkt_x27_950_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v___x_961_, lean_object* v_entries_962_, lean_object* v_indexes_963_, lean_object* v_status_964_, uint8_t v_version_965_, lean_object* v_x_966_){
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
v_indexes_987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_984_, v_indexes_963_, v___x_981_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v___x_995_, lean_object* v_entries_996_, lean_object* v_indexes_997_, lean_object* v_status_998_, lean_object* v_version_999_, lean_object* v_x_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_version_boxed_1002_; lean_object* v_res_1003_; 
v_version_boxed_1002_ = lean_unbox(v_version_999_);
v_res_1003_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v___x_995_, v_entries_996_, v_indexes_997_, v_status_998_, v_version_boxed_1002_, v_x_1000_);
lean_dec_ref(v___x_995_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_a_1004_, lean_object* v___x_1005_, lean_object* v_x_1006_){
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
v___x_1012_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_a_1024_, lean_object* v___x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_a_1024_, v___x_1025_, v_x_1026_);
lean_dec_ref(v___x_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(lean_object* v_m_1028_, lean_object* v_a_1029_){
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
v___x_1045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1029_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg___boxed(lean_object* v_m_1046_, lean_object* v_a_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_m_1046_, v_a_1047_);
lean_dec_ref(v_a_1047_);
lean_dec_ref(v_m_1046_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1050_, lean_object* v_head_1051_){
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
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_indexes_1061_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v_val_1071_; lean_object* v___x_1075_; 
lean_inc(v_status_1058_);
lean_dec_ref(v_head_1051_);
v___x_1067_ = l_Std_Time_TimeZone_UTC;
v___x_1068_ = lean_box(v_version_1059_);
v___f_1069_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
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
v___f_1080_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
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
v___x_1074_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1073_, v___x_1066_, v___x_1072_, v___f_1069_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1098_, lean_object* v_head_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1098_, v_head_1099_);
lean_dec_ref(v_config_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_nat_to_int(v_a_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_nat_to_int(v_a_1104_);
v___x_1106_ = l_Rat_ofInt(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___redArg(v_m_1108_, v_a_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_00_u03b2_1111_, v_m_1112_, v_a_1113_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_m_1112_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1116_, lean_object* v_a_1117_, lean_object* v_x_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_a_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1120_, v_a_1121_, v_x_1122_);
lean_dec(v_x_1122_);
lean_dec_ref(v_a_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1125_, lean_object* v_data_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1128_, lean_object* v_i_1129_, lean_object* v_source_1130_, lean_object* v_target_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v_i_1129_, v_source_1130_, v_target_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1137_, lean_object* v_____r_1138_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1144_, lean_object* v_____r_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1144_, v_____r_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1148_, lean_object* v_x_1149_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1162_, v_x_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1166_, lean_object* v_body_1167_, lean_object* v___f_1168_, lean_object* v___f_1169_, lean_object* v_x_1170_){
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
v___x_1186_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1184_, v___x_1185_, v___x_1183_, v___f_1168_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1189_, lean_object* v_body_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1189_, v_body_1190_, v___f_1191_, v___f_1192_, v_x_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v___x_1196_, lean_object* v_x1_1197_, lean_object* v_x2_1198_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v___x_1202_, lean_object* v_x1_1203_, lean_object* v_x2_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v___x_1202_, v_x1_1203_, v_x2_1204_);
lean_dec_ref(v___x_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___f_1206_, lean_object* v___f_1207_, lean_object* v_x1_1208_, lean_object* v_x2_1209_){
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
v_f_1217_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
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
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___f_1246_; 
v___x_1245_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1246_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1246_, 0, v___x_1245_);
return v___f_1246_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___f_1253_; 
v___x_1252_ = l_Std_Http_Header_Name_contentLength;
v___f_1253_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1253_, 0, v___x_1252_);
return v___f_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v___y_1254_, lean_object* v_body_1255_, lean_object* v_isClosed_1256_, lean_object* v_close_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___y_1261_; uint8_t v_omitBody_1262_; lean_object* v___y_1275_; uint8_t v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; 
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
uint8_t v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v___x_1442_; uint8_t v___y_1444_; uint8_t v___y_1445_; uint8_t v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1448_; uint8_t v___y_1449_; uint8_t v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1458_; uint8_t v___y_1471_; uint8_t v___y_1472_; uint8_t v___y_1475_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
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
v___x_1363_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1364_ = lean_nat_dec_lt(v___y_1358_, v___x_1362_);
if (v___x_1364_ == 0)
{
lean_dec_ref(v___y_1361_);
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___y_1360_;
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
v___y_1348_ = v___y_1360_;
goto v___jp_1346_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = lean_usize_of_nat(v___x_1362_);
lean_inc_ref(v___y_1359_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___y_1359_, v___y_1361_, v___x_1366_, v___x_1367_, v___y_1360_);
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
lean_inc_ref(v___y_1359_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___y_1359_, v___y_1361_, v___x_1369_, v___x_1370_, v___y_1360_);
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___x_1371_;
goto v___jp_1346_;
}
}
}
v___jp_1372_:
{
lean_object* v_entries_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_entries_1379_ = lean_ctor_get(v___y_1378_, 0);
lean_inc_ref(v_entries_1379_);
lean_dec_ref(v___y_1378_);
v___x_1380_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1377_, v___y_1375_);
lean_dec_ref(v___y_1375_);
lean_dec_ref(v___y_1377_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_array_get_size(v_entries_1379_);
v___x_1383_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1384_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1385_ = lean_nat_dec_lt(v___x_1381_, v___x_1382_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_entries_1379_);
v___y_1357_ = v___y_1373_;
v___y_1358_ = v___x_1381_;
v___y_1359_ = v___y_1376_;
v___y_1360_ = v___x_1380_;
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
v___y_1357_ = v___y_1373_;
v___y_1358_ = v___x_1381_;
v___y_1359_ = v___y_1376_;
v___y_1360_ = v___x_1380_;
v___y_1361_ = v___x_1383_;
goto v___jp_1356_;
}
else
{
size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = lean_usize_of_nat(v___x_1382_);
lean_inc_ref(v___y_1374_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1384_, v___y_1374_, v_entries_1379_, v___x_1387_, v___x_1388_, v___x_1383_);
v___y_1357_ = v___y_1373_;
v___y_1358_ = v___x_1381_;
v___y_1359_ = v___y_1376_;
v___y_1360_ = v___x_1380_;
v___y_1361_ = v___x_1389_;
goto v___jp_1356_;
}
}
else
{
size_t v___x_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = lean_usize_of_nat(v___x_1382_);
lean_inc_ref(v___y_1374_);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1384_, v___y_1374_, v_entries_1379_, v___x_1390_, v___x_1391_, v___x_1383_);
v___y_1357_ = v___y_1373_;
v___y_1358_ = v___x_1381_;
v___y_1359_ = v___y_1376_;
v___y_1360_ = v___x_1380_;
v___y_1361_ = v___x_1392_;
goto v___jp_1356_;
}
}
}
v___jp_1393_:
{
lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___f_1399_; lean_object* v___f_1400_; lean_object* v___f_1401_; uint8_t v___x_1402_; 
v___x_1397_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1398_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___f_1399_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1400_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1401_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1402_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1399_, v___f_1400_, v___x_1397_, v___y_1396_);
if (v___x_1402_ == 0)
{
if (v___y_1395_ == 0)
{
v___y_1373_ = v___y_1394_;
v___y_1374_ = v___f_1398_;
v___y_1375_ = v___f_1400_;
v___y_1376_ = v___f_1401_;
v___y_1377_ = v___f_1399_;
v___y_1378_ = v___y_1396_;
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
v___y_1373_ = v___y_1394_;
v___y_1374_ = v___f_1398_;
v___y_1375_ = v___f_1400_;
v___y_1376_ = v___f_1401_;
v___y_1377_ = v___f_1399_;
v___y_1378_ = v___y_1396_;
goto v___jp_1372_;
}
}
v___jp_1403_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_array_get_size(v___y_1409_);
v___x_1411_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1412_ = lean_nat_dec_lt(v___y_1406_, v___x_1410_);
if (v___x_1412_ == 0)
{
lean_dec_ref(v___y_1409_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1405_;
v___y_1396_ = v___y_1407_;
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
v___y_1395_ = v___y_1405_;
v___y_1396_ = v___y_1407_;
goto v___jp_1393_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1410_);
lean_inc_ref(v___y_1408_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___y_1408_, v___y_1409_, v___x_1414_, v___x_1415_, v___y_1407_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1405_;
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
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___y_1408_, v___y_1409_, v___x_1417_, v___x_1418_, v___y_1407_);
v___y_1394_ = v___y_1404_;
v___y_1395_ = v___y_1405_;
v___y_1396_ = v___x_1419_;
goto v___jp_1393_;
}
}
}
v___jp_1420_:
{
lean_object* v_entries_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_entries_1428_ = lean_ctor_get(v___y_1422_, 0);
lean_inc_ref(v_entries_1428_);
lean_dec_ref(v___y_1422_);
v___x_1429_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1423_, v___y_1426_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v___y_1423_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_array_get_size(v_entries_1428_);
v___x_1432_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1433_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1434_ = lean_nat_dec_lt(v___x_1430_, v___x_1431_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v_entries_1428_);
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___x_1430_;
v___y_1407_ = v___x_1429_;
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
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___x_1430_;
v___y_1407_ = v___x_1429_;
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
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___x_1430_;
v___y_1407_ = v___x_1429_;
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
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___x_1430_;
v___y_1407_ = v___x_1429_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___x_1441_;
goto v___jp_1403_;
}
}
}
v___jp_1443_:
{
lean_object* v_headerSize_1450_; lean_object* v_machine_1451_; lean_object* v_machine_1452_; lean_object* v_reader_1453_; lean_object* v_state_1454_; 
v_headerSize_1450_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1444_, v_a_1325_, v___y_1448_);
v_machine_1451_ = l___private_Std_Internal_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1442_, v___y_1447_, v_headerSize_1450_, v___y_1449_);
v_machine_1452_ = l___private_Std_Internal_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1442_, v_machine_1451_, v_a_1325_);
lean_dec(v_a_1325_);
v_reader_1453_ = lean_ctor_get(v_machine_1452_, 0);
lean_inc_ref(v_reader_1453_);
v_state_1454_ = lean_ctor_get(v_reader_1453_, 0);
lean_inc(v_state_1454_);
lean_dec_ref(v_reader_1453_);
if (lean_obj_tag(v_state_1454_) == 7)
{
lean_dec_ref(v_state_1454_);
v___y_1310_ = v___y_1446_;
v___y_1311_ = v_machine_1452_;
v___y_1312_ = v___y_1445_;
goto v___jp_1309_;
}
else
{
lean_dec(v_state_1454_);
v___y_1310_ = v___y_1446_;
v___y_1311_ = v_machine_1452_;
v___y_1312_ = v___y_1448_;
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
v___f_1465_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1466_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1465_, v___f_1466_, v_indexes_1461_, v___x_1464_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1465_, v___f_1466_, v_indexes_1461_, v___x_1468_);
lean_dec_ref(v_indexes_1461_);
v___y_1444_ = v___x_1459_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1458_;
v___y_1447_ = v_machine_1463_;
v___y_1448_ = v___y_1457_;
v___y_1449_ = v___x_1469_;
goto v___jp_1443_;
}
else
{
lean_dec_ref(v_indexes_1461_);
v___y_1444_ = v___x_1459_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1458_;
v___y_1447_ = v_machine_1463_;
v___y_1448_ = v___y_1457_;
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
v___f_1486_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15);
v___f_1487_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1488_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1489_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1490_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1487_, v___f_1488_, v___x_1485_, v___x_1484_);
if (v___x_1490_ == 0)
{
if (v___x_1482_ == 0)
{
v___y_1421_ = v___x_1483_;
v___y_1422_ = v___x_1484_;
v___y_1423_ = v___f_1487_;
v___y_1424_ = v___x_1482_;
v___y_1425_ = v___f_1486_;
v___y_1426_ = v___f_1488_;
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
v___y_1422_ = v___x_1484_;
v___y_1423_ = v___f_1487_;
v___y_1424_ = v___x_1482_;
v___y_1425_ = v___f_1486_;
v___y_1426_ = v___f_1488_;
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
v___f_1268_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1268_, 0, v___y_1261_);
lean_inc_ref(v___f_1268_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1269_, 0, v___f_1268_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1270_, 0, v_close_1257_);
lean_closure_set(v___f_1270_, 1, v_body_1255_);
lean_closure_set(v___f_1270_, 2, v___f_1269_);
lean_closure_set(v___f_1270_, 3, v___f_1268_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = 0;
v___x_1273_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1271_, v___x_1272_, v___x_1267_, v___f_1270_);
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
v___y_1275_ = v___y_1311_;
goto v___jp_1274_;
}
else
{
if (v___y_1310_ == 0)
{
lean_object* v_writer_1313_; uint8_t v_omitBody_1314_; 
v_writer_1313_ = lean_ctor_get(v___y_1311_, 1);
v_omitBody_1314_ = lean_ctor_get_uint8(v_writer_1313_, sizeof(void*)*6 + 2);
v___y_1261_ = v___y_1311_;
v_omitBody_1262_ = v_omitBody_1314_;
goto v___jp_1260_;
}
else
{
v___y_1275_ = v___y_1311_;
goto v___jp_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1494_, lean_object* v_body_1495_, lean_object* v_isClosed_1496_, lean_object* v_close_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1494_, v_body_1495_, v_isClosed_1496_, v_close_1497_, v_x_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v_config_1501_, lean_object* v_line_1502_, lean_object* v_body_1503_, lean_object* v_isClosed_1504_, lean_object* v_close_1505_, lean_object* v_machine_1506_, lean_object* v_x_1507_){
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
v___x_1511_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1501_, v_line_1502_);
v___f_1512_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1512_, 0, v___y_1510_);
lean_closure_set(v___f_1512_, 1, v_body_1503_);
lean_closure_set(v___f_1512_, 2, v_isClosed_1504_);
lean_closure_set(v___f_1512_, 3, v_close_1505_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = 0;
v___x_1515_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1513_, v___x_1514_, v___x_1511_, v___f_1512_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v_config_1558_, lean_object* v_line_1559_, lean_object* v_body_1560_, lean_object* v_isClosed_1561_, lean_object* v_close_1562_, lean_object* v_machine_1563_, lean_object* v_x_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v_config_1558_, v_line_1559_, v_body_1560_, v_isClosed_1561_, v_close_1562_, v_machine_1563_, v_x_1564_);
lean_dec_ref(v_config_1558_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1567_, lean_object* v_config_1568_, lean_object* v_machine_1569_, lean_object* v_res_1570_){
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
v___f_1578_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_1578_, 0, v_config_1568_);
lean_closure_set(v___f_1578_, 1, v_line_1575_);
lean_closure_set(v___f_1578_, 2, v_body_1576_);
lean_closure_set(v___f_1578_, 3, v_isClosed_1573_);
lean_closure_set(v___f_1578_, 4, v_close_1572_);
lean_closure_set(v___f_1578_, 5, v_machine_1569_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = 0;
v___x_1581_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1579_, v___x_1580_, v___x_1577_, v___f_1578_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1582_, lean_object* v_config_1583_, lean_object* v_machine_1584_, lean_object* v_res_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1582_, v_config_1583_, v_machine_1584_, v_res_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1588_, lean_object* v_inst_1589_, lean_object* v_config_1590_, lean_object* v_machine_1591_, lean_object* v_res_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1589_, v_config_1590_, v_machine_1591_, v_res_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1595_, lean_object* v_inst_1596_, lean_object* v_config_1597_, lean_object* v_machine_1598_, lean_object* v_res_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1595_, v_inst_1596_, v_config_1597_, v_machine_1598_, v_res_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1602_, lean_object* v___y_1603_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v_____do__lift_1609_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1617_, lean_object* v___y_1618_){
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
v___x_1632_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1636_, v___y_1637_);
lean_dec(v___y_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1640_, lean_object* v_x_1641_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1662_, v_x_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1666_, lean_object* v_requestStream_1667_, lean_object* v_keepAliveTimeout_1668_, lean_object* v_currentTimeout_1669_, lean_object* v_headerTimeout_1670_, lean_object* v_response_1671_, lean_object* v_respStream_1672_, lean_object* v_expectData_1673_, uint8_t v_handlerDispatched_1674_, lean_object* v_____r_1675_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1683_, lean_object* v_requestStream_1684_, lean_object* v_keepAliveTimeout_1685_, lean_object* v_currentTimeout_1686_, lean_object* v_headerTimeout_1687_, lean_object* v_response_1688_, lean_object* v_respStream_1689_, lean_object* v_expectData_1690_, lean_object* v_handlerDispatched_1691_, lean_object* v_____r_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_handlerDispatched_boxed_1694_; lean_object* v_res_1695_; 
v_handlerDispatched_boxed_1694_ = lean_unbox(v_handlerDispatched_1691_);
v_res_1695_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1683_, v_requestStream_1684_, v_keepAliveTimeout_1685_, v_currentTimeout_1686_, v_headerTimeout_1687_, v_response_1688_, v_respStream_1689_, v_expectData_1690_, v_handlerDispatched_boxed_1694_, v_____r_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1696_, lean_object* v_x_1697_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1710_, v_x_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1714_, lean_object* v___f_1715_, lean_object* v___f_1716_, lean_object* v_x_1717_){
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
v___x_1733_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1731_, v___x_1732_, v___x_1730_, v___f_1715_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1736_, lean_object* v___f_1737_, lean_object* v___f_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1736_, v___f_1737_, v___f_1738_, v_x_1739_);
return v_res_1741_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1758_, lean_object* v___f_1759_, lean_object* v_x_1760_){
_start:
{
if (lean_obj_tag(v_x_1760_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v___f_1759_);
lean_dec_ref(v___y_1758_);
v_a_1762_ = lean_ctor_get(v_x_1760_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_x_1760_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1764_ = v_x_1760_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v_x_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
}
else
{
lean_object* v_machine_1771_; lean_object* v_requestStream_1772_; lean_object* v_keepAliveTimeout_1773_; lean_object* v_currentTimeout_1774_; lean_object* v_headerTimeout_1775_; lean_object* v_response_1776_; lean_object* v_respStream_1777_; lean_object* v_expectData_1778_; uint8_t v_handlerDispatched_1779_; lean_object* v___x_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_4824__overap_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___f_1789_; lean_object* v___f_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
lean_dec_ref(v_x_1760_);
v_machine_1771_ = lean_ctor_get(v___y_1758_, 0);
lean_inc_ref(v_machine_1771_);
v_requestStream_1772_ = lean_ctor_get(v___y_1758_, 1);
lean_inc_ref_n(v_requestStream_1772_, 3);
v_keepAliveTimeout_1773_ = lean_ctor_get(v___y_1758_, 2);
lean_inc(v_keepAliveTimeout_1773_);
v_currentTimeout_1774_ = lean_ctor_get(v___y_1758_, 3);
lean_inc(v_currentTimeout_1774_);
v_headerTimeout_1775_ = lean_ctor_get(v___y_1758_, 4);
lean_inc(v_headerTimeout_1775_);
v_response_1776_ = lean_ctor_get(v___y_1758_, 5);
lean_inc_ref(v_response_1776_);
v_respStream_1777_ = lean_ctor_get(v___y_1758_, 6);
lean_inc(v_respStream_1777_);
v_expectData_1778_ = lean_ctor_get(v___y_1758_, 7);
lean_inc(v_expectData_1778_);
v_handlerDispatched_1779_ = lean_ctor_get_uint8(v___y_1758_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1758_);
v___x_1780_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1781_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_1782_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_1783_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8));
v___x_1784_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1784_, 0, lean_box(0));
lean_closure_set(v___x_1784_, 1, lean_box(0));
lean_closure_set(v___x_1784_, 2, lean_box(0));
lean_closure_set(v___x_1784_, 3, v___x_1780_);
lean_closure_set(v___x_1784_, 4, lean_box(0));
lean_closure_set(v___x_1784_, 5, lean_box(0));
lean_closure_set(v___x_1784_, 6, v___x_1783_);
lean_closure_set(v___x_1784_, 7, v___f_1759_);
v___x_4824__overap_1785_ = l_Std_Mutex_atomically___redArg(v___x_1780_, v___f_1781_, v___f_1782_, v_requestStream_1772_, v___x_1784_);
v___x_1786_ = lean_apply_1(v___x_4824__overap_1785_, lean_box(0));
v___x_1787_ = lean_box(v_handlerDispatched_1779_);
v___f_1788_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1788_, 0, v_machine_1771_);
lean_closure_set(v___f_1788_, 1, v_requestStream_1772_);
lean_closure_set(v___f_1788_, 2, v_keepAliveTimeout_1773_);
lean_closure_set(v___f_1788_, 3, v_currentTimeout_1774_);
lean_closure_set(v___f_1788_, 4, v_headerTimeout_1775_);
lean_closure_set(v___f_1788_, 5, v_response_1776_);
lean_closure_set(v___f_1788_, 6, v_respStream_1777_);
lean_closure_set(v___f_1788_, 7, v_expectData_1778_);
lean_closure_set(v___f_1788_, 8, v___x_1787_);
lean_inc_ref(v___f_1788_);
v___f_1789_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1789_, 0, v___f_1788_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1790_, 0, v_requestStream_1772_);
lean_closure_set(v___f_1790_, 1, v___f_1789_);
lean_closure_set(v___f_1790_, 2, v___f_1788_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = 0;
v___x_1793_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1791_, v___x_1792_, v___x_1786_, v___f_1790_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1794_, lean_object* v___f_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1794_, v___f_1795_, v_x_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1799_, lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v___y_1799_);
v_a_1802_ = lean_ctor_get(v_x_1800_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_x_1800_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1804_ = v_x_1800_;
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v_x_1800_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
}
else
{
lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1819_; 
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1800_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v_x_1800_, 0);
lean_dec(v_unused_1820_);
v___x_1812_ = v_x_1800_;
v_isShared_1813_ = v_isSharedCheck_1819_;
goto v_resetjp_1811_;
}
else
{
lean_dec(v_x_1800_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1819_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___y_1799_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1821_, v_x_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1825_, lean_object* v___f_1826_, lean_object* v___y_1827_, lean_object* v_x_1828_){
_start:
{
if (lean_obj_tag(v_x_1828_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___f_1826_);
lean_dec_ref(v_requestStream_1825_);
v_a_1830_ = lean_ctor_get(v_x_1828_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1828_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1832_ = v_x_1828_;
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v_x_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1853_; 
v_a_1839_ = lean_ctor_get(v_x_1828_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_x_1828_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1841_ = v_x_1828_;
v_isShared_1842_ = v_isSharedCheck_1853_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v_x_1828_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1853_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_unbox(v_a_1839_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1841_);
lean_dec_ref(v___y_1827_);
v___x_1844_ = l_Std_Http_Body_Stream_close(v_requestStream_1825_);
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = lean_unbox(v_a_1839_);
lean_dec(v_a_1839_);
v___x_1847_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1845_, v___x_1846_, v___x_1844_, v___f_1826_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v_a_1839_);
lean_dec_ref(v___f_1826_);
lean_dec_ref(v_requestStream_1825_);
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___y_1827_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1848_);
v___x_1850_ = v___x_1841_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1854_, lean_object* v___f_1855_, lean_object* v___y_1856_, lean_object* v_x_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1854_, v___f_1855_, v___y_1856_, v_x_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1860_, lean_object* v_machine_1861_, lean_object* v_a_1862_, uint8_t v_requiresData_1863_, lean_object* v_expectData_1864_, lean_object* v_pendingHead_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_pendingHead_1865_);
lean_dec(v_expectData_1864_);
lean_dec_ref(v_a_1862_);
lean_dec_ref(v_machine_1861_);
v_a_1868_ = lean_ctor_get(v_x_1866_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_x_1866_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1870_ = v_x_1866_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v_x_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1891_; 
v_a_1877_ = lean_ctor_get(v_x_1866_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_x_1866_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1879_ = v_x_1866_;
v_isShared_1880_ = v_isSharedCheck_1891_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v_x_1866_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1891_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_keepAliveTimeout_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v_keepAliveTimeout_1881_ = lean_ctor_get(v_config_1860_, 5);
lean_inc_n(v_keepAliveTimeout_1881_, 2);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_keepAliveTimeout_1881_);
v___x_1883_ = lean_box(0);
v___x_1884_ = 0;
v___x_1885_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1885_, 0, v_machine_1861_);
lean_ctor_set(v___x_1885_, 1, v_a_1862_);
lean_ctor_set(v___x_1885_, 2, v___x_1882_);
lean_ctor_set(v___x_1885_, 3, v_keepAliveTimeout_1881_);
lean_ctor_set(v___x_1885_, 4, v___x_1883_);
lean_ctor_set(v___x_1885_, 5, v_a_1877_);
lean_ctor_set(v___x_1885_, 6, v___x_1883_);
lean_ctor_set(v___x_1885_, 7, v_expectData_1864_);
lean_ctor_set(v___x_1885_, 8, v_pendingHead_1865_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*9, v_requiresData_1863_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*9 + 1, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1886_);
v___x_1888_ = v___x_1879_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1892_, lean_object* v_machine_1893_, lean_object* v_a_1894_, lean_object* v_requiresData_1895_, lean_object* v_expectData_1896_, lean_object* v_pendingHead_1897_, lean_object* v_x_1898_, lean_object* v___y_1899_){
_start:
{
uint8_t v_requiresData_boxed_1900_; lean_object* v_res_1901_; 
v_requiresData_boxed_1900_ = lean_unbox(v_requiresData_1895_);
v_res_1901_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1892_, v_machine_1893_, v_a_1894_, v_requiresData_boxed_1900_, v_expectData_1896_, v_pendingHead_1897_, v_x_1898_);
lean_dec_ref(v_config_1892_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1902_, lean_object* v_machine_1903_, uint8_t v_requiresData_1904_, lean_object* v_expectData_1905_, lean_object* v_pendingHead_1906_, lean_object* v_x_1907_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_pendingHead_1906_);
lean_dec(v_expectData_1905_);
lean_dec_ref(v_machine_1903_);
lean_dec_ref(v_config_1902_);
v_a_1909_ = lean_ctor_get(v_x_1907_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_x_1907_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1911_ = v_x_1907_;
v_isShared_1912_ = v_isSharedCheck_1917_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v_x_1907_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1917_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1933_; 
v_a_1918_ = lean_ctor_get(v_x_1907_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1907_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1920_ = v_x_1907_;
v_isShared_1921_ = v_isSharedCheck_1933_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v_x_1907_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1933_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___f_1925_; lean_object* v___x_1927_; 
v___x_1922_ = lean_box(0);
v___x_1923_ = l_Std_CloseableChannel_new___redArg(v___x_1922_);
v___x_1924_ = lean_box(v_requiresData_1904_);
v___f_1925_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1925_, 0, v_config_1902_);
lean_closure_set(v___f_1925_, 1, v_machine_1903_);
lean_closure_set(v___f_1925_, 2, v_a_1918_);
lean_closure_set(v___f_1925_, 3, v___x_1924_);
lean_closure_set(v___f_1925_, 4, v_expectData_1905_);
lean_closure_set(v___f_1925_, 5, v_pendingHead_1906_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1923_);
v___x_1927_ = v___x_1920_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1923_);
v___x_1927_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = 0;
v___x_1931_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1929_, v___x_1930_, v___x_1928_, v___f_1925_);
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1934_, lean_object* v_machine_1935_, lean_object* v_requiresData_1936_, lean_object* v_expectData_1937_, lean_object* v_pendingHead_1938_, lean_object* v_x_1939_, lean_object* v___y_1940_){
_start:
{
uint8_t v_requiresData_boxed_1941_; lean_object* v_res_1942_; 
v_requiresData_boxed_1941_ = lean_unbox(v_requiresData_1936_);
v_res_1942_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1934_, v_machine_1935_, v_requiresData_boxed_1941_, v_expectData_1937_, v_pendingHead_1938_, v_x_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1943_, lean_object* v_____r_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = l_Std_Http_Body_mkStream();
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = 0;
v___x_1949_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1947_, v___x_1948_, v___x_1946_, v___f_1943_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1950_, lean_object* v_____r_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1950_, v_____r_1951_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1954_, lean_object* v_val_1955_, lean_object* v___f_1956_, lean_object* v___f_1957_, lean_object* v_x_1958_){
_start:
{
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v___f_1957_);
lean_dec_ref(v___f_1956_);
lean_dec(v_val_1955_);
lean_dec_ref(v_close_1954_);
v_a_1960_ = lean_ctor_get(v_x_1958_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1962_ = v_x_1958_;
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v_x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1960_);
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
else
{
lean_object* v_a_1969_; uint8_t v___x_1970_; 
v_a_1969_ = lean_ctor_get(v_x_1958_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v_x_1958_);
v___x_1970_ = lean_unbox(v_a_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref(v___f_1957_);
v___x_1971_ = lean_apply_2(v_close_1954_, v_val_1955_, lean_box(0));
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_unbox(v_a_1969_);
lean_dec(v_a_1969_);
v___x_1974_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1972_, v___x_1973_, v___x_1971_, v___f_1956_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec(v_a_1969_);
lean_dec_ref(v___f_1956_);
lean_dec(v_val_1955_);
lean_dec_ref(v_close_1954_);
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_apply_2(v___f_1957_, v___x_1975_, lean_box(0));
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1977_, lean_object* v_val_1978_, lean_object* v___f_1979_, lean_object* v___f_1980_, lean_object* v_x_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1977_, v_val_1978_, v___f_1979_, v___f_1980_, v_x_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1984_, lean_object* v_inst_1985_, lean_object* v___f_1986_, lean_object* v___f_1987_, lean_object* v_____r_1988_){
_start:
{
if (lean_obj_tag(v_respStream_1984_) == 1)
{
lean_object* v_val_1990_; lean_object* v_close_1991_; lean_object* v_isClosed_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; 
v_val_1990_ = lean_ctor_get(v_respStream_1984_, 0);
lean_inc_n(v_val_1990_, 2);
lean_dec_ref(v_respStream_1984_);
v_close_1991_ = lean_ctor_get(v_inst_1985_, 1);
lean_inc_ref(v_close_1991_);
v_isClosed_1992_ = lean_ctor_get(v_inst_1985_, 2);
lean_inc_ref(v_isClosed_1992_);
lean_dec_ref(v_inst_1985_);
v___x_1993_ = lean_apply_2(v_isClosed_1992_, v_val_1990_, lean_box(0));
v___f_1994_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1994_, 0, v_close_1991_);
lean_closure_set(v___f_1994_, 1, v_val_1990_);
lean_closure_set(v___f_1994_, 2, v___f_1986_);
lean_closure_set(v___f_1994_, 3, v___f_1987_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = 0;
v___x_1997_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1995_, v___x_1996_, v___x_1993_, v___f_1994_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec_ref(v___f_1986_);
lean_dec_ref(v_inst_1985_);
lean_dec(v_respStream_1984_);
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_apply_2(v___f_1987_, v___x_1998_, lean_box(0));
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_2000_, lean_object* v_inst_2001_, lean_object* v___f_2002_, lean_object* v___f_2003_, lean_object* v_____r_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_2000_, v_inst_2001_, v___f_2002_, v___f_2003_, v_____r_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2007_, lean_object* v_keepAliveTimeout_2008_, lean_object* v_currentTimeout_2009_, lean_object* v_headerTimeout_2010_, lean_object* v_response_2011_, lean_object* v_respStream_2012_, uint8_t v_requiresData_2013_, lean_object* v_expectData_2014_, uint8_t v_handlerDispatched_2015_, lean_object* v_pendingHead_2016_, lean_object* v_x_2017_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_pendingHead_2016_);
lean_dec(v_expectData_2014_);
lean_dec(v_respStream_2012_);
lean_dec_ref(v_response_2011_);
lean_dec(v_headerTimeout_2010_);
lean_dec(v_currentTimeout_2009_);
lean_dec(v_keepAliveTimeout_2008_);
lean_dec_ref(v_requestStream_2007_);
v_a_2019_ = lean_ctor_get(v_x_2017_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_x_2017_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2021_ = v_x_2017_;
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v_x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2049_; 
v_a_2028_ = lean_ctor_get(v_x_2017_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_x_2017_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2030_ = v_x_2017_;
v_isShared_2031_ = v_isSharedCheck_2049_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v_x_2017_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2049_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_snd_2032_; uint8_t v___x_2033_; 
v_snd_2032_ = lean_ctor_get(v_a_2028_, 1);
v___x_2033_ = lean_unbox(v_snd_2032_);
if (v___x_2033_ == 0)
{
lean_object* v_fst_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_fst_2034_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_fst_2034_);
lean_dec(v_a_2028_);
v___x_2035_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2035_, 0, v_fst_2034_);
lean_ctor_set(v___x_2035_, 1, v_requestStream_2007_);
lean_ctor_set(v___x_2035_, 2, v_keepAliveTimeout_2008_);
lean_ctor_set(v___x_2035_, 3, v_currentTimeout_2009_);
lean_ctor_set(v___x_2035_, 4, v_headerTimeout_2010_);
lean_ctor_set(v___x_2035_, 5, v_response_2011_);
lean_ctor_set(v___x_2035_, 6, v_respStream_2012_);
lean_ctor_set(v___x_2035_, 7, v_expectData_2014_);
lean_ctor_set(v___x_2035_, 8, v_pendingHead_2016_);
lean_ctor_set_uint8(v___x_2035_, sizeof(void*)*9, v_requiresData_2013_);
lean_ctor_set_uint8(v___x_2035_, sizeof(void*)*9 + 1, v_handlerDispatched_2015_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2036_);
v___x_2038_ = v___x_2030_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
else
{
lean_object* v_fst_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
lean_dec(v_pendingHead_2016_);
v_fst_2041_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_fst_2041_);
lean_dec(v_a_2028_);
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2043_, 0, v_fst_2041_);
lean_ctor_set(v___x_2043_, 1, v_requestStream_2007_);
lean_ctor_set(v___x_2043_, 2, v_keepAliveTimeout_2008_);
lean_ctor_set(v___x_2043_, 3, v_currentTimeout_2009_);
lean_ctor_set(v___x_2043_, 4, v_headerTimeout_2010_);
lean_ctor_set(v___x_2043_, 5, v_response_2011_);
lean_ctor_set(v___x_2043_, 6, v_respStream_2012_);
lean_ctor_set(v___x_2043_, 7, v_expectData_2014_);
lean_ctor_set(v___x_2043_, 8, v___x_2042_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*9, v_requiresData_2013_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*9 + 1, v_handlerDispatched_2015_);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2044_);
v___x_2046_ = v___x_2030_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2050_, lean_object* v_keepAliveTimeout_2051_, lean_object* v_currentTimeout_2052_, lean_object* v_headerTimeout_2053_, lean_object* v_response_2054_, lean_object* v_respStream_2055_, lean_object* v_requiresData_2056_, lean_object* v_expectData_2057_, lean_object* v_handlerDispatched_2058_, lean_object* v_pendingHead_2059_, lean_object* v_x_2060_, lean_object* v___y_2061_){
_start:
{
uint8_t v_requiresData_boxed_2062_; uint8_t v_handlerDispatched_boxed_2063_; lean_object* v_res_2064_; 
v_requiresData_boxed_2062_ = lean_unbox(v_requiresData_2056_);
v_handlerDispatched_boxed_2063_ = lean_unbox(v_handlerDispatched_2058_);
v_res_2064_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2050_, v_keepAliveTimeout_2051_, v_currentTimeout_2052_, v_headerTimeout_2053_, v_response_2054_, v_respStream_2055_, v_requiresData_boxed_2062_, v_expectData_2057_, v_handlerDispatched_boxed_2063_, v_pendingHead_2059_, v_x_2060_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2077_, lean_object* v_inst_2078_, lean_object* v___f_2079_, lean_object* v_handler_2080_, lean_object* v___f_2081_, lean_object* v___f_2082_, lean_object* v_inst_2083_, lean_object* v_connectionContext_2084_, lean_object* v_a_2085_, lean_object* v_x_2086_, lean_object* v___y_2087_){
_start:
{
switch(lean_obj_tag(v_a_2085_))
{
case 0:
{
lean_object* v_head_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_connectionContext_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v___f_2081_);
lean_dec(v_handler_2080_);
lean_dec_ref(v___f_2079_);
lean_dec_ref(v_inst_2078_);
v_head_2089_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2091_ = v_a_2085_;
v_isShared_2092_ = v_isSharedCheck_2132_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_head_2089_);
lean_dec(v_a_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2132_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_machine_2093_; lean_object* v_requestStream_2094_; lean_object* v_response_2095_; lean_object* v_respStream_2096_; uint8_t v_requiresData_2097_; lean_object* v_expectData_2098_; uint8_t v_handlerDispatched_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2127_; 
v_machine_2093_ = lean_ctor_get(v___y_2087_, 0);
v_requestStream_2094_ = lean_ctor_get(v___y_2087_, 1);
v_response_2095_ = lean_ctor_get(v___y_2087_, 5);
v_respStream_2096_ = lean_ctor_get(v___y_2087_, 6);
v_requiresData_2097_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*9);
v_expectData_2098_ = lean_ctor_get(v___y_2087_, 7);
v_handlerDispatched_2099_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*9 + 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___y_2087_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; 
v_unused_2128_ = lean_ctor_get(v___y_2087_, 8);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v___y_2087_, 4);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v___y_2087_, 3);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v___y_2087_, 2);
lean_dec(v_unused_2131_);
v___x_2101_ = v___y_2087_;
v_isShared_2102_ = v_isSharedCheck_2127_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_expectData_2098_);
lean_inc(v_respStream_2096_);
lean_inc(v_response_2095_);
lean_inc(v_requestStream_2094_);
lean_inc(v_machine_2093_);
lean_dec(v___y_2087_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2127_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_lingeringTimeout_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v_lingeringTimeout_2103_ = lean_ctor_get(v_config_2077_, 4);
lean_inc(v_lingeringTimeout_2103_);
lean_dec_ref(v_config_2077_);
v___x_2104_ = lean_box(0);
lean_inc(v_head_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 1);
v___x_2106_ = v___x_2091_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_head_2089_);
v___x_2106_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
lean_inc_ref(v_requestStream_2094_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 8, v___x_2106_);
lean_ctor_set(v___x_2101_, 4, v___x_2104_);
lean_ctor_set(v___x_2101_, 3, v_lingeringTimeout_2103_);
lean_ctor_set(v___x_2101_, 2, v___x_2104_);
v___x_2108_ = v___x_2101_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_machine_2093_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_requestStream_2094_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_lingeringTimeout_2103_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2125_, 5, v_response_2095_);
lean_ctor_set(v_reuseFailAlloc_2125_, 6, v_respStream_2096_);
lean_ctor_set(v_reuseFailAlloc_2125_, 7, v_expectData_2098_);
lean_ctor_set(v_reuseFailAlloc_2125_, 8, v___x_2106_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*9, v_requiresData_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*9 + 1, v_handlerDispatched_2099_);
v___x_2108_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
uint8_t v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = 0;
v___x_2110_ = 1;
v___x_2111_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2109_, v_head_2089_, v___x_2110_);
lean_dec(v_head_2089_);
if (lean_obj_tag(v___x_2111_) == 1)
{
lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___f_2114_; lean_object* v___f_2115_; lean_object* v___x_5015__overap_2116_; lean_object* v___x_2117_; lean_object* v___f_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___f_2112_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2112_, 0, v___x_2111_);
v___x_2113_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2114_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_2115_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_5015__overap_2116_ = l_Std_Mutex_atomically___redArg(v___x_2113_, v___f_2114_, v___f_2115_, v_requestStream_2094_, v___f_2112_);
v___x_2117_ = lean_apply_1(v___x_5015__overap_2116_, lean_box(0));
v___f_2118_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2118_, 0, v___x_2108_);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = 0;
v___x_2121_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2119_, v___x_2120_, v___x_2117_, v___f_2118_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec(v___x_2111_);
lean_dec_ref(v_requestStream_2094_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2108_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_connectionContext_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v___f_2081_);
lean_dec(v_handler_2080_);
lean_dec_ref(v___f_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v_config_2077_);
v_size_2133_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2135_ = v_a_2085_;
v_isShared_2136_ = v_isSharedCheck_2160_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_size_2133_);
lean_dec(v_a_2085_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2160_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_machine_2137_; lean_object* v_requestStream_2138_; lean_object* v_keepAliveTimeout_2139_; lean_object* v_currentTimeout_2140_; lean_object* v_headerTimeout_2141_; lean_object* v_response_2142_; lean_object* v_respStream_2143_; uint8_t v_handlerDispatched_2144_; lean_object* v_pendingHead_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2158_; 
v_machine_2137_ = lean_ctor_get(v___y_2087_, 0);
v_requestStream_2138_ = lean_ctor_get(v___y_2087_, 1);
v_keepAliveTimeout_2139_ = lean_ctor_get(v___y_2087_, 2);
v_currentTimeout_2140_ = lean_ctor_get(v___y_2087_, 3);
v_headerTimeout_2141_ = lean_ctor_get(v___y_2087_, 4);
v_response_2142_ = lean_ctor_get(v___y_2087_, 5);
v_respStream_2143_ = lean_ctor_get(v___y_2087_, 6);
v_handlerDispatched_2144_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*9 + 1);
v_pendingHead_2145_ = lean_ctor_get(v___y_2087_, 8);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___y_2087_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v___y_2087_, 7);
lean_dec(v_unused_2159_);
v___x_2147_ = v___y_2087_;
v_isShared_2148_ = v_isSharedCheck_2158_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_pendingHead_2145_);
lean_inc(v_respStream_2143_);
lean_inc(v_response_2142_);
lean_inc(v_headerTimeout_2141_);
lean_inc(v_currentTimeout_2140_);
lean_inc(v_keepAliveTimeout_2139_);
lean_inc(v_requestStream_2138_);
lean_inc(v_machine_2137_);
lean_dec(v___y_2087_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2158_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
uint8_t v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = 1;
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 7, v_size_2133_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_machine_2137_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_requestStream_2138_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_keepAliveTimeout_2139_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_currentTimeout_2140_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_headerTimeout_2141_);
lean_ctor_set(v_reuseFailAlloc_2157_, 5, v_response_2142_);
lean_ctor_set(v_reuseFailAlloc_2157_, 6, v_respStream_2143_);
lean_ctor_set(v_reuseFailAlloc_2157_, 7, v_size_2133_);
lean_ctor_set(v_reuseFailAlloc_2157_, 8, v_pendingHead_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*9 + 1, v_handlerDispatched_2144_);
v___x_2151_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*9, v___x_2149_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2151_);
v___x_2153_ = v___x_2135_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2161_; lean_object* v_onFailure_2162_; lean_object* v___f_2163_; lean_object* v___y_2165_; 
lean_dec_ref(v_connectionContext_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v_config_2077_);
v_err_2161_ = lean_ctor_get(v_a_2085_, 0);
lean_inc(v_err_2161_);
lean_dec_ref(v_a_2085_);
v_onFailure_2162_ = lean_ctor_get(v_inst_2078_, 2);
lean_inc_ref(v_onFailure_2162_);
lean_dec_ref(v_inst_2078_);
v___f_2163_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2163_, 0, v___y_2087_);
lean_closure_set(v___f_2163_, 1, v___f_2079_);
switch(lean_obj_tag(v_err_2161_))
{
case 0:
{
lean_object* v___x_2171_; 
v___x_2171_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2165_ = v___x_2171_;
goto v___jp_2164_;
}
case 1:
{
lean_object* v___x_2172_; 
v___x_2172_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2165_ = v___x_2172_;
goto v___jp_2164_;
}
case 2:
{
lean_object* v___x_2173_; 
v___x_2173_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2165_ = v___x_2173_;
goto v___jp_2164_;
}
case 3:
{
lean_object* v___x_2174_; 
v___x_2174_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2165_ = v___x_2174_;
goto v___jp_2164_;
}
case 4:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2165_ = v___x_2175_;
goto v___jp_2164_;
}
case 5:
{
lean_object* v___x_2176_; 
v___x_2176_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2165_ = v___x_2176_;
goto v___jp_2164_;
}
case 6:
{
lean_object* v___x_2177_; 
v___x_2177_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2165_ = v___x_2177_;
goto v___jp_2164_;
}
case 7:
{
lean_object* v___x_2178_; 
v___x_2178_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2165_ = v___x_2178_;
goto v___jp_2164_;
}
case 8:
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2165_ = v___x_2179_;
goto v___jp_2164_;
}
case 9:
{
lean_object* v___x_2180_; 
v___x_2180_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2165_ = v___x_2180_;
goto v___jp_2164_;
}
case 10:
{
lean_object* v___x_2181_; 
v___x_2181_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2165_ = v___x_2181_;
goto v___jp_2164_;
}
default: 
{
lean_object* v_message_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_message_2182_ = lean_ctor_get(v_err_2161_, 0);
lean_inc_ref(v_message_2182_);
lean_dec_ref(v_err_2161_);
v___x_2183_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2184_ = lean_string_append(v___x_2183_, v_message_2182_);
lean_dec_ref(v_message_2182_);
v___y_2165_ = v___x_2184_;
goto v___jp_2164_;
}
}
v___jp_2164_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2166_ = lean_mk_io_user_error(v___y_2165_);
v___x_2167_ = lean_apply_3(v_onFailure_2162_, v_handler_2080_, v___x_2166_, lean_box(0));
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = 0;
v___x_2170_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2168_, v___x_2169_, v___x_2167_, v___f_2163_);
return v___x_2170_;
}
}
case 4:
{
lean_object* v_requestStream_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; lean_object* v___f_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_5068__overap_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v_connectionContext_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec_ref(v___f_2082_);
lean_dec(v_handler_2080_);
lean_dec_ref(v___f_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v_config_2077_);
v_requestStream_2185_ = lean_ctor_get(v___y_2087_, 1);
lean_inc_ref_n(v_requestStream_2185_, 2);
v___x_2186_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2187_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_2188_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_2189_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8));
v___x_2190_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2190_, 0, lean_box(0));
lean_closure_set(v___x_2190_, 1, lean_box(0));
lean_closure_set(v___x_2190_, 2, lean_box(0));
lean_closure_set(v___x_2190_, 3, v___x_2186_);
lean_closure_set(v___x_2190_, 4, lean_box(0));
lean_closure_set(v___x_2190_, 5, lean_box(0));
lean_closure_set(v___x_2190_, 6, v___x_2189_);
lean_closure_set(v___x_2190_, 7, v___f_2081_);
v___x_5068__overap_2191_ = l_Std_Mutex_atomically___redArg(v___x_2186_, v___f_2187_, v___f_2188_, v_requestStream_2185_, v___x_2190_);
v___x_2192_ = lean_apply_1(v___x_5068__overap_2191_, lean_box(0));
lean_inc_ref(v___y_2087_);
v___f_2193_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2193_, 0, v___y_2087_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2194_, 0, v_requestStream_2185_);
lean_closure_set(v___f_2194_, 1, v___f_2193_);
lean_closure_set(v___f_2194_, 2, v___y_2087_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = 0;
v___x_2197_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2195_, v___x_2196_, v___x_2192_, v___f_2194_);
return v___x_2197_;
}
case 6:
{
lean_object* v_machine_2198_; lean_object* v_requestStream_2199_; lean_object* v_respStream_2200_; uint8_t v_requiresData_2201_; lean_object* v_expectData_2202_; lean_object* v_pendingHead_2203_; lean_object* v___x_2204_; lean_object* v___f_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_5086__overap_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; 
lean_dec_ref(v_connectionContext_2084_);
lean_dec_ref(v___f_2081_);
lean_dec(v_handler_2080_);
lean_dec_ref(v___f_2079_);
lean_dec_ref(v_inst_2078_);
v_machine_2198_ = lean_ctor_get(v___y_2087_, 0);
lean_inc_ref(v_machine_2198_);
v_requestStream_2199_ = lean_ctor_get(v___y_2087_, 1);
lean_inc_ref_n(v_requestStream_2199_, 2);
v_respStream_2200_ = lean_ctor_get(v___y_2087_, 6);
lean_inc(v_respStream_2200_);
v_requiresData_2201_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*9);
v_expectData_2202_ = lean_ctor_get(v___y_2087_, 7);
lean_inc(v_expectData_2202_);
v_pendingHead_2203_ = lean_ctor_get(v___y_2087_, 8);
lean_inc(v_pendingHead_2203_);
lean_dec_ref(v___y_2087_);
v___x_2204_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2205_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_2206_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_2207_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8));
v___x_2208_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2208_, 0, lean_box(0));
lean_closure_set(v___x_2208_, 1, lean_box(0));
lean_closure_set(v___x_2208_, 2, lean_box(0));
lean_closure_set(v___x_2208_, 3, v___x_2204_);
lean_closure_set(v___x_2208_, 4, lean_box(0));
lean_closure_set(v___x_2208_, 5, lean_box(0));
lean_closure_set(v___x_2208_, 6, v___x_2207_);
lean_closure_set(v___x_2208_, 7, v___f_2082_);
v___x_5086__overap_2209_ = l_Std_Mutex_atomically___redArg(v___x_2204_, v___f_2205_, v___f_2206_, v_requestStream_2199_, v___x_2208_);
v___x_2210_ = lean_apply_1(v___x_5086__overap_2209_, lean_box(0));
v___x_2211_ = lean_box(v_requiresData_2201_);
v___f_2212_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2212_, 0, v_config_2077_);
lean_closure_set(v___f_2212_, 1, v_machine_2198_);
lean_closure_set(v___f_2212_, 2, v___x_2211_);
lean_closure_set(v___f_2212_, 3, v_expectData_2202_);
lean_closure_set(v___f_2212_, 4, v_pendingHead_2203_);
v___f_2213_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2213_, 0, v___f_2212_);
lean_inc_ref(v___f_2213_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2214_, 0, v___f_2213_);
v___f_2215_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2215_, 0, v_respStream_2200_);
lean_closure_set(v___f_2215_, 1, v_inst_2083_);
lean_closure_set(v___f_2215_, 2, v___f_2214_);
lean_closure_set(v___f_2215_, 3, v___f_2213_);
lean_inc_ref(v___f_2215_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2216_, 0, v___f_2215_);
v___f_2217_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2217_, 0, v_requestStream_2199_);
lean_closure_set(v___f_2217_, 1, v___f_2216_);
lean_closure_set(v___f_2217_, 2, v___f_2215_);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = 0;
v___x_2220_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2218_, v___x_2219_, v___x_2210_, v___f_2217_);
return v___x_2220_;
}
case 7:
{
lean_object* v_pendingHead_2221_; 
lean_dec_ref(v_inst_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v___f_2079_);
v_pendingHead_2221_ = lean_ctor_get(v___y_2087_, 8);
if (lean_obj_tag(v_pendingHead_2221_) == 1)
{
lean_object* v_machine_2222_; lean_object* v_requestStream_2223_; lean_object* v_keepAliveTimeout_2224_; lean_object* v_currentTimeout_2225_; lean_object* v_headerTimeout_2226_; lean_object* v_response_2227_; lean_object* v_respStream_2228_; uint8_t v_requiresData_2229_; lean_object* v_expectData_2230_; uint8_t v_handlerDispatched_2231_; lean_object* v_val_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___f_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; 
lean_inc_ref(v_pendingHead_2221_);
v_machine_2222_ = lean_ctor_get(v___y_2087_, 0);
lean_inc_ref(v_machine_2222_);
v_requestStream_2223_ = lean_ctor_get(v___y_2087_, 1);
lean_inc_ref(v_requestStream_2223_);
v_keepAliveTimeout_2224_ = lean_ctor_get(v___y_2087_, 2);
lean_inc(v_keepAliveTimeout_2224_);
v_currentTimeout_2225_ = lean_ctor_get(v___y_2087_, 3);
lean_inc(v_currentTimeout_2225_);
v_headerTimeout_2226_ = lean_ctor_get(v___y_2087_, 4);
lean_inc(v_headerTimeout_2226_);
v_response_2227_ = lean_ctor_get(v___y_2087_, 5);
lean_inc_ref(v_response_2227_);
v_respStream_2228_ = lean_ctor_get(v___y_2087_, 6);
lean_inc(v_respStream_2228_);
v_requiresData_2229_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*9);
v_expectData_2230_ = lean_ctor_get(v___y_2087_, 7);
lean_inc(v_expectData_2230_);
v_handlerDispatched_2231_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2087_);
v_val_2232_ = lean_ctor_get(v_pendingHead_2221_, 0);
lean_inc(v_val_2232_);
v___x_2233_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2078_, v_handler_2080_, v_machine_2222_, v_val_2232_, v_config_2077_, v_connectionContext_2084_);
v___x_2234_ = lean_box(v_requiresData_2229_);
v___x_2235_ = lean_box(v_handlerDispatched_2231_);
v___f_2236_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2236_, 0, v_requestStream_2223_);
lean_closure_set(v___f_2236_, 1, v_keepAliveTimeout_2224_);
lean_closure_set(v___f_2236_, 2, v_currentTimeout_2225_);
lean_closure_set(v___f_2236_, 3, v_headerTimeout_2226_);
lean_closure_set(v___f_2236_, 4, v_response_2227_);
lean_closure_set(v___f_2236_, 5, v_respStream_2228_);
lean_closure_set(v___f_2236_, 6, v___x_2234_);
lean_closure_set(v___f_2236_, 7, v_expectData_2230_);
lean_closure_set(v___f_2236_, 8, v___x_2235_);
lean_closure_set(v___f_2236_, 9, v_pendingHead_2221_);
v___x_2237_ = lean_unsigned_to_nat(0u);
v___x_2238_ = 0;
v___x_2239_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2237_, v___x_2238_, v___x_2233_, v___f_2236_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v_connectionContext_2084_);
lean_dec(v_handler_2080_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v_config_2077_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2087_);
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
default: 
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v_a_2085_);
lean_dec_ref(v_connectionContext_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec_ref(v___f_2082_);
lean_dec_ref(v___f_2081_);
lean_dec(v_handler_2080_);
lean_dec_ref(v___f_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v_config_2077_);
v___x_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___y_2087_);
v___x_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2246_, lean_object* v_inst_2247_, lean_object* v___f_2248_, lean_object* v_handler_2249_, lean_object* v___f_2250_, lean_object* v___f_2251_, lean_object* v_inst_2252_, lean_object* v_connectionContext_2253_, lean_object* v_a_2254_, lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2246_, v_inst_2247_, v___f_2248_, v_handler_2249_, v___f_2250_, v___f_2251_, v_inst_2252_, v_connectionContext_2253_, v_a_2254_, v_x_2255_, v___y_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v_x_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_handler_2269_, lean_object* v_config_2270_, lean_object* v_connectionContext_2271_, lean_object* v_events_2272_, lean_object* v_state_2273_){
_start:
{
lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; size_t v_sz_2278_; size_t v___x_2279_; lean_object* v___x_4027__overap_2280_; lean_object* v___x_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___f_2275_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2276_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2276_, 0, v_config_2270_);
lean_closure_set(v___f_2276_, 1, v_inst_2267_);
lean_closure_set(v___f_2276_, 2, v___f_2275_);
lean_closure_set(v___f_2276_, 3, v_handler_2269_);
lean_closure_set(v___f_2276_, 4, v___f_2275_);
lean_closure_set(v___f_2276_, 5, v___f_2275_);
lean_closure_set(v___f_2276_, 6, v_inst_2268_);
lean_closure_set(v___f_2276_, 7, v_connectionContext_2271_);
v___x_2277_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2278_ = lean_array_size(v_events_2272_);
v___x_2279_ = ((size_t)0ULL);
v___x_4027__overap_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2277_, v_events_2272_, v___f_2276_, v_sz_2278_, v___x_2279_, v_state_2273_);
v___x_2281_ = lean_apply_1(v___x_4027__overap_2280_, lean_box(0));
v___f_2282_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = 0;
v___x_2285_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2283_, v___x_2284_, v___x_2281_, v___f_2282_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_handler_2288_, lean_object* v_config_2289_, lean_object* v_connectionContext_2290_, lean_object* v_events_2291_, lean_object* v_state_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2286_, v_inst_2287_, v_handler_2288_, v_config_2289_, v_connectionContext_2290_, v_events_2291_, v_state_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2295_, lean_object* v_00_u03b2_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_handler_2299_, lean_object* v_config_2300_, lean_object* v_connectionContext_2301_, lean_object* v_events_2302_, lean_object* v_state_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2297_, v_inst_2298_, v_handler_2299_, v_config_2300_, v_connectionContext_2301_, v_events_2302_, v_state_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2306_, lean_object* v_00_u03b2_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_handler_2310_, lean_object* v_config_2311_, lean_object* v_connectionContext_2312_, lean_object* v_events_2313_, lean_object* v_state_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2306_, v_00_u03b2_2307_, v_inst_2308_, v_inst_2309_, v_handler_2310_, v_config_2311_, v_connectionContext_2312_, v_events_2313_, v_state_2314_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2317_){
_start:
{
if (lean_obj_tag(v_x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v_x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref(v_x_2317_);
v___x_2319_ = lean_task_pure(v_a_2318_);
return v___x_2319_;
}
else
{
lean_object* v_a_2320_; 
v_a_2320_ = lean_ctor_get(v_x_2317_, 0);
lean_inc_ref(v_a_2320_);
lean_dec_ref(v_x_2317_);
return v_a_2320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2321_, lean_object* v_requestStream_2322_, lean_object* v_keepAliveTimeout_2323_, lean_object* v_currentTimeout_2324_, lean_object* v_headerTimeout_2325_, lean_object* v_response_2326_, lean_object* v_respStream_2327_, uint8_t v_requiresData_2328_, lean_object* v_expectData_2329_, lean_object* v_x_2330_){
_start:
{
if (lean_obj_tag(v_x_2330_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_expectData_2329_);
lean_dec(v_respStream_2327_);
lean_dec_ref(v_response_2326_);
lean_dec(v_headerTimeout_2325_);
lean_dec(v_currentTimeout_2324_);
lean_dec(v_keepAliveTimeout_2323_);
lean_dec_ref(v_requestStream_2322_);
lean_dec_ref(v_machine_2321_);
v_a_2332_ = lean_ctor_get(v_x_2330_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_x_2330_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2334_ = v_x_2330_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v_x_2330_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
}
}
else
{
lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2351_; 
v_isSharedCheck_2351_ = !lean_is_exclusive(v_x_2330_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_x_2330_, 0);
lean_dec(v_unused_2352_);
v___x_2342_ = v_x_2330_;
v_isShared_2343_ = v_isSharedCheck_2351_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v_x_2330_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2351_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2344_ = 1;
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2346_, 0, v_machine_2321_);
lean_ctor_set(v___x_2346_, 1, v_requestStream_2322_);
lean_ctor_set(v___x_2346_, 2, v_keepAliveTimeout_2323_);
lean_ctor_set(v___x_2346_, 3, v_currentTimeout_2324_);
lean_ctor_set(v___x_2346_, 4, v_headerTimeout_2325_);
lean_ctor_set(v___x_2346_, 5, v_response_2326_);
lean_ctor_set(v___x_2346_, 6, v_respStream_2327_);
lean_ctor_set(v___x_2346_, 7, v_expectData_2329_);
lean_ctor_set(v___x_2346_, 8, v___x_2345_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*9, v_requiresData_2328_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*9 + 1, v___x_2344_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2346_);
v___x_2348_ = v___x_2342_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2346_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2353_, lean_object* v_requestStream_2354_, lean_object* v_keepAliveTimeout_2355_, lean_object* v_currentTimeout_2356_, lean_object* v_headerTimeout_2357_, lean_object* v_response_2358_, lean_object* v_respStream_2359_, lean_object* v_requiresData_2360_, lean_object* v_expectData_2361_, lean_object* v_x_2362_, lean_object* v___y_2363_){
_start:
{
uint8_t v_requiresData_boxed_2364_; lean_object* v_res_2365_; 
v_requiresData_boxed_2364_ = lean_unbox(v_requiresData_2360_);
v_res_2365_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2353_, v_requestStream_2354_, v_keepAliveTimeout_2355_, v_currentTimeout_2356_, v_headerTimeout_2357_, v_response_2358_, v_respStream_2359_, v_requiresData_boxed_2364_, v_expectData_2361_, v_x_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2366_, lean_object* v_response_2367_, lean_object* v___x_2368_, lean_object* v___f_2369_, lean_object* v_x_2370_){
_start:
{
if (lean_obj_tag(v_x_2370_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v___f_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v_response_2367_);
lean_dec_ref(v_toFunctor_2366_);
v_a_2372_ = lean_ctor_get(v_x_2370_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_x_2370_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2374_ = v_x_2370_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v_x_2370_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2395_; 
v_a_2381_ = lean_ctor_get(v_x_2370_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_x_2370_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2383_ = v_x_2370_;
v_isShared_2384_ = v_isSharedCheck_2395_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v_x_2370_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2395_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2385_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2385_, 0, lean_box(0));
lean_closure_set(v___x_2385_, 1, lean_box(0));
lean_closure_set(v___x_2385_, 2, v_toFunctor_2366_);
v___x_2386_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2386_, 0, lean_box(0));
lean_closure_set(v___x_2386_, 1, v_response_2367_);
v___x_2387_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2387_, 0, lean_box(0));
lean_closure_set(v___x_2387_, 1, lean_box(0));
lean_closure_set(v___x_2387_, 2, lean_box(0));
lean_closure_set(v___x_2387_, 3, v___x_2385_);
lean_closure_set(v___x_2387_, 4, v___x_2386_);
v___x_2388_ = 0;
lean_inc(v___x_2368_);
v___x_2389_ = l_BaseIO_chainTask___redArg(v_a_2381_, v___x_2387_, v___x_2368_, v___x_2388_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2389_);
v___x_2391_ = v___x_2383_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
v___x_2393_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2368_, v___x_2388_, v___x_2392_, v___f_2369_);
return v___x_2393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2396_, lean_object* v_response_2397_, lean_object* v___x_2398_, lean_object* v___f_2399_, lean_object* v_x_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2396_, v_response_2397_, v___x_2398_, v___f_2399_, v_x_2400_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2404_, lean_object* v_handler_2405_, lean_object* v_extensions_2406_, lean_object* v_connectionContext_2407_, lean_object* v_state_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v_toApplicative_2411_; lean_object* v_pendingHead_2412_; 
v___x_2410_ = l_instMonadBaseIO;
v_toApplicative_2411_ = lean_ctor_get(v___x_2410_, 0);
v_pendingHead_2412_ = lean_ctor_get(v_state_2408_, 8);
lean_inc(v_pendingHead_2412_);
if (lean_obj_tag(v_pendingHead_2412_) == 1)
{
lean_object* v_toFunctor_2413_; lean_object* v_machine_2414_; lean_object* v_requestStream_2415_; lean_object* v_keepAliveTimeout_2416_; lean_object* v_currentTimeout_2417_; lean_object* v_headerTimeout_2418_; lean_object* v_response_2419_; lean_object* v_respStream_2420_; uint8_t v_requiresData_2421_; lean_object* v_expectData_2422_; lean_object* v_val_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2445_; 
v_toFunctor_2413_ = lean_ctor_get(v_toApplicative_2411_, 0);
v_machine_2414_ = lean_ctor_get(v_state_2408_, 0);
lean_inc_ref(v_machine_2414_);
v_requestStream_2415_ = lean_ctor_get(v_state_2408_, 1);
lean_inc_ref(v_requestStream_2415_);
v_keepAliveTimeout_2416_ = lean_ctor_get(v_state_2408_, 2);
lean_inc(v_keepAliveTimeout_2416_);
v_currentTimeout_2417_ = lean_ctor_get(v_state_2408_, 3);
lean_inc(v_currentTimeout_2417_);
v_headerTimeout_2418_ = lean_ctor_get(v_state_2408_, 4);
lean_inc(v_headerTimeout_2418_);
v_response_2419_ = lean_ctor_get(v_state_2408_, 5);
lean_inc_ref(v_response_2419_);
v_respStream_2420_ = lean_ctor_get(v_state_2408_, 6);
lean_inc(v_respStream_2420_);
v_requiresData_2421_ = lean_ctor_get_uint8(v_state_2408_, sizeof(void*)*9);
v_expectData_2422_ = lean_ctor_get(v_state_2408_, 7);
lean_inc(v_expectData_2422_);
lean_dec_ref(v_state_2408_);
v_val_2423_ = lean_ctor_get(v_pendingHead_2412_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_pendingHead_2412_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2425_ = v_pendingHead_2412_;
v_isShared_2426_ = v_isSharedCheck_2445_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_val_2423_);
lean_dec(v_pendingHead_2412_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2445_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_onRequest_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___f_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v_onRequest_2427_ = lean_ctor_get(v_inst_2404_, 1);
lean_inc_ref(v_onRequest_2427_);
lean_dec_ref(v_inst_2404_);
lean_inc_ref(v_requestStream_2415_);
v___x_2428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2428_, 0, v_val_2423_);
lean_ctor_set(v___x_2428_, 1, v_requestStream_2415_);
lean_ctor_set(v___x_2428_, 2, v_extensions_2406_);
v___x_2429_ = lean_apply_3(v_onRequest_2427_, v_handler_2405_, v___x_2428_, v_connectionContext_2407_);
v___x_2430_ = lean_unsigned_to_nat(0u);
v___x_2431_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2431_, 0, lean_box(0));
lean_closure_set(v___x_2431_, 1, v___x_2429_);
v___x_2432_ = lean_io_as_task(v___x_2431_, v___x_2430_);
v___f_2433_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2434_ = lean_box(v_requiresData_2421_);
lean_inc_ref(v_response_2419_);
v___f_2435_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2435_, 0, v_machine_2414_);
lean_closure_set(v___f_2435_, 1, v_requestStream_2415_);
lean_closure_set(v___f_2435_, 2, v_keepAliveTimeout_2416_);
lean_closure_set(v___f_2435_, 3, v_currentTimeout_2417_);
lean_closure_set(v___f_2435_, 4, v_headerTimeout_2418_);
lean_closure_set(v___f_2435_, 5, v_response_2419_);
lean_closure_set(v___f_2435_, 6, v_respStream_2420_);
lean_closure_set(v___f_2435_, 7, v___x_2434_);
lean_closure_set(v___f_2435_, 8, v_expectData_2422_);
lean_inc_ref(v_toFunctor_2413_);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2436_, 0, v_toFunctor_2413_);
lean_closure_set(v___f_2436_, 1, v_response_2419_);
lean_closure_set(v___f_2436_, 2, v___x_2430_);
lean_closure_set(v___f_2436_, 3, v___f_2435_);
v___x_2437_ = 1;
v___x_2438_ = lean_task_bind(v___x_2432_, v___f_2433_, v___x_2430_, v___x_2437_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2438_);
v___x_2440_ = v___x_2425_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
v___x_2442_ = 0;
v___x_2443_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2430_, v___x_2442_, v___x_2441_, v___f_2436_);
return v___x_2443_;
}
}
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v_pendingHead_2412_);
lean_dec_ref(v_connectionContext_2407_);
lean_dec(v_extensions_2406_);
lean_dec(v_handler_2405_);
lean_dec_ref(v_inst_2404_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_state_2408_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2448_, lean_object* v_handler_2449_, lean_object* v_extensions_2450_, lean_object* v_connectionContext_2451_, lean_object* v_state_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2448_, v_handler_2449_, v_extensions_2450_, v_connectionContext_2451_, v_state_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2455_, lean_object* v_inst_2456_, lean_object* v_handler_2457_, lean_object* v_extensions_2458_, lean_object* v_connectionContext_2459_, lean_object* v_state_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2456_, v_handler_2457_, v_extensions_2458_, v_connectionContext_2459_, v_state_2460_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2463_, lean_object* v_inst_2464_, lean_object* v_handler_2465_, lean_object* v_extensions_2466_, lean_object* v_connectionContext_2467_, lean_object* v_state_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2463_, v_inst_2464_, v_handler_2465_, v_extensions_2466_, v_connectionContext_2467_, v_state_2468_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2471_, lean_object* v_____r_2472_){
_start:
{
lean_object* v_writer_2474_; lean_object* v_reader_2475_; lean_object* v_config_2476_; lean_object* v_events_2477_; lean_object* v_error_2478_; lean_object* v_instant_2479_; uint8_t v_keepAlive_2480_; uint8_t v_forcedFlush_2481_; uint8_t v_pullBodyStalled_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2509_; 
v_writer_2474_ = lean_ctor_get(v_machine_2471_, 1);
v_reader_2475_ = lean_ctor_get(v_machine_2471_, 0);
v_config_2476_ = lean_ctor_get(v_machine_2471_, 2);
v_events_2477_ = lean_ctor_get(v_machine_2471_, 3);
v_error_2478_ = lean_ctor_get(v_machine_2471_, 4);
v_instant_2479_ = lean_ctor_get(v_machine_2471_, 5);
v_keepAlive_2480_ = lean_ctor_get_uint8(v_machine_2471_, sizeof(void*)*6);
v_forcedFlush_2481_ = lean_ctor_get_uint8(v_machine_2471_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2482_ = lean_ctor_get_uint8(v_machine_2471_, sizeof(void*)*6 + 2);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_machine_2471_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2484_ = v_machine_2471_;
v_isShared_2485_ = v_isSharedCheck_2509_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_instant_2479_);
lean_inc(v_error_2478_);
lean_inc(v_events_2477_);
lean_inc(v_config_2476_);
lean_inc(v_writer_2474_);
lean_inc(v_reader_2475_);
lean_dec(v_machine_2471_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2509_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_userData_2486_; lean_object* v_outputData_2487_; lean_object* v_state_2488_; lean_object* v_knownSize_2489_; lean_object* v_messageHead_2490_; uint8_t v_sentMessage_2491_; uint8_t v_omitBody_2492_; lean_object* v_userDataBytes_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2508_; 
v_userData_2486_ = lean_ctor_get(v_writer_2474_, 0);
v_outputData_2487_ = lean_ctor_get(v_writer_2474_, 1);
v_state_2488_ = lean_ctor_get(v_writer_2474_, 2);
v_knownSize_2489_ = lean_ctor_get(v_writer_2474_, 3);
v_messageHead_2490_ = lean_ctor_get(v_writer_2474_, 4);
v_sentMessage_2491_ = lean_ctor_get_uint8(v_writer_2474_, sizeof(void*)*6);
v_omitBody_2492_ = lean_ctor_get_uint8(v_writer_2474_, sizeof(void*)*6 + 2);
v_userDataBytes_2493_ = lean_ctor_get(v_writer_2474_, 5);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_writer_2474_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2495_ = v_writer_2474_;
v_isShared_2496_ = v_isSharedCheck_2508_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_userDataBytes_2493_);
lean_inc(v_messageHead_2490_);
lean_inc(v_knownSize_2489_);
lean_inc(v_state_2488_);
lean_inc(v_outputData_2487_);
lean_inc(v_userData_2486_);
lean_dec(v_writer_2474_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2508_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
uint8_t v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = 1;
if (v_isShared_2496_ == 0)
{
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_userData_2486_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_outputData_2487_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_state_2488_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v_knownSize_2489_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v_messageHead_2490_);
lean_ctor_set(v_reuseFailAlloc_2507_, 5, v_userDataBytes_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, sizeof(void*)*6, v_sentMessage_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, sizeof(void*)*6 + 2, v_omitBody_2492_);
v___x_2499_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2501_; 
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*6 + 1, v___x_2497_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2499_);
v___x_2501_ = v___x_2484_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_reader_2475_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_config_2476_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_events_2477_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v_error_2478_);
lean_ctor_set(v_reuseFailAlloc_2506_, 5, v_instant_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*6, v_keepAlive_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*6 + 1, v_forcedFlush_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*6 + 2, v_pullBodyStalled_2482_);
v___x_2501_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2510_, lean_object* v_____r_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2510_, v_____r_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2514_, lean_object* v_x2_2515_){
_start:
{
lean_object* v_data_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_data_2516_ = lean_ctor_get(v_x2_2515_, 0);
v___x_2517_ = lean_byte_array_size(v_data_2516_);
v___x_2518_ = lean_nat_add(v_x1_2514_, v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2519_, lean_object* v_x2_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2519_, v_x2_2520_);
lean_dec_ref(v_x2_2520_);
lean_dec(v_x1_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2522_, lean_object* v_machine_2523_, lean_object* v_isClosed_2524_, lean_object* v___f_2525_, lean_object* v___f_2526_, lean_object* v_x_2527_){
_start:
{
lean_object* v___y_2530_; 
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v___f_2526_);
lean_dec_ref(v___f_2525_);
lean_dec_ref(v_isClosed_2524_);
lean_dec_ref(v_machine_2523_);
lean_dec(v_body_2522_);
v_a_2535_ = lean_ctor_get(v_x_2527_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2537_ = v_x_2527_;
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v_x_2527_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2611_; 
v_a_2544_ = lean_ctor_get(v_x_2527_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2546_ = v_x_2527_;
v_isShared_2547_ = v_isSharedCheck_2611_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v_x_2527_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2611_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
if (lean_obj_tag(v_a_2544_) == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_dec_ref(v___f_2526_);
lean_dec_ref(v___f_2525_);
lean_dec_ref(v_isClosed_2524_);
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_body_2522_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_machine_2523_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2549_);
v___x_2551_ = v___x_2546_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
else
{
lean_object* v_val_2554_; 
lean_del_object(v___x_2546_);
v_val_2554_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_val_2554_);
lean_dec_ref(v_a_2544_);
if (lean_obj_tag(v_val_2554_) == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_machine_2523_);
v___x_2555_ = lean_apply_2(v_isClosed_2524_, v_body_2522_, lean_box(0));
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = 0;
v___x_2558_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2556_, v___x_2557_, v___x_2555_, v___f_2525_);
return v___x_2558_;
}
else
{
lean_object* v_val_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
lean_dec_ref(v___f_2525_);
lean_dec_ref(v_isClosed_2524_);
v_val_2559_ = lean_ctor_get(v_val_2554_, 0);
lean_inc(v_val_2559_);
lean_dec_ref(v_val_2554_);
v___x_2560_ = lean_unsigned_to_nat(1u);
v___x_2561_ = lean_mk_empty_array_with_capacity(v___x_2560_);
v___x_2562_ = lean_array_push(v___x_2561_, v_val_2559_);
v___x_2563_ = lean_array_get_size(v___x_2562_);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = lean_nat_dec_eq(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v_reader_2566_; lean_object* v_writer_2567_; lean_object* v_config_2568_; lean_object* v_events_2569_; lean_object* v_error_2570_; lean_object* v_instant_2571_; uint8_t v_keepAlive_2572_; uint8_t v_forcedFlush_2573_; uint8_t v_pullBodyStalled_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2610_; 
v_reader_2566_ = lean_ctor_get(v_machine_2523_, 0);
v_writer_2567_ = lean_ctor_get(v_machine_2523_, 1);
v_config_2568_ = lean_ctor_get(v_machine_2523_, 2);
v_events_2569_ = lean_ctor_get(v_machine_2523_, 3);
v_error_2570_ = lean_ctor_get(v_machine_2523_, 4);
v_instant_2571_ = lean_ctor_get(v_machine_2523_, 5);
v_keepAlive_2572_ = lean_ctor_get_uint8(v_machine_2523_, sizeof(void*)*6);
v_forcedFlush_2573_ = lean_ctor_get_uint8(v_machine_2523_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2574_ = lean_ctor_get_uint8(v_machine_2523_, sizeof(void*)*6 + 2);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_machine_2523_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2576_ = v_machine_2523_;
v_isShared_2577_ = v_isSharedCheck_2610_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_instant_2571_);
lean_inc(v_error_2570_);
lean_inc(v_events_2569_);
lean_inc(v_config_2568_);
lean_inc(v_writer_2567_);
lean_inc(v_reader_2566_);
lean_dec(v_machine_2523_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2610_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___y_2579_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2602_ = lean_nat_dec_lt(v___x_2564_, v___x_2563_);
if (v___x_2602_ == 0)
{
lean_dec_ref(v___f_2526_);
v___y_2579_ = v___x_2564_;
goto v___jp_2578_;
}
else
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_nat_dec_le(v___x_2563_, v___x_2563_);
if (v___x_2603_ == 0)
{
if (v___x_2602_ == 0)
{
lean_dec_ref(v___f_2526_);
v___y_2579_ = v___x_2564_;
goto v___jp_2578_;
}
else
{
size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = lean_usize_of_nat(v___x_2563_);
lean_inc_ref(v___x_2562_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2601_, v___f_2526_, v___x_2562_, v___x_2604_, v___x_2605_, v___x_2564_);
v___y_2579_ = v___x_2606_;
goto v___jp_2578_;
}
}
else
{
size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = lean_usize_of_nat(v___x_2563_);
lean_inc_ref(v___x_2562_);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2601_, v___f_2526_, v___x_2562_, v___x_2607_, v___x_2608_, v___x_2564_);
v___y_2579_ = v___x_2609_;
goto v___jp_2578_;
}
}
v___jp_2578_:
{
lean_object* v_userData_2580_; lean_object* v_outputData_2581_; lean_object* v_state_2582_; lean_object* v_knownSize_2583_; lean_object* v_messageHead_2584_; uint8_t v_sentMessage_2585_; uint8_t v_userClosedBody_2586_; uint8_t v_omitBody_2587_; lean_object* v_userDataBytes_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2600_; 
v_userData_2580_ = lean_ctor_get(v_writer_2567_, 0);
v_outputData_2581_ = lean_ctor_get(v_writer_2567_, 1);
v_state_2582_ = lean_ctor_get(v_writer_2567_, 2);
v_knownSize_2583_ = lean_ctor_get(v_writer_2567_, 3);
v_messageHead_2584_ = lean_ctor_get(v_writer_2567_, 4);
v_sentMessage_2585_ = lean_ctor_get_uint8(v_writer_2567_, sizeof(void*)*6);
v_userClosedBody_2586_ = lean_ctor_get_uint8(v_writer_2567_, sizeof(void*)*6 + 1);
v_omitBody_2587_ = lean_ctor_get_uint8(v_writer_2567_, sizeof(void*)*6 + 2);
v_userDataBytes_2588_ = lean_ctor_get(v_writer_2567_, 5);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_writer_2567_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2590_ = v_writer_2567_;
v_isShared_2591_ = v_isSharedCheck_2600_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_userDataBytes_2588_);
lean_inc(v_messageHead_2584_);
lean_inc(v_knownSize_2583_);
lean_inc(v_state_2582_);
lean_inc(v_outputData_2581_);
lean_inc(v_userData_2580_);
lean_dec(v_writer_2567_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2600_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2592_ = l_Array_append___redArg(v_userData_2580_, v___x_2562_);
lean_dec_ref(v___x_2562_);
v___x_2593_ = lean_nat_add(v_userDataBytes_2588_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec(v_userDataBytes_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 5, v___x_2593_);
lean_ctor_set(v___x_2590_, 0, v___x_2592_);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_outputData_2581_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_state_2582_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_knownSize_2583_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_messageHead_2584_);
lean_ctor_set(v_reuseFailAlloc_2599_, 5, v___x_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*6, v_sentMessage_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*6 + 1, v_userClosedBody_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*6 + 2, v_omitBody_2587_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v___x_2595_);
v___x_2597_ = v___x_2576_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_reader_2566_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_config_2568_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_events_2569_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_error_2570_);
lean_ctor_set(v_reuseFailAlloc_2598_, 5, v_instant_2571_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, sizeof(void*)*6, v_keepAlive_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, sizeof(void*)*6 + 1, v_forcedFlush_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, sizeof(void*)*6 + 2, v_pullBodyStalled_2574_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
v___y_2530_ = v___x_2597_;
goto v___jp_2529_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2562_);
lean_dec_ref(v___f_2526_);
v___y_2530_ = v_machine_2523_;
goto v___jp_2529_;
}
}
}
}
}
v___jp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_body_2522_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___y_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2612_, lean_object* v_machine_2613_, lean_object* v_isClosed_2614_, lean_object* v___f_2615_, lean_object* v___f_2616_, lean_object* v_x_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2612_, v_machine_2613_, v_isClosed_2614_, v___f_2615_, v___f_2616_, v_x_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2621_, lean_object* v_machine_2622_, lean_object* v_body_2623_){
_start:
{
lean_object* v_close_2625_; lean_object* v_isClosed_2626_; lean_object* v_tryRecv_2627_; lean_object* v___x_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; 
v_close_2625_ = lean_ctor_get(v_inst_2621_, 1);
lean_inc_ref(v_close_2625_);
v_isClosed_2626_ = lean_ctor_get(v_inst_2621_, 2);
lean_inc_ref(v_isClosed_2626_);
v_tryRecv_2627_ = lean_ctor_get(v_inst_2621_, 4);
lean_inc_ref(v_tryRecv_2627_);
lean_dec_ref(v_inst_2621_);
lean_inc_n(v_body_2623_, 2);
v___x_2628_ = lean_apply_2(v_tryRecv_2627_, v_body_2623_, lean_box(0));
lean_inc_ref(v_machine_2622_);
v___f_2629_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2629_, 0, v_machine_2622_);
lean_inc_ref(v___f_2629_);
v___f_2630_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2630_, 0, v___f_2629_);
v___f_2631_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2631_, 0, v_close_2625_);
lean_closure_set(v___f_2631_, 1, v_body_2623_);
lean_closure_set(v___f_2631_, 2, v___f_2630_);
lean_closure_set(v___f_2631_, 3, v___f_2629_);
v___f_2632_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2633_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2633_, 0, v_body_2623_);
lean_closure_set(v___f_2633_, 1, v_machine_2622_);
lean_closure_set(v___f_2633_, 2, v_isClosed_2626_);
lean_closure_set(v___f_2633_, 3, v___f_2631_);
lean_closure_set(v___f_2633_, 4, v___f_2632_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = 0;
v___x_2636_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2634_, v___x_2635_, v___x_2628_, v___f_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2637_, lean_object* v_machine_2638_, lean_object* v_body_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2637_, v_machine_2638_, v_body_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2642_, lean_object* v_inst_2643_, lean_object* v_machine_2644_, lean_object* v_body_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2643_, v_machine_2644_, v_body_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2648_, lean_object* v_inst_2649_, lean_object* v_machine_2650_, lean_object* v_body_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2648_, v_inst_2649_, v_machine_2650_, v_body_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2660_, lean_object* v_____r_2661_, lean_object* v_st_2662_){
_start:
{
lean_object* v_machine_2664_; lean_object* v_requestStream_2665_; lean_object* v_keepAliveTimeout_2666_; lean_object* v_currentTimeout_2667_; lean_object* v_headerTimeout_2668_; lean_object* v_response_2669_; lean_object* v_respStream_2670_; uint8_t v_requiresData_2671_; lean_object* v_expectData_2672_; uint8_t v_handlerDispatched_2673_; lean_object* v_pendingHead_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2756_; 
v_machine_2664_ = lean_ctor_get(v_st_2662_, 0);
v_requestStream_2665_ = lean_ctor_get(v_st_2662_, 1);
v_keepAliveTimeout_2666_ = lean_ctor_get(v_st_2662_, 2);
v_currentTimeout_2667_ = lean_ctor_get(v_st_2662_, 3);
v_headerTimeout_2668_ = lean_ctor_get(v_st_2662_, 4);
v_response_2669_ = lean_ctor_get(v_st_2662_, 5);
v_respStream_2670_ = lean_ctor_get(v_st_2662_, 6);
v_requiresData_2671_ = lean_ctor_get_uint8(v_st_2662_, sizeof(void*)*9);
v_expectData_2672_ = lean_ctor_get(v_st_2662_, 7);
v_handlerDispatched_2673_ = lean_ctor_get_uint8(v_st_2662_, sizeof(void*)*9 + 1);
v_pendingHead_2674_ = lean_ctor_get(v_st_2662_, 8);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_st_2662_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2676_ = v_st_2662_;
v_isShared_2677_ = v_isSharedCheck_2756_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_pendingHead_2674_);
lean_inc(v_expectData_2672_);
lean_inc(v_respStream_2670_);
lean_inc(v_response_2669_);
lean_inc(v_headerTimeout_2668_);
lean_inc(v_currentTimeout_2667_);
lean_inc(v_keepAliveTimeout_2666_);
lean_inc(v_requestStream_2665_);
lean_inc(v_machine_2664_);
lean_dec(v_st_2662_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2756_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___y_2679_; lean_object* v_reader_2688_; lean_object* v_state_2689_; 
v_reader_2688_ = lean_ctor_get(v_machine_2664_, 0);
lean_inc_ref(v_reader_2688_);
v_state_2689_ = lean_ctor_get(v_reader_2688_, 0);
lean_inc(v_state_2689_);
if (lean_obj_tag(v_state_2689_) == 6)
{
lean_dec_ref(v_reader_2688_);
lean_dec_ref(v_val_2660_);
v___y_2679_ = v_machine_2664_;
goto v___jp_2678_;
}
else
{
if (lean_obj_tag(v_state_2689_) == 7)
{
lean_dec_ref(v_state_2689_);
lean_dec_ref(v_reader_2688_);
lean_dec_ref(v_val_2660_);
v___y_2679_ = v_machine_2664_;
goto v___jp_2678_;
}
else
{
lean_object* v_input_2690_; lean_object* v_writer_2691_; lean_object* v_config_2692_; lean_object* v_events_2693_; lean_object* v_error_2694_; lean_object* v_instant_2695_; uint8_t v_keepAlive_2696_; uint8_t v_forcedFlush_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2754_; 
v_input_2690_ = lean_ctor_get(v_reader_2688_, 1);
lean_inc_ref(v_input_2690_);
v_writer_2691_ = lean_ctor_get(v_machine_2664_, 1);
v_config_2692_ = lean_ctor_get(v_machine_2664_, 2);
v_events_2693_ = lean_ctor_get(v_machine_2664_, 3);
v_error_2694_ = lean_ctor_get(v_machine_2664_, 4);
v_instant_2695_ = lean_ctor_get(v_machine_2664_, 5);
v_keepAlive_2696_ = lean_ctor_get_uint8(v_machine_2664_, sizeof(void*)*6);
v_forcedFlush_2697_ = lean_ctor_get_uint8(v_machine_2664_, sizeof(void*)*6 + 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_machine_2664_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v_machine_2664_, 0);
lean_dec(v_unused_2755_);
v___x_2699_ = v_machine_2664_;
v_isShared_2700_ = v_isSharedCheck_2754_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_instant_2695_);
lean_inc(v_error_2694_);
lean_inc(v_events_2693_);
lean_inc(v_config_2692_);
lean_inc(v_writer_2691_);
lean_dec(v_machine_2664_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2754_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_messageHead_2701_; lean_object* v_messageCount_2702_; lean_object* v_bodyBytesRead_2703_; lean_object* v_headerBytesRead_2704_; uint8_t v_noMoreInput_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2751_; 
v_messageHead_2701_ = lean_ctor_get(v_reader_2688_, 2);
v_messageCount_2702_ = lean_ctor_get(v_reader_2688_, 3);
v_bodyBytesRead_2703_ = lean_ctor_get(v_reader_2688_, 4);
v_headerBytesRead_2704_ = lean_ctor_get(v_reader_2688_, 5);
v_noMoreInput_2705_ = lean_ctor_get_uint8(v_reader_2688_, sizeof(void*)*6);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_reader_2688_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2752_ = lean_ctor_get(v_reader_2688_, 1);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_reader_2688_, 0);
lean_dec(v_unused_2753_);
v___x_2707_ = v_reader_2688_;
v_isShared_2708_ = v_isSharedCheck_2751_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_headerBytesRead_2704_);
lean_inc(v_bodyBytesRead_2703_);
lean_inc(v_messageCount_2702_);
lean_inc(v_messageHead_2701_);
lean_dec(v_reader_2688_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2751_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v_array_2709_; lean_object* v_idx_2710_; uint8_t v___x_2711_; lean_object* v___y_2713_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_array_2709_ = lean_ctor_get(v_input_2690_, 0);
lean_inc_ref(v_array_2709_);
v_idx_2710_ = lean_ctor_get(v_input_2690_, 1);
lean_inc(v_idx_2710_);
lean_dec_ref(v_input_2690_);
v___x_2711_ = 0;
v___x_2742_ = lean_byte_array_size(v_array_2709_);
v___x_2743_ = lean_nat_dec_le(v___x_2742_, v_idx_2710_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2744_ = l_ByteArray_extract(v_array_2709_, v_idx_2710_, v___x_2742_);
lean_dec_ref(v_array_2709_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_byte_array_size(v___x_2744_);
v___x_2747_ = lean_byte_array_size(v_val_2660_);
v___x_2748_ = lean_byte_array_copy_slice(v_val_2660_, v___x_2745_, v___x_2744_, v___x_2746_, v___x_2747_, v___x_2743_);
lean_dec_ref(v_val_2660_);
v___x_2749_ = l_ByteArray_mkIterator(v___x_2748_);
v___y_2713_ = v___x_2749_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2750_; 
lean_dec(v_idx_2710_);
lean_dec_ref(v_array_2709_);
v___x_2750_ = l_ByteArray_mkIterator(v_val_2660_);
v___y_2713_ = v___x_2750_;
goto v___jp_2712_;
}
v___jp_2712_:
{
lean_object* v_maxHeaderBytes_2714_; lean_object* v_maxStartLineLength_2715_; lean_object* v_maxChunkLineLength_2716_; lean_object* v_maxBodySize_2717_; lean_object* v_array_2718_; lean_object* v_idx_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_maxHeaderBytes_2714_ = lean_ctor_get(v_config_2692_, 2);
v_maxStartLineLength_2715_ = lean_ctor_get(v_config_2692_, 5);
v_maxChunkLineLength_2716_ = lean_ctor_get(v_config_2692_, 13);
v_maxBodySize_2717_ = lean_ctor_get(v_config_2692_, 15);
v_array_2718_ = lean_ctor_get(v___y_2713_, 0);
v_idx_2719_ = lean_ctor_get(v___y_2713_, 1);
v___x_2720_ = lean_nat_add(v_maxBodySize_2717_, v_maxHeaderBytes_2714_);
v___x_2721_ = lean_nat_add(v___x_2720_, v_maxStartLineLength_2715_);
lean_dec(v___x_2720_);
v___x_2722_ = lean_nat_add(v___x_2721_, v_maxChunkLineLength_2716_);
lean_dec(v___x_2721_);
v___x_2723_ = lean_byte_array_size(v_array_2718_);
v___x_2724_ = lean_nat_sub(v___x_2723_, v_idx_2719_);
v___x_2725_ = lean_nat_dec_lt(v___x_2722_, v___x_2724_);
lean_dec(v___x_2724_);
lean_dec(v___x_2722_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___y_2713_);
v___x_2727_ = v___x_2707_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_state_2689_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v___y_2713_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_messageHead_2701_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_messageCount_2702_);
lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_bodyBytesRead_2703_);
lean_ctor_set(v_reuseFailAlloc_2731_, 5, v_headerBytesRead_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, sizeof(void*)*6, v_noMoreInput_2705_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v_machine_2729_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2727_);
v_machine_2729_ = v___x_2699_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_writer_2691_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_config_2692_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_events_2693_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_error_2694_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v_instant_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*6, v_keepAlive_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*6 + 1, v_forcedFlush_2697_);
v_machine_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_ctor_set_uint8(v_machine_2729_, sizeof(void*)*6 + 2, v___x_2711_);
v___y_2679_ = v_machine_2729_;
goto v___jp_2678_;
}
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_dec(v_error_2694_);
lean_dec(v_state_2689_);
v___x_2732_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2733_ = lean_array_push(v_events_2693_, v___x_2732_);
v___x_2734_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___y_2713_);
lean_ctor_set(v___x_2707_, 0, v___x_2734_);
v___x_2736_ = v___x_2707_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___y_2713_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_messageHead_2701_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v_messageCount_2702_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v_bodyBytesRead_2703_);
lean_ctor_set(v_reuseFailAlloc_2741_, 5, v_headerBytesRead_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2741_, sizeof(void*)*6, v_noMoreInput_2705_);
v___x_2736_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 4, v___x_2737_);
lean_ctor_set(v___x_2699_, 3, v___x_2733_);
lean_ctor_set(v___x_2699_, 0, v___x_2736_);
v___x_2739_ = v___x_2699_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_writer_2691_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_config_2692_);
lean_ctor_set(v_reuseFailAlloc_2740_, 3, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2740_, 4, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2740_, 5, v_instant_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2740_, sizeof(void*)*6, v_keepAlive_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2740_, sizeof(void*)*6 + 1, v_forcedFlush_2697_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*6 + 2, v___x_2711_);
v___y_2679_ = v___x_2739_;
goto v___jp_2678_;
}
}
}
}
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___y_2679_);
v___x_2681_ = v___x_2676_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___y_2679_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_requestStream_2665_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_keepAliveTimeout_2666_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_currentTimeout_2667_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_headerTimeout_2668_);
lean_ctor_set(v_reuseFailAlloc_2687_, 5, v_response_2669_);
lean_ctor_set(v_reuseFailAlloc_2687_, 6, v_respStream_2670_);
lean_ctor_set(v_reuseFailAlloc_2687_, 7, v_expectData_2672_);
lean_ctor_set(v_reuseFailAlloc_2687_, 8, v_pendingHead_2674_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*9, v_requiresData_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*9 + 1, v_handlerDispatched_2673_);
v___x_2681_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2682_ = 0;
v___x_2683_ = lean_box(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2757_, lean_object* v_____r_2758_, lean_object* v_st_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2757_, v_____r_2758_, v_st_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2762_, lean_object* v_machine_2763_, lean_object* v_requestStream_2764_, lean_object* v_currentTimeout_2765_, lean_object* v_response_2766_, lean_object* v_respStream_2767_, uint8_t v_requiresData_2768_, lean_object* v_expectData_2769_, uint8_t v_handlerDispatched_2770_, lean_object* v_pendingHead_2771_, lean_object* v___f_2772_, lean_object* v_x_2773_){
_start:
{
if (lean_obj_tag(v_x_2773_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v___f_2772_);
lean_dec(v_pendingHead_2771_);
lean_dec(v_expectData_2769_);
lean_dec(v_respStream_2767_);
lean_dec_ref(v_response_2766_);
lean_dec(v_currentTimeout_2765_);
lean_dec_ref(v_requestStream_2764_);
lean_dec_ref(v_machine_2763_);
v_a_2775_ = lean_ctor_get(v_x_2773_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_x_2773_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2777_ = v_x_2773_;
v_isShared_2778_ = v_isSharedCheck_2783_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v_x_2773_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2783_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
return v___x_2781_;
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v_headerTimeout_2785_; lean_object* v_second_2786_; lean_object* v_nano_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v_second_2791_; lean_object* v_nano_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2784_ = lean_ctor_get(v_x_2773_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v_x_2773_);
v_headerTimeout_2785_ = lean_ctor_get(v_config_2762_, 6);
v_second_2786_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_second_2786_);
v_nano_2787_ = lean_ctor_get(v_a_2784_, 1);
lean_inc(v_nano_2787_);
lean_dec(v_a_2784_);
v___x_2788_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2789_ = lean_int_mul(v_headerTimeout_2785_, v___x_2788_);
v___x_2790_ = l_Std_Time_Duration_ofNanoseconds(v___x_2789_);
lean_dec(v___x_2789_);
v_second_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_second_2791_);
v_nano_2792_ = lean_ctor_get(v___x_2790_, 1);
lean_inc(v_nano_2792_);
lean_dec_ref(v___x_2790_);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2795_ = lean_int_mul(v_second_2786_, v___x_2794_);
lean_dec(v_second_2786_);
v___x_2796_ = lean_int_add(v___x_2795_, v_nano_2787_);
lean_dec(v_nano_2787_);
lean_dec(v___x_2795_);
v___x_2797_ = lean_int_mul(v_second_2791_, v___x_2794_);
lean_dec(v_second_2791_);
v___x_2798_ = lean_int_add(v___x_2797_, v_nano_2792_);
lean_dec(v_nano_2792_);
lean_dec(v___x_2797_);
v___x_2799_ = lean_int_add(v___x_2796_, v___x_2798_);
lean_dec(v___x_2798_);
lean_dec(v___x_2796_);
v___x_2800_ = l_Std_Time_Duration_ofNanoseconds(v___x_2799_);
lean_dec(v___x_2799_);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2802_, 0, v_machine_2763_);
lean_ctor_set(v___x_2802_, 1, v_requestStream_2764_);
lean_ctor_set(v___x_2802_, 2, v___x_2793_);
lean_ctor_set(v___x_2802_, 3, v_currentTimeout_2765_);
lean_ctor_set(v___x_2802_, 4, v___x_2801_);
lean_ctor_set(v___x_2802_, 5, v_response_2766_);
lean_ctor_set(v___x_2802_, 6, v_respStream_2767_);
lean_ctor_set(v___x_2802_, 7, v_expectData_2769_);
lean_ctor_set(v___x_2802_, 8, v_pendingHead_2771_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*9, v_requiresData_2768_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*9 + 1, v_handlerDispatched_2770_);
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_apply_3(v___f_2772_, v___x_2803_, v___x_2802_, lean_box(0));
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2805_, lean_object* v_machine_2806_, lean_object* v_requestStream_2807_, lean_object* v_currentTimeout_2808_, lean_object* v_response_2809_, lean_object* v_respStream_2810_, lean_object* v_requiresData_2811_, lean_object* v_expectData_2812_, lean_object* v_handlerDispatched_2813_, lean_object* v_pendingHead_2814_, lean_object* v___f_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_){
_start:
{
uint8_t v_requiresData_boxed_2818_; uint8_t v_handlerDispatched_boxed_2819_; lean_object* v_res_2820_; 
v_requiresData_boxed_2818_ = lean_unbox(v_requiresData_2811_);
v_handlerDispatched_boxed_2819_ = lean_unbox(v_handlerDispatched_2813_);
v_res_2820_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2805_, v_machine_2806_, v_requestStream_2807_, v_currentTimeout_2808_, v_response_2809_, v_respStream_2810_, v_requiresData_boxed_2818_, v_expectData_2812_, v_handlerDispatched_boxed_2819_, v_pendingHead_2814_, v___f_2815_, v_x_2816_);
lean_dec_ref(v_config_2805_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2821_, lean_object* v_requestStream_2822_, lean_object* v_keepAliveTimeout_2823_, lean_object* v_currentTimeout_2824_, lean_object* v_headerTimeout_2825_, lean_object* v_response_2826_, uint8_t v_requiresData_2827_, lean_object* v_expectData_2828_, uint8_t v_handlerDispatched_2829_, lean_object* v_pendingHead_2830_, lean_object* v_____r_2831_){
_start:
{
lean_object* v_writer_2833_; lean_object* v_reader_2834_; lean_object* v_config_2835_; lean_object* v_events_2836_; lean_object* v_error_2837_; lean_object* v_instant_2838_; uint8_t v_keepAlive_2839_; uint8_t v_forcedFlush_2840_; uint8_t v_pullBodyStalled_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2871_; 
v_writer_2833_ = lean_ctor_get(v_machine_2821_, 1);
v_reader_2834_ = lean_ctor_get(v_machine_2821_, 0);
v_config_2835_ = lean_ctor_get(v_machine_2821_, 2);
v_events_2836_ = lean_ctor_get(v_machine_2821_, 3);
v_error_2837_ = lean_ctor_get(v_machine_2821_, 4);
v_instant_2838_ = lean_ctor_get(v_machine_2821_, 5);
v_keepAlive_2839_ = lean_ctor_get_uint8(v_machine_2821_, sizeof(void*)*6);
v_forcedFlush_2840_ = lean_ctor_get_uint8(v_machine_2821_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2841_ = lean_ctor_get_uint8(v_machine_2821_, sizeof(void*)*6 + 2);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_machine_2821_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2843_ = v_machine_2821_;
v_isShared_2844_ = v_isSharedCheck_2871_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_instant_2838_);
lean_inc(v_error_2837_);
lean_inc(v_events_2836_);
lean_inc(v_config_2835_);
lean_inc(v_writer_2833_);
lean_inc(v_reader_2834_);
lean_dec(v_machine_2821_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2871_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_userData_2845_; lean_object* v_outputData_2846_; lean_object* v_state_2847_; lean_object* v_knownSize_2848_; lean_object* v_messageHead_2849_; uint8_t v_sentMessage_2850_; uint8_t v_omitBody_2851_; lean_object* v_userDataBytes_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2870_; 
v_userData_2845_ = lean_ctor_get(v_writer_2833_, 0);
v_outputData_2846_ = lean_ctor_get(v_writer_2833_, 1);
v_state_2847_ = lean_ctor_get(v_writer_2833_, 2);
v_knownSize_2848_ = lean_ctor_get(v_writer_2833_, 3);
v_messageHead_2849_ = lean_ctor_get(v_writer_2833_, 4);
v_sentMessage_2850_ = lean_ctor_get_uint8(v_writer_2833_, sizeof(void*)*6);
v_omitBody_2851_ = lean_ctor_get_uint8(v_writer_2833_, sizeof(void*)*6 + 2);
v_userDataBytes_2852_ = lean_ctor_get(v_writer_2833_, 5);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_writer_2833_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2854_ = v_writer_2833_;
v_isShared_2855_ = v_isSharedCheck_2870_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_userDataBytes_2852_);
lean_inc(v_messageHead_2849_);
lean_inc(v_knownSize_2848_);
lean_inc(v_state_2847_);
lean_inc(v_outputData_2846_);
lean_inc(v_userData_2845_);
lean_dec(v_writer_2833_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2870_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
uint8_t v___x_2856_; lean_object* v___x_2858_; 
v___x_2856_ = 1;
if (v_isShared_2855_ == 0)
{
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_userData_2845_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_outputData_2846_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_state_2847_);
lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_knownSize_2848_);
lean_ctor_set(v_reuseFailAlloc_2869_, 4, v_messageHead_2849_);
lean_ctor_set(v_reuseFailAlloc_2869_, 5, v_userDataBytes_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*6, v_sentMessage_2850_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*6 + 2, v_omitBody_2851_);
v___x_2858_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2860_; 
lean_ctor_set_uint8(v___x_2858_, sizeof(void*)*6 + 1, v___x_2856_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 1, v___x_2858_);
v___x_2860_ = v___x_2843_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_reader_2834_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_config_2835_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_events_2836_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_error_2837_);
lean_ctor_set(v_reuseFailAlloc_2868_, 5, v_instant_2838_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*6, v_keepAlive_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*6 + 1, v_forcedFlush_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*6 + 2, v_pullBodyStalled_2841_);
v___x_2860_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v_requestStream_2822_);
lean_ctor_set(v___x_2862_, 2, v_keepAliveTimeout_2823_);
lean_ctor_set(v___x_2862_, 3, v_currentTimeout_2824_);
lean_ctor_set(v___x_2862_, 4, v_headerTimeout_2825_);
lean_ctor_set(v___x_2862_, 5, v_response_2826_);
lean_ctor_set(v___x_2862_, 6, v___x_2861_);
lean_ctor_set(v___x_2862_, 7, v_expectData_2828_);
lean_ctor_set(v___x_2862_, 8, v_pendingHead_2830_);
lean_ctor_set_uint8(v___x_2862_, sizeof(void*)*9, v_requiresData_2827_);
lean_ctor_set_uint8(v___x_2862_, sizeof(void*)*9 + 1, v_handlerDispatched_2829_);
v___x_2863_ = 0;
v___x_2864_ = lean_box(v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2862_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2872_, lean_object* v_requestStream_2873_, lean_object* v_keepAliveTimeout_2874_, lean_object* v_currentTimeout_2875_, lean_object* v_headerTimeout_2876_, lean_object* v_response_2877_, lean_object* v_requiresData_2878_, lean_object* v_expectData_2879_, lean_object* v_handlerDispatched_2880_, lean_object* v_pendingHead_2881_, lean_object* v_____r_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v_requiresData_boxed_2884_; uint8_t v_handlerDispatched_boxed_2885_; lean_object* v_res_2886_; 
v_requiresData_boxed_2884_ = lean_unbox(v_requiresData_2878_);
v_handlerDispatched_boxed_2885_ = lean_unbox(v_handlerDispatched_2880_);
v_res_2886_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2872_, v_requestStream_2873_, v_keepAliveTimeout_2874_, v_currentTimeout_2875_, v_headerTimeout_2876_, v_response_2877_, v_requiresData_boxed_2884_, v_expectData_2879_, v_handlerDispatched_boxed_2885_, v_pendingHead_2881_, v_____r_2882_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2887_, lean_object* v_x_2888_){
_start:
{
if (lean_obj_tag(v_x_2888_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2898_; 
lean_dec_ref(v___f_2887_);
v_a_2890_ = lean_ctor_get(v_x_2888_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_x_2888_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2892_ = v_x_2888_;
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v_x_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2900_; 
v_a_2899_ = lean_ctor_get(v_x_2888_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v_x_2888_);
v___x_2900_ = lean_apply_2(v___f_2887_, v_a_2899_, lean_box(0));
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2901_, lean_object* v_x_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2901_, v_x_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2905_, lean_object* v_val_2906_, lean_object* v___f_2907_, lean_object* v___f_2908_, lean_object* v_x_2909_){
_start:
{
if (lean_obj_tag(v_x_2909_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___f_2908_);
lean_dec_ref(v___f_2907_);
lean_dec(v_val_2906_);
lean_dec_ref(v_close_2905_);
v_a_2911_ = lean_ctor_get(v_x_2909_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_x_2909_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2913_ = v_x_2909_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v_x_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
}
}
else
{
lean_object* v_a_2920_; uint8_t v___x_2921_; 
v_a_2920_ = lean_ctor_get(v_x_2909_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v_x_2909_);
v___x_2921_ = lean_unbox(v_a_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; lean_object* v___x_2925_; 
lean_dec_ref(v___f_2908_);
v___x_2922_ = lean_apply_2(v_close_2905_, v_val_2906_, lean_box(0));
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = lean_unbox(v_a_2920_);
lean_dec(v_a_2920_);
v___x_2925_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2923_, v___x_2924_, v___x_2922_, v___f_2907_);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v_a_2920_);
lean_dec_ref(v___f_2907_);
lean_dec(v_val_2906_);
lean_dec_ref(v_close_2905_);
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_apply_2(v___f_2908_, v___x_2926_, lean_box(0));
return v___x_2927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2928_, lean_object* v_val_2929_, lean_object* v___f_2930_, lean_object* v___f_2931_, lean_object* v_x_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2928_, v_val_2929_, v___f_2930_, v___f_2931_, v_x_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2935_, lean_object* v_handler_2936_, lean_object* v_x_2937_){
_start:
{
if (lean_obj_tag(v_x_2937_) == 0)
{
lean_object* v_a_2939_; lean_object* v_onFailure_2940_; lean_object* v___x_2941_; 
v_a_2939_ = lean_ctor_get(v_x_2937_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v_x_2937_);
v_onFailure_2940_ = lean_ctor_get(v_inst_2935_, 2);
lean_inc_ref(v_onFailure_2940_);
lean_dec_ref(v_inst_2935_);
v___x_2941_ = lean_apply_3(v_onFailure_2940_, v_handler_2936_, v_a_2939_, lean_box(0));
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; 
lean_dec(v_handler_2936_);
lean_dec_ref(v_inst_2935_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_x_2937_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2943_, lean_object* v_handler_2944_, lean_object* v_x_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2943_, v_handler_2944_, v_x_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2948_, lean_object* v_____r_2949_){
_start:
{
uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2951_ = 0;
v___x_2952_ = lean_box(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_st_2948_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2956_, lean_object* v_____r_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2956_, v_____r_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2960_, lean_object* v___f_2961_, lean_object* v___f_2962_, lean_object* v_x_2963_){
_start:
{
if (lean_obj_tag(v_x_2963_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v___f_2962_);
lean_dec_ref(v___f_2961_);
lean_dec_ref(v_requestStream_2960_);
v_a_2965_ = lean_ctor_get(v_x_2963_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_x_2963_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2967_ = v_x_2963_;
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v_x_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
}
}
else
{
lean_object* v_a_2974_; uint8_t v___x_2975_; 
v_a_2974_ = lean_ctor_get(v_x_2963_, 0);
lean_inc(v_a_2974_);
lean_dec_ref(v_x_2963_);
v___x_2975_ = lean_unbox(v_a_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref(v___f_2962_);
v___x_2976_ = l_Std_Http_Body_Stream_close(v_requestStream_2960_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_unbox(v_a_2974_);
lean_dec(v_a_2974_);
v___x_2979_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2977_, v___x_2978_, v___x_2976_, v___f_2961_);
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v_a_2974_);
lean_dec_ref(v___f_2961_);
lean_dec_ref(v_requestStream_2960_);
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_apply_2(v___f_2962_, v___x_2980_, lean_box(0));
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2982_, lean_object* v___f_2983_, lean_object* v___f_2984_, lean_object* v_x_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2982_, v___f_2983_, v___f_2984_, v_x_2985_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2988_, lean_object* v___f_2989_, lean_object* v___f_2990_, lean_object* v_requestStream_2991_, lean_object* v___f_2992_, lean_object* v_x_2993_){
_start:
{
if (lean_obj_tag(v_x_2993_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v___f_2992_);
lean_dec_ref(v_requestStream_2991_);
lean_dec_ref(v___f_2990_);
lean_dec_ref(v___f_2989_);
v_a_2995_ = lean_ctor_get(v_x_2993_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_x_2993_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2997_ = v_x_2993_;
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v_x_2993_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
}
else
{
lean_dec_ref(v_x_2993_);
if (v_final_2988_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec_ref(v___f_2992_);
lean_dec_ref(v_requestStream_2991_);
lean_dec_ref(v___f_2990_);
v___x_3004_ = lean_box(0);
v___x_3005_ = lean_apply_2(v___f_2989_, v___x_3004_, lean_box(0));
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; lean_object* v___f_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_6977__overap_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; 
lean_dec_ref(v___f_2989_);
v___x_3006_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3007_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_3008_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_3009_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8));
v___x_3010_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3010_, 0, lean_box(0));
lean_closure_set(v___x_3010_, 1, lean_box(0));
lean_closure_set(v___x_3010_, 2, lean_box(0));
lean_closure_set(v___x_3010_, 3, v___x_3006_);
lean_closure_set(v___x_3010_, 4, lean_box(0));
lean_closure_set(v___x_3010_, 5, lean_box(0));
lean_closure_set(v___x_3010_, 6, v___x_3009_);
lean_closure_set(v___x_3010_, 7, v___f_2990_);
v___x_6977__overap_3011_ = l_Std_Mutex_atomically___redArg(v___x_3006_, v___f_3007_, v___f_3008_, v_requestStream_2991_, v___x_3010_);
v___x_3012_ = lean_apply_1(v___x_6977__overap_3011_, lean_box(0));
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = 0;
v___x_3015_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3013_, v___x_3014_, v___x_3012_, v___f_2992_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3016_, lean_object* v___f_3017_, lean_object* v___f_3018_, lean_object* v_requestStream_3019_, lean_object* v___f_3020_, lean_object* v_x_3021_, lean_object* v___y_3022_){
_start:
{
uint8_t v_final_boxed_3023_; lean_object* v_res_3024_; 
v_final_boxed_3023_ = lean_unbox(v_final_3016_);
v_res_3024_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3023_, v___f_3017_, v___f_3018_, v_requestStream_3019_, v___f_3020_, v_x_3021_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3025_, lean_object* v_x_3026_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v_state_3025_);
v_a_3028_ = lean_ctor_get(v_x_3026_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_x_3026_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3030_ = v_x_3026_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v_x_3026_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
}
}
else
{
lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3066_; 
v_isSharedCheck_3066_ = !lean_is_exclusive(v_x_3026_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v_x_3026_, 0);
lean_dec(v_unused_3067_);
v___x_3038_ = v_x_3026_;
v_isShared_3039_ = v_isSharedCheck_3066_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v_x_3026_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3066_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_machine_3040_; lean_object* v_requestStream_3041_; lean_object* v_keepAliveTimeout_3042_; lean_object* v_currentTimeout_3043_; lean_object* v_headerTimeout_3044_; lean_object* v_response_3045_; lean_object* v_respStream_3046_; uint8_t v_requiresData_3047_; lean_object* v_expectData_3048_; lean_object* v_pendingHead_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3065_; 
v_machine_3040_ = lean_ctor_get(v_state_3025_, 0);
v_requestStream_3041_ = lean_ctor_get(v_state_3025_, 1);
v_keepAliveTimeout_3042_ = lean_ctor_get(v_state_3025_, 2);
v_currentTimeout_3043_ = lean_ctor_get(v_state_3025_, 3);
v_headerTimeout_3044_ = lean_ctor_get(v_state_3025_, 4);
v_response_3045_ = lean_ctor_get(v_state_3025_, 5);
v_respStream_3046_ = lean_ctor_get(v_state_3025_, 6);
v_requiresData_3047_ = lean_ctor_get_uint8(v_state_3025_, sizeof(void*)*9);
v_expectData_3048_ = lean_ctor_get(v_state_3025_, 7);
v_pendingHead_3049_ = lean_ctor_get(v_state_3025_, 8);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_state_3025_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3051_ = v_state_3025_;
v_isShared_3052_ = v_isSharedCheck_3065_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_pendingHead_3049_);
lean_inc(v_expectData_3048_);
lean_inc(v_respStream_3046_);
lean_inc(v_response_3045_);
lean_inc(v_headerTimeout_3044_);
lean_inc(v_currentTimeout_3043_);
lean_inc(v_keepAliveTimeout_3042_);
lean_inc(v_requestStream_3041_);
lean_inc(v_machine_3040_);
lean_dec(v_state_3025_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3065_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3057_; 
v___x_3053_ = lean_box(52);
v___x_3054_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3040_, v___x_3053_);
v___x_3055_ = 0;
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3057_ = v___x_3051_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_requestStream_3041_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_keepAliveTimeout_3042_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_currentTimeout_3043_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_headerTimeout_3044_);
lean_ctor_set(v_reuseFailAlloc_3064_, 5, v_response_3045_);
lean_ctor_set(v_reuseFailAlloc_3064_, 6, v_respStream_3046_);
lean_ctor_set(v_reuseFailAlloc_3064_, 7, v_expectData_3048_);
lean_ctor_set(v_reuseFailAlloc_3064_, 8, v_pendingHead_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3064_, sizeof(void*)*9, v_requiresData_3047_);
v___x_3057_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*9 + 1, v___x_3055_);
v___x_3058_ = lean_box(v___x_3055_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3059_);
v___x_3061_ = v___x_3038_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3068_, lean_object* v_x_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3068_, v_x_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3072_, lean_object* v_requestStream_3073_, lean_object* v_keepAliveTimeout_3074_, lean_object* v_currentTimeout_3075_, lean_object* v_headerTimeout_3076_, lean_object* v_response_3077_, lean_object* v_respStream_3078_, uint8_t v_requiresData_3079_, lean_object* v_expectData_3080_, lean_object* v_pendingHead_3081_, lean_object* v_____r_3082_){
_start:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3084_ = 0;
v___x_3085_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3085_, 0, v_machine_3072_);
lean_ctor_set(v___x_3085_, 1, v_requestStream_3073_);
lean_ctor_set(v___x_3085_, 2, v_keepAliveTimeout_3074_);
lean_ctor_set(v___x_3085_, 3, v_currentTimeout_3075_);
lean_ctor_set(v___x_3085_, 4, v_headerTimeout_3076_);
lean_ctor_set(v___x_3085_, 5, v_response_3077_);
lean_ctor_set(v___x_3085_, 6, v_respStream_3078_);
lean_ctor_set(v___x_3085_, 7, v_expectData_3080_);
lean_ctor_set(v___x_3085_, 8, v_pendingHead_3081_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*9, v_requiresData_3079_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*9 + 1, v___x_3084_);
v___x_3086_ = lean_box(v___x_3084_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3090_, lean_object* v_requestStream_3091_, lean_object* v_keepAliveTimeout_3092_, lean_object* v_currentTimeout_3093_, lean_object* v_headerTimeout_3094_, lean_object* v_response_3095_, lean_object* v_respStream_3096_, lean_object* v_requiresData_3097_, lean_object* v_expectData_3098_, lean_object* v_pendingHead_3099_, lean_object* v_____r_3100_, lean_object* v___y_3101_){
_start:
{
uint8_t v_requiresData_boxed_3102_; lean_object* v_res_3103_; 
v_requiresData_boxed_3102_ = lean_unbox(v_requiresData_3097_);
v_res_3103_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3090_, v_requestStream_3091_, v_keepAliveTimeout_3092_, v_currentTimeout_3093_, v_headerTimeout_3094_, v_response_3095_, v_respStream_3096_, v_requiresData_boxed_3102_, v_expectData_3098_, v_pendingHead_3099_, v_____r_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3104_, lean_object* v_body_3105_, lean_object* v___f_3106_, lean_object* v___f_3107_, lean_object* v_x_3108_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v___f_3107_);
lean_dec_ref(v___f_3106_);
lean_dec(v_body_3105_);
lean_dec_ref(v_close_3104_);
v_a_3110_ = lean_ctor_get(v_x_3108_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_x_3108_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3112_ = v_x_3108_;
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v_x_3108_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; uint8_t v___x_3120_; 
v_a_3119_ = lean_ctor_get(v_x_3108_, 0);
lean_inc(v_a_3119_);
lean_dec_ref(v_x_3108_);
v___x_3120_ = lean_unbox(v_a_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; lean_object* v___x_3124_; 
lean_dec_ref(v___f_3107_);
v___x_3121_ = lean_apply_2(v_close_3104_, v_body_3105_, lean_box(0));
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = lean_unbox(v_a_3119_);
lean_dec(v_a_3119_);
v___x_3124_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3122_, v___x_3123_, v___x_3121_, v___f_3106_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v_a_3119_);
lean_dec_ref(v___f_3106_);
lean_dec(v_body_3105_);
lean_dec_ref(v_close_3104_);
v___x_3125_ = lean_box(0);
v___x_3126_ = lean_apply_2(v___f_3107_, v___x_3125_, lean_box(0));
return v___x_3126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3127_, lean_object* v_body_3128_, lean_object* v___f_3129_, lean_object* v___f_3130_, lean_object* v_x_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3127_, v_body_3128_, v___f_3129_, v___f_3130_, v_x_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3134_, lean_object* v_keepAliveTimeout_3135_, lean_object* v_currentTimeout_3136_, lean_object* v_headerTimeout_3137_, lean_object* v_response_3138_, uint8_t v_requiresData_3139_, lean_object* v_expectData_3140_, uint8_t v___x_3141_, lean_object* v_pendingHead_3142_, lean_object* v_____x_3143_){
_start:
{
lean_object* v_fst_3145_; lean_object* v_snd_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3157_; 
v_fst_3145_ = lean_ctor_get(v_____x_3143_, 0);
v_snd_3146_ = lean_ctor_get(v_____x_3143_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_____x_3143_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3148_ = v_____x_3143_;
v_isShared_3149_ = v_isSharedCheck_3157_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_snd_3146_);
lean_inc(v_fst_3145_);
lean_dec(v_____x_3143_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3157_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3150_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3150_, 0, v_fst_3145_);
lean_ctor_set(v___x_3150_, 1, v_requestStream_3134_);
lean_ctor_set(v___x_3150_, 2, v_keepAliveTimeout_3135_);
lean_ctor_set(v___x_3150_, 3, v_currentTimeout_3136_);
lean_ctor_set(v___x_3150_, 4, v_headerTimeout_3137_);
lean_ctor_set(v___x_3150_, 5, v_response_3138_);
lean_ctor_set(v___x_3150_, 6, v_snd_3146_);
lean_ctor_set(v___x_3150_, 7, v_expectData_3140_);
lean_ctor_set(v___x_3150_, 8, v_pendingHead_3142_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*9, v_requiresData_3139_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*9 + 1, v___x_3141_);
v___x_3151_ = lean_box(v___x_3141_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v___x_3151_);
lean_ctor_set(v___x_3148_, 0, v___x_3150_);
v___x_3153_ = v___x_3148_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3158_, lean_object* v_keepAliveTimeout_3159_, lean_object* v_currentTimeout_3160_, lean_object* v_headerTimeout_3161_, lean_object* v_response_3162_, lean_object* v_requiresData_3163_, lean_object* v_expectData_3164_, lean_object* v___x_3165_, lean_object* v_pendingHead_3166_, lean_object* v_____x_3167_, lean_object* v___y_3168_){
_start:
{
uint8_t v_requiresData_boxed_3169_; uint8_t v___x_7723__boxed_3170_; lean_object* v_res_3171_; 
v_requiresData_boxed_3169_ = lean_unbox(v_requiresData_3163_);
v___x_7723__boxed_3170_ = lean_unbox(v___x_3165_);
v_res_3171_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3158_, v_keepAliveTimeout_3159_, v_currentTimeout_3160_, v_headerTimeout_3161_, v_response_3162_, v_requiresData_boxed_3169_, v_expectData_3164_, v___x_7723__boxed_3170_, v_pendingHead_3166_, v_____x_3167_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3172_, lean_object* v_x_3173_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v___f_3172_);
v_a_3175_ = lean_ctor_get(v_x_3173_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3177_ = v_x_3173_;
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v_x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3185_; 
v_a_3184_ = lean_ctor_get(v_x_3173_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v_x_3173_);
v___x_3185_ = lean_apply_2(v___f_3172_, v_a_3184_, lean_box(0));
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3186_, lean_object* v_x_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3186_, v_x_3187_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3190_, lean_object* v___f_3191_, lean_object* v_inst_3192_, lean_object* v___f_3193_, lean_object* v_x_3194_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v___f_3193_);
lean_dec_ref(v_inst_3192_);
lean_dec_ref(v___f_3191_);
v_a_3196_ = lean_ctor_get(v_x_3194_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_x_3194_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3198_ = v_x_3194_;
v_isShared_3199_ = v_isSharedCheck_3204_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v_x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3204_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v_snd_3206_; 
v_a_3205_ = lean_ctor_get(v_x_3194_, 0);
v_snd_3206_ = lean_ctor_get(v_a_3205_, 1);
if (lean_obj_tag(v_snd_3206_) == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec_ref(v___f_3193_);
lean_dec_ref(v_inst_3192_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_x_3194_);
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3208_, v___x_3190_, v___x_3207_, v___f_3191_);
return v___x_3209_;
}
else
{
lean_object* v_fst_3210_; lean_object* v_val_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_inc_ref(v_snd_3206_);
lean_inc(v_a_3205_);
lean_dec_ref(v_x_3194_);
lean_dec_ref(v___f_3191_);
v_fst_3210_ = lean_ctor_get(v_a_3205_, 0);
lean_inc(v_fst_3210_);
lean_dec(v_a_3205_);
v_val_3211_ = lean_ctor_get(v_snd_3206_, 0);
lean_inc(v_val_3211_);
lean_dec_ref(v_snd_3206_);
v___x_3212_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3192_, v_fst_3210_, v_val_3211_);
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3213_, v___x_3190_, v___x_3212_, v___f_3193_);
return v___x_3214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3215_, lean_object* v___f_3216_, lean_object* v_inst_3217_, lean_object* v___f_3218_, lean_object* v_x_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v___x_7789__boxed_3221_; lean_object* v_res_3222_; 
v___x_7789__boxed_3221_ = lean_unbox(v___x_3215_);
v_res_3222_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7789__boxed_3221_, v___f_3216_, v_inst_3217_, v___f_3218_, v_x_3219_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_state_3223_, lean_object* v_x_3224_){
_start:
{
if (lean_obj_tag(v_x_3224_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v_state_3223_);
v_a_3226_ = lean_ctor_get(v_x_3224_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_x_3224_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3228_ = v_x_3224_;
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v_x_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
}
else
{
lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3264_; 
v_isSharedCheck_3264_ = !lean_is_exclusive(v_x_3224_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_x_3224_, 0);
lean_dec(v_unused_3265_);
v___x_3236_ = v_x_3224_;
v_isShared_3237_ = v_isSharedCheck_3264_;
goto v_resetjp_3235_;
}
else
{
lean_dec(v_x_3224_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3264_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v_machine_3238_; lean_object* v_requestStream_3239_; lean_object* v_keepAliveTimeout_3240_; lean_object* v_currentTimeout_3241_; lean_object* v_headerTimeout_3242_; lean_object* v_response_3243_; lean_object* v_respStream_3244_; uint8_t v_requiresData_3245_; lean_object* v_expectData_3246_; lean_object* v_pendingHead_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3263_; 
v_machine_3238_ = lean_ctor_get(v_state_3223_, 0);
v_requestStream_3239_ = lean_ctor_get(v_state_3223_, 1);
v_keepAliveTimeout_3240_ = lean_ctor_get(v_state_3223_, 2);
v_currentTimeout_3241_ = lean_ctor_get(v_state_3223_, 3);
v_headerTimeout_3242_ = lean_ctor_get(v_state_3223_, 4);
v_response_3243_ = lean_ctor_get(v_state_3223_, 5);
v_respStream_3244_ = lean_ctor_get(v_state_3223_, 6);
v_requiresData_3245_ = lean_ctor_get_uint8(v_state_3223_, sizeof(void*)*9);
v_expectData_3246_ = lean_ctor_get(v_state_3223_, 7);
v_pendingHead_3247_ = lean_ctor_get(v_state_3223_, 8);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_state_3223_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3249_ = v_state_3223_;
v_isShared_3250_ = v_isSharedCheck_3263_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_pendingHead_3247_);
lean_inc(v_expectData_3246_);
lean_inc(v_respStream_3244_);
lean_inc(v_response_3243_);
lean_inc(v_headerTimeout_3242_);
lean_inc(v_currentTimeout_3241_);
lean_inc(v_keepAliveTimeout_3240_);
lean_inc(v_requestStream_3239_);
lean_inc(v_machine_3238_);
lean_dec(v_state_3223_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3263_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3255_; 
v___x_3251_ = lean_box(31);
v___x_3252_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3238_, v___x_3251_);
v___x_3253_ = 0;
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3252_);
v___x_3255_ = v___x_3249_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_requestStream_3239_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_keepAliveTimeout_3240_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_currentTimeout_3241_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v_headerTimeout_3242_);
lean_ctor_set(v_reuseFailAlloc_3262_, 5, v_response_3243_);
lean_ctor_set(v_reuseFailAlloc_3262_, 6, v_respStream_3244_);
lean_ctor_set(v_reuseFailAlloc_3262_, 7, v_expectData_3246_);
lean_ctor_set(v_reuseFailAlloc_3262_, 8, v_pendingHead_3247_);
lean_ctor_set_uint8(v_reuseFailAlloc_3262_, sizeof(void*)*9, v_requiresData_3245_);
v___x_3255_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*9 + 1, v___x_3253_);
v___x_3256_ = lean_box(v___x_3253_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3257_);
v___x_3259_ = v___x_3236_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
return v___x_3260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_state_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_state_3266_, v_x_3267_);
return v_res_3269_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3272_ = lean_mk_io_user_error(v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3273_, lean_object* v_inst_3274_, lean_object* v_handler_3275_, lean_object* v_config_3276_, lean_object* v_event_3277_, lean_object* v_state_3278_){
_start:
{
switch(lean_obj_tag(v_event_3277_))
{
case 0:
{
lean_object* v_x_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3387_; 
lean_dec(v_handler_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_inst_3273_);
v_x_3280_ = lean_ctor_get(v_event_3277_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_event_3277_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3282_ = v_event_3277_;
v_isShared_3283_ = v_isSharedCheck_3387_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_x_3280_);
lean_dec(v_event_3277_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3387_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
if (lean_obj_tag(v_x_3280_) == 0)
{
lean_object* v_machine_3284_; lean_object* v_reader_3285_; lean_object* v_requestStream_3286_; lean_object* v_keepAliveTimeout_3287_; lean_object* v_currentTimeout_3288_; lean_object* v_headerTimeout_3289_; lean_object* v_response_3290_; lean_object* v_respStream_3291_; uint8_t v_requiresData_3292_; lean_object* v_expectData_3293_; uint8_t v_handlerDispatched_3294_; lean_object* v_pendingHead_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_config_3276_);
v_machine_3284_ = lean_ctor_get(v_state_3278_, 0);
lean_inc_ref(v_machine_3284_);
v_reader_3285_ = lean_ctor_get(v_machine_3284_, 0);
lean_inc_ref(v_reader_3285_);
v_requestStream_3286_ = lean_ctor_get(v_state_3278_, 1);
v_keepAliveTimeout_3287_ = lean_ctor_get(v_state_3278_, 2);
v_currentTimeout_3288_ = lean_ctor_get(v_state_3278_, 3);
v_headerTimeout_3289_ = lean_ctor_get(v_state_3278_, 4);
v_response_3290_ = lean_ctor_get(v_state_3278_, 5);
v_respStream_3291_ = lean_ctor_get(v_state_3278_, 6);
v_requiresData_3292_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3293_ = lean_ctor_get(v_state_3278_, 7);
v_handlerDispatched_3294_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9 + 1);
v_pendingHead_3295_ = lean_ctor_get(v_state_3278_, 8);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_state_3278_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_state_3278_, 0);
lean_dec(v_unused_3339_);
v___x_3297_ = v_state_3278_;
v_isShared_3298_ = v_isSharedCheck_3338_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_pendingHead_3295_);
lean_inc(v_expectData_3293_);
lean_inc(v_respStream_3291_);
lean_inc(v_response_3290_);
lean_inc(v_headerTimeout_3289_);
lean_inc(v_currentTimeout_3288_);
lean_inc(v_keepAliveTimeout_3287_);
lean_inc(v_requestStream_3286_);
lean_dec(v_state_3278_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3338_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_writer_3299_; lean_object* v_config_3300_; lean_object* v_events_3301_; lean_object* v_error_3302_; lean_object* v_instant_3303_; uint8_t v_keepAlive_3304_; uint8_t v_forcedFlush_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3336_; 
v_writer_3299_ = lean_ctor_get(v_machine_3284_, 1);
v_config_3300_ = lean_ctor_get(v_machine_3284_, 2);
v_events_3301_ = lean_ctor_get(v_machine_3284_, 3);
v_error_3302_ = lean_ctor_get(v_machine_3284_, 4);
v_instant_3303_ = lean_ctor_get(v_machine_3284_, 5);
v_keepAlive_3304_ = lean_ctor_get_uint8(v_machine_3284_, sizeof(void*)*6);
v_forcedFlush_3305_ = lean_ctor_get_uint8(v_machine_3284_, sizeof(void*)*6 + 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_machine_3284_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_machine_3284_, 0);
lean_dec(v_unused_3337_);
v___x_3307_ = v_machine_3284_;
v_isShared_3308_ = v_isSharedCheck_3336_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_instant_3303_);
lean_inc(v_error_3302_);
lean_inc(v_events_3301_);
lean_inc(v_config_3300_);
lean_inc(v_writer_3299_);
lean_dec(v_machine_3284_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3336_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v_state_3309_; lean_object* v_input_3310_; lean_object* v_messageHead_3311_; lean_object* v_messageCount_3312_; lean_object* v_bodyBytesRead_3313_; lean_object* v_headerBytesRead_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3335_; 
v_state_3309_ = lean_ctor_get(v_reader_3285_, 0);
v_input_3310_ = lean_ctor_get(v_reader_3285_, 1);
v_messageHead_3311_ = lean_ctor_get(v_reader_3285_, 2);
v_messageCount_3312_ = lean_ctor_get(v_reader_3285_, 3);
v_bodyBytesRead_3313_ = lean_ctor_get(v_reader_3285_, 4);
v_headerBytesRead_3314_ = lean_ctor_get(v_reader_3285_, 5);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_reader_3285_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3316_ = v_reader_3285_;
v_isShared_3317_ = v_isSharedCheck_3335_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_headerBytesRead_3314_);
lean_inc(v_bodyBytesRead_3313_);
lean_inc(v_messageCount_3312_);
lean_inc(v_messageHead_3311_);
lean_inc(v_input_3310_);
lean_inc(v_state_3309_);
lean_dec(v_reader_3285_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3335_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
uint8_t v___x_3318_; lean_object* v___x_3320_; 
v___x_3318_ = 1;
if (v_isShared_3317_ == 0)
{
v___x_3320_ = v___x_3316_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_state_3309_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_input_3310_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_messageHead_3311_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_messageCount_3312_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_bodyBytesRead_3313_);
lean_ctor_set(v_reuseFailAlloc_3334_, 5, v_headerBytesRead_3314_);
v___x_3320_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
uint8_t v___x_3321_; lean_object* v___x_3323_; 
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*6, v___x_3318_);
v___x_3321_ = 0;
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3320_);
v___x_3323_ = v___x_3307_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_writer_3299_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_config_3300_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v_events_3301_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v_error_3302_);
lean_ctor_set(v_reuseFailAlloc_3333_, 5, v_instant_3303_);
lean_ctor_set_uint8(v_reuseFailAlloc_3333_, sizeof(void*)*6, v_keepAlive_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3333_, sizeof(void*)*6 + 1, v_forcedFlush_3305_);
v___x_3323_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3325_; 
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*6 + 2, v___x_3321_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3323_);
v___x_3325_ = v___x_3297_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_requestStream_3286_);
lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_keepAliveTimeout_3287_);
lean_ctor_set(v_reuseFailAlloc_3332_, 3, v_currentTimeout_3288_);
lean_ctor_set(v_reuseFailAlloc_3332_, 4, v_headerTimeout_3289_);
lean_ctor_set(v_reuseFailAlloc_3332_, 5, v_response_3290_);
lean_ctor_set(v_reuseFailAlloc_3332_, 6, v_respStream_3291_);
lean_ctor_set(v_reuseFailAlloc_3332_, 7, v_expectData_3293_);
lean_ctor_set(v_reuseFailAlloc_3332_, 8, v_pendingHead_3295_);
lean_ctor_set_uint8(v_reuseFailAlloc_3332_, sizeof(void*)*9, v_requiresData_3292_);
lean_ctor_set_uint8(v_reuseFailAlloc_3332_, sizeof(void*)*9 + 1, v_handlerDispatched_3294_);
v___x_3325_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3326_ = lean_box(v___x_3321_);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 1);
lean_ctor_set(v___x_3282_, 0, v___x_3327_);
v___x_3329_ = v___x_3282_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
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
lean_object* v_val_3340_; lean_object* v_machine_3341_; lean_object* v_requestStream_3342_; lean_object* v_keepAliveTimeout_3343_; lean_object* v_currentTimeout_3344_; lean_object* v_response_3345_; lean_object* v_respStream_3346_; uint8_t v_requiresData_3347_; lean_object* v_expectData_3348_; uint8_t v_handlerDispatched_3349_; lean_object* v_pendingHead_3350_; lean_object* v___f_3351_; 
lean_del_object(v___x_3282_);
v_val_3340_ = lean_ctor_get(v_x_3280_, 0);
lean_inc_n(v_val_3340_, 2);
lean_dec_ref(v_x_3280_);
v_machine_3341_ = lean_ctor_get(v_state_3278_, 0);
v_requestStream_3342_ = lean_ctor_get(v_state_3278_, 1);
v_keepAliveTimeout_3343_ = lean_ctor_get(v_state_3278_, 2);
lean_inc(v_keepAliveTimeout_3343_);
v_currentTimeout_3344_ = lean_ctor_get(v_state_3278_, 3);
v_response_3345_ = lean_ctor_get(v_state_3278_, 5);
v_respStream_3346_ = lean_ctor_get(v_state_3278_, 6);
v_requiresData_3347_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3348_ = lean_ctor_get(v_state_3278_, 7);
v_handlerDispatched_3349_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9 + 1);
v_pendingHead_3350_ = lean_ctor_get(v_state_3278_, 8);
v___f_3351_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3351_, 0, v_val_3340_);
if (lean_obj_tag(v_keepAliveTimeout_3343_) == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v___f_3351_);
lean_dec_ref(v_config_3276_);
v___x_3352_ = lean_box(0);
v___x_3353_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3340_, v___x_3352_, v_state_3278_);
return v___x_3353_;
}
else
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3385_; 
lean_inc(v_pendingHead_3350_);
lean_inc(v_expectData_3348_);
lean_inc(v_respStream_3346_);
lean_inc_ref(v_response_3345_);
lean_inc(v_currentTimeout_3344_);
lean_inc_ref(v_requestStream_3342_);
lean_inc_ref(v_machine_3341_);
lean_dec(v_val_3340_);
lean_dec_ref(v_state_3278_);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_keepAliveTimeout_3343_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v_keepAliveTimeout_3343_, 0);
lean_dec(v_unused_3386_);
v___x_3355_ = v_keepAliveTimeout_3343_;
v_isShared_3356_ = v_isSharedCheck_3385_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v_keepAliveTimeout_3343_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3385_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v_val_3361_; lean_object* v___x_3368_; 
v___x_3357_ = lean_box(v_requiresData_3347_);
v___x_3358_ = lean_box(v_handlerDispatched_3349_);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3359_, 0, v_config_3276_);
lean_closure_set(v___f_3359_, 1, v_machine_3341_);
lean_closure_set(v___f_3359_, 2, v_requestStream_3342_);
lean_closure_set(v___f_3359_, 3, v_currentTimeout_3344_);
lean_closure_set(v___f_3359_, 4, v_response_3345_);
lean_closure_set(v___f_3359_, 5, v_respStream_3346_);
lean_closure_set(v___f_3359_, 6, v___x_3357_);
lean_closure_set(v___f_3359_, 7, v_expectData_3348_);
lean_closure_set(v___f_3359_, 8, v___x_3358_);
lean_closure_set(v___f_3359_, 9, v_pendingHead_3350_);
lean_closure_set(v___f_3359_, 10, v___f_3351_);
v___x_3368_ = lean_get_current_time();
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 1);
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
v_val_3361_ = v___x_3374_;
goto v___jp_3360_;
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_a_3377_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3368_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3368_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 0);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
v_val_3361_ = v___x_3382_;
goto v___jp_3360_;
}
}
}
v___jp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 0);
lean_ctor_set(v___x_3355_, 0, v_val_3361_);
v___x_3363_ = v___x_3355_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_val_3361_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; uint8_t v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_unsigned_to_nat(0u);
v___x_3365_ = 0;
v___x_3366_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3364_, v___x_3365_, v___x_3363_, v___f_3359_);
return v___x_3366_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_config_3276_);
lean_dec(v_handler_3275_);
lean_dec_ref(v_inst_3273_);
v_x_3388_ = lean_ctor_get(v_event_3277_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_event_3277_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3390_ = v_event_3277_;
v_isShared_3391_ = v_isSharedCheck_3503_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_x_3388_);
lean_dec(v_event_3277_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3503_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
if (lean_obj_tag(v_x_3388_) == 0)
{
lean_object* v_machine_3392_; lean_object* v_requestStream_3393_; lean_object* v_keepAliveTimeout_3394_; lean_object* v_currentTimeout_3395_; lean_object* v_headerTimeout_3396_; lean_object* v_response_3397_; lean_object* v_respStream_3398_; uint8_t v_requiresData_3399_; lean_object* v_expectData_3400_; uint8_t v_handlerDispatched_3401_; lean_object* v_pendingHead_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___f_3405_; 
lean_del_object(v___x_3390_);
v_machine_3392_ = lean_ctor_get(v_state_3278_, 0);
lean_inc_ref_n(v_machine_3392_, 2);
v_requestStream_3393_ = lean_ctor_get(v_state_3278_, 1);
lean_inc_ref_n(v_requestStream_3393_, 2);
v_keepAliveTimeout_3394_ = lean_ctor_get(v_state_3278_, 2);
lean_inc_n(v_keepAliveTimeout_3394_, 2);
v_currentTimeout_3395_ = lean_ctor_get(v_state_3278_, 3);
lean_inc_n(v_currentTimeout_3395_, 2);
v_headerTimeout_3396_ = lean_ctor_get(v_state_3278_, 4);
lean_inc_n(v_headerTimeout_3396_, 2);
v_response_3397_ = lean_ctor_get(v_state_3278_, 5);
lean_inc_ref_n(v_response_3397_, 2);
v_respStream_3398_ = lean_ctor_get(v_state_3278_, 6);
lean_inc(v_respStream_3398_);
v_requiresData_3399_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3400_ = lean_ctor_get(v_state_3278_, 7);
lean_inc_n(v_expectData_3400_, 2);
v_handlerDispatched_3401_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9 + 1);
v_pendingHead_3402_ = lean_ctor_get(v_state_3278_, 8);
lean_inc_n(v_pendingHead_3402_, 2);
lean_dec_ref(v_state_3278_);
v___x_3403_ = lean_box(v_requiresData_3399_);
v___x_3404_ = lean_box(v_handlerDispatched_3401_);
v___f_3405_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3405_, 0, v_machine_3392_);
lean_closure_set(v___f_3405_, 1, v_requestStream_3393_);
lean_closure_set(v___f_3405_, 2, v_keepAliveTimeout_3394_);
lean_closure_set(v___f_3405_, 3, v_currentTimeout_3395_);
lean_closure_set(v___f_3405_, 4, v_headerTimeout_3396_);
lean_closure_set(v___f_3405_, 5, v_response_3397_);
lean_closure_set(v___f_3405_, 6, v___x_3403_);
lean_closure_set(v___f_3405_, 7, v_expectData_3400_);
lean_closure_set(v___f_3405_, 8, v___x_3404_);
lean_closure_set(v___f_3405_, 9, v_pendingHead_3402_);
if (lean_obj_tag(v_respStream_3398_) == 1)
{
lean_object* v_val_3406_; lean_object* v_close_3407_; lean_object* v_isClosed_3408_; lean_object* v___x_3409_; lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v_pendingHead_3402_);
lean_dec(v_expectData_3400_);
lean_dec_ref(v_response_3397_);
lean_dec(v_headerTimeout_3396_);
lean_dec(v_currentTimeout_3395_);
lean_dec(v_keepAliveTimeout_3394_);
lean_dec_ref(v_requestStream_3393_);
lean_dec_ref(v_machine_3392_);
v_val_3406_ = lean_ctor_get(v_respStream_3398_, 0);
lean_inc_n(v_val_3406_, 2);
lean_dec_ref(v_respStream_3398_);
v_close_3407_ = lean_ctor_get(v_inst_3274_, 1);
lean_inc_ref(v_close_3407_);
v_isClosed_3408_ = lean_ctor_get(v_inst_3274_, 2);
lean_inc_ref(v_isClosed_3408_);
lean_dec_ref(v_inst_3274_);
v___x_3409_ = lean_apply_2(v_isClosed_3408_, v_val_3406_, lean_box(0));
lean_inc_ref(v___f_3405_);
v___f_3410_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3410_, 0, v___f_3405_);
v___f_3411_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3411_, 0, v_close_3407_);
lean_closure_set(v___f_3411_, 1, v_val_3406_);
lean_closure_set(v___f_3411_, 2, v___f_3410_);
lean_closure_set(v___f_3411_, 3, v___f_3405_);
v___x_3412_ = lean_unsigned_to_nat(0u);
v___x_3413_ = 0;
v___x_3414_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3412_, v___x_3413_, v___x_3409_, v___f_3411_);
return v___x_3414_;
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec_ref(v___f_3405_);
lean_dec(v_respStream_3398_);
lean_dec_ref(v_inst_3274_);
v___x_3415_ = lean_box(0);
v___x_3416_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3392_, v_requestStream_3393_, v_keepAliveTimeout_3394_, v_currentTimeout_3395_, v_headerTimeout_3396_, v_response_3397_, v_requiresData_3399_, v_expectData_3400_, v_handlerDispatched_3401_, v_pendingHead_3402_, v___x_3415_);
return v___x_3416_;
}
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref(v_inst_3274_);
v_val_3417_ = lean_ctor_get(v_x_3388_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_x_3388_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3419_ = v_x_3388_;
v_isShared_3420_ = v_isSharedCheck_3502_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v_x_3388_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3502_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_machine_3421_; lean_object* v_requestStream_3422_; lean_object* v_keepAliveTimeout_3423_; lean_object* v_currentTimeout_3424_; lean_object* v_headerTimeout_3425_; lean_object* v_response_3426_; lean_object* v_respStream_3427_; uint8_t v_requiresData_3428_; lean_object* v_expectData_3429_; uint8_t v_handlerDispatched_3430_; lean_object* v_pendingHead_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3501_; 
v_machine_3421_ = lean_ctor_get(v_state_3278_, 0);
v_requestStream_3422_ = lean_ctor_get(v_state_3278_, 1);
v_keepAliveTimeout_3423_ = lean_ctor_get(v_state_3278_, 2);
v_currentTimeout_3424_ = lean_ctor_get(v_state_3278_, 3);
v_headerTimeout_3425_ = lean_ctor_get(v_state_3278_, 4);
v_response_3426_ = lean_ctor_get(v_state_3278_, 5);
v_respStream_3427_ = lean_ctor_get(v_state_3278_, 6);
v_requiresData_3428_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3429_ = lean_ctor_get(v_state_3278_, 7);
v_handlerDispatched_3430_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9 + 1);
v_pendingHead_3431_ = lean_ctor_get(v_state_3278_, 8);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_state_3278_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3433_ = v_state_3278_;
v_isShared_3434_ = v_isSharedCheck_3501_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_pendingHead_3431_);
lean_inc(v_expectData_3429_);
lean_inc(v_respStream_3427_);
lean_inc(v_response_3426_);
lean_inc(v_headerTimeout_3425_);
lean_inc(v_currentTimeout_3424_);
lean_inc(v_keepAliveTimeout_3423_);
lean_inc(v_requestStream_3422_);
lean_inc(v_machine_3421_);
lean_dec(v_state_3278_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3501_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___y_3436_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3449_ = lean_unsigned_to_nat(1u);
v___x_3450_ = lean_mk_empty_array_with_capacity(v___x_3449_);
v___x_3451_ = lean_array_push(v___x_3450_, v_val_3417_);
v___x_3452_ = lean_array_get_size(v___x_3451_);
v___x_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = lean_nat_dec_eq(v___x_3452_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_object* v_reader_3455_; lean_object* v_writer_3456_; lean_object* v_config_3457_; lean_object* v_events_3458_; lean_object* v_error_3459_; lean_object* v_instant_3460_; uint8_t v_keepAlive_3461_; uint8_t v_forcedFlush_3462_; uint8_t v_pullBodyStalled_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3500_; 
v_reader_3455_ = lean_ctor_get(v_machine_3421_, 0);
v_writer_3456_ = lean_ctor_get(v_machine_3421_, 1);
v_config_3457_ = lean_ctor_get(v_machine_3421_, 2);
v_events_3458_ = lean_ctor_get(v_machine_3421_, 3);
v_error_3459_ = lean_ctor_get(v_machine_3421_, 4);
v_instant_3460_ = lean_ctor_get(v_machine_3421_, 5);
v_keepAlive_3461_ = lean_ctor_get_uint8(v_machine_3421_, sizeof(void*)*6);
v_forcedFlush_3462_ = lean_ctor_get_uint8(v_machine_3421_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3463_ = lean_ctor_get_uint8(v_machine_3421_, sizeof(void*)*6 + 2);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_machine_3421_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3465_ = v_machine_3421_;
v_isShared_3466_ = v_isSharedCheck_3500_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_instant_3460_);
lean_inc(v_error_3459_);
lean_inc(v_events_3458_);
lean_inc(v_config_3457_);
lean_inc(v_writer_3456_);
lean_inc(v_reader_3455_);
lean_dec(v_machine_3421_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3500_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___y_3468_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3490_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3491_ = lean_nat_dec_lt(v___x_3453_, v___x_3452_);
if (v___x_3491_ == 0)
{
v___y_3468_ = v___x_3453_;
goto v___jp_3467_;
}
else
{
lean_object* v___f_3492_; uint8_t v___x_3493_; 
v___f_3492_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3493_ = lean_nat_dec_le(v___x_3452_, v___x_3452_);
if (v___x_3493_ == 0)
{
if (v___x_3491_ == 0)
{
v___y_3468_ = v___x_3453_;
goto v___jp_3467_;
}
else
{
size_t v___x_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = lean_usize_of_nat(v___x_3452_);
lean_inc_ref(v___x_3451_);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3490_, v___f_3492_, v___x_3451_, v___x_3494_, v___x_3495_, v___x_3453_);
v___y_3468_ = v___x_3496_;
goto v___jp_3467_;
}
}
else
{
size_t v___x_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = lean_usize_of_nat(v___x_3452_);
lean_inc_ref(v___x_3451_);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3490_, v___f_3492_, v___x_3451_, v___x_3497_, v___x_3498_, v___x_3453_);
v___y_3468_ = v___x_3499_;
goto v___jp_3467_;
}
}
v___jp_3467_:
{
lean_object* v_userData_3469_; lean_object* v_outputData_3470_; lean_object* v_state_3471_; lean_object* v_knownSize_3472_; lean_object* v_messageHead_3473_; uint8_t v_sentMessage_3474_; uint8_t v_userClosedBody_3475_; uint8_t v_omitBody_3476_; lean_object* v_userDataBytes_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3489_; 
v_userData_3469_ = lean_ctor_get(v_writer_3456_, 0);
v_outputData_3470_ = lean_ctor_get(v_writer_3456_, 1);
v_state_3471_ = lean_ctor_get(v_writer_3456_, 2);
v_knownSize_3472_ = lean_ctor_get(v_writer_3456_, 3);
v_messageHead_3473_ = lean_ctor_get(v_writer_3456_, 4);
v_sentMessage_3474_ = lean_ctor_get_uint8(v_writer_3456_, sizeof(void*)*6);
v_userClosedBody_3475_ = lean_ctor_get_uint8(v_writer_3456_, sizeof(void*)*6 + 1);
v_omitBody_3476_ = lean_ctor_get_uint8(v_writer_3456_, sizeof(void*)*6 + 2);
v_userDataBytes_3477_ = lean_ctor_get(v_writer_3456_, 5);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_writer_3456_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3479_ = v_writer_3456_;
v_isShared_3480_ = v_isSharedCheck_3489_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_userDataBytes_3477_);
lean_inc(v_messageHead_3473_);
lean_inc(v_knownSize_3472_);
lean_inc(v_state_3471_);
lean_inc(v_outputData_3470_);
lean_inc(v_userData_3469_);
lean_dec(v_writer_3456_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3489_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3481_ = l_Array_append___redArg(v_userData_3469_, v___x_3451_);
lean_dec_ref(v___x_3451_);
v___x_3482_ = lean_nat_add(v_userDataBytes_3477_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec(v_userDataBytes_3477_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 5, v___x_3482_);
lean_ctor_set(v___x_3479_, 0, v___x_3481_);
v___x_3484_ = v___x_3479_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_outputData_3470_);
lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_state_3471_);
lean_ctor_set(v_reuseFailAlloc_3488_, 3, v_knownSize_3472_);
lean_ctor_set(v_reuseFailAlloc_3488_, 4, v_messageHead_3473_);
lean_ctor_set(v_reuseFailAlloc_3488_, 5, v___x_3482_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*6, v_sentMessage_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*6 + 1, v_userClosedBody_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*6 + 2, v_omitBody_3476_);
v___x_3484_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3486_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v___x_3484_);
v___x_3486_ = v___x_3465_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_reader_3455_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_config_3457_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_events_3458_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_error_3459_);
lean_ctor_set(v_reuseFailAlloc_3487_, 5, v_instant_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, sizeof(void*)*6, v_keepAlive_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, sizeof(void*)*6 + 1, v_forcedFlush_3462_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, sizeof(void*)*6 + 2, v_pullBodyStalled_3463_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
v___y_3436_ = v___x_3486_;
goto v___jp_3435_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3451_);
v___y_3436_ = v_machine_3421_;
goto v___jp_3435_;
}
v___jp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___y_3436_);
v___x_3438_ = v___x_3433_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___y_3436_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_requestStream_3422_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_keepAliveTimeout_3423_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_currentTimeout_3424_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_headerTimeout_3425_);
lean_ctor_set(v_reuseFailAlloc_3448_, 5, v_response_3426_);
lean_ctor_set(v_reuseFailAlloc_3448_, 6, v_respStream_3427_);
lean_ctor_set(v_reuseFailAlloc_3448_, 7, v_expectData_3429_);
lean_ctor_set(v_reuseFailAlloc_3448_, 8, v_pendingHead_3431_);
lean_ctor_set_uint8(v_reuseFailAlloc_3448_, sizeof(void*)*9, v_requiresData_3428_);
lean_ctor_set_uint8(v_reuseFailAlloc_3448_, sizeof(void*)*9 + 1, v_handlerDispatched_3430_);
v___x_3438_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
uint8_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3439_ = 0;
v___x_3440_ = lean_box(v___x_3439_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3438_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3441_);
v___x_3443_ = v___x_3419_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3443_);
v___x_3445_ = v___x_3390_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
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
uint8_t v_x_3504_; 
lean_dec_ref(v_config_3276_);
lean_dec_ref(v_inst_3274_);
v_x_3504_ = lean_ctor_get_uint8(v_event_3277_, 0);
lean_dec_ref(v_event_3277_);
if (v_x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec(v_handler_3275_);
lean_dec_ref(v_inst_3273_);
v___x_3505_ = lean_box(v_x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v_state_3278_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
return v___x_3508_;
}
else
{
lean_object* v_machine_3509_; lean_object* v_requestStream_3510_; lean_object* v_keepAliveTimeout_3511_; lean_object* v_currentTimeout_3512_; lean_object* v_headerTimeout_3513_; lean_object* v_response_3514_; lean_object* v_respStream_3515_; uint8_t v_requiresData_3516_; lean_object* v_expectData_3517_; uint8_t v_handlerDispatched_3518_; lean_object* v_pendingHead_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3569_; 
v_machine_3509_ = lean_ctor_get(v_state_3278_, 0);
v_requestStream_3510_ = lean_ctor_get(v_state_3278_, 1);
v_keepAliveTimeout_3511_ = lean_ctor_get(v_state_3278_, 2);
v_currentTimeout_3512_ = lean_ctor_get(v_state_3278_, 3);
v_headerTimeout_3513_ = lean_ctor_get(v_state_3278_, 4);
v_response_3514_ = lean_ctor_get(v_state_3278_, 5);
v_respStream_3515_ = lean_ctor_get(v_state_3278_, 6);
v_requiresData_3516_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3517_ = lean_ctor_get(v_state_3278_, 7);
v_handlerDispatched_3518_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9 + 1);
v_pendingHead_3519_ = lean_ctor_get(v_state_3278_, 8);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_state_3278_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3521_ = v_state_3278_;
v_isShared_3522_ = v_isSharedCheck_3569_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_pendingHead_3519_);
lean_inc(v_expectData_3517_);
lean_inc(v_respStream_3515_);
lean_inc(v_response_3514_);
lean_inc(v_headerTimeout_3513_);
lean_inc(v_currentTimeout_3512_);
lean_inc(v_keepAliveTimeout_3511_);
lean_inc(v_requestStream_3510_);
lean_inc(v_machine_3509_);
lean_dec(v_state_3278_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3569_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
uint8_t v___x_3523_; lean_object* v___x_3524_; lean_object* v_fst_3525_; lean_object* v_snd_3526_; lean_object* v_reader_3527_; lean_object* v_writer_3528_; lean_object* v_config_3529_; lean_object* v_events_3530_; lean_object* v_error_3531_; lean_object* v_instant_3532_; uint8_t v_keepAlive_3533_; uint8_t v_forcedFlush_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3568_; 
v___x_3523_ = 0;
v___x_3524_ = l___private_Std_Internal_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3523_, v_machine_3509_);
v_fst_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_fst_3525_);
v_snd_3526_ = lean_ctor_get(v___x_3524_, 1);
lean_inc(v_snd_3526_);
lean_dec_ref(v___x_3524_);
v_reader_3527_ = lean_ctor_get(v_fst_3525_, 0);
v_writer_3528_ = lean_ctor_get(v_fst_3525_, 1);
v_config_3529_ = lean_ctor_get(v_fst_3525_, 2);
v_events_3530_ = lean_ctor_get(v_fst_3525_, 3);
v_error_3531_ = lean_ctor_get(v_fst_3525_, 4);
v_instant_3532_ = lean_ctor_get(v_fst_3525_, 5);
v_keepAlive_3533_ = lean_ctor_get_uint8(v_fst_3525_, sizeof(void*)*6);
v_forcedFlush_3534_ = lean_ctor_get_uint8(v_fst_3525_, sizeof(void*)*6 + 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_fst_3525_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3536_ = v_fst_3525_;
v_isShared_3537_ = v_isSharedCheck_3568_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_instant_3532_);
lean_inc(v_error_3531_);
lean_inc(v_events_3530_);
lean_inc(v_config_3529_);
lean_inc(v_writer_3528_);
lean_inc(v_reader_3527_);
lean_dec(v_fst_3525_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3568_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___f_3538_; lean_object* v___f_3539_; uint8_t v___y_3541_; 
v___f_3538_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3538_, 0, v_inst_3273_);
lean_closure_set(v___f_3538_, 1, v_handler_3275_);
v___f_3539_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3526_) == 0)
{
uint8_t v_sentMessage_3564_; 
v_sentMessage_3564_ = lean_ctor_get_uint8(v_writer_3528_, sizeof(void*)*6);
if (v_sentMessage_3564_ == 0)
{
lean_object* v_state_3565_; 
v_state_3565_ = lean_ctor_get(v_reader_3527_, 0);
if (lean_obj_tag(v_state_3565_) == 2)
{
v___y_3541_ = v_x_3504_;
goto v___jp_3540_;
}
else
{
v___y_3541_ = v_sentMessage_3564_;
goto v___jp_3540_;
}
}
else
{
uint8_t v___x_3566_; 
v___x_3566_ = 0;
v___y_3541_ = v___x_3566_;
goto v___jp_3540_;
}
}
else
{
uint8_t v___x_3567_; 
v___x_3567_ = 0;
v___y_3541_ = v___x_3567_;
goto v___jp_3540_;
}
v___jp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3537_ == 0)
{
v___x_3543_ = v___x_3536_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_reader_3527_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_writer_3528_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_config_3529_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_events_3530_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_error_3531_);
lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_instant_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*6, v_keepAlive_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*6 + 1, v_forcedFlush_3534_);
v___x_3543_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v_st_3545_; 
lean_ctor_set_uint8(v___x_3543_, sizeof(void*)*6 + 2, v___y_3541_);
lean_inc_ref(v_requestStream_3510_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3543_);
v_st_3545_ = v___x_3521_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_requestStream_3510_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_keepAliveTimeout_3511_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v_currentTimeout_3512_);
lean_ctor_set(v_reuseFailAlloc_3562_, 4, v_headerTimeout_3513_);
lean_ctor_set(v_reuseFailAlloc_3562_, 5, v_response_3514_);
lean_ctor_set(v_reuseFailAlloc_3562_, 6, v_respStream_3515_);
lean_ctor_set(v_reuseFailAlloc_3562_, 7, v_expectData_3517_);
lean_ctor_set(v_reuseFailAlloc_3562_, 8, v_pendingHead_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*9, v_requiresData_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*9 + 1, v_handlerDispatched_3518_);
v_st_3545_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___f_3546_; 
lean_inc_ref(v_st_3545_);
v___f_3546_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3546_, 0, v_st_3545_);
if (lean_obj_tag(v_snd_3526_) == 1)
{
lean_object* v_val_3547_; uint8_t v_final_3548_; uint8_t v_incomplete_3549_; lean_object* v_chunk_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___f_3555_; lean_object* v___f_3556_; lean_object* v___x_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; 
lean_dec_ref(v_st_3545_);
v_val_3547_ = lean_ctor_get(v_snd_3526_, 0);
lean_inc(v_val_3547_);
lean_dec_ref(v_snd_3526_);
v_final_3548_ = lean_ctor_get_uint8(v_val_3547_, sizeof(void*)*1);
v_incomplete_3549_ = lean_ctor_get_uint8(v_val_3547_, sizeof(void*)*1 + 1);
v_chunk_3550_ = lean_ctor_get(v_val_3547_, 0);
lean_inc_ref(v_chunk_3550_);
lean_dec(v_val_3547_);
lean_inc_ref_n(v_requestStream_3510_, 2);
v___x_3551_ = l_Std_Http_Body_Stream_send(v_requestStream_3510_, v_chunk_3550_, v_incomplete_3549_);
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = 0;
v___x_3554_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3552_, v___x_3553_, v___x_3551_, v___f_3538_);
lean_inc_ref_n(v___f_3546_, 2);
v___f_3555_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3555_, 0, v___f_3546_);
v___f_3556_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3556_, 0, v_requestStream_3510_);
lean_closure_set(v___f_3556_, 1, v___f_3555_);
lean_closure_set(v___f_3556_, 2, v___f_3546_);
v___x_3557_ = lean_box(v_final_3548_);
v___f_3558_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3558_, 0, v___x_3557_);
lean_closure_set(v___f_3558_, 1, v___f_3546_);
lean_closure_set(v___f_3558_, 2, v___f_3539_);
lean_closure_set(v___f_3558_, 3, v_requestStream_3510_);
lean_closure_set(v___f_3558_, 4, v___f_3556_);
v___x_3559_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3552_, v___x_3553_, v___x_3554_, v___f_3558_);
return v___x_3559_;
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec_ref(v___f_3546_);
lean_dec_ref(v___f_3538_);
lean_dec(v_snd_3526_);
lean_dec_ref(v_requestStream_3510_);
v___x_3560_ = lean_box(0);
v___x_3561_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3545_, v___x_3560_);
return v___x_3561_;
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
lean_object* v_x_3570_; 
v_x_3570_ = lean_ctor_get(v_event_3277_, 0);
lean_inc_ref(v_x_3570_);
lean_dec_ref(v_event_3277_);
if (lean_obj_tag(v_x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v_onFailure_3572_; lean_object* v___x_3573_; lean_object* v___f_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; lean_object* v___x_3577_; 
lean_dec_ref(v_config_3276_);
lean_dec_ref(v_inst_3274_);
v_a_3571_ = lean_ctor_get(v_x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v_x_3570_);
v_onFailure_3572_ = lean_ctor_get(v_inst_3273_, 2);
lean_inc_ref(v_onFailure_3572_);
lean_dec_ref(v_inst_3273_);
v___x_3573_ = lean_apply_3(v_onFailure_3572_, v_handler_3275_, v_a_3571_, lean_box(0));
v___f_3574_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3574_, 0, v_state_3278_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = 0;
v___x_3577_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3575_, v___x_3576_, v___x_3573_, v___f_3574_);
return v___x_3577_;
}
else
{
lean_object* v_machine_3578_; lean_object* v_reader_3579_; lean_object* v_state_3580_; 
lean_dec(v_handler_3275_);
lean_dec_ref(v_inst_3273_);
v_machine_3578_ = lean_ctor_get(v_state_3278_, 0);
lean_inc_ref(v_machine_3578_);
v_reader_3579_ = lean_ctor_get(v_machine_3578_, 0);
v_state_3580_ = lean_ctor_get(v_reader_3579_, 0);
if (lean_obj_tag(v_state_3580_) == 7)
{
lean_object* v_a_3581_; lean_object* v_requestStream_3582_; lean_object* v_keepAliveTimeout_3583_; lean_object* v_currentTimeout_3584_; lean_object* v_headerTimeout_3585_; lean_object* v_response_3586_; lean_object* v_respStream_3587_; uint8_t v_requiresData_3588_; lean_object* v_expectData_3589_; lean_object* v_pendingHead_3590_; lean_object* v_close_3591_; lean_object* v_isClosed_3592_; lean_object* v_body_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___f_3596_; lean_object* v___f_3597_; lean_object* v___f_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; 
lean_dec_ref(v_config_3276_);
v_a_3581_ = lean_ctor_get(v_x_3570_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v_x_3570_);
v_requestStream_3582_ = lean_ctor_get(v_state_3278_, 1);
lean_inc_ref(v_requestStream_3582_);
v_keepAliveTimeout_3583_ = lean_ctor_get(v_state_3278_, 2);
lean_inc(v_keepAliveTimeout_3583_);
v_currentTimeout_3584_ = lean_ctor_get(v_state_3278_, 3);
lean_inc(v_currentTimeout_3584_);
v_headerTimeout_3585_ = lean_ctor_get(v_state_3278_, 4);
lean_inc(v_headerTimeout_3585_);
v_response_3586_ = lean_ctor_get(v_state_3278_, 5);
lean_inc_ref(v_response_3586_);
v_respStream_3587_ = lean_ctor_get(v_state_3278_, 6);
lean_inc(v_respStream_3587_);
v_requiresData_3588_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3589_ = lean_ctor_get(v_state_3278_, 7);
lean_inc(v_expectData_3589_);
v_pendingHead_3590_ = lean_ctor_get(v_state_3278_, 8);
lean_inc(v_pendingHead_3590_);
lean_dec_ref(v_state_3278_);
v_close_3591_ = lean_ctor_get(v_inst_3274_, 1);
lean_inc_ref(v_close_3591_);
v_isClosed_3592_ = lean_ctor_get(v_inst_3274_, 2);
lean_inc_ref(v_isClosed_3592_);
lean_dec_ref(v_inst_3274_);
v_body_3593_ = lean_ctor_get(v_a_3581_, 1);
lean_inc_n(v_body_3593_, 2);
lean_dec(v_a_3581_);
v___x_3594_ = lean_apply_2(v_isClosed_3592_, v_body_3593_, lean_box(0));
v___x_3595_ = lean_box(v_requiresData_3588_);
v___f_3596_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3596_, 0, v_machine_3578_);
lean_closure_set(v___f_3596_, 1, v_requestStream_3582_);
lean_closure_set(v___f_3596_, 2, v_keepAliveTimeout_3583_);
lean_closure_set(v___f_3596_, 3, v_currentTimeout_3584_);
lean_closure_set(v___f_3596_, 4, v_headerTimeout_3585_);
lean_closure_set(v___f_3596_, 5, v_response_3586_);
lean_closure_set(v___f_3596_, 6, v_respStream_3587_);
lean_closure_set(v___f_3596_, 7, v___x_3595_);
lean_closure_set(v___f_3596_, 8, v_expectData_3589_);
lean_closure_set(v___f_3596_, 9, v_pendingHead_3590_);
lean_inc_ref(v___f_3596_);
v___f_3597_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3597_, 0, v___f_3596_);
v___f_3598_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3598_, 0, v_close_3591_);
lean_closure_set(v___f_3598_, 1, v_body_3593_);
lean_closure_set(v___f_3598_, 2, v___f_3597_);
lean_closure_set(v___f_3598_, 3, v___f_3596_);
v___x_3599_ = lean_unsigned_to_nat(0u);
v___x_3600_ = 0;
v___x_3601_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3599_, v___x_3600_, v___x_3594_, v___f_3598_);
return v___x_3601_;
}
else
{
lean_object* v_a_3602_; lean_object* v_requestStream_3603_; lean_object* v_keepAliveTimeout_3604_; lean_object* v_currentTimeout_3605_; lean_object* v_headerTimeout_3606_; lean_object* v_response_3607_; uint8_t v_requiresData_3608_; lean_object* v_expectData_3609_; lean_object* v_pendingHead_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_a_3602_ = lean_ctor_get(v_x_3570_, 0);
lean_inc(v_a_3602_);
lean_dec_ref(v_x_3570_);
v_requestStream_3603_ = lean_ctor_get(v_state_3278_, 1);
lean_inc_ref(v_requestStream_3603_);
v_keepAliveTimeout_3604_ = lean_ctor_get(v_state_3278_, 2);
lean_inc(v_keepAliveTimeout_3604_);
v_currentTimeout_3605_ = lean_ctor_get(v_state_3278_, 3);
lean_inc(v_currentTimeout_3605_);
v_headerTimeout_3606_ = lean_ctor_get(v_state_3278_, 4);
lean_inc(v_headerTimeout_3606_);
v_response_3607_ = lean_ctor_get(v_state_3278_, 5);
lean_inc_ref(v_response_3607_);
v_requiresData_3608_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3609_ = lean_ctor_get(v_state_3278_, 7);
lean_inc(v_expectData_3609_);
v_pendingHead_3610_ = lean_ctor_get(v_state_3278_, 8);
lean_inc(v_pendingHead_3610_);
lean_dec_ref(v_state_3278_);
lean_inc_ref(v_inst_3274_);
v___x_3611_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3274_, v_config_3276_, v_machine_3578_, v_a_3602_);
v___x_3612_ = 0;
v___x_3613_ = lean_box(v_requiresData_3608_);
v___x_3614_ = lean_box(v___x_3612_);
v___f_3615_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3615_, 0, v_requestStream_3603_);
lean_closure_set(v___f_3615_, 1, v_keepAliveTimeout_3604_);
lean_closure_set(v___f_3615_, 2, v_currentTimeout_3605_);
lean_closure_set(v___f_3615_, 3, v_headerTimeout_3606_);
lean_closure_set(v___f_3615_, 4, v_response_3607_);
lean_closure_set(v___f_3615_, 5, v___x_3613_);
lean_closure_set(v___f_3615_, 6, v_expectData_3609_);
lean_closure_set(v___f_3615_, 7, v___x_3614_);
lean_closure_set(v___f_3615_, 8, v_pendingHead_3610_);
v___f_3616_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3616_, 0, v___f_3615_);
v___x_3617_ = lean_box(v___x_3612_);
lean_inc_ref(v___f_3616_);
v___f_3618_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 6, 4);
lean_closure_set(v___f_3618_, 0, v___x_3617_);
lean_closure_set(v___f_3618_, 1, v___f_3616_);
lean_closure_set(v___f_3618_, 2, v_inst_3274_);
lean_closure_set(v___f_3618_, 3, v___f_3616_);
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3619_, v___x_3612_, v___x_3611_, v___f_3618_);
return v___x_3620_;
}
}
}
case 4:
{
lean_object* v_onFailure_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; lean_object* v___x_3627_; 
lean_dec_ref(v_config_3276_);
lean_dec_ref(v_inst_3274_);
v_onFailure_3621_ = lean_ctor_get(v_inst_3273_, 2);
lean_inc_ref(v_onFailure_3621_);
lean_dec_ref(v_inst_3273_);
v___x_3622_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_3623_ = lean_apply_3(v_onFailure_3621_, v_handler_3275_, v___x_3622_, lean_box(0));
v___f_3624_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 3, 1);
lean_closure_set(v___f_3624_, 0, v_state_3278_);
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = 0;
v___x_3627_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3625_, v___x_3626_, v___x_3623_, v___f_3624_);
return v___x_3627_;
}
case 5:
{
lean_object* v_machine_3628_; lean_object* v_requestStream_3629_; lean_object* v_keepAliveTimeout_3630_; lean_object* v_currentTimeout_3631_; lean_object* v_headerTimeout_3632_; lean_object* v_response_3633_; lean_object* v_respStream_3634_; uint8_t v_requiresData_3635_; lean_object* v_expectData_3636_; lean_object* v_pendingHead_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3651_; 
lean_dec_ref(v_config_3276_);
lean_dec(v_handler_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_inst_3273_);
v_machine_3628_ = lean_ctor_get(v_state_3278_, 0);
v_requestStream_3629_ = lean_ctor_get(v_state_3278_, 1);
v_keepAliveTimeout_3630_ = lean_ctor_get(v_state_3278_, 2);
v_currentTimeout_3631_ = lean_ctor_get(v_state_3278_, 3);
v_headerTimeout_3632_ = lean_ctor_get(v_state_3278_, 4);
v_response_3633_ = lean_ctor_get(v_state_3278_, 5);
v_respStream_3634_ = lean_ctor_get(v_state_3278_, 6);
v_requiresData_3635_ = lean_ctor_get_uint8(v_state_3278_, sizeof(void*)*9);
v_expectData_3636_ = lean_ctor_get(v_state_3278_, 7);
v_pendingHead_3637_ = lean_ctor_get(v_state_3278_, 8);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_state_3278_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3639_ = v_state_3278_;
v_isShared_3640_ = v_isSharedCheck_3651_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_pendingHead_3637_);
lean_inc(v_expectData_3636_);
lean_inc(v_respStream_3634_);
lean_inc(v_response_3633_);
lean_inc(v_headerTimeout_3632_);
lean_inc(v_currentTimeout_3631_);
lean_inc(v_keepAliveTimeout_3630_);
lean_inc(v_requestStream_3629_);
lean_inc(v_machine_3628_);
lean_dec(v_state_3278_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3651_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3645_; 
v___x_3641_ = lean_box(55);
v___x_3642_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3628_, v___x_3641_);
v___x_3643_ = 0;
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3642_);
v___x_3645_ = v___x_3639_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_requestStream_3629_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_keepAliveTimeout_3630_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_currentTimeout_3631_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_headerTimeout_3632_);
lean_ctor_set(v_reuseFailAlloc_3650_, 5, v_response_3633_);
lean_ctor_set(v_reuseFailAlloc_3650_, 6, v_respStream_3634_);
lean_ctor_set(v_reuseFailAlloc_3650_, 7, v_expectData_3636_);
lean_ctor_set(v_reuseFailAlloc_3650_, 8, v_pendingHead_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3650_, sizeof(void*)*9, v_requiresData_3635_);
v___x_3645_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*9 + 1, v___x_3643_);
v___x_3646_ = lean_box(v___x_3643_);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
return v___x_3649_;
}
}
}
default: 
{
uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec_ref(v_config_3276_);
lean_dec(v_handler_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_inst_3273_);
v___x_3652_ = 1;
v___x_3653_ = lean_box(v___x_3652_);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v_state_3278_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3657_, lean_object* v_inst_3658_, lean_object* v_handler_3659_, lean_object* v_config_3660_, lean_object* v_event_3661_, lean_object* v_state_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3657_, v_inst_3658_, v_handler_3659_, v_config_3660_, v_event_3661_, v_state_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3665_, lean_object* v_00_u03b2_3666_, lean_object* v_inst_3667_, lean_object* v_inst_3668_, lean_object* v_handler_3669_, lean_object* v_config_3670_, lean_object* v_event_3671_, lean_object* v_state_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3667_, v_inst_3668_, v_handler_3669_, v_config_3670_, v_event_3671_, v_state_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3675_, lean_object* v_00_u03b2_3676_, lean_object* v_inst_3677_, lean_object* v_inst_3678_, lean_object* v_handler_3679_, lean_object* v_config_3680_, lean_object* v_event_3681_, lean_object* v_state_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3675_, v_00_u03b2_3676_, v_inst_3677_, v_inst_3678_, v_handler_3679_, v_config_3680_, v_event_3681_, v_state_3682_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3685_, uint8_t v_handlerDispatched_3686_, lean_object* v_headerTimeout_3687_, lean_object* v_expectData_3688_, lean_object* v_keepAliveTimeout_3689_, lean_object* v_currentTimeout_3690_, lean_object* v_respStream_3691_, lean_object* v_response_3692_, lean_object* v_socket_3693_, uint8_t v_requiresData_3694_, uint8_t v_sentMessage_3695_, lean_object* v_reader_3696_, uint8_t v_requestBodyInterested_3697_, lean_object* v_requestBody_3698_){
_start:
{
lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3712_; 
if (v_requiresData_3694_ == 0)
{
if (v_handlerDispatched_3686_ == 0)
{
goto v___jp_3715_;
}
else
{
if (lean_obj_tag(v_respStream_3691_) == 0)
{
if (v_sentMessage_3695_ == 0)
{
lean_object* v_state_3719_; 
v_state_3719_ = lean_ctor_get(v_reader_3696_, 0);
if (lean_obj_tag(v_state_3719_) == 2)
{
if (v_requestBodyInterested_3697_ == 0)
{
lean_dec(v_socket_3693_);
goto v___jp_3717_;
}
else
{
goto v___jp_3715_;
}
}
else
{
lean_dec(v_socket_3693_);
goto v___jp_3717_;
}
}
else
{
goto v___jp_3715_;
}
}
else
{
goto v___jp_3715_;
}
}
}
else
{
goto v___jp_3715_;
}
v___jp_3700_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3708_, 0, v___y_3701_);
lean_ctor_set(v___x_3708_, 1, v___y_3703_);
lean_ctor_set(v___x_3708_, 2, v___y_3707_);
lean_ctor_set(v___x_3708_, 3, v___y_3706_);
lean_ctor_set(v___x_3708_, 4, v_requestBody_3698_);
lean_ctor_set(v___x_3708_, 5, v___y_3705_);
lean_ctor_set(v___x_3708_, 6, v___y_3704_);
lean_ctor_set(v___x_3708_, 7, v___y_3702_);
lean_ctor_set(v___x_3708_, 8, v_connectionContext_3685_);
v___x_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
return v___x_3710_;
}
v___jp_3711_:
{
if (v_handlerDispatched_3686_ == 0)
{
lean_object* v___x_3713_; 
lean_dec_ref(v_response_3692_);
v___x_3713_ = lean_box(0);
v___y_3701_ = v___y_3712_;
v___y_3702_ = v_headerTimeout_3687_;
v___y_3703_ = v_expectData_3688_;
v___y_3704_ = v_keepAliveTimeout_3689_;
v___y_3705_ = v_currentTimeout_3690_;
v___y_3706_ = v_respStream_3691_;
v___y_3707_ = v___x_3713_;
goto v___jp_3700_;
}
else
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3714_, 0, v_response_3692_);
v___y_3701_ = v___y_3712_;
v___y_3702_ = v_headerTimeout_3687_;
v___y_3703_ = v_expectData_3688_;
v___y_3704_ = v_keepAliveTimeout_3689_;
v___y_3705_ = v_currentTimeout_3690_;
v___y_3706_ = v_respStream_3691_;
v___y_3707_ = v___x_3714_;
goto v___jp_3700_;
}
}
v___jp_3715_:
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_socket_3693_);
v___y_3712_ = v___x_3716_;
goto v___jp_3711_;
}
v___jp_3717_:
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_box(0);
v___y_3712_ = v___x_3718_;
goto v___jp_3711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3720_, lean_object* v_handlerDispatched_3721_, lean_object* v_headerTimeout_3722_, lean_object* v_expectData_3723_, lean_object* v_keepAliveTimeout_3724_, lean_object* v_currentTimeout_3725_, lean_object* v_respStream_3726_, lean_object* v_response_3727_, lean_object* v_socket_3728_, lean_object* v_requiresData_3729_, lean_object* v_sentMessage_3730_, lean_object* v_reader_3731_, lean_object* v_requestBodyInterested_3732_, lean_object* v_requestBody_3733_, lean_object* v___y_3734_){
_start:
{
uint8_t v_handlerDispatched_boxed_3735_; uint8_t v_requiresData_boxed_3736_; uint8_t v_sentMessage_boxed_3737_; uint8_t v_requestBodyInterested_boxed_3738_; lean_object* v_res_3739_; 
v_handlerDispatched_boxed_3735_ = lean_unbox(v_handlerDispatched_3721_);
v_requiresData_boxed_3736_ = lean_unbox(v_requiresData_3729_);
v_sentMessage_boxed_3737_ = lean_unbox(v_sentMessage_3730_);
v_requestBodyInterested_boxed_3738_ = lean_unbox(v_requestBodyInterested_3732_);
v_res_3739_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3720_, v_handlerDispatched_boxed_3735_, v_headerTimeout_3722_, v_expectData_3723_, v_keepAliveTimeout_3724_, v_currentTimeout_3725_, v_respStream_3726_, v_response_3727_, v_socket_3728_, v_requiresData_boxed_3736_, v_sentMessage_boxed_3737_, v_reader_3731_, v_requestBodyInterested_boxed_3738_, v_requestBody_3733_);
lean_dec_ref(v_reader_3731_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3740_, lean_object* v_x_3741_){
_start:
{
if (lean_obj_tag(v_x_3741_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v___f_3740_);
v_a_3743_ = lean_ctor_get(v_x_3741_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_x_3741_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3745_ = v_x_3741_;
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v_x_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3753_; 
v_a_3752_ = lean_ctor_get(v_x_3741_, 0);
lean_inc(v_a_3752_);
lean_dec_ref(v_x_3741_);
v___x_3753_ = lean_apply_2(v___f_3740_, v_a_3752_, lean_box(0));
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3754_, lean_object* v_x_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3754_, v_x_3755_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3762_, uint8_t v_handlerDispatched_3763_, lean_object* v_headerTimeout_3764_, lean_object* v_expectData_3765_, lean_object* v_keepAliveTimeout_3766_, lean_object* v_currentTimeout_3767_, lean_object* v_respStream_3768_, lean_object* v_response_3769_, lean_object* v_socket_3770_, uint8_t v_requiresData_3771_, uint8_t v_sentMessage_3772_, lean_object* v_reader_3773_, uint8_t v_pullBodyStalled_3774_, uint8_t v_requestBodyOpen_3775_, lean_object* v_requestStream_3776_, uint8_t v_requestBodyInterested_3777_){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___f_3783_; lean_object* v___f_3784_; 
v___x_3779_ = lean_box(v_handlerDispatched_3763_);
v___x_3780_ = lean_box(v_requiresData_3771_);
v___x_3781_ = lean_box(v_sentMessage_3772_);
v___x_3782_ = lean_box(v_requestBodyInterested_3777_);
lean_inc_ref(v_reader_3773_);
v___f_3783_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3783_, 0, v_connectionContext_3762_);
lean_closure_set(v___f_3783_, 1, v___x_3779_);
lean_closure_set(v___f_3783_, 2, v_headerTimeout_3764_);
lean_closure_set(v___f_3783_, 3, v_expectData_3765_);
lean_closure_set(v___f_3783_, 4, v_keepAliveTimeout_3766_);
lean_closure_set(v___f_3783_, 5, v_currentTimeout_3767_);
lean_closure_set(v___f_3783_, 6, v_respStream_3768_);
lean_closure_set(v___f_3783_, 7, v_response_3769_);
lean_closure_set(v___f_3783_, 8, v_socket_3770_);
lean_closure_set(v___f_3783_, 9, v___x_3780_);
lean_closure_set(v___f_3783_, 10, v___x_3781_);
lean_closure_set(v___f_3783_, 11, v_reader_3773_);
lean_closure_set(v___f_3783_, 12, v___x_3782_);
v___f_3784_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3784_, 0, v___f_3783_);
if (v_sentMessage_3772_ == 0)
{
lean_object* v_state_3790_; 
v_state_3790_ = lean_ctor_get(v_reader_3773_, 0);
lean_inc(v_state_3790_);
lean_dec_ref(v_reader_3773_);
if (lean_obj_tag(v_state_3790_) == 2)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3801_; 
v_isSharedCheck_3801_ = !lean_is_exclusive(v_state_3790_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v_state_3790_, 0);
lean_dec(v_unused_3802_);
v___x_3792_ = v_state_3790_;
v_isShared_3793_ = v_isSharedCheck_3801_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v_state_3790_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3801_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
if (v_pullBodyStalled_3774_ == 0)
{
if (v_requestBodyOpen_3775_ == 0)
{
lean_del_object(v___x_3792_);
lean_dec_ref(v_requestStream_3776_);
goto v___jp_3785_;
}
else
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 1);
lean_ctor_set(v___x_3792_, 0, v_requestStream_3776_);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_requestStream_3776_);
v___x_3795_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
v___x_3798_ = lean_unsigned_to_nat(0u);
v___x_3799_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3798_, v_pullBodyStalled_3774_, v___x_3797_, v___f_3784_);
return v___x_3799_;
}
}
}
else
{
lean_del_object(v___x_3792_);
lean_dec_ref(v_requestStream_3776_);
goto v___jp_3785_;
}
}
}
else
{
lean_dec(v_state_3790_);
lean_dec_ref(v_requestStream_3776_);
goto v___jp_3785_;
}
}
else
{
lean_dec_ref(v_requestStream_3776_);
lean_dec_ref(v_reader_3773_);
goto v___jp_3785_;
}
v___jp_3785_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; lean_object* v___x_3789_; 
v___x_3786_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3787_ = lean_unsigned_to_nat(0u);
v___x_3788_ = 0;
v___x_3789_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3787_, v___x_3788_, v___x_3786_, v___f_3784_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3803_ = _args[0];
lean_object* v_handlerDispatched_3804_ = _args[1];
lean_object* v_headerTimeout_3805_ = _args[2];
lean_object* v_expectData_3806_ = _args[3];
lean_object* v_keepAliveTimeout_3807_ = _args[4];
lean_object* v_currentTimeout_3808_ = _args[5];
lean_object* v_respStream_3809_ = _args[6];
lean_object* v_response_3810_ = _args[7];
lean_object* v_socket_3811_ = _args[8];
lean_object* v_requiresData_3812_ = _args[9];
lean_object* v_sentMessage_3813_ = _args[10];
lean_object* v_reader_3814_ = _args[11];
lean_object* v_pullBodyStalled_3815_ = _args[12];
lean_object* v_requestBodyOpen_3816_ = _args[13];
lean_object* v_requestStream_3817_ = _args[14];
lean_object* v_requestBodyInterested_3818_ = _args[15];
lean_object* v___y_3819_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3820_; uint8_t v_requiresData_boxed_3821_; uint8_t v_sentMessage_boxed_3822_; uint8_t v_pullBodyStalled_boxed_3823_; uint8_t v_requestBodyOpen_boxed_3824_; uint8_t v_requestBodyInterested_boxed_3825_; lean_object* v_res_3826_; 
v_handlerDispatched_boxed_3820_ = lean_unbox(v_handlerDispatched_3804_);
v_requiresData_boxed_3821_ = lean_unbox(v_requiresData_3812_);
v_sentMessage_boxed_3822_ = lean_unbox(v_sentMessage_3813_);
v_pullBodyStalled_boxed_3823_ = lean_unbox(v_pullBodyStalled_3815_);
v_requestBodyOpen_boxed_3824_ = lean_unbox(v_requestBodyOpen_3816_);
v_requestBodyInterested_boxed_3825_ = lean_unbox(v_requestBodyInterested_3818_);
v_res_3826_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3803_, v_handlerDispatched_boxed_3820_, v_headerTimeout_3805_, v_expectData_3806_, v_keepAliveTimeout_3807_, v_currentTimeout_3808_, v_respStream_3809_, v_response_3810_, v_socket_3811_, v_requiresData_boxed_3821_, v_sentMessage_boxed_3822_, v_reader_3814_, v_pullBodyStalled_boxed_3823_, v_requestBodyOpen_boxed_3824_, v_requestStream_3817_, v_requestBodyInterested_boxed_3825_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3827_, lean_object* v_x_3828_){
_start:
{
if (lean_obj_tag(v_x_3828_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v___f_3827_);
v_a_3830_ = lean_ctor_get(v_x_3828_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_x_3828_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3832_ = v_x_3828_;
v_isShared_3833_ = v_isSharedCheck_3838_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v_x_3828_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3838_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
return v___x_3836_;
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3840_; 
v_a_3839_ = lean_ctor_get(v_x_3828_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v_x_3828_);
v___x_3840_ = lean_apply_2(v___f_3827_, v_a_3839_, lean_box(0));
return v___x_3840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3841_, lean_object* v_x_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3841_, v_x_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3850_, uint8_t v_handlerDispatched_3851_, lean_object* v_headerTimeout_3852_, lean_object* v_expectData_3853_, lean_object* v_keepAliveTimeout_3854_, lean_object* v_currentTimeout_3855_, lean_object* v_respStream_3856_, lean_object* v_response_3857_, lean_object* v_socket_3858_, uint8_t v_requiresData_3859_, uint8_t v_sentMessage_3860_, lean_object* v_reader_3861_, uint8_t v_pullBodyStalled_3862_, lean_object* v_requestStream_3863_, uint8_t v_requestBodyOpen_3864_){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___f_3871_; lean_object* v___f_3872_; 
v___x_3866_ = lean_box(v_handlerDispatched_3851_);
v___x_3867_ = lean_box(v_requiresData_3859_);
v___x_3868_ = lean_box(v_sentMessage_3860_);
v___x_3869_ = lean_box(v_pullBodyStalled_3862_);
v___x_3870_ = lean_box(v_requestBodyOpen_3864_);
lean_inc_ref(v_requestStream_3863_);
lean_inc_ref(v_reader_3861_);
v___f_3871_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3871_, 0, v_connectionContext_3850_);
lean_closure_set(v___f_3871_, 1, v___x_3866_);
lean_closure_set(v___f_3871_, 2, v_headerTimeout_3852_);
lean_closure_set(v___f_3871_, 3, v_expectData_3853_);
lean_closure_set(v___f_3871_, 4, v_keepAliveTimeout_3854_);
lean_closure_set(v___f_3871_, 5, v_currentTimeout_3855_);
lean_closure_set(v___f_3871_, 6, v_respStream_3856_);
lean_closure_set(v___f_3871_, 7, v_response_3857_);
lean_closure_set(v___f_3871_, 8, v_socket_3858_);
lean_closure_set(v___f_3871_, 9, v___x_3867_);
lean_closure_set(v___f_3871_, 10, v___x_3868_);
lean_closure_set(v___f_3871_, 11, v_reader_3861_);
lean_closure_set(v___f_3871_, 12, v___x_3869_);
lean_closure_set(v___f_3871_, 13, v___x_3870_);
lean_closure_set(v___f_3871_, 14, v_requestStream_3863_);
v___f_3872_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3872_, 0, v___f_3871_);
if (v_sentMessage_3860_ == 0)
{
lean_object* v_state_3878_; 
v_state_3878_ = lean_ctor_get(v_reader_3861_, 0);
lean_inc(v_state_3878_);
lean_dec_ref(v_reader_3861_);
if (lean_obj_tag(v_state_3878_) == 2)
{
lean_dec_ref(v_state_3878_);
if (v_requestBodyOpen_3864_ == 0)
{
lean_dec_ref(v_requestStream_3863_);
goto v___jp_3873_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3863_);
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3880_, v_sentMessage_3860_, v___x_3879_, v___f_3872_);
return v___x_3881_;
}
}
else
{
lean_dec(v_state_3878_);
lean_dec_ref(v_requestStream_3863_);
goto v___jp_3873_;
}
}
else
{
lean_dec_ref(v_requestStream_3863_);
lean_dec_ref(v_reader_3861_);
goto v___jp_3873_;
}
v___jp_3873_:
{
uint8_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = 0;
v___x_3875_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3876_, v___x_3874_, v___x_3875_, v___f_3872_);
return v___x_3877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3882_, lean_object* v_handlerDispatched_3883_, lean_object* v_headerTimeout_3884_, lean_object* v_expectData_3885_, lean_object* v_keepAliveTimeout_3886_, lean_object* v_currentTimeout_3887_, lean_object* v_respStream_3888_, lean_object* v_response_3889_, lean_object* v_socket_3890_, lean_object* v_requiresData_3891_, lean_object* v_sentMessage_3892_, lean_object* v_reader_3893_, lean_object* v_pullBodyStalled_3894_, lean_object* v_requestStream_3895_, lean_object* v_requestBodyOpen_3896_, lean_object* v___y_3897_){
_start:
{
uint8_t v_handlerDispatched_boxed_3898_; uint8_t v_requiresData_boxed_3899_; uint8_t v_sentMessage_boxed_3900_; uint8_t v_pullBodyStalled_boxed_3901_; uint8_t v_requestBodyOpen_boxed_3902_; lean_object* v_res_3903_; 
v_handlerDispatched_boxed_3898_ = lean_unbox(v_handlerDispatched_3883_);
v_requiresData_boxed_3899_ = lean_unbox(v_requiresData_3891_);
v_sentMessage_boxed_3900_ = lean_unbox(v_sentMessage_3892_);
v_pullBodyStalled_boxed_3901_ = lean_unbox(v_pullBodyStalled_3894_);
v_requestBodyOpen_boxed_3902_ = lean_unbox(v_requestBodyOpen_3896_);
v_res_3903_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3882_, v_handlerDispatched_boxed_3898_, v_headerTimeout_3884_, v_expectData_3885_, v_keepAliveTimeout_3886_, v_currentTimeout_3887_, v_respStream_3888_, v_response_3889_, v_socket_3890_, v_requiresData_boxed_3899_, v_sentMessage_boxed_3900_, v_reader_3893_, v_pullBodyStalled_boxed_3901_, v_requestStream_3895_, v_requestBodyOpen_boxed_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3904_, lean_object* v___f_3905_, uint8_t v___x_3906_, lean_object* v_x_3907_){
_start:
{
uint8_t v___y_3910_; 
if (lean_obj_tag(v_x_3907_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref(v___f_3905_);
v_a_3916_ = lean_ctor_get(v_x_3907_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_x_3907_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v_x_3907_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v_x_3907_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
}
}
else
{
lean_object* v_a_3925_; uint8_t v___x_3926_; 
v_a_3925_ = lean_ctor_get(v_x_3907_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v_x_3907_);
v___x_3926_ = lean_unbox(v_a_3925_);
lean_dec(v_a_3925_);
if (v___x_3926_ == 0)
{
v___y_3910_ = v___x_3906_;
goto v___jp_3909_;
}
else
{
v___y_3910_ = v_sentMessage_3904_;
goto v___jp_3909_;
}
}
v___jp_3909_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3911_ = lean_box(v___y_3910_);
v___x_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3914_, v_sentMessage_3904_, v___x_3913_, v___f_3905_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3927_, lean_object* v___f_3928_, lean_object* v___x_3929_, lean_object* v_x_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v_sentMessage_boxed_3932_; uint8_t v___x_3774__boxed_3933_; lean_object* v_res_3934_; 
v_sentMessage_boxed_3932_ = lean_unbox(v_sentMessage_3927_);
v___x_3774__boxed_3933_ = lean_unbox(v___x_3929_);
v_res_3934_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3932_, v___f_3928_, v___x_3774__boxed_3933_, v_x_3930_);
return v_res_3934_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___f_3935_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3936_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8));
v___x_3937_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3938_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3938_, 0, lean_box(0));
lean_closure_set(v___x_3938_, 1, lean_box(0));
lean_closure_set(v___x_3938_, 2, lean_box(0));
lean_closure_set(v___x_3938_, 3, v___x_3937_);
lean_closure_set(v___x_3938_, 4, lean_box(0));
lean_closure_set(v___x_3938_, 5, lean_box(0));
lean_closure_set(v___x_3938_, 6, v___x_3936_);
lean_closure_set(v___x_3938_, 7, v___f_3935_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3939_, lean_object* v_connectionContext_3940_, lean_object* v_state_3941_){
_start:
{
lean_object* v_machine_3943_; lean_object* v_writer_3944_; lean_object* v_requestStream_3945_; lean_object* v_keepAliveTimeout_3946_; lean_object* v_currentTimeout_3947_; lean_object* v_headerTimeout_3948_; lean_object* v_response_3949_; lean_object* v_respStream_3950_; uint8_t v_requiresData_3951_; lean_object* v_expectData_3952_; uint8_t v_handlerDispatched_3953_; lean_object* v_reader_3954_; uint8_t v_pullBodyStalled_3955_; uint8_t v_sentMessage_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___f_3961_; lean_object* v___f_3962_; uint8_t v___y_3964_; 
v_machine_3943_ = lean_ctor_get(v_state_3941_, 0);
lean_inc_ref(v_machine_3943_);
v_writer_3944_ = lean_ctor_get(v_machine_3943_, 1);
lean_inc_ref(v_writer_3944_);
v_requestStream_3945_ = lean_ctor_get(v_state_3941_, 1);
lean_inc_ref_n(v_requestStream_3945_, 2);
v_keepAliveTimeout_3946_ = lean_ctor_get(v_state_3941_, 2);
lean_inc(v_keepAliveTimeout_3946_);
v_currentTimeout_3947_ = lean_ctor_get(v_state_3941_, 3);
lean_inc(v_currentTimeout_3947_);
v_headerTimeout_3948_ = lean_ctor_get(v_state_3941_, 4);
lean_inc(v_headerTimeout_3948_);
v_response_3949_ = lean_ctor_get(v_state_3941_, 5);
lean_inc_ref(v_response_3949_);
v_respStream_3950_ = lean_ctor_get(v_state_3941_, 6);
lean_inc(v_respStream_3950_);
v_requiresData_3951_ = lean_ctor_get_uint8(v_state_3941_, sizeof(void*)*9);
v_expectData_3952_ = lean_ctor_get(v_state_3941_, 7);
lean_inc(v_expectData_3952_);
v_handlerDispatched_3953_ = lean_ctor_get_uint8(v_state_3941_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3941_);
v_reader_3954_ = lean_ctor_get(v_machine_3943_, 0);
lean_inc_ref_n(v_reader_3954_, 2);
v_pullBodyStalled_3955_ = lean_ctor_get_uint8(v_machine_3943_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3943_);
v_sentMessage_3956_ = lean_ctor_get_uint8(v_writer_3944_, sizeof(void*)*6);
lean_dec_ref(v_writer_3944_);
v___x_3957_ = lean_box(v_handlerDispatched_3953_);
v___x_3958_ = lean_box(v_requiresData_3951_);
v___x_3959_ = lean_box(v_sentMessage_3956_);
v___x_3960_ = lean_box(v_pullBodyStalled_3955_);
v___f_3961_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3961_, 0, v_connectionContext_3940_);
lean_closure_set(v___f_3961_, 1, v___x_3957_);
lean_closure_set(v___f_3961_, 2, v_headerTimeout_3948_);
lean_closure_set(v___f_3961_, 3, v_expectData_3952_);
lean_closure_set(v___f_3961_, 4, v_keepAliveTimeout_3946_);
lean_closure_set(v___f_3961_, 5, v_currentTimeout_3947_);
lean_closure_set(v___f_3961_, 6, v_respStream_3950_);
lean_closure_set(v___f_3961_, 7, v_response_3949_);
lean_closure_set(v___f_3961_, 8, v_socket_3939_);
lean_closure_set(v___f_3961_, 9, v___x_3958_);
lean_closure_set(v___f_3961_, 10, v___x_3959_);
lean_closure_set(v___f_3961_, 11, v_reader_3954_);
lean_closure_set(v___f_3961_, 12, v___x_3960_);
lean_closure_set(v___f_3961_, 13, v_requestStream_3945_);
v___f_3962_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3962_, 0, v___f_3961_);
if (v_sentMessage_3956_ == 0)
{
lean_object* v_state_3970_; 
v_state_3970_ = lean_ctor_get(v_reader_3954_, 0);
lean_inc(v_state_3970_);
lean_dec_ref(v_reader_3954_);
if (lean_obj_tag(v_state_3970_) == 2)
{
lean_object* v___x_3971_; lean_object* v___f_3972_; lean_object* v___f_3973_; lean_object* v___x_3974_; lean_object* v___x_3290__overap_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___f_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec_ref(v_state_3970_);
v___x_3971_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3972_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_3973_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_3974_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3290__overap_3975_ = l_Std_Mutex_atomically___redArg(v___x_3971_, v___f_3972_, v___f_3973_, v_requestStream_3945_, v___x_3974_);
v___x_3976_ = lean_apply_1(v___x_3290__overap_3975_, lean_box(0));
v___x_3977_ = 1;
v___x_3978_ = lean_box(v_sentMessage_3956_);
v___x_3979_ = lean_box(v___x_3977_);
v___f_3980_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3980_, 0, v___x_3978_);
lean_closure_set(v___f_3980_, 1, v___f_3962_);
lean_closure_set(v___f_3980_, 2, v___x_3979_);
v___x_3981_ = lean_unsigned_to_nat(0u);
v___x_3982_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3981_, v_sentMessage_3956_, v___x_3976_, v___f_3980_);
return v___x_3982_;
}
else
{
lean_dec(v_state_3970_);
lean_dec_ref(v_requestStream_3945_);
v___y_3964_ = v_sentMessage_3956_;
goto v___jp_3963_;
}
}
else
{
uint8_t v___x_3983_; 
lean_dec_ref(v_reader_3954_);
lean_dec_ref(v_requestStream_3945_);
v___x_3983_ = 0;
v___y_3964_ = v___x_3983_;
goto v___jp_3963_;
}
v___jp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3965_ = lean_box(v___y_3964_);
v___x_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3968_, v___y_3964_, v___x_3967_, v___f_3962_);
return v___x_3969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3984_, lean_object* v_connectionContext_3985_, lean_object* v_state_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3984_, v_connectionContext_3985_, v_state_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3989_, lean_object* v_00_u03b2_3990_, lean_object* v_inst_3991_, lean_object* v_socket_3992_, lean_object* v_connectionContext_3993_, lean_object* v_state_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3992_, v_connectionContext_3993_, v_state_3994_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_3997_, lean_object* v_00_u03b2_3998_, lean_object* v_inst_3999_, lean_object* v_socket_4000_, lean_object* v_connectionContext_4001_, lean_object* v_state_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_3997_, v_00_u03b2_3998_, v_inst_3999_, v_socket_4000_, v_connectionContext_4001_, v_state_4002_);
lean_dec_ref(v_inst_3999_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4005_){
_start:
{
if (lean_obj_tag(v_x_4005_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4015_; 
v_a_4007_ = lean_ctor_get(v_x_4005_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v_x_4005_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4009_ = v_x_4005_;
v_isShared_4010_ = v_isSharedCheck_4015_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v_x_4005_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4015_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4034_; 
v_a_4016_ = lean_ctor_get(v_x_4005_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_x_4005_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4018_ = v_x_4005_;
v_isShared_4019_ = v_isSharedCheck_4034_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v_x_4005_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4034_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v_snd_4020_; uint8_t v___x_4021_; 
v_snd_4020_ = lean_ctor_get(v_a_4016_, 1);
v___x_4021_ = lean_unbox(v_snd_4020_);
if (v___x_4021_ == 0)
{
lean_object* v_fst_4022_; lean_object* v___x_4023_; lean_object* v___x_4025_; 
v_fst_4022_ = lean_ctor_get(v_a_4016_, 0);
lean_inc(v_fst_4022_);
lean_dec(v_a_4016_);
v___x_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4023_, 0, v_fst_4022_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4023_);
v___x_4025_ = v___x_4018_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
else
{
lean_object* v_fst_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v_fst_4028_ = lean_ctor_get(v_a_4016_, 0);
lean_inc(v_fst_4028_);
lean_dec(v_a_4016_);
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v_fst_4028_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4029_);
v___x_4031_ = v___x_4018_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4035_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4038_){
_start:
{
if (lean_obj_tag(v_x_4038_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4048_; 
v_a_4040_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4042_ = v_x_4038_;
v_isShared_4043_ = v_isSharedCheck_4048_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v_x_4038_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4048_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4058_; 
v_a_4049_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4051_ = v_x_4038_;
v_isShared_4052_ = v_isSharedCheck_4058_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v_x_4038_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4058_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v_a_4049_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4053_);
v___x_4055_ = v___x_4051_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; 
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4059_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4066_){
_start:
{
if (lean_obj_tag(v_x_4066_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4076_; 
v_a_4068_ = lean_ctor_get(v_x_4066_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4070_ = v_x_4066_;
v_isShared_4071_ = v_isSharedCheck_4076_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v_x_4066_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4076_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
}
else
{
lean_object* v___x_4077_; 
lean_dec_ref(v_x_4066_);
v___x_4077_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4078_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4081_, lean_object* v_handler_4082_, lean_object* v___f_4083_, lean_object* v_x_4084_){
_start:
{
if (lean_obj_tag(v_x_4084_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; 
v_a_4086_ = lean_ctor_get(v_x_4084_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v_x_4084_);
v___x_4087_ = lean_apply_3(v_onFailure_4081_, v_handler_4082_, v_a_4086_, lean_box(0));
v___x_4088_ = lean_unsigned_to_nat(0u);
v___x_4089_ = 0;
v___x_4090_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4088_, v___x_4089_, v___x_4087_, v___f_4083_);
return v___x_4090_;
}
else
{
lean_object* v___x_4091_; 
lean_dec_ref(v___f_4083_);
lean_dec(v_handler_4082_);
lean_dec_ref(v_onFailure_4081_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_x_4084_);
return v___x_4091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4092_, lean_object* v_handler_4093_, lean_object* v___f_4094_, lean_object* v_x_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4092_, v_handler_4093_, v___f_4094_, v_x_4095_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4098_, lean_object* v_socket_4099_, lean_object* v_____r_4100_){
_start:
{
lean_object* v_val_4103_; lean_object* v_close_4105_; lean_object* v___x_4106_; 
v_close_4105_ = lean_ctor_get(v_inst_4098_, 3);
lean_inc_ref(v_close_4105_);
lean_dec_ref(v_inst_4098_);
v___x_4106_ = lean_apply_2(v_close_4105_, v_socket_4099_, lean_box(0));
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set_tag(v___x_4109_, 1);
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
v_val_4103_ = v___x_4112_;
goto v___jp_4102_;
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_a_4115_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4106_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4106_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set_tag(v___x_4117_, 0);
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
v_val_4103_ = v___x_4120_;
goto v___jp_4102_;
}
}
}
v___jp_4102_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_val_4103_);
return v___x_4104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4123_, lean_object* v_socket_4124_, lean_object* v_____r_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4123_, v_socket_4124_, v_____r_4125_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4128_, lean_object* v_x_4129_){
_start:
{
if (lean_obj_tag(v_x_4129_) == 0)
{
lean_object* v___x_4131_; 
lean_dec_ref(v___f_4128_);
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v_x_4129_);
return v___x_4131_;
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4133_; 
v_a_4132_ = lean_ctor_get(v_x_4129_, 0);
lean_inc(v_a_4132_);
lean_dec_ref(v_x_4129_);
v___x_4133_ = lean_apply_2(v___f_4128_, v_a_4132_, lean_box(0));
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4134_, lean_object* v_x_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4134_, v_x_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4138_, lean_object* v_val_4139_, lean_object* v___f_4140_, lean_object* v___f_4141_, lean_object* v_x_4142_){
_start:
{
if (lean_obj_tag(v_x_4142_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v___f_4141_);
lean_dec_ref(v___f_4140_);
lean_dec(v_val_4139_);
lean_dec_ref(v_close_4138_);
v_a_4144_ = lean_ctor_get(v_x_4142_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_x_4142_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4146_ = v_x_4142_;
v_isShared_4147_ = v_isSharedCheck_4152_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v_x_4142_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4152_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
return v___x_4150_;
}
}
}
else
{
lean_object* v_a_4153_; uint8_t v___x_4154_; 
v_a_4153_ = lean_ctor_get(v_x_4142_, 0);
lean_inc(v_a_4153_);
lean_dec_ref(v_x_4142_);
v___x_4154_ = lean_unbox(v_a_4153_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; 
lean_dec_ref(v___f_4141_);
v___x_4155_ = lean_apply_2(v_close_4138_, v_val_4139_, lean_box(0));
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = lean_unbox(v_a_4153_);
lean_dec(v_a_4153_);
v___x_4158_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4156_, v___x_4157_, v___x_4155_, v___f_4140_);
return v___x_4158_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec(v_a_4153_);
lean_dec_ref(v___f_4140_);
lean_dec(v_val_4139_);
lean_dec_ref(v_close_4138_);
v___x_4159_ = lean_box(0);
v___x_4160_ = lean_apply_2(v___f_4141_, v___x_4159_, lean_box(0));
return v___x_4160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4161_, lean_object* v_val_4162_, lean_object* v___f_4163_, lean_object* v___f_4164_, lean_object* v_x_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4161_, v_val_4162_, v___f_4163_, v___f_4164_, v_x_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4168_, lean_object* v_responseBodyInstance_4169_, lean_object* v___f_4170_, lean_object* v___f_4171_, lean_object* v_____r_4172_){
_start:
{
if (lean_obj_tag(v_respStream_4168_) == 1)
{
lean_object* v_val_4174_; lean_object* v_close_4175_; lean_object* v_isClosed_4176_; lean_object* v___x_4177_; lean_object* v___f_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; 
v_val_4174_ = lean_ctor_get(v_respStream_4168_, 0);
lean_inc_n(v_val_4174_, 2);
lean_dec_ref(v_respStream_4168_);
v_close_4175_ = lean_ctor_get(v_responseBodyInstance_4169_, 1);
lean_inc_ref(v_close_4175_);
v_isClosed_4176_ = lean_ctor_get(v_responseBodyInstance_4169_, 2);
lean_inc_ref(v_isClosed_4176_);
lean_dec_ref(v_responseBodyInstance_4169_);
v___x_4177_ = lean_apply_2(v_isClosed_4176_, v_val_4174_, lean_box(0));
v___f_4178_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4178_, 0, v_close_4175_);
lean_closure_set(v___f_4178_, 1, v_val_4174_);
lean_closure_set(v___f_4178_, 2, v___f_4170_);
lean_closure_set(v___f_4178_, 3, v___f_4171_);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = 0;
v___x_4181_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4179_, v___x_4180_, v___x_4177_, v___f_4178_);
return v___x_4181_;
}
else
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v___f_4170_);
lean_dec_ref(v_responseBodyInstance_4169_);
lean_dec(v_respStream_4168_);
v___x_4182_ = lean_box(0);
v___x_4183_ = lean_apply_2(v___f_4171_, v___x_4182_, lean_box(0));
return v___x_4183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4184_, lean_object* v_responseBodyInstance_4185_, lean_object* v___f_4186_, lean_object* v___f_4187_, lean_object* v_____r_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4184_, v_responseBodyInstance_4185_, v___f_4186_, v___f_4187_, v_____r_4188_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4191_, lean_object* v___f_4192_, lean_object* v___f_4193_, lean_object* v_x_4194_){
_start:
{
if (lean_obj_tag(v_x_4194_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4204_; 
lean_dec_ref(v___f_4193_);
lean_dec_ref(v___f_4192_);
lean_dec_ref(v_requestStream_4191_);
v_a_4196_ = lean_ctor_get(v_x_4194_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_x_4194_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4198_ = v_x_4194_;
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v_x_4194_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
return v___x_4202_;
}
}
}
else
{
lean_object* v_a_4205_; uint8_t v___x_4206_; 
v_a_4205_ = lean_ctor_get(v_x_4194_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v_x_4194_);
v___x_4206_ = lean_unbox(v_a_4205_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; lean_object* v___x_4210_; 
lean_dec_ref(v___f_4193_);
v___x_4207_ = l_Std_Http_Body_Stream_close(v_requestStream_4191_);
v___x_4208_ = lean_unsigned_to_nat(0u);
v___x_4209_ = lean_unbox(v_a_4205_);
lean_dec(v_a_4205_);
v___x_4210_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4208_, v___x_4209_, v___x_4207_, v___f_4192_);
return v___x_4210_;
}
else
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_dec(v_a_4205_);
lean_dec_ref(v___f_4192_);
lean_dec_ref(v_requestStream_4191_);
v___x_4211_ = lean_box(0);
v___x_4212_ = lean_apply_2(v___f_4193_, v___x_4211_, lean_box(0));
return v___x_4212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4213_, lean_object* v___f_4214_, lean_object* v___f_4215_, lean_object* v_x_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4213_, v___f_4214_, v___f_4215_, v_x_4216_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4219_, lean_object* v_responseBodyInstance_4220_, lean_object* v___f_4221_, lean_object* v___f_4222_, lean_object* v_x_4223_){
_start:
{
if (lean_obj_tag(v_x_4223_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v___f_4222_);
lean_dec_ref(v___f_4221_);
lean_dec_ref(v_responseBodyInstance_4220_);
lean_dec_ref(v___f_4219_);
v_a_4225_ = lean_ctor_get(v_x_4223_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v_x_4223_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4227_ = v_x_4223_;
v_isShared_4228_ = v_isSharedCheck_4233_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v_x_4223_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4233_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
return v___x_4231_;
}
}
}
else
{
lean_object* v_a_4234_; lean_object* v_requestStream_4235_; lean_object* v_respStream_4236_; lean_object* v___x_4237_; lean_object* v___f_4238_; lean_object* v___f_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4955__overap_4242_; lean_object* v___x_4243_; lean_object* v___f_4244_; lean_object* v___f_4245_; lean_object* v___f_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; lean_object* v___x_4249_; 
v_a_4234_ = lean_ctor_get(v_x_4223_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v_x_4223_);
v_requestStream_4235_ = lean_ctor_get(v_a_4234_, 1);
lean_inc_ref_n(v_requestStream_4235_, 2);
v_respStream_4236_ = lean_ctor_get(v_a_4234_, 6);
lean_inc(v_respStream_4236_);
lean_dec(v_a_4234_);
v___x_4237_ = lean_obj_once(&l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4238_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3));
v___f_4239_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___x_4240_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8));
v___x_4241_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_4241_, 0, lean_box(0));
lean_closure_set(v___x_4241_, 1, lean_box(0));
lean_closure_set(v___x_4241_, 2, lean_box(0));
lean_closure_set(v___x_4241_, 3, v___x_4237_);
lean_closure_set(v___x_4241_, 4, lean_box(0));
lean_closure_set(v___x_4241_, 5, lean_box(0));
lean_closure_set(v___x_4241_, 6, v___x_4240_);
lean_closure_set(v___x_4241_, 7, v___f_4219_);
v___x_4955__overap_4242_ = l_Std_Mutex_atomically___redArg(v___x_4237_, v___f_4238_, v___f_4239_, v_requestStream_4235_, v___x_4241_);
v___x_4243_ = lean_apply_1(v___x_4955__overap_4242_, lean_box(0));
v___f_4244_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4244_, 0, v_respStream_4236_);
lean_closure_set(v___f_4244_, 1, v_responseBodyInstance_4220_);
lean_closure_set(v___f_4244_, 2, v___f_4221_);
lean_closure_set(v___f_4244_, 3, v___f_4222_);
lean_inc_ref(v___f_4244_);
v___f_4245_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4245_, 0, v___f_4244_);
v___f_4246_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4246_, 0, v_requestStream_4235_);
lean_closure_set(v___f_4246_, 1, v___f_4245_);
lean_closure_set(v___f_4246_, 2, v___f_4244_);
v___x_4247_ = lean_unsigned_to_nat(0u);
v___x_4248_ = 0;
v___x_4249_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4247_, v___x_4248_, v___x_4243_, v___f_4246_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4250_, lean_object* v_responseBodyInstance_4251_, lean_object* v___f_4252_, lean_object* v___f_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4250_, v_responseBodyInstance_4251_, v___f_4252_, v___f_4253_, v_x_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4257_, lean_object* v_responseBodyInstance_4258_, lean_object* v_handler_4259_, lean_object* v_config_4260_, lean_object* v___x_4261_, uint8_t v___x_4262_, lean_object* v___f_4263_, lean_object* v_x_4264_){
_start:
{
if (lean_obj_tag(v_x_4264_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4274_; 
lean_dec_ref(v___f_4263_);
lean_dec_ref(v___x_4261_);
lean_dec_ref(v_config_4260_);
lean_dec(v_handler_4259_);
lean_dec_ref(v_responseBodyInstance_4258_);
lean_dec_ref(v_h_4257_);
v_a_4266_ = lean_ctor_get(v_x_4264_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v_x_4264_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4268_ = v_x_4264_;
v_isShared_4269_ = v_isSharedCheck_4274_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v_x_4264_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4274_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4272_; 
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4271_);
return v___x_4272_;
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v_a_4275_ = lean_ctor_get(v_x_4264_, 0);
lean_inc(v_a_4275_);
lean_dec_ref(v_x_4264_);
v___x_4276_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4257_, v_responseBodyInstance_4258_, v_handler_4259_, v_config_4260_, v_a_4275_, v___x_4261_);
v___x_4277_ = lean_unsigned_to_nat(0u);
v___x_4278_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4277_, v___x_4262_, v___x_4276_, v___f_4263_);
return v___x_4278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4279_, lean_object* v_responseBodyInstance_4280_, lean_object* v_handler_4281_, lean_object* v_config_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v___f_4285_, lean_object* v_x_4286_, lean_object* v___y_4287_){
_start:
{
uint8_t v___x_5616__boxed_4288_; lean_object* v_res_4289_; 
v___x_5616__boxed_4288_ = lean_unbox(v___x_4284_);
v_res_4289_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4279_, v_responseBodyInstance_4280_, v_handler_4281_, v_config_4282_, v___x_4283_, v___x_5616__boxed_4288_, v___f_4285_, v_x_4286_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4290_, lean_object* v_h_4291_, lean_object* v_responseBodyInstance_4292_, lean_object* v_config_4293_, lean_object* v_handler_4294_, uint8_t v___x_4295_, lean_object* v___f_4296_, lean_object* v_x_4297_){
_start:
{
if (lean_obj_tag(v_x_4297_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v___f_4296_);
lean_dec(v_handler_4294_);
lean_dec_ref(v_config_4293_);
lean_dec_ref(v_responseBodyInstance_4292_);
lean_dec_ref(v_h_4291_);
lean_dec_ref(v_inst_4290_);
v_a_4299_ = lean_ctor_get(v_x_4297_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v_x_4297_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4301_ = v_x_4297_;
v_isShared_4302_ = v_isSharedCheck_4307_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v_x_4297_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4307_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4299_);
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
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_a_4308_ = lean_ctor_get(v_x_4297_, 0);
lean_inc(v_a_4308_);
lean_dec_ref(v_x_4297_);
v___x_4309_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4290_, v_h_4291_, v_responseBodyInstance_4292_, v_config_4293_, v_handler_4294_, v_a_4308_);
v___x_4310_ = lean_unsigned_to_nat(0u);
v___x_4311_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4310_, v___x_4295_, v___x_4309_, v___f_4296_);
return v___x_4311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4312_, lean_object* v_h_4313_, lean_object* v_responseBodyInstance_4314_, lean_object* v_config_4315_, lean_object* v_handler_4316_, lean_object* v___x_4317_, lean_object* v___f_4318_, lean_object* v_x_4319_, lean_object* v___y_4320_){
_start:
{
uint8_t v___x_5657__boxed_4321_; lean_object* v_res_4322_; 
v___x_5657__boxed_4321_ = lean_unbox(v___x_4317_);
v_res_4322_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4312_, v_h_4313_, v_responseBodyInstance_4314_, v_config_4315_, v_handler_4316_, v___x_5657__boxed_4321_, v___f_4318_, v_x_4319_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4323_, lean_object* v_socket_4324_, lean_object* v_connectionContext_4325_, lean_object* v_h_4326_, lean_object* v_responseBodyInstance_4327_, lean_object* v_handler_4328_, lean_object* v_config_4329_, lean_object* v___f_4330_, lean_object* v_inst_4331_, lean_object* v_x_4332_){
_start:
{
if (lean_obj_tag(v_x_4332_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v_inst_4331_);
lean_dec_ref(v___f_4330_);
lean_dec_ref(v_config_4329_);
lean_dec(v_handler_4328_);
lean_dec_ref(v_responseBodyInstance_4327_);
lean_dec_ref(v_h_4326_);
lean_dec_ref(v_connectionContext_4325_);
lean_dec(v_socket_4324_);
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
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4377_; 
v_a_4343_ = lean_ctor_get(v_x_4332_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v_x_4332_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4345_ = v_x_4332_;
v_isShared_4346_ = v_isSharedCheck_4377_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v_x_4332_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4377_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v_machine_4353_; lean_object* v_requestStream_4354_; lean_object* v_keepAliveTimeout_4355_; lean_object* v_currentTimeout_4356_; lean_object* v_headerTimeout_4357_; lean_object* v_response_4358_; lean_object* v_respStream_4359_; uint8_t v_requiresData_4360_; lean_object* v_expectData_4361_; uint8_t v_handlerDispatched_4362_; lean_object* v_pendingHead_4363_; 
v_machine_4353_ = lean_ctor_get(v_a_4343_, 0);
v_requestStream_4354_ = lean_ctor_get(v_a_4343_, 1);
v_keepAliveTimeout_4355_ = lean_ctor_get(v_a_4343_, 2);
v_currentTimeout_4356_ = lean_ctor_get(v_a_4343_, 3);
v_headerTimeout_4357_ = lean_ctor_get(v_a_4343_, 4);
v_response_4358_ = lean_ctor_get(v_a_4343_, 5);
v_respStream_4359_ = lean_ctor_get(v_a_4343_, 6);
v_requiresData_4360_ = lean_ctor_get_uint8(v_a_4343_, sizeof(void*)*9);
v_expectData_4361_ = lean_ctor_get(v_a_4343_, 7);
v_handlerDispatched_4362_ = lean_ctor_get_uint8(v_a_4343_, sizeof(void*)*9 + 1);
v_pendingHead_4363_ = lean_ctor_get(v_a_4343_, 8);
if (v_requiresData_4360_ == 0)
{
if (v_handlerDispatched_4362_ == 0)
{
if (lean_obj_tag(v_respStream_4359_) == 0)
{
lean_object* v_writer_4373_; uint8_t v_sentMessage_4374_; 
v_writer_4373_ = lean_ctor_get(v_machine_4353_, 1);
v_sentMessage_4374_ = lean_ctor_get_uint8(v_writer_4373_, sizeof(void*)*6);
if (v_sentMessage_4374_ == 0)
{
lean_object* v_reader_4375_; lean_object* v_state_4376_; 
v_reader_4375_ = lean_ctor_get(v_machine_4353_, 0);
v_state_4376_ = lean_ctor_get(v_reader_4375_, 0);
if (lean_obj_tag(v_state_4376_) == 2)
{
lean_inc(v_respStream_4359_);
lean_inc(v_pendingHead_4363_);
lean_inc(v_expectData_4361_);
lean_inc_ref(v_response_4358_);
lean_inc(v_headerTimeout_4357_);
lean_inc(v_currentTimeout_4356_);
lean_inc(v_keepAliveTimeout_4355_);
lean_inc_ref(v_requestStream_4354_);
lean_inc_ref(v_machine_4353_);
lean_del_object(v___x_4345_);
lean_dec(v_a_4343_);
goto v___jp_4364_;
}
else
{
lean_dec_ref(v_inst_4331_);
lean_dec_ref(v___f_4330_);
lean_dec_ref(v_config_4329_);
lean_dec(v_handler_4328_);
lean_dec_ref(v_responseBodyInstance_4327_);
lean_dec_ref(v_h_4326_);
lean_dec_ref(v_connectionContext_4325_);
lean_dec(v_socket_4324_);
goto v___jp_4347_;
}
}
else
{
lean_dec_ref(v_inst_4331_);
lean_dec_ref(v___f_4330_);
lean_dec_ref(v_config_4329_);
lean_dec(v_handler_4328_);
lean_dec_ref(v_responseBodyInstance_4327_);
lean_dec_ref(v_h_4326_);
lean_dec_ref(v_connectionContext_4325_);
lean_dec(v_socket_4324_);
goto v___jp_4347_;
}
}
else
{
lean_inc_ref(v_respStream_4359_);
lean_inc(v_pendingHead_4363_);
lean_inc(v_expectData_4361_);
lean_inc_ref(v_response_4358_);
lean_inc(v_headerTimeout_4357_);
lean_inc(v_currentTimeout_4356_);
lean_inc(v_keepAliveTimeout_4355_);
lean_inc_ref(v_requestStream_4354_);
lean_inc_ref(v_machine_4353_);
lean_del_object(v___x_4345_);
lean_dec(v_a_4343_);
goto v___jp_4364_;
}
}
else
{
lean_inc(v_pendingHead_4363_);
lean_inc(v_expectData_4361_);
lean_inc(v_respStream_4359_);
lean_inc_ref(v_response_4358_);
lean_inc(v_headerTimeout_4357_);
lean_inc(v_currentTimeout_4356_);
lean_inc(v_keepAliveTimeout_4355_);
lean_inc_ref(v_requestStream_4354_);
lean_inc_ref(v_machine_4353_);
lean_del_object(v___x_4345_);
lean_dec(v_a_4343_);
goto v___jp_4364_;
}
}
else
{
lean_inc(v_pendingHead_4363_);
lean_inc(v_expectData_4361_);
lean_inc(v_respStream_4359_);
lean_inc_ref(v_response_4358_);
lean_inc(v_headerTimeout_4357_);
lean_inc(v_currentTimeout_4356_);
lean_inc(v_keepAliveTimeout_4355_);
lean_inc_ref(v_requestStream_4354_);
lean_inc_ref(v_machine_4353_);
lean_del_object(v___x_4345_);
lean_dec(v_a_4343_);
goto v___jp_4364_;
}
v___jp_4347_:
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4348_, 0, v_a_4343_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4348_);
v___x_4350_ = v___x_4345_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
return v___x_4351_;
}
}
v___jp_4364_:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; lean_object* v___x_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4365_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4365_, 0, v_machine_4353_);
lean_ctor_set(v___x_4365_, 1, v_requestStream_4354_);
lean_ctor_set(v___x_4365_, 2, v_keepAliveTimeout_4355_);
lean_ctor_set(v___x_4365_, 3, v_currentTimeout_4356_);
lean_ctor_set(v___x_4365_, 4, v_headerTimeout_4357_);
lean_ctor_set(v___x_4365_, 5, v_response_4358_);
lean_ctor_set(v___x_4365_, 6, v_respStream_4359_);
lean_ctor_set(v___x_4365_, 7, v_expectData_4361_);
lean_ctor_set(v___x_4365_, 8, v_pendingHead_4363_);
lean_ctor_set_uint8(v___x_4365_, sizeof(void*)*9, v___x_4323_);
lean_ctor_set_uint8(v___x_4365_, sizeof(void*)*9 + 1, v_handlerDispatched_4362_);
lean_inc_ref(v___x_4365_);
v___x_4366_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4324_, v_connectionContext_4325_, v___x_4365_);
v___x_4367_ = lean_box(v___x_4323_);
lean_inc_ref(v_config_4329_);
lean_inc(v_handler_4328_);
lean_inc_ref(v_responseBodyInstance_4327_);
lean_inc_ref(v_h_4326_);
v___f_4368_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4368_, 0, v_h_4326_);
lean_closure_set(v___f_4368_, 1, v_responseBodyInstance_4327_);
lean_closure_set(v___f_4368_, 2, v_handler_4328_);
lean_closure_set(v___f_4368_, 3, v_config_4329_);
lean_closure_set(v___f_4368_, 4, v___x_4365_);
lean_closure_set(v___f_4368_, 5, v___x_4367_);
lean_closure_set(v___f_4368_, 6, v___f_4330_);
v___x_4369_ = lean_box(v___x_4323_);
v___f_4370_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4370_, 0, v_inst_4331_);
lean_closure_set(v___f_4370_, 1, v_h_4326_);
lean_closure_set(v___f_4370_, 2, v_responseBodyInstance_4327_);
lean_closure_set(v___f_4370_, 3, v_config_4329_);
lean_closure_set(v___f_4370_, 4, v_handler_4328_);
lean_closure_set(v___f_4370_, 5, v___x_4369_);
lean_closure_set(v___f_4370_, 6, v___f_4368_);
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4371_, v___x_4323_, v___x_4366_, v___f_4370_);
return v___x_4372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4378_, lean_object* v_socket_4379_, lean_object* v_connectionContext_4380_, lean_object* v_h_4381_, lean_object* v_responseBodyInstance_4382_, lean_object* v_handler_4383_, lean_object* v_config_4384_, lean_object* v___f_4385_, lean_object* v_inst_4386_, lean_object* v_x_4387_, lean_object* v___y_4388_){
_start:
{
uint8_t v___x_5697__boxed_4389_; lean_object* v_res_4390_; 
v___x_5697__boxed_4389_ = lean_unbox(v___x_4378_);
v_res_4390_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5697__boxed_4389_, v_socket_4379_, v_connectionContext_4380_, v_h_4381_, v_responseBodyInstance_4382_, v_handler_4383_, v_config_4384_, v___f_4385_, v_inst_4386_, v_x_4387_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4391_, lean_object* v_handler_4392_, lean_object* v_extensions_4393_, lean_object* v_connectionContext_4394_, uint8_t v___x_4395_, lean_object* v___f_4396_, lean_object* v_x_4397_){
_start:
{
if (lean_obj_tag(v_x_4397_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4407_; 
lean_dec_ref(v___f_4396_);
lean_dec_ref(v_connectionContext_4394_);
lean_dec(v_extensions_4393_);
lean_dec(v_handler_4392_);
lean_dec_ref(v_h_4391_);
v_a_4399_ = lean_ctor_get(v_x_4397_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_x_4397_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4401_ = v_x_4397_;
v_isShared_4402_ = v_isSharedCheck_4407_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v_x_4397_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4407_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; 
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4408_ = lean_ctor_get(v_x_4397_, 0);
lean_inc(v_a_4408_);
lean_dec_ref(v_x_4397_);
v___x_4409_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4391_, v_handler_4392_, v_extensions_4393_, v_connectionContext_4394_, v_a_4408_);
v___x_4410_ = lean_unsigned_to_nat(0u);
v___x_4411_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4410_, v___x_4395_, v___x_4409_, v___f_4396_);
return v___x_4411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4412_, lean_object* v_handler_4413_, lean_object* v_extensions_4414_, lean_object* v_connectionContext_4415_, lean_object* v___x_4416_, lean_object* v___f_4417_, lean_object* v_x_4418_, lean_object* v___y_4419_){
_start:
{
uint8_t v___x_5772__boxed_4420_; lean_object* v_res_4421_; 
v___x_5772__boxed_4420_ = lean_unbox(v___x_4416_);
v_res_4421_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4412_, v_handler_4413_, v_extensions_4414_, v_connectionContext_4415_, v___x_5772__boxed_4420_, v___f_4417_, v_x_4418_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4422_, lean_object* v_responseBodyInstance_4423_, lean_object* v_handler_4424_, lean_object* v_config_4425_, lean_object* v_connectionContext_4426_, lean_object* v_events_4427_, lean_object* v___x_4428_, uint8_t v___x_4429_, lean_object* v___f_4430_, lean_object* v_____r_4431_){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4433_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4422_, v_responseBodyInstance_4423_, v_handler_4424_, v_config_4425_, v_connectionContext_4426_, v_events_4427_, v___x_4428_);
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4434_, v___x_4429_, v___x_4433_, v___f_4430_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4436_, lean_object* v_responseBodyInstance_4437_, lean_object* v_handler_4438_, lean_object* v_config_4439_, lean_object* v_connectionContext_4440_, lean_object* v_events_4441_, lean_object* v___x_4442_, lean_object* v___x_4443_, lean_object* v___f_4444_, lean_object* v_____r_4445_, lean_object* v___y_4446_){
_start:
{
uint8_t v___x_5811__boxed_4447_; lean_object* v_res_4448_; 
v___x_5811__boxed_4447_ = lean_unbox(v___x_4443_);
v_res_4448_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4436_, v_responseBodyInstance_4437_, v_handler_4438_, v_config_4439_, v_connectionContext_4440_, v_events_4441_, v___x_4442_, v___x_5811__boxed_4447_, v___f_4444_, v_____r_4445_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4449_, lean_object* v___f_4450_, lean_object* v_x_4451_){
_start:
{
if (lean_obj_tag(v_x_4451_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4461_; 
lean_dec_ref(v___f_4450_);
lean_dec_ref(v___x_4449_);
v_a_4453_ = lean_ctor_get(v_x_4451_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_x_4451_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4455_ = v_x_4451_;
v_isShared_4456_ = v_isSharedCheck_4461_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v_x_4451_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4461_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4473_; 
v_a_4462_ = lean_ctor_get(v_x_4451_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_x_4451_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4464_ = v_x_4451_;
v_isShared_4465_ = v_isSharedCheck_4473_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v_x_4451_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4473_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
if (lean_obj_tag(v_a_4462_) == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec_ref(v___f_4450_);
v___x_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4449_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4466_);
v___x_4468_ = v___x_4464_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; 
v___x_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
return v___x_4469_;
}
}
else
{
lean_object* v_val_4471_; lean_object* v___x_4472_; 
lean_del_object(v___x_4464_);
lean_dec_ref(v___x_4449_);
v_val_4471_ = lean_ctor_get(v_a_4462_, 0);
lean_inc(v_val_4471_);
lean_dec_ref(v_a_4462_);
v___x_4472_ = lean_apply_2(v___f_4450_, v_val_4471_, lean_box(0));
return v___x_4472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4474_, lean_object* v___f_4475_, lean_object* v_x_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4474_, v___f_4475_, v_x_4476_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4479_, lean_object* v_responseBodyInstance_4480_, lean_object* v_handler_4481_, lean_object* v_config_4482_, lean_object* v_connectionContext_4483_, uint8_t v___x_4484_, lean_object* v___f_4485_, lean_object* v_inst_4486_, lean_object* v_socket_4487_, lean_object* v___f_4488_, lean_object* v___f_4489_, lean_object* v_x_4490_, lean_object* v_____s_4491_){
_start:
{
lean_object* v_machine_4493_; lean_object* v_reader_4494_; lean_object* v_requestStream_4495_; lean_object* v_keepAliveTimeout_4496_; lean_object* v_currentTimeout_4497_; lean_object* v_headerTimeout_4498_; lean_object* v_response_4499_; lean_object* v_respStream_4500_; uint8_t v_requiresData_4501_; lean_object* v_expectData_4502_; uint8_t v_handlerDispatched_4503_; lean_object* v_pendingHead_4504_; lean_object* v_writer_4505_; lean_object* v_state_4506_; uint8_t v___x_4507_; 
v_machine_4493_ = lean_ctor_get(v_____s_4491_, 0);
v_reader_4494_ = lean_ctor_get(v_machine_4493_, 0);
v_requestStream_4495_ = lean_ctor_get(v_____s_4491_, 1);
v_keepAliveTimeout_4496_ = lean_ctor_get(v_____s_4491_, 2);
v_currentTimeout_4497_ = lean_ctor_get(v_____s_4491_, 3);
v_headerTimeout_4498_ = lean_ctor_get(v_____s_4491_, 4);
v_response_4499_ = lean_ctor_get(v_____s_4491_, 5);
v_respStream_4500_ = lean_ctor_get(v_____s_4491_, 6);
v_requiresData_4501_ = lean_ctor_get_uint8(v_____s_4491_, sizeof(void*)*9);
v_expectData_4502_ = lean_ctor_get(v_____s_4491_, 7);
v_handlerDispatched_4503_ = lean_ctor_get_uint8(v_____s_4491_, sizeof(void*)*9 + 1);
v_pendingHead_4504_ = lean_ctor_get(v_____s_4491_, 8);
v_writer_4505_ = lean_ctor_get(v_machine_4493_, 1);
v_state_4506_ = lean_ctor_get(v_reader_4494_, 0);
v___x_4507_ = 0;
if (lean_obj_tag(v_state_4506_) == 6)
{
lean_object* v_state_4529_; 
v_state_4529_ = lean_ctor_get(v_writer_4505_, 2);
if (lean_obj_tag(v_state_4529_) == 7)
{
lean_object* v_outputData_4530_; lean_object* v_size_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v_outputData_4530_ = lean_ctor_get(v_writer_4505_, 1);
v_size_4531_ = lean_ctor_get(v_outputData_4530_, 1);
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = lean_nat_dec_eq(v_size_4531_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_inc(v_pendingHead_4504_);
lean_inc(v_expectData_4502_);
lean_inc(v_respStream_4500_);
lean_inc_ref(v_response_4499_);
lean_inc(v_headerTimeout_4498_);
lean_inc(v_currentTimeout_4497_);
lean_inc(v_keepAliveTimeout_4496_);
lean_inc_ref(v_requestStream_4495_);
lean_inc_ref(v_machine_4493_);
lean_dec_ref(v_____s_4491_);
goto v___jp_4508_;
}
else
{
if (v___x_4533_ == 0)
{
lean_inc(v_pendingHead_4504_);
lean_inc(v_expectData_4502_);
lean_inc(v_respStream_4500_);
lean_inc_ref(v_response_4499_);
lean_inc(v_headerTimeout_4498_);
lean_inc(v_currentTimeout_4497_);
lean_inc(v_keepAliveTimeout_4496_);
lean_inc_ref(v_requestStream_4495_);
lean_inc_ref(v_machine_4493_);
lean_dec_ref(v_____s_4491_);
goto v___jp_4508_;
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_dec_ref(v___f_4489_);
lean_dec_ref(v___f_4488_);
lean_dec(v_socket_4487_);
lean_dec_ref(v_inst_4486_);
lean_dec_ref(v___f_4485_);
lean_dec_ref(v_connectionContext_4483_);
lean_dec_ref(v_config_4482_);
lean_dec(v_handler_4481_);
lean_dec_ref(v_responseBodyInstance_4480_);
lean_dec_ref(v_h_4479_);
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v_____s_4491_);
v___x_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
}
else
{
lean_inc(v_pendingHead_4504_);
lean_inc(v_expectData_4502_);
lean_inc(v_respStream_4500_);
lean_inc_ref(v_response_4499_);
lean_inc(v_headerTimeout_4498_);
lean_inc(v_currentTimeout_4497_);
lean_inc(v_keepAliveTimeout_4496_);
lean_inc_ref(v_requestStream_4495_);
lean_inc_ref(v_machine_4493_);
lean_dec_ref(v_____s_4491_);
goto v___jp_4508_;
}
}
else
{
lean_inc(v_pendingHead_4504_);
lean_inc(v_expectData_4502_);
lean_inc(v_respStream_4500_);
lean_inc_ref(v_response_4499_);
lean_inc(v_headerTimeout_4498_);
lean_inc(v_currentTimeout_4497_);
lean_inc(v_keepAliveTimeout_4496_);
lean_inc_ref(v_requestStream_4495_);
lean_inc_ref(v_machine_4493_);
lean_dec_ref(v_____s_4491_);
goto v___jp_4508_;
}
v___jp_4508_:
{
lean_object* v___x_4509_; lean_object* v_snd_4510_; lean_object* v_output_4511_; lean_object* v_fst_4512_; lean_object* v_events_4513_; lean_object* v_data_4514_; lean_object* v_size_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___f_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4509_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4507_, v_machine_4493_);
v_snd_4510_ = lean_ctor_get(v___x_4509_, 1);
lean_inc(v_snd_4510_);
v_output_4511_ = lean_ctor_get(v_snd_4510_, 1);
lean_inc_ref(v_output_4511_);
v_fst_4512_ = lean_ctor_get(v___x_4509_, 0);
lean_inc(v_fst_4512_);
lean_dec_ref(v___x_4509_);
v_events_4513_ = lean_ctor_get(v_snd_4510_, 0);
lean_inc_ref_n(v_events_4513_, 2);
lean_dec(v_snd_4510_);
v_data_4514_ = lean_ctor_get(v_output_4511_, 0);
lean_inc_ref(v_data_4514_);
v_size_4515_ = lean_ctor_get(v_output_4511_, 1);
lean_inc(v_size_4515_);
lean_dec_ref(v_output_4511_);
v___x_4516_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4516_, 0, v_fst_4512_);
lean_ctor_set(v___x_4516_, 1, v_requestStream_4495_);
lean_ctor_set(v___x_4516_, 2, v_keepAliveTimeout_4496_);
lean_ctor_set(v___x_4516_, 3, v_currentTimeout_4497_);
lean_ctor_set(v___x_4516_, 4, v_headerTimeout_4498_);
lean_ctor_set(v___x_4516_, 5, v_response_4499_);
lean_ctor_set(v___x_4516_, 6, v_respStream_4500_);
lean_ctor_set(v___x_4516_, 7, v_expectData_4502_);
lean_ctor_set(v___x_4516_, 8, v_pendingHead_4504_);
lean_ctor_set_uint8(v___x_4516_, sizeof(void*)*9, v_requiresData_4501_);
lean_ctor_set_uint8(v___x_4516_, sizeof(void*)*9 + 1, v_handlerDispatched_4503_);
v___x_4517_ = lean_box(v___x_4484_);
lean_inc_ref(v___f_4485_);
lean_inc_ref(v___x_4516_);
lean_inc_ref(v_connectionContext_4483_);
lean_inc_ref(v_config_4482_);
lean_inc(v_handler_4481_);
lean_inc_ref(v_responseBodyInstance_4480_);
lean_inc_ref(v_h_4479_);
v___f_4518_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4518_, 0, v_h_4479_);
lean_closure_set(v___f_4518_, 1, v_responseBodyInstance_4480_);
lean_closure_set(v___f_4518_, 2, v_handler_4481_);
lean_closure_set(v___f_4518_, 3, v_config_4482_);
lean_closure_set(v___f_4518_, 4, v_connectionContext_4483_);
lean_closure_set(v___f_4518_, 5, v_events_4513_);
lean_closure_set(v___f_4518_, 6, v___x_4516_);
lean_closure_set(v___f_4518_, 7, v___x_4517_);
lean_closure_set(v___f_4518_, 8, v___f_4485_);
v___x_4519_ = lean_unsigned_to_nat(0u);
v___x_4520_ = lean_nat_dec_lt(v___x_4519_, v_size_4515_);
lean_dec(v_size_4515_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_dec_ref(v___f_4518_);
lean_dec_ref(v_data_4514_);
lean_dec_ref(v___f_4489_);
lean_dec_ref(v___f_4488_);
lean_dec(v_socket_4487_);
lean_dec_ref(v_inst_4486_);
v___x_4521_ = lean_box(0);
v___x_4522_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4479_, v_responseBodyInstance_4480_, v_handler_4481_, v_config_4482_, v_connectionContext_4483_, v_events_4513_, v___x_4516_, v___x_4484_, v___f_4485_, v___x_4521_);
return v___x_4522_;
}
else
{
lean_object* v_sendAll_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___f_4527_; lean_object* v___x_4528_; 
lean_dec_ref(v_events_4513_);
lean_dec_ref(v___f_4485_);
lean_dec_ref(v_connectionContext_4483_);
lean_dec_ref(v_config_4482_);
lean_dec(v_handler_4481_);
lean_dec_ref(v_responseBodyInstance_4480_);
lean_dec_ref(v_h_4479_);
v_sendAll_4523_ = lean_ctor_get(v_inst_4486_, 1);
lean_inc_ref(v_sendAll_4523_);
lean_dec_ref(v_inst_4486_);
v___x_4524_ = lean_apply_3(v_sendAll_4523_, v_socket_4487_, v_data_4514_, lean_box(0));
v___x_4525_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4519_, v___x_4484_, v___x_4524_, v___f_4488_);
v___x_4526_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4519_, v___x_4484_, v___x_4525_, v___f_4489_);
v___f_4527_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4527_, 0, v___x_4516_);
lean_closure_set(v___f_4527_, 1, v___f_4518_);
v___x_4528_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4519_, v___x_4484_, v___x_4526_, v___f_4527_);
return v___x_4528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4537_, lean_object* v_responseBodyInstance_4538_, lean_object* v_handler_4539_, lean_object* v_config_4540_, lean_object* v_connectionContext_4541_, lean_object* v___x_4542_, lean_object* v___f_4543_, lean_object* v_inst_4544_, lean_object* v_socket_4545_, lean_object* v___f_4546_, lean_object* v___f_4547_, lean_object* v_x_4548_, lean_object* v_____s_4549_, lean_object* v___y_4550_){
_start:
{
uint8_t v___x_5885__boxed_4551_; lean_object* v_res_4552_; 
v___x_5885__boxed_4551_ = lean_unbox(v___x_4542_);
v_res_4552_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4537_, v_responseBodyInstance_4538_, v_handler_4539_, v_config_4540_, v_connectionContext_4541_, v___x_5885__boxed_4551_, v___f_4543_, v_inst_4544_, v_socket_4545_, v___f_4546_, v___f_4547_, v_x_4548_, v_____s_4549_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4553_, lean_object* v_x_4554_){
_start:
{
if (lean_obj_tag(v_x_4554_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4564_; 
v_a_4556_ = lean_ctor_get(v_x_4554_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v_x_4554_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4558_ = v_x_4554_;
v_isShared_4559_ = v_isSharedCheck_4564_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v_x_4554_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4564_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
return v___x_4562_;
}
}
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
lean_dec_ref(v_x_4554_);
v___x_4565_ = l_IO_Promise_result_x21___redArg(v_a_4553_);
v___x_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4567_, lean_object* v_x_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4567_, v_x_4568_);
lean_dec(v_a_4567_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4571_, lean_object* v___x_4572_, lean_object* v___x_4573_, uint8_t v___x_4574_, lean_object* v_x_4575_){
_start:
{
if (lean_obj_tag(v_x_4575_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4585_; 
lean_dec_ref(v___x_4573_);
lean_dec(v___x_4572_);
lean_dec_ref(v___f_4571_);
v_a_4577_ = lean_ctor_get(v_x_4575_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_x_4575_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4579_ = v_x_4575_;
v_isShared_4580_ = v_isSharedCheck_4585_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v_x_4575_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4585_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
return v___x_4583_;
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4597_; 
v_a_4586_ = lean_ctor_get(v_x_4575_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v_x_4575_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4588_ = v_x_4575_;
v_isShared_4589_ = v_isSharedCheck_4597_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v_x_4575_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4597_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4590_; lean_object* v___f_4591_; lean_object* v___x_4593_; 
lean_inc(v_a_4586_);
lean_inc(v___x_4572_);
v___x_4590_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4571_, v___x_4572_, v_a_4586_, v___x_4573_);
v___f_4591_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4591_, 0, v_a_4586_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4590_);
v___x_4593_ = v___x_4588_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4590_);
v___x_4593_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4593_);
v___x_4595_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4572_, v___x_4574_, v___x_4594_, v___f_4591_);
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4598_, lean_object* v___x_4599_, lean_object* v___x_4600_, lean_object* v___x_4601_, lean_object* v_x_4602_, lean_object* v___y_4603_){
_start:
{
uint8_t v___x_5988__boxed_4604_; lean_object* v_res_4605_; 
v___x_5988__boxed_4604_ = lean_unbox(v___x_4601_);
v_res_4605_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4598_, v___x_4599_, v___x_4600_, v___x_5988__boxed_4604_, v_x_4602_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4606_, lean_object* v_machine_4607_, lean_object* v_a_4608_, lean_object* v___x_4609_, lean_object* v_socket_4610_, lean_object* v_connectionContext_4611_, lean_object* v_h_4612_, lean_object* v_responseBodyInstance_4613_, lean_object* v_handler_4614_, lean_object* v___f_4615_, lean_object* v_inst_4616_, lean_object* v_extensions_4617_, lean_object* v___f_4618_, lean_object* v___f_4619_, lean_object* v___f_4620_, lean_object* v_x_4621_){
_start:
{
if (lean_obj_tag(v_x_4621_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4631_; 
lean_dec_ref(v___f_4620_);
lean_dec_ref(v___f_4619_);
lean_dec_ref(v___f_4618_);
lean_dec(v_extensions_4617_);
lean_dec_ref(v_inst_4616_);
lean_dec_ref(v___f_4615_);
lean_dec(v_handler_4614_);
lean_dec_ref(v_responseBodyInstance_4613_);
lean_dec_ref(v_h_4612_);
lean_dec_ref(v_connectionContext_4611_);
lean_dec(v_socket_4610_);
lean_dec(v___x_4609_);
lean_dec_ref(v_a_4608_);
lean_dec_ref(v_machine_4607_);
lean_dec_ref(v_config_4606_);
v_a_4623_ = lean_ctor_get(v_x_4621_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v_x_4621_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4625_ = v_x_4621_;
v_isShared_4626_ = v_isSharedCheck_4631_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v_x_4621_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4631_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
return v___x_4629_;
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4657_; 
v_a_4632_ = lean_ctor_get(v_x_4621_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_x_4621_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4634_ = v_x_4621_;
v_isShared_4635_ = v_isSharedCheck_4657_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v_x_4621_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4657_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v_keepAliveTimeout_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___f_4643_; lean_object* v___x_4644_; lean_object* v___f_4645_; lean_object* v___x_4646_; lean_object* v___f_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___f_4650_; lean_object* v___x_4652_; 
v_keepAliveTimeout_4636_ = lean_ctor_get(v_config_4606_, 5);
lean_inc_n(v_keepAliveTimeout_4636_, 2);
v___x_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_keepAliveTimeout_4636_);
v___x_4638_ = lean_box(0);
v___x_4639_ = 0;
v___x_4640_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4640_, 0, v_machine_4607_);
lean_ctor_set(v___x_4640_, 1, v_a_4608_);
lean_ctor_set(v___x_4640_, 2, v___x_4637_);
lean_ctor_set(v___x_4640_, 3, v_keepAliveTimeout_4636_);
lean_ctor_set(v___x_4640_, 4, v___x_4638_);
lean_ctor_set(v___x_4640_, 5, v_a_4632_);
lean_ctor_set(v___x_4640_, 6, v___x_4638_);
lean_ctor_set(v___x_4640_, 7, v___x_4609_);
lean_ctor_set(v___x_4640_, 8, v___x_4638_);
lean_ctor_set_uint8(v___x_4640_, sizeof(void*)*9, v___x_4639_);
lean_ctor_set_uint8(v___x_4640_, sizeof(void*)*9 + 1, v___x_4639_);
v___x_4641_ = lean_io_promise_new();
v___x_4642_ = lean_box(v___x_4639_);
lean_inc_ref(v_inst_4616_);
lean_inc_ref(v_config_4606_);
lean_inc_n(v_handler_4614_, 2);
lean_inc_ref(v_responseBodyInstance_4613_);
lean_inc_ref_n(v_h_4612_, 2);
lean_inc_ref_n(v_connectionContext_4611_, 2);
lean_inc(v_socket_4610_);
v___f_4643_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4643_, 0, v___x_4642_);
lean_closure_set(v___f_4643_, 1, v_socket_4610_);
lean_closure_set(v___f_4643_, 2, v_connectionContext_4611_);
lean_closure_set(v___f_4643_, 3, v_h_4612_);
lean_closure_set(v___f_4643_, 4, v_responseBodyInstance_4613_);
lean_closure_set(v___f_4643_, 5, v_handler_4614_);
lean_closure_set(v___f_4643_, 6, v_config_4606_);
lean_closure_set(v___f_4643_, 7, v___f_4615_);
lean_closure_set(v___f_4643_, 8, v_inst_4616_);
v___x_4644_ = lean_box(v___x_4639_);
v___f_4645_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4645_, 0, v_h_4612_);
lean_closure_set(v___f_4645_, 1, v_handler_4614_);
lean_closure_set(v___f_4645_, 2, v_extensions_4617_);
lean_closure_set(v___f_4645_, 3, v_connectionContext_4611_);
lean_closure_set(v___f_4645_, 4, v___x_4644_);
lean_closure_set(v___f_4645_, 5, v___f_4643_);
v___x_4646_ = lean_box(v___x_4639_);
v___f_4647_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4647_, 0, v_h_4612_);
lean_closure_set(v___f_4647_, 1, v_responseBodyInstance_4613_);
lean_closure_set(v___f_4647_, 2, v_handler_4614_);
lean_closure_set(v___f_4647_, 3, v_config_4606_);
lean_closure_set(v___f_4647_, 4, v_connectionContext_4611_);
lean_closure_set(v___f_4647_, 5, v___x_4646_);
lean_closure_set(v___f_4647_, 6, v___f_4645_);
lean_closure_set(v___f_4647_, 7, v_inst_4616_);
lean_closure_set(v___f_4647_, 8, v_socket_4610_);
lean_closure_set(v___f_4647_, 9, v___f_4618_);
lean_closure_set(v___f_4647_, 10, v___f_4619_);
v___x_4648_ = lean_unsigned_to_nat(0u);
v___x_4649_ = lean_box(v___x_4639_);
v___f_4650_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4650_, 0, v___f_4647_);
lean_closure_set(v___f_4650_, 1, v___x_4648_);
lean_closure_set(v___f_4650_, 2, v___x_4640_);
lean_closure_set(v___f_4650_, 3, v___x_4649_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 0, v___x_4641_);
v___x_4652_ = v___x_4634_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4641_);
v___x_4652_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
v___x_4654_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4648_, v___x_4639_, v___x_4653_, v___f_4650_);
v___x_4655_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4648_, v___x_4639_, v___x_4654_, v___f_4620_);
return v___x_4655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4658_ = _args[0];
lean_object* v_machine_4659_ = _args[1];
lean_object* v_a_4660_ = _args[2];
lean_object* v___x_4661_ = _args[3];
lean_object* v_socket_4662_ = _args[4];
lean_object* v_connectionContext_4663_ = _args[5];
lean_object* v_h_4664_ = _args[6];
lean_object* v_responseBodyInstance_4665_ = _args[7];
lean_object* v_handler_4666_ = _args[8];
lean_object* v___f_4667_ = _args[9];
lean_object* v_inst_4668_ = _args[10];
lean_object* v_extensions_4669_ = _args[11];
lean_object* v___f_4670_ = _args[12];
lean_object* v___f_4671_ = _args[13];
lean_object* v___f_4672_ = _args[14];
lean_object* v_x_4673_ = _args[15];
lean_object* v___y_4674_ = _args[16];
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4658_, v_machine_4659_, v_a_4660_, v___x_4661_, v_socket_4662_, v_connectionContext_4663_, v_h_4664_, v_responseBodyInstance_4665_, v_handler_4666_, v___f_4667_, v_inst_4668_, v_extensions_4669_, v___f_4670_, v___f_4671_, v___f_4672_, v_x_4673_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4676_, lean_object* v_machine_4677_, lean_object* v_socket_4678_, lean_object* v_connectionContext_4679_, lean_object* v_h_4680_, lean_object* v_responseBodyInstance_4681_, lean_object* v_handler_4682_, lean_object* v___f_4683_, lean_object* v_inst_4684_, lean_object* v_extensions_4685_, lean_object* v___f_4686_, lean_object* v___f_4687_, lean_object* v___f_4688_, lean_object* v_x_4689_){
_start:
{
if (lean_obj_tag(v_x_4689_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4699_; 
lean_dec_ref(v___f_4688_);
lean_dec_ref(v___f_4687_);
lean_dec_ref(v___f_4686_);
lean_dec(v_extensions_4685_);
lean_dec_ref(v_inst_4684_);
lean_dec_ref(v___f_4683_);
lean_dec(v_handler_4682_);
lean_dec_ref(v_responseBodyInstance_4681_);
lean_dec_ref(v_h_4680_);
lean_dec_ref(v_connectionContext_4679_);
lean_dec(v_socket_4678_);
lean_dec_ref(v_machine_4677_);
lean_dec_ref(v_config_4676_);
v_a_4691_ = lean_ctor_get(v_x_4689_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_x_4689_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4693_ = v_x_4689_;
v_isShared_4694_ = v_isSharedCheck_4699_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v_x_4689_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4699_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
return v___x_4697_;
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4714_; 
v_a_4700_ = lean_ctor_get(v_x_4689_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v_x_4689_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4702_ = v_x_4689_;
v_isShared_4703_ = v_isSharedCheck_4714_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v_x_4689_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4714_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___f_4706_; lean_object* v___x_4708_; 
v___x_4704_ = lean_box(0);
v___x_4705_ = l_Std_CloseableChannel_new___redArg(v___x_4704_);
v___f_4706_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4706_, 0, v_config_4676_);
lean_closure_set(v___f_4706_, 1, v_machine_4677_);
lean_closure_set(v___f_4706_, 2, v_a_4700_);
lean_closure_set(v___f_4706_, 3, v___x_4704_);
lean_closure_set(v___f_4706_, 4, v_socket_4678_);
lean_closure_set(v___f_4706_, 5, v_connectionContext_4679_);
lean_closure_set(v___f_4706_, 6, v_h_4680_);
lean_closure_set(v___f_4706_, 7, v_responseBodyInstance_4681_);
lean_closure_set(v___f_4706_, 8, v_handler_4682_);
lean_closure_set(v___f_4706_, 9, v___f_4683_);
lean_closure_set(v___f_4706_, 10, v_inst_4684_);
lean_closure_set(v___f_4706_, 11, v_extensions_4685_);
lean_closure_set(v___f_4706_, 12, v___f_4686_);
lean_closure_set(v___f_4706_, 13, v___f_4687_);
lean_closure_set(v___f_4706_, 14, v___f_4688_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4705_);
v___x_4708_ = v___x_4702_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4705_);
v___x_4708_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; lean_object* v___x_4712_; 
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
v___x_4710_ = lean_unsigned_to_nat(0u);
v___x_4711_ = 0;
v___x_4712_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4710_, v___x_4711_, v___x_4709_, v___f_4706_);
return v___x_4712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4715_, lean_object* v_machine_4716_, lean_object* v_socket_4717_, lean_object* v_connectionContext_4718_, lean_object* v_h_4719_, lean_object* v_responseBodyInstance_4720_, lean_object* v_handler_4721_, lean_object* v___f_4722_, lean_object* v_inst_4723_, lean_object* v_extensions_4724_, lean_object* v___f_4725_, lean_object* v___f_4726_, lean_object* v___f_4727_, lean_object* v_x_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4715_, v_machine_4716_, v_socket_4717_, v_connectionContext_4718_, v_h_4719_, v_responseBodyInstance_4720_, v_handler_4721_, v___f_4722_, v_inst_4723_, v_extensions_4724_, v___f_4725_, v___f_4726_, v___f_4727_, v_x_4728_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4734_, lean_object* v_h_4735_, lean_object* v_connection_4736_, lean_object* v_config_4737_, lean_object* v_connectionContext_4738_, lean_object* v_handler_4739_){
_start:
{
lean_object* v_responseBodyInstance_4741_; lean_object* v_onFailure_4742_; lean_object* v___x_4743_; lean_object* v_socket_4744_; lean_object* v_machine_4745_; lean_object* v_extensions_4746_; lean_object* v___f_4747_; lean_object* v___f_4748_; lean_object* v___f_4749_; lean_object* v___f_4750_; lean_object* v___f_4751_; lean_object* v___f_4752_; lean_object* v___f_4753_; lean_object* v___f_4754_; lean_object* v___f_4755_; lean_object* v___x_4756_; uint8_t v___x_4757_; lean_object* v___x_4758_; 
v_responseBodyInstance_4741_ = lean_ctor_get(v_h_4735_, 0);
lean_inc_ref_n(v_responseBodyInstance_4741_, 2);
v_onFailure_4742_ = lean_ctor_get(v_h_4735_, 2);
v___x_4743_ = l_Std_Http_Body_mkStream();
v_socket_4744_ = lean_ctor_get(v_connection_4736_, 0);
lean_inc_n(v_socket_4744_, 2);
v_machine_4745_ = lean_ctor_get(v_connection_4736_, 1);
lean_inc_ref(v_machine_4745_);
v_extensions_4746_ = lean_ctor_get(v_connection_4736_, 2);
lean_inc(v_extensions_4746_);
lean_dec_ref(v_connection_4736_);
v___f_4747_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4748_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4749_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4750_ = ((lean_object*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4739_);
lean_inc_ref(v_onFailure_4742_);
v___f_4751_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4751_, 0, v_onFailure_4742_);
lean_closure_set(v___f_4751_, 1, v_handler_4739_);
lean_closure_set(v___f_4751_, 2, v___f_4750_);
lean_inc_ref(v_inst_4734_);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4752_, 0, v_inst_4734_);
lean_closure_set(v___f_4752_, 1, v_socket_4744_);
lean_inc_ref(v___f_4752_);
v___f_4753_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4753_, 0, v___f_4752_);
v___f_4754_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4754_, 0, v___f_4747_);
lean_closure_set(v___f_4754_, 1, v_responseBodyInstance_4741_);
lean_closure_set(v___f_4754_, 2, v___f_4753_);
lean_closure_set(v___f_4754_, 3, v___f_4752_);
v___f_4755_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4755_, 0, v_config_4737_);
lean_closure_set(v___f_4755_, 1, v_machine_4745_);
lean_closure_set(v___f_4755_, 2, v_socket_4744_);
lean_closure_set(v___f_4755_, 3, v_connectionContext_4738_);
lean_closure_set(v___f_4755_, 4, v_h_4735_);
lean_closure_set(v___f_4755_, 5, v_responseBodyInstance_4741_);
lean_closure_set(v___f_4755_, 6, v_handler_4739_);
lean_closure_set(v___f_4755_, 7, v___f_4748_);
lean_closure_set(v___f_4755_, 8, v_inst_4734_);
lean_closure_set(v___f_4755_, 9, v_extensions_4746_);
lean_closure_set(v___f_4755_, 10, v___f_4749_);
lean_closure_set(v___f_4755_, 11, v___f_4751_);
lean_closure_set(v___f_4755_, 12, v___f_4754_);
v___x_4756_ = lean_unsigned_to_nat(0u);
v___x_4757_ = 0;
v___x_4758_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4756_, v___x_4757_, v___x_4743_, v___f_4755_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4759_, lean_object* v_h_4760_, lean_object* v_connection_4761_, lean_object* v_config_4762_, lean_object* v_connectionContext_4763_, lean_object* v_handler_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4759_, v_h_4760_, v_connection_4761_, v_config_4762_, v_connectionContext_4763_, v_handler_4764_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4767_, lean_object* v_00_u03c3_4768_, lean_object* v_inst_4769_, lean_object* v_h_4770_, lean_object* v_connection_4771_, lean_object* v_config_4772_, lean_object* v_connectionContext_4773_, lean_object* v_handler_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4769_, v_h_4770_, v_connection_4771_, v_config_4772_, v_connectionContext_4773_, v_handler_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_00_u03c3_4778_, lean_object* v_inst_4779_, lean_object* v_h_4780_, lean_object* v_connection_4781_, lean_object* v_config_4782_, lean_object* v_connectionContext_4783_, lean_object* v_handler_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4777_, v_00_u03c3_4778_, v_inst_4779_, v_h_4780_, v_connection_4781_, v_config_4782_, v_connectionContext_4783_, v_handler_4784_);
return v_res_4786_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = 0;
v___x_4788_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4787_);
return v___x_4788_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4789_ = lean_unsigned_to_nat(4096u);
v___x_4790_ = lean_mk_empty_byte_array(v___x_4789_);
return v___x_4790_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4792_ = l_ByteArray_mkIterator(v___x_4791_);
return v___x_4792_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4793_ = 0;
v___x_4794_ = lean_unsigned_to_nat(0u);
v___x_4795_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4796_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4797_ = lean_box(0);
v___x_4798_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
lean_ctor_set(v___x_4798_, 1, v___x_4796_);
lean_ctor_set(v___x_4798_, 2, v___x_4795_);
lean_ctor_set(v___x_4798_, 3, v___x_4794_);
lean_ctor_set(v___x_4798_, 4, v___x_4794_);
lean_ctor_set(v___x_4798_, 5, v___x_4794_);
lean_ctor_set_uint8(v___x_4798_, sizeof(void*)*6, v___x_4793_);
return v___x_4798_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4806_; lean_object* v___x_4807_; 
v___x_4806_ = 1;
v___x_4807_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4806_);
return v___x_4807_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4808_; uint8_t v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4808_ = lean_unsigned_to_nat(0u);
v___x_4809_ = 0;
v___x_4810_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4811_ = lean_box(0);
v___x_4812_ = lean_box(0);
v___x_4813_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4814_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4815_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
lean_ctor_set(v___x_4815_, 1, v___x_4813_);
lean_ctor_set(v___x_4815_, 2, v___x_4812_);
lean_ctor_set(v___x_4815_, 3, v___x_4811_);
lean_ctor_set(v___x_4815_, 4, v___x_4810_);
lean_ctor_set(v___x_4815_, 5, v___x_4808_);
lean_ctor_set_uint8(v___x_4815_, sizeof(void*)*6, v___x_4809_);
lean_ctor_set_uint8(v___x_4815_, sizeof(void*)*6 + 1, v___x_4809_);
lean_ctor_set_uint8(v___x_4815_, sizeof(void*)*6 + 2, v___x_4809_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4816_, lean_object* v_client_4817_, lean_object* v_extensions_4818_, lean_object* v_inst_4819_, lean_object* v_inst_4820_, lean_object* v_handler_4821_, lean_object* v_x_4822_){
_start:
{
if (lean_obj_tag(v_x_4822_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4832_; 
lean_dec(v_handler_4821_);
lean_dec_ref(v_inst_4820_);
lean_dec_ref(v_inst_4819_);
lean_dec(v_extensions_4818_);
lean_dec(v_client_4817_);
lean_dec_ref(v_config_4816_);
v_a_4824_ = lean_ctor_get(v_x_4822_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v_x_4822_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4826_ = v_x_4822_;
v_isShared_4827_ = v_isSharedCheck_4832_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v_x_4822_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4832_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4829_);
return v___x_4830_;
}
}
}
else
{
lean_object* v_a_4833_; uint8_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; uint8_t v_enableKeepAlive_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v_a_4833_ = lean_ctor_get(v_x_4822_, 0);
lean_inc(v_a_4833_);
lean_dec_ref(v_x_4822_);
v___x_4834_ = 0;
v___x_4835_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4836_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4837_ = lean_box(0);
v___x_4838_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4839_ = l_Std_Http_Config_toH1Config(v_config_4816_);
v_enableKeepAlive_4840_ = lean_ctor_get_uint8(v___x_4839_, sizeof(void*)*18);
v___x_4841_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4841_, 0, v___x_4835_);
lean_ctor_set(v___x_4841_, 1, v___x_4838_);
lean_ctor_set(v___x_4841_, 2, v___x_4839_);
lean_ctor_set(v___x_4841_, 3, v___x_4836_);
lean_ctor_set(v___x_4841_, 4, v___x_4837_);
lean_ctor_set(v___x_4841_, 5, v___x_4837_);
lean_ctor_set_uint8(v___x_4841_, sizeof(void*)*6, v_enableKeepAlive_4840_);
lean_ctor_set_uint8(v___x_4841_, sizeof(void*)*6 + 1, v___x_4834_);
lean_ctor_set_uint8(v___x_4841_, sizeof(void*)*6 + 2, v___x_4834_);
v___x_4842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4842_, 0, v_client_4817_);
lean_ctor_set(v___x_4842_, 1, v___x_4841_);
lean_ctor_set(v___x_4842_, 2, v_extensions_4818_);
v___x_4843_ = l___private_Std_Internal_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4819_, v_inst_4820_, v___x_4842_, v_config_4816_, v_a_4833_, v_handler_4821_);
return v___x_4843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4844_, lean_object* v_client_4845_, lean_object* v_extensions_4846_, lean_object* v_inst_4847_, lean_object* v_inst_4848_, lean_object* v_handler_4849_, lean_object* v_x_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4844_, v_client_4845_, v_extensions_4846_, v_inst_4847_, v_inst_4848_, v_handler_4849_, v_x_4850_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4853_, lean_object* v_inst_4854_, lean_object* v_client_4855_, lean_object* v_handler_4856_, lean_object* v_config_4857_, lean_object* v_extensions_4858_, lean_object* v_a_4859_){
_start:
{
lean_object* v___f_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; lean_object* v___x_4866_; 
v___f_4861_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4861_, 0, v_config_4857_);
lean_closure_set(v___f_4861_, 1, v_client_4855_);
lean_closure_set(v___f_4861_, 2, v_extensions_4858_);
lean_closure_set(v___f_4861_, 3, v_inst_4853_);
lean_closure_set(v___f_4861_, 4, v_inst_4854_);
lean_closure_set(v___f_4861_, 5, v_handler_4856_);
lean_inc_ref(v_a_4859_);
v___x_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4862_, 0, v_a_4859_);
v___x_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4862_);
v___x_4864_ = lean_unsigned_to_nat(0u);
v___x_4865_ = 0;
v___x_4866_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4864_, v___x_4865_, v___x_4863_, v___f_4861_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4867_, lean_object* v_inst_4868_, lean_object* v_client_4869_, lean_object* v_handler_4870_, lean_object* v_config_4871_, lean_object* v_extensions_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4867_, v_inst_4868_, v_client_4869_, v_handler_4870_, v_config_4871_, v_extensions_4872_, v_a_4873_);
lean_dec_ref(v_a_4873_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4876_, lean_object* v_00_u03c3_4877_, lean_object* v_inst_4878_, lean_object* v_inst_4879_, lean_object* v_client_4880_, lean_object* v_handler_4881_, lean_object* v_config_4882_, lean_object* v_extensions_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4878_, v_inst_4879_, v_client_4880_, v_handler_4881_, v_config_4882_, v_extensions_4883_, v_a_4884_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4887_, lean_object* v_00_u03c3_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_client_4891_, lean_object* v_handler_4892_, lean_object* v_config_4893_, lean_object* v_extensions_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Std_Http_Server_serveConnection(v_t_4887_, v_00_u03c3_4888_, v_inst_4889_, v_inst_4890_, v_client_4891_, v_handler_4892_, v_config_4893_, v_extensions_4894_, v_a_4895_);
lean_dec_ref(v_a_4895_);
return v_res_4897_;
}
}
lean_object* runtime_initialize_Std_Internal_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_ContextAsync(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Transport(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Server_Handler(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Async_TCP(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_ContextAsync(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Transport(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Protocol_H1(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Server_Config(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Server_Handler(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Server_Connection(builtin);
}
#ifdef __cplusplus
}
#endif
