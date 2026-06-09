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
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v___x_959_, lean_object* v_entries_960_, lean_object* v_indexes_961_, lean_object* v_status_962_, uint8_t v_version_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_status_962_);
lean_dec_ref(v_indexes_961_);
lean_dec_ref(v_entries_960_);
v_a_966_ = lean_ctor_get(v_x_964_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_974_ == 0)
{
v___x_968_ = v_x_964_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v_x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_973_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_992_; 
v_a_975_ = lean_ctor_get(v_x_964_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_992_ == 0)
{
v___x_977_ = v_x_964_;
v_isShared_978_ = v_isSharedCheck_992_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v_x_964_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_992_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_i_982_; lean_object* v___x_983_; lean_object* v_entries_984_; lean_object* v_indexes_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_979_ = l_Std_Http_Header_Name_date;
v___x_980_ = l_Std_Time_DateTime_toRFC822String(v___x_959_, v_a_975_);
v___x_981_ = l_Std_Http_Header_Value_ofString_x21(v___x_980_);
v_i_982_ = lean_array_get_size(v_entries_960_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_979_);
lean_ctor_set(v___x_983_, 1, v___x_981_);
v_entries_984_ = lean_array_push(v_entries_960_, v___x_983_);
v_indexes_985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_982_, v_indexes_961_, v___x_979_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_entries_984_);
lean_ctor_set(v___x_986_, 1, v_indexes_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_987_, 0, v_status_962_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*2, v_version_963_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_987_);
v___x_989_ = v___x_977_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v___x_993_, lean_object* v_entries_994_, lean_object* v_indexes_995_, lean_object* v_status_996_, lean_object* v_version_997_, lean_object* v_x_998_, lean_object* v___y_999_){
_start:
{
uint8_t v_version_boxed_1000_; lean_object* v_res_1001_; 
v_version_boxed_1000_ = lean_unbox(v_version_997_);
v_res_1001_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v___x_993_, v_entries_994_, v_indexes_995_, v_status_996_, v_version_boxed_1000_, v_x_998_);
lean_dec_ref(v___x_993_);
return v_res_1001_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_nat_to_int(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v___x_1004_, lean_object* v_a_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v_offset_1007_; lean_object* v_second_1008_; lean_object* v_nano_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_offset_1007_ = lean_ctor_get(v___x_1004_, 0);
v_second_1008_ = lean_ctor_get(v_a_1005_, 0);
v_nano_1009_ = lean_ctor_get(v_a_1005_, 1);
v___x_1010_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_1011_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_1012_ = lean_int_mul(v_second_1008_, v___x_1011_);
v___x_1013_ = lean_int_add(v___x_1012_, v_nano_1009_);
lean_dec(v___x_1012_);
v___x_1014_ = lean_int_mul(v_offset_1007_, v___x_1011_);
v___x_1015_ = lean_int_add(v___x_1014_, v___x_1010_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_int_add(v___x_1013_, v___x_1015_);
lean_dec(v___x_1015_);
lean_dec(v___x_1013_);
v___x_1017_ = l_Std_Time_Duration_ofNanoseconds(v___x_1016_);
lean_dec(v___x_1016_);
v___x_1018_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v___x_1019_, lean_object* v_a_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v___x_1019_, v_a_1020_, v_x_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v___x_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(lean_object* v_m_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_buckets_1025_; lean_object* v___x_1026_; uint64_t v___x_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v_fold_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_buckets_1025_ = lean_ctor_get(v_m_1023_, 1);
v___x_1026_ = lean_array_get_size(v_buckets_1025_);
v___x_1027_ = lean_string_hash(v_a_1024_);
v___x_1028_ = 32ULL;
v___x_1029_ = lean_uint64_shift_right(v___x_1027_, v___x_1028_);
v_fold_1030_ = lean_uint64_xor(v___x_1027_, v___x_1029_);
v___x_1031_ = 16ULL;
v___x_1032_ = lean_uint64_shift_right(v_fold_1030_, v___x_1031_);
v___x_1033_ = lean_uint64_xor(v_fold_1030_, v___x_1032_);
v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
v___x_1035_ = lean_usize_of_nat(v___x_1026_);
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_sub(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_usize_land(v___x_1034_, v___x_1037_);
v___x_1039_ = lean_array_uget_borrowed(v_buckets_1025_, v___x_1038_);
v___x_1040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1024_, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg___boxed(lean_object* v_m_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_m_1041_, v_a_1042_);
lean_dec_ref(v_a_1042_);
lean_dec_ref(v_m_1041_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1045_, lean_object* v_head_1046_){
_start:
{
uint8_t v_generateDate_1051_; 
v_generateDate_1051_ = lean_ctor_get_uint8(v_config_1045_, sizeof(void*)*24 + 1);
if (v_generateDate_1051_ == 0)
{
goto v___jp_1048_;
}
else
{
lean_object* v_headers_1052_; lean_object* v_status_1053_; uint8_t v_version_1054_; lean_object* v_entries_1055_; lean_object* v_indexes_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1092_; 
v_headers_1052_ = lean_ctor_get(v_head_1046_, 1);
lean_inc_ref(v_headers_1052_);
v_status_1053_ = lean_ctor_get(v_head_1046_, 0);
v_version_1054_ = lean_ctor_get_uint8(v_head_1046_, sizeof(void*)*2);
v_entries_1055_ = lean_ctor_get(v_headers_1052_, 0);
v_indexes_1056_ = lean_ctor_get(v_headers_1052_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_headers_1052_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1058_ = v_headers_1052_;
v_isShared_1059_ = v_isSharedCheck_1092_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_indexes_1056_);
lean_inc(v_entries_1055_);
lean_dec(v_headers_1052_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1092_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = l_Std_Http_Header_Name_date;
v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_indexes_1056_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v_val_1066_; lean_object* v___x_1070_; 
lean_inc(v_status_1053_);
lean_dec_ref(v_head_1046_);
v___x_1062_ = l_Std_Time_TimeZone_UTC;
v___x_1063_ = lean_box(v_version_1054_);
v___f_1064_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1064_, 0, v___x_1062_);
lean_closure_set(v___f_1064_, 1, v_entries_1055_);
lean_closure_set(v___f_1064_, 2, v_indexes_1056_);
lean_closure_set(v___f_1064_, 3, v_status_1053_);
lean_closure_set(v___f_1064_, 4, v___x_1063_);
v___x_1070_ = lean_get_current_time();
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1083_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1083_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1083_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_inc(v_a_1071_);
v___f_1075_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1075_, 0, v___x_1062_);
lean_closure_set(v___f_1075_, 1, v_a_1071_);
v___x_1076_ = lean_mk_thunk(v___f_1075_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1076_);
lean_ctor_set(v___x_1058_, 0, v_a_1071_);
v___x_1078_ = v___x_1058_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1078_);
v___x_1080_ = v___x_1073_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v_val_1066_ = v___x_1080_;
goto v___jp_1065_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_del_object(v___x_1058_);
v_a_1084_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1070_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1070_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set_tag(v___x_1086_, 0);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
v_val_1066_ = v___x_1089_;
goto v___jp_1065_;
}
}
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_val_1066_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1068_, v___x_1061_, v___x_1067_, v___f_1064_);
return v___x_1069_;
}
}
else
{
lean_del_object(v___x_1058_);
lean_dec_ref(v_indexes_1056_);
lean_dec_ref(v_entries_1055_);
goto v___jp_1048_;
}
}
}
v___jp_1048_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_head_1046_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1093_, lean_object* v_head_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1093_, v_head_1094_);
lean_dec_ref(v_config_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_nat_to_int(v_a_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_nat_to_int(v_a_1099_);
v___x_1101_ = l_Rat_ofInt(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_00_u03b2_1102_, lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_m_1103_, v_a_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_a_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(v_00_u03b2_1106_, v_m_1107_, v_a_1108_);
lean_dec_ref(v_a_1108_);
lean_dec_ref(v_m_1107_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1111_, lean_object* v_a_1112_, lean_object* v_x_1113_){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1112_, v_x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1115_, lean_object* v_a_1116_, lean_object* v_x_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1115_, v_a_1116_, v_x_1117_);
lean_dec(v_x_1117_);
lean_dec_ref(v_a_1116_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1120_, lean_object* v_data_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1123_, lean_object* v_i_1124_, lean_object* v_source_1125_, lean_object* v_target_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v_i_1124_, v_source_1125_, v_target_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1132_, lean_object* v_____r_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___y_1132_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1139_, lean_object* v_____r_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1139_, v_____r_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1143_, lean_object* v_x_1144_){
_start:
{
if (lean_obj_tag(v_x_1144_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v___f_1143_);
v_a_1146_ = lean_ctor_get(v_x_1144_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v_x_1144_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v_x_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v_x_1144_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v_x_1144_, 1);
v___x_1156_ = lean_apply_2(v___f_1143_, v_a_1155_, lean_box(0));
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1157_, v_x_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1161_, lean_object* v_body_1162_, lean_object* v___f_1163_, lean_object* v___f_1164_, lean_object* v_x_1165_){
_start:
{
if (lean_obj_tag(v_x_1165_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v___f_1164_);
lean_dec_ref(v___f_1163_);
lean_dec(v_body_1162_);
lean_dec_ref(v_close_1161_);
v_a_1167_ = lean_ctor_get(v_x_1165_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v_x_1165_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v_x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1176_; uint8_t v___x_1177_; 
v_a_1176_ = lean_ctor_get(v_x_1165_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v_x_1165_, 1);
v___x_1177_ = lean_unbox(v_a_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref(v___f_1164_);
v___x_1178_ = lean_apply_2(v_close_1161_, v_body_1162_, lean_box(0));
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_unbox(v_a_1176_);
lean_dec(v_a_1176_);
v___x_1181_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1179_, v___x_1180_, v___x_1178_, v___f_1163_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_a_1176_);
lean_dec_ref(v___f_1163_);
lean_dec(v_body_1162_);
lean_dec_ref(v_close_1161_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_apply_2(v___f_1164_, v___x_1182_, lean_box(0));
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1184_, lean_object* v_body_1185_, lean_object* v___f_1186_, lean_object* v___f_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1184_, v_body_1185_, v___f_1186_, v___f_1187_, v_x_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v___x_1191_, lean_object* v_x1_1192_, lean_object* v_x2_1193_){
_start:
{
lean_object* v_fst_1194_; uint8_t v___x_1195_; 
v_fst_1194_ = lean_ctor_get(v_x2_1193_, 0);
v___x_1195_ = lean_string_dec_eq(v_fst_1194_, v___x_1191_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_array_push(v_x1_1192_, v_x2_1193_);
return v___x_1196_;
}
else
{
lean_dec_ref(v_x2_1193_);
return v_x1_1192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v___x_1197_, lean_object* v_x1_1198_, lean_object* v_x2_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v___x_1197_, v_x1_1198_, v_x2_1199_);
lean_dec_ref(v___x_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___f_1201_, lean_object* v___f_1202_, lean_object* v_x1_1203_, lean_object* v_x2_1204_){
_start:
{
lean_object* v_fst_1205_; lean_object* v_entries_1206_; lean_object* v_indexes_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1218_; 
v_fst_1205_ = lean_ctor_get(v_x2_1204_, 0);
lean_inc(v_fst_1205_);
v_entries_1206_ = lean_ctor_get(v_x1_1203_, 0);
v_indexes_1207_ = lean_ctor_get(v_x1_1203_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x1_1203_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1209_ = v_x1_1203_;
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_indexes_1207_);
lean_inc(v_entries_1206_);
lean_dec(v_x1_1203_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_i_1211_; lean_object* v_f_1212_; lean_object* v_entries_1213_; lean_object* v_indexes_1214_; lean_object* v___x_1216_; 
v_i_1211_ = lean_array_get_size(v_entries_1206_);
v_f_1212_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1212_, 0, v_i_1211_);
v_entries_1213_ = lean_array_push(v_entries_1206_, v_x2_1204_);
v_indexes_1214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1201_, v___f_1202_, v_indexes_1207_, v_fst_1205_, v_f_1212_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_indexes_1214_);
lean_ctor_set(v___x_1209_, 0, v_entries_1213_);
v___x_1216_ = v___x_1209_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_entries_1213_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_indexes_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___f_1241_; 
v___x_1240_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1241_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1241_, 0, v___x_1240_);
return v___f_1241_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___f_1248_; 
v___x_1247_ = l_Std_Http_Header_Name_contentLength;
v___f_1248_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1248_, 0, v___x_1247_);
return v___f_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v___y_1249_, lean_object* v_body_1250_, lean_object* v_isClosed_1251_, lean_object* v_close_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v___y_1256_; uint8_t v_omitBody_1257_; lean_object* v___y_1270_; uint8_t v___y_1305_; lean_object* v___y_1306_; uint8_t v___y_1307_; 
if (lean_obj_tag(v_x_1253_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_close_1252_);
lean_dec_ref(v_isClosed_1251_);
lean_dec(v_body_1250_);
lean_dec_ref(v___y_1249_);
v_a_1310_ = lean_ctor_get(v_x_1253_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1312_ = v_x_1253_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v_x_1253_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
}
else
{
lean_object* v_writer_1319_; lean_object* v_a_1320_; lean_object* v_reader_1321_; lean_object* v_config_1322_; lean_object* v_events_1323_; lean_object* v_error_1324_; lean_object* v_instant_1325_; uint8_t v_keepAlive_1326_; uint8_t v_forcedFlush_1327_; uint8_t v_pullBodyStalled_1328_; lean_object* v_userData_1329_; lean_object* v_outputData_1330_; lean_object* v_state_1331_; lean_object* v_knownSize_1332_; lean_object* v_messageHead_1333_; uint8_t v_sentMessage_1334_; uint8_t v_userClosedBody_1335_; uint8_t v_omitBody_1336_; lean_object* v_userDataBytes_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1488_; 
v_writer_1319_ = lean_ctor_get(v___y_1249_, 1);
lean_inc_ref(v_writer_1319_);
v_a_1320_ = lean_ctor_get(v_x_1253_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v_x_1253_, 1);
v_reader_1321_ = lean_ctor_get(v___y_1249_, 0);
v_config_1322_ = lean_ctor_get(v___y_1249_, 2);
v_events_1323_ = lean_ctor_get(v___y_1249_, 3);
v_error_1324_ = lean_ctor_get(v___y_1249_, 4);
v_instant_1325_ = lean_ctor_get(v___y_1249_, 5);
v_keepAlive_1326_ = lean_ctor_get_uint8(v___y_1249_, sizeof(void*)*6);
v_forcedFlush_1327_ = lean_ctor_get_uint8(v___y_1249_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1328_ = lean_ctor_get_uint8(v___y_1249_, sizeof(void*)*6 + 2);
v_userData_1329_ = lean_ctor_get(v_writer_1319_, 0);
v_outputData_1330_ = lean_ctor_get(v_writer_1319_, 1);
v_state_1331_ = lean_ctor_get(v_writer_1319_, 2);
v_knownSize_1332_ = lean_ctor_get(v_writer_1319_, 3);
v_messageHead_1333_ = lean_ctor_get(v_writer_1319_, 4);
v_sentMessage_1334_ = lean_ctor_get_uint8(v_writer_1319_, sizeof(void*)*6);
v_userClosedBody_1335_ = lean_ctor_get_uint8(v_writer_1319_, sizeof(void*)*6 + 1);
v_omitBody_1336_ = lean_ctor_get_uint8(v_writer_1319_, sizeof(void*)*6 + 2);
v_userDataBytes_1337_ = lean_ctor_get(v_writer_1319_, 5);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_writer_1319_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1339_ = v_writer_1319_;
v_isShared_1340_ = v_isSharedCheck_1488_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_userDataBytes_1337_);
lean_inc(v_messageHead_1333_);
lean_inc(v_knownSize_1332_);
lean_inc(v_state_1331_);
lean_inc(v_outputData_1330_);
lean_inc(v_userData_1329_);
lean_dec(v_writer_1319_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1488_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; uint8_t v___y_1389_; uint8_t v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___x_1437_; lean_object* v___y_1439_; uint8_t v___y_1440_; uint8_t v___y_1441_; uint8_t v___y_1442_; uint8_t v___y_1443_; uint8_t v___y_1444_; uint8_t v___y_1451_; uint8_t v___y_1452_; uint8_t v___y_1453_; uint8_t v___y_1466_; uint8_t v___y_1467_; uint8_t v___y_1470_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1437_ = 0;
v___x_1486_ = lean_box(1);
v___x_1487_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1331_, v___x_1486_);
if (v___x_1487_ == 0)
{
v___y_1470_ = v___x_1487_;
goto v___jp_1469_;
}
else
{
if (v_sentMessage_1334_ == 0)
{
v___y_1470_ = v___x_1487_;
goto v___jp_1469_;
}
else
{
lean_del_object(v___x_1339_);
lean_dec(v_userDataBytes_1337_);
lean_dec(v_messageHead_1333_);
lean_dec(v_knownSize_1332_);
lean_dec(v_state_1331_);
lean_dec_ref(v_outputData_1330_);
lean_dec_ref(v_userData_1329_);
lean_dec(v_a_1320_);
v___y_1256_ = v___y_1249_;
v_omitBody_1257_ = v_omitBody_1336_;
goto v___jp_1255_;
}
}
v___jp_1341_:
{
lean_object* v_message_1344_; lean_object* v___x_2280__overap_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v_message_1344_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1342_, v_a_1320_, v___y_1343_);
v___x_2280__overap_1345_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1342_);
v___x_1346_ = lean_apply_2(v___x_2280__overap_1345_, v_outputData_1330_, v_message_1344_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1346_);
v___x_1348_ = v___x_1339_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_userData_1329_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_state_1331_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_knownSize_1332_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_messageHead_1333_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_userDataBytes_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6, v_sentMessage_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6 + 1, v_userClosedBody_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6 + 2, v_omitBody_1336_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1349_, 0, v_reader_1321_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
lean_ctor_set(v___x_1349_, 2, v_config_1322_);
lean_ctor_set(v___x_1349_, 3, v_events_1323_);
lean_ctor_set(v___x_1349_, 4, v_error_1324_);
lean_ctor_set(v___x_1349_, 5, v_instant_1325_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*6, v_keepAlive_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*6 + 1, v_forcedFlush_1327_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*6 + 2, v_pullBodyStalled_1328_);
v___y_1256_ = v___x_1349_;
v_omitBody_1257_ = v_omitBody_1336_;
goto v___jp_1255_;
}
}
v___jp_1351_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_array_get_size(v___y_1356_);
v___x_1358_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1359_ = lean_nat_dec_lt(v___y_1353_, v___x_1357_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v___y_1356_);
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___y_1355_;
goto v___jp_1341_;
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_nat_dec_le(v___x_1357_, v___x_1357_);
if (v___x_1360_ == 0)
{
if (v___x_1359_ == 0)
{
lean_dec_ref(v___y_1356_);
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___y_1355_;
goto v___jp_1341_;
}
else
{
size_t v___x_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = lean_usize_of_nat(v___x_1357_);
lean_inc_ref(v___y_1352_);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1358_, v___y_1352_, v___y_1356_, v___x_1361_, v___x_1362_, v___y_1355_);
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___x_1363_;
goto v___jp_1341_;
}
}
else
{
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_of_nat(v___x_1357_);
lean_inc_ref(v___y_1352_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1358_, v___y_1352_, v___y_1356_, v___x_1364_, v___x_1365_, v___y_1355_);
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___x_1366_;
goto v___jp_1341_;
}
}
}
v___jp_1367_:
{
lean_object* v_entries_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_entries_1374_ = lean_ctor_get(v___y_1371_, 0);
lean_inc_ref(v_entries_1374_);
lean_dec_ref(v___y_1371_);
v___x_1375_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1373_, v___y_1370_);
lean_dec_ref(v___y_1370_);
lean_dec_ref(v___y_1373_);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_entries_1374_);
v___x_1378_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1379_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1380_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1380_ == 0)
{
lean_dec_ref(v_entries_1374_);
v___y_1352_ = v___y_1368_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1375_;
v___y_1356_ = v___x_1378_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_le(v___x_1377_, v___x_1377_);
if (v___x_1381_ == 0)
{
if (v___x_1380_ == 0)
{
lean_dec_ref(v_entries_1374_);
v___y_1352_ = v___y_1368_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1375_;
v___y_1356_ = v___x_1378_;
goto v___jp_1351_;
}
else
{
size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1377_);
lean_inc_ref(v___y_1369_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1379_, v___y_1369_, v_entries_1374_, v___x_1382_, v___x_1383_, v___x_1378_);
v___y_1352_ = v___y_1368_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1375_;
v___y_1356_ = v___x_1384_;
goto v___jp_1351_;
}
}
else
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = lean_usize_of_nat(v___x_1377_);
lean_inc_ref(v___y_1369_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1379_, v___y_1369_, v_entries_1374_, v___x_1385_, v___x_1386_, v___x_1378_);
v___y_1352_ = v___y_1368_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___x_1375_;
v___y_1356_ = v___x_1387_;
goto v___jp_1351_;
}
}
}
v___jp_1388_:
{
lean_object* v___x_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; uint8_t v___x_1397_; 
v___x_1392_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1393_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___f_1394_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1395_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1396_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1397_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1394_, v___f_1395_, v___x_1392_, v___y_1391_);
if (v___x_1397_ == 0)
{
if (v___y_1389_ == 0)
{
v___y_1368_ = v___f_1396_;
v___y_1369_ = v___f_1393_;
v___y_1370_ = v___f_1395_;
v___y_1371_ = v___y_1391_;
v___y_1372_ = v___y_1390_;
v___y_1373_ = v___f_1394_;
goto v___jp_1367_;
}
else
{
v___y_1342_ = v___y_1390_;
v___y_1343_ = v___y_1391_;
goto v___jp_1341_;
}
}
else
{
v___y_1368_ = v___f_1396_;
v___y_1369_ = v___f_1393_;
v___y_1370_ = v___f_1395_;
v___y_1371_ = v___y_1391_;
v___y_1372_ = v___y_1390_;
v___y_1373_ = v___f_1394_;
goto v___jp_1367_;
}
}
v___jp_1398_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = lean_array_get_size(v___y_1404_);
v___x_1406_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1407_ = lean_nat_dec_lt(v___y_1401_, v___x_1405_);
if (v___x_1407_ == 0)
{
lean_dec_ref(v___y_1404_);
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___y_1403_;
goto v___jp_1388_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_le(v___x_1405_, v___x_1405_);
if (v___x_1408_ == 0)
{
if (v___x_1407_ == 0)
{
lean_dec_ref(v___y_1404_);
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___y_1403_;
goto v___jp_1388_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1405_);
lean_inc_ref(v___y_1399_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___y_1399_, v___y_1404_, v___x_1409_, v___x_1410_, v___y_1403_);
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___x_1411_;
goto v___jp_1388_;
}
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_of_nat(v___x_1405_);
lean_inc_ref(v___y_1399_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___y_1399_, v___y_1404_, v___x_1412_, v___x_1413_, v___y_1403_);
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___x_1414_;
goto v___jp_1388_;
}
}
}
v___jp_1415_:
{
lean_object* v_entries_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_entries_1423_ = lean_ctor_get(v___y_1419_, 0);
lean_inc_ref(v_entries_1423_);
lean_dec_ref(v___y_1419_);
v___x_1424_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1421_, v___y_1422_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1421_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_array_get_size(v_entries_1423_);
v___x_1427_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1428_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1429_ = lean_nat_dec_lt(v___x_1425_, v___x_1426_);
if (v___x_1429_ == 0)
{
lean_dec_ref(v_entries_1423_);
v___y_1399_ = v___y_1416_;
v___y_1400_ = v___y_1418_;
v___y_1401_ = v___x_1425_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v___x_1424_;
v___y_1404_ = v___x_1427_;
goto v___jp_1398_;
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_nat_dec_le(v___x_1426_, v___x_1426_);
if (v___x_1430_ == 0)
{
if (v___x_1429_ == 0)
{
lean_dec_ref(v_entries_1423_);
v___y_1399_ = v___y_1416_;
v___y_1400_ = v___y_1418_;
v___y_1401_ = v___x_1425_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v___x_1424_;
v___y_1404_ = v___x_1427_;
goto v___jp_1398_;
}
else
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = lean_usize_of_nat(v___x_1426_);
lean_inc_ref(v___y_1417_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1428_, v___y_1417_, v_entries_1423_, v___x_1431_, v___x_1432_, v___x_1427_);
v___y_1399_ = v___y_1416_;
v___y_1400_ = v___y_1418_;
v___y_1401_ = v___x_1425_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v___x_1424_;
v___y_1404_ = v___x_1433_;
goto v___jp_1398_;
}
}
else
{
size_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = lean_usize_of_nat(v___x_1426_);
lean_inc_ref(v___y_1417_);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1428_, v___y_1417_, v_entries_1423_, v___x_1434_, v___x_1435_, v___x_1427_);
v___y_1399_ = v___y_1416_;
v___y_1400_ = v___y_1418_;
v___y_1401_ = v___x_1425_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v___x_1424_;
v___y_1404_ = v___x_1436_;
goto v___jp_1398_;
}
}
}
v___jp_1438_:
{
lean_object* v_headerSize_1445_; lean_object* v_machine_1446_; lean_object* v_machine_1447_; lean_object* v_reader_1448_; lean_object* v_state_1449_; 
v_headerSize_1445_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1443_, v_a_1320_, v___y_1441_);
v_machine_1446_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1437_, v___y_1439_, v_headerSize_1445_, v___y_1444_);
v_machine_1447_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1437_, v_machine_1446_, v_a_1320_);
lean_dec(v_a_1320_);
v_reader_1448_ = lean_ctor_get(v_machine_1447_, 0);
lean_inc_ref(v_reader_1448_);
v_state_1449_ = lean_ctor_get(v_reader_1448_, 0);
lean_inc(v_state_1449_);
lean_dec_ref(v_reader_1448_);
if (lean_obj_tag(v_state_1449_) == 7)
{
lean_dec_ref_known(v_state_1449_, 1);
v___y_1305_ = v___y_1440_;
v___y_1306_ = v_machine_1447_;
v___y_1307_ = v___y_1442_;
goto v___jp_1304_;
}
else
{
lean_dec(v_state_1449_);
v___y_1305_ = v___y_1440_;
v___y_1306_ = v_machine_1447_;
v___y_1307_ = v___y_1441_;
goto v___jp_1304_;
}
}
v___jp_1450_:
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v_indexes_1456_; lean_object* v___x_1457_; lean_object* v_machine_1458_; lean_object* v___x_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; uint8_t v___x_1462_; 
v___x_1454_ = 1;
v___x_1455_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1454_, v_a_1320_);
v_indexes_1456_ = lean_ctor_get(v___x_1455_, 1);
lean_inc_ref(v_indexes_1456_);
lean_dec_ref(v___x_1455_);
lean_inc(v_a_1320_);
v___x_1457_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1457_, 0, v_userData_1329_);
lean_ctor_set(v___x_1457_, 1, v_outputData_1330_);
lean_ctor_set(v___x_1457_, 2, v_state_1331_);
lean_ctor_set(v___x_1457_, 3, v_knownSize_1332_);
lean_ctor_set(v___x_1457_, 4, v_a_1320_);
lean_ctor_set(v___x_1457_, 5, v_userDataBytes_1337_);
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*6, v___y_1452_);
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*6 + 1, v_userClosedBody_1335_);
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*6 + 2, v_omitBody_1336_);
v_machine_1458_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1458_, 0, v_reader_1321_);
lean_ctor_set(v_machine_1458_, 1, v___x_1457_);
lean_ctor_set(v_machine_1458_, 2, v_config_1322_);
lean_ctor_set(v_machine_1458_, 3, v_events_1323_);
lean_ctor_set(v_machine_1458_, 4, v_error_1324_);
lean_ctor_set(v_machine_1458_, 5, v_instant_1325_);
lean_ctor_set_uint8(v_machine_1458_, sizeof(void*)*6, v_keepAlive_1326_);
lean_ctor_set_uint8(v_machine_1458_, sizeof(void*)*6 + 1, v_forcedFlush_1327_);
lean_ctor_set_uint8(v_machine_1458_, sizeof(void*)*6 + 2, v_pullBodyStalled_1328_);
v___x_1459_ = l_Std_Http_Header_Name_contentLength;
v___f_1460_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1461_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1460_, v___f_1461_, v_indexes_1456_, v___x_1459_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1460_, v___f_1461_, v_indexes_1456_, v___x_1463_);
lean_dec_ref(v_indexes_1456_);
v___y_1439_ = v_machine_1458_;
v___y_1440_ = v___y_1453_;
v___y_1441_ = v___y_1451_;
v___y_1442_ = v___y_1452_;
v___y_1443_ = v___x_1454_;
v___y_1444_ = v___x_1464_;
goto v___jp_1438_;
}
else
{
lean_dec_ref(v_indexes_1456_);
v___y_1439_ = v_machine_1458_;
v___y_1440_ = v___y_1453_;
v___y_1441_ = v___y_1451_;
v___y_1442_ = v___y_1452_;
v___y_1443_ = v___x_1454_;
v___y_1444_ = v___x_1462_;
goto v___jp_1438_;
}
}
v___jp_1465_:
{
lean_object* v_state_1468_; 
v_state_1468_ = lean_ctor_get(v_reader_1321_, 0);
if (lean_obj_tag(v_state_1468_) == 7)
{
v___y_1451_ = v___y_1467_;
v___y_1452_ = v___y_1466_;
v___y_1453_ = v___y_1466_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v___y_1467_;
v___y_1452_ = v___y_1466_;
v___y_1453_ = v___y_1467_;
goto v___jp_1450_;
}
}
v___jp_1469_:
{
if (v___y_1470_ == 0)
{
lean_del_object(v___x_1339_);
lean_dec(v_userDataBytes_1337_);
lean_dec(v_messageHead_1333_);
lean_dec(v_knownSize_1332_);
lean_dec(v_state_1331_);
lean_dec_ref(v_outputData_1330_);
lean_dec_ref(v_userData_1329_);
lean_dec(v_a_1320_);
v___y_1256_ = v___y_1249_;
v_omitBody_1257_ = v_omitBody_1336_;
goto v___jp_1255_;
}
else
{
lean_object* v_status_1471_; uint8_t v___x_1472_; uint16_t v___x_1473_; uint16_t v___x_1474_; uint8_t v___x_1475_; 
lean_inc(v_instant_1325_);
lean_inc(v_error_1324_);
lean_inc_ref(v_events_1323_);
lean_inc_ref(v_config_1322_);
lean_inc_ref(v_reader_1321_);
lean_dec_ref(v___y_1249_);
v_status_1471_ = lean_ctor_get(v_a_1320_, 0);
v___x_1472_ = 0;
v___x_1473_ = 100;
v___x_1474_ = l_Std_Http_Status_toCode(v_status_1471_);
v___x_1475_ = lean_uint16_dec_le(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_del_object(v___x_1339_);
lean_dec(v_messageHead_1333_);
v___y_1466_ = v___y_1470_;
v___y_1467_ = v___x_1472_;
goto v___jp_1465_;
}
else
{
uint16_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = 200;
v___x_1477_ = lean_uint16_dec_lt(v___x_1474_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_del_object(v___x_1339_);
lean_dec(v_messageHead_1333_);
v___y_1466_ = v___y_1470_;
v___y_1467_ = v___x_1472_;
goto v___jp_1465_;
}
else
{
uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; lean_object* v___f_1484_; uint8_t v___x_1485_; 
v___x_1478_ = 1;
v___x_1479_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1478_, v_a_1320_);
v___x_1480_ = l_Std_Http_Header_Name_contentLength;
v___f_1481_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15);
v___f_1482_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1483_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1484_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1485_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1482_, v___f_1483_, v___x_1480_, v___x_1479_);
if (v___x_1485_ == 0)
{
if (v___x_1477_ == 0)
{
v___y_1416_ = v___f_1484_;
v___y_1417_ = v___f_1481_;
v___y_1418_ = v___x_1477_;
v___y_1419_ = v___x_1479_;
v___y_1420_ = v___x_1478_;
v___y_1421_ = v___f_1482_;
v___y_1422_ = v___f_1483_;
goto v___jp_1415_;
}
else
{
v___y_1389_ = v___x_1477_;
v___y_1390_ = v___x_1478_;
v___y_1391_ = v___x_1479_;
goto v___jp_1388_;
}
}
else
{
v___y_1416_ = v___f_1484_;
v___y_1417_ = v___f_1481_;
v___y_1418_ = v___x_1477_;
v___y_1419_ = v___x_1479_;
v___y_1420_ = v___x_1478_;
v___y_1421_ = v___f_1482_;
v___y_1422_ = v___f_1483_;
goto v___jp_1415_;
}
}
}
}
}
}
}
v___jp_1255_:
{
if (v_omitBody_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec_ref(v_close_1252_);
lean_dec_ref(v_isClosed_1251_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_body_1250_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___y_1256_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; 
lean_inc(v_body_1250_);
v___x_1262_ = lean_apply_2(v_isClosed_1251_, v_body_1250_, lean_box(0));
v___f_1263_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1263_, 0, v___y_1256_);
lean_inc_ref(v___f_1263_);
v___f_1264_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1264_, 0, v___f_1263_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1265_, 0, v_close_1252_);
lean_closure_set(v___f_1265_, 1, v_body_1250_);
lean_closure_set(v___f_1265_, 2, v___f_1264_);
lean_closure_set(v___f_1265_, 3, v___f_1263_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = 0;
v___x_1268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1266_, v___x_1267_, v___x_1262_, v___f_1265_);
return v___x_1268_;
}
}
v___jp_1269_:
{
lean_object* v_writer_1271_; lean_object* v_reader_1272_; lean_object* v_config_1273_; lean_object* v_events_1274_; lean_object* v_error_1275_; lean_object* v_instant_1276_; uint8_t v_keepAlive_1277_; uint8_t v_forcedFlush_1278_; uint8_t v_pullBodyStalled_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1303_; 
v_writer_1271_ = lean_ctor_get(v___y_1270_, 1);
v_reader_1272_ = lean_ctor_get(v___y_1270_, 0);
v_config_1273_ = lean_ctor_get(v___y_1270_, 2);
v_events_1274_ = lean_ctor_get(v___y_1270_, 3);
v_error_1275_ = lean_ctor_get(v___y_1270_, 4);
v_instant_1276_ = lean_ctor_get(v___y_1270_, 5);
v_keepAlive_1277_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*6);
v_forcedFlush_1278_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1279_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*6 + 2);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___y_1270_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1281_ = v___y_1270_;
v_isShared_1282_ = v_isSharedCheck_1303_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_instant_1276_);
lean_inc(v_error_1275_);
lean_inc(v_events_1274_);
lean_inc(v_config_1273_);
lean_inc(v_writer_1271_);
lean_inc(v_reader_1272_);
lean_dec(v___y_1270_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1303_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_userData_1283_; lean_object* v_outputData_1284_; lean_object* v_knownSize_1285_; lean_object* v_messageHead_1286_; uint8_t v_sentMessage_1287_; uint8_t v_userClosedBody_1288_; uint8_t v_omitBody_1289_; lean_object* v_userDataBytes_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1301_; 
v_userData_1283_ = lean_ctor_get(v_writer_1271_, 0);
v_outputData_1284_ = lean_ctor_get(v_writer_1271_, 1);
v_knownSize_1285_ = lean_ctor_get(v_writer_1271_, 3);
v_messageHead_1286_ = lean_ctor_get(v_writer_1271_, 4);
v_sentMessage_1287_ = lean_ctor_get_uint8(v_writer_1271_, sizeof(void*)*6);
v_userClosedBody_1288_ = lean_ctor_get_uint8(v_writer_1271_, sizeof(void*)*6 + 1);
v_omitBody_1289_ = lean_ctor_get_uint8(v_writer_1271_, sizeof(void*)*6 + 2);
v_userDataBytes_1290_ = lean_ctor_get(v_writer_1271_, 5);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_writer_1271_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_writer_1271_, 2);
lean_dec(v_unused_1302_);
v___x_1292_ = v_writer_1271_;
v_isShared_1293_ = v_isSharedCheck_1301_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_userDataBytes_1290_);
lean_inc(v_messageHead_1286_);
lean_inc(v_knownSize_1285_);
lean_inc(v_outputData_1284_);
lean_inc(v_userData_1283_);
lean_dec(v_writer_1271_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1301_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(2);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 2, v___x_1294_);
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_userData_1283_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_outputData_1284_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_knownSize_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_messageHead_1286_);
lean_ctor_set(v_reuseFailAlloc_1300_, 5, v_userDataBytes_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*6, v_sentMessage_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*6 + 1, v_userClosedBody_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*6 + 2, v_omitBody_1289_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1296_);
v___x_1298_ = v___x_1281_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_reader_1272_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_config_1273_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_events_1274_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_error_1275_);
lean_ctor_set(v_reuseFailAlloc_1299_, 5, v_instant_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*6, v_keepAlive_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*6 + 1, v_forcedFlush_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*6 + 2, v_pullBodyStalled_1279_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
v___y_1256_ = v___x_1298_;
v_omitBody_1257_ = v_omitBody_1289_;
goto v___jp_1255_;
}
}
}
}
}
v___jp_1304_:
{
if (v___y_1307_ == 0)
{
v___y_1270_ = v___y_1306_;
goto v___jp_1269_;
}
else
{
if (v___y_1305_ == 0)
{
lean_object* v_writer_1308_; uint8_t v_omitBody_1309_; 
v_writer_1308_ = lean_ctor_get(v___y_1306_, 1);
v_omitBody_1309_ = lean_ctor_get_uint8(v_writer_1308_, sizeof(void*)*6 + 2);
v___y_1256_ = v___y_1306_;
v_omitBody_1257_ = v_omitBody_1309_;
goto v___jp_1255_;
}
else
{
v___y_1270_ = v___y_1306_;
goto v___jp_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1489_, lean_object* v_body_1490_, lean_object* v_isClosed_1491_, lean_object* v_close_1492_, lean_object* v_x_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1489_, v_body_1490_, v_isClosed_1491_, v_close_1492_, v_x_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v_config_1496_, lean_object* v_line_1497_, lean_object* v_body_1498_, lean_object* v_isClosed_1499_, lean_object* v_close_1500_, lean_object* v_machine_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v___y_1505_; 
if (lean_obj_tag(v_x_1502_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v_machine_1501_);
lean_dec_ref(v_close_1500_);
lean_dec_ref(v_isClosed_1499_);
lean_dec(v_body_1498_);
lean_dec_ref(v_line_1497_);
v_a_1511_ = lean_ctor_get(v_x_1502_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1502_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1513_ = v_x_1502_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v_x_1502_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1520_; 
v_a_1520_ = lean_ctor_get(v_x_1502_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v_x_1502_, 1);
if (lean_obj_tag(v_a_1520_) == 1)
{
lean_object* v_writer_1521_; lean_object* v_reader_1522_; lean_object* v_config_1523_; lean_object* v_events_1524_; lean_object* v_error_1525_; lean_object* v_instant_1526_; uint8_t v_keepAlive_1527_; uint8_t v_forcedFlush_1528_; uint8_t v_pullBodyStalled_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1552_; 
v_writer_1521_ = lean_ctor_get(v_machine_1501_, 1);
v_reader_1522_ = lean_ctor_get(v_machine_1501_, 0);
v_config_1523_ = lean_ctor_get(v_machine_1501_, 2);
v_events_1524_ = lean_ctor_get(v_machine_1501_, 3);
v_error_1525_ = lean_ctor_get(v_machine_1501_, 4);
v_instant_1526_ = lean_ctor_get(v_machine_1501_, 5);
v_keepAlive_1527_ = lean_ctor_get_uint8(v_machine_1501_, sizeof(void*)*6);
v_forcedFlush_1528_ = lean_ctor_get_uint8(v_machine_1501_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1529_ = lean_ctor_get_uint8(v_machine_1501_, sizeof(void*)*6 + 2);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_machine_1501_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1531_ = v_machine_1501_;
v_isShared_1532_ = v_isSharedCheck_1552_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_instant_1526_);
lean_inc(v_error_1525_);
lean_inc(v_events_1524_);
lean_inc(v_config_1523_);
lean_inc(v_writer_1521_);
lean_inc(v_reader_1522_);
lean_dec(v_machine_1501_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1552_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_userData_1533_; lean_object* v_outputData_1534_; lean_object* v_state_1535_; lean_object* v_messageHead_1536_; uint8_t v_sentMessage_1537_; uint8_t v_userClosedBody_1538_; uint8_t v_omitBody_1539_; lean_object* v_userDataBytes_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1550_; 
v_userData_1533_ = lean_ctor_get(v_writer_1521_, 0);
v_outputData_1534_ = lean_ctor_get(v_writer_1521_, 1);
v_state_1535_ = lean_ctor_get(v_writer_1521_, 2);
v_messageHead_1536_ = lean_ctor_get(v_writer_1521_, 4);
v_sentMessage_1537_ = lean_ctor_get_uint8(v_writer_1521_, sizeof(void*)*6);
v_userClosedBody_1538_ = lean_ctor_get_uint8(v_writer_1521_, sizeof(void*)*6 + 1);
v_omitBody_1539_ = lean_ctor_get_uint8(v_writer_1521_, sizeof(void*)*6 + 2);
v_userDataBytes_1540_ = lean_ctor_get(v_writer_1521_, 5);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_writer_1521_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_writer_1521_, 3);
lean_dec(v_unused_1551_);
v___x_1542_ = v_writer_1521_;
v_isShared_1543_ = v_isSharedCheck_1550_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_userDataBytes_1540_);
lean_inc(v_messageHead_1536_);
lean_inc(v_state_1535_);
lean_inc(v_outputData_1534_);
lean_inc(v_userData_1533_);
lean_dec(v_writer_1521_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1550_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 3, v_a_1520_);
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_userData_1533_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_outputData_1534_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_state_1535_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_a_1520_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_messageHead_1536_);
lean_ctor_set(v_reuseFailAlloc_1549_, 5, v_userDataBytes_1540_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*6, v_sentMessage_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*6 + 1, v_userClosedBody_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*6 + 2, v_omitBody_1539_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v___x_1545_);
v___x_1547_ = v___x_1531_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_reader_1522_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_config_1523_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_events_1524_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_error_1525_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_instant_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*6, v_keepAlive_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*6 + 1, v_forcedFlush_1528_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*6 + 2, v_pullBodyStalled_1529_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
v___y_1505_ = v___x_1547_;
goto v___jp_1504_;
}
}
}
}
}
else
{
lean_dec(v_a_1520_);
v___y_1505_ = v_machine_1501_;
goto v___jp_1504_;
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___f_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1506_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1496_, v_line_1497_);
v___f_1507_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1507_, 0, v___y_1505_);
lean_closure_set(v___f_1507_, 1, v_body_1498_);
lean_closure_set(v___f_1507_, 2, v_isClosed_1499_);
lean_closure_set(v___f_1507_, 3, v_close_1500_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = 0;
v___x_1510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1508_, v___x_1509_, v___x_1506_, v___f_1507_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v_config_1553_, lean_object* v_line_1554_, lean_object* v_body_1555_, lean_object* v_isClosed_1556_, lean_object* v_close_1557_, lean_object* v_machine_1558_, lean_object* v_x_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v_config_1553_, v_line_1554_, v_body_1555_, v_isClosed_1556_, v_close_1557_, v_machine_1558_, v_x_1559_);
lean_dec_ref(v_config_1553_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1562_, lean_object* v_config_1563_, lean_object* v_machine_1564_, lean_object* v_res_1565_){
_start:
{
lean_object* v_close_1567_; lean_object* v_isClosed_1568_; lean_object* v_getKnownSize_1569_; lean_object* v_line_1570_; lean_object* v_body_1571_; lean_object* v___x_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; 
v_close_1567_ = lean_ctor_get(v_inst_1562_, 1);
lean_inc_ref(v_close_1567_);
v_isClosed_1568_ = lean_ctor_get(v_inst_1562_, 2);
lean_inc_ref(v_isClosed_1568_);
v_getKnownSize_1569_ = lean_ctor_get(v_inst_1562_, 5);
lean_inc_ref(v_getKnownSize_1569_);
lean_dec_ref(v_inst_1562_);
v_line_1570_ = lean_ctor_get(v_res_1565_, 0);
lean_inc_ref(v_line_1570_);
v_body_1571_ = lean_ctor_get(v_res_1565_, 1);
lean_inc_n(v_body_1571_, 2);
lean_dec_ref(v_res_1565_);
v___x_1572_ = lean_apply_2(v_getKnownSize_1569_, v_body_1571_, lean_box(0));
v___f_1573_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_1573_, 0, v_config_1563_);
lean_closure_set(v___f_1573_, 1, v_line_1570_);
lean_closure_set(v___f_1573_, 2, v_body_1571_);
lean_closure_set(v___f_1573_, 3, v_isClosed_1568_);
lean_closure_set(v___f_1573_, 4, v_close_1567_);
lean_closure_set(v___f_1573_, 5, v_machine_1564_);
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = 0;
v___x_1576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1574_, v___x_1575_, v___x_1572_, v___f_1573_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1577_, lean_object* v_config_1578_, lean_object* v_machine_1579_, lean_object* v_res_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1577_, v_config_1578_, v_machine_1579_, v_res_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1583_, lean_object* v_inst_1584_, lean_object* v_config_1585_, lean_object* v_machine_1586_, lean_object* v_res_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1584_, v_config_1585_, v_machine_1586_, v_res_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1590_, lean_object* v_inst_1591_, lean_object* v_config_1592_, lean_object* v_machine_1593_, lean_object* v_res_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1590_, v_inst_1591_, v_config_1592_, v_machine_1593_, v_res_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_closed_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_closed_1600_ = lean_ctor_get_uint8(v_____do__lift_1597_, sizeof(void*)*5);
v___x_1601_ = lean_box(v_closed_1600_);
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v_____do__lift_1604_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v_pendingProducer_1616_; lean_object* v_pendingConsumer_1617_; lean_object* v_interestWaiter_1618_; uint8_t v_closed_1619_; lean_object* v_pendingIncompleteChunk_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1629_; 
v___x_1615_ = lean_st_ref_take(v___y_1613_);
v_pendingProducer_1616_ = lean_ctor_get(v___x_1615_, 0);
v_pendingConsumer_1617_ = lean_ctor_get(v___x_1615_, 1);
v_interestWaiter_1618_ = lean_ctor_get(v___x_1615_, 2);
v_closed_1619_ = lean_ctor_get_uint8(v___x_1615_, sizeof(void*)*5);
v_pendingIncompleteChunk_1620_ = lean_ctor_get(v___x_1615_, 4);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v___x_1615_, 3);
lean_dec(v_unused_1630_);
v___x_1622_ = v___x_1615_;
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1620_);
lean_inc(v_interestWaiter_1618_);
lean_inc(v_pendingConsumer_1617_);
lean_inc(v_pendingProducer_1616_);
lean_dec(v___x_1615_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 3, v___x_1612_);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_pendingProducer_1616_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_pendingConsumer_1617_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_interestWaiter_1618_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_pendingIncompleteChunk_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*5, v_closed_1619_);
v___x_1625_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_st_ref_set(v___y_1613_, v___x_1625_);
v___x_1627_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1631_, v___y_1632_);
lean_dec(v___y_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___x_1635_);
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
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1655_; 
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1636_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v_x_1636_, 0);
lean_dec(v_unused_1656_);
v___x_1648_ = v_x_1636_;
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1635_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1657_, v_x_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1661_, lean_object* v_requestStream_1662_, lean_object* v_keepAliveTimeout_1663_, lean_object* v_currentTimeout_1664_, lean_object* v_headerTimeout_1665_, lean_object* v_response_1666_, lean_object* v_respStream_1667_, lean_object* v_expectData_1668_, uint8_t v_handlerDispatched_1669_, lean_object* v_____r_1670_){
_start:
{
uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1672_ = 0;
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1674_, 0, v_machine_1661_);
lean_ctor_set(v___x_1674_, 1, v_requestStream_1662_);
lean_ctor_set(v___x_1674_, 2, v_keepAliveTimeout_1663_);
lean_ctor_set(v___x_1674_, 3, v_currentTimeout_1664_);
lean_ctor_set(v___x_1674_, 4, v_headerTimeout_1665_);
lean_ctor_set(v___x_1674_, 5, v_response_1666_);
lean_ctor_set(v___x_1674_, 6, v_respStream_1667_);
lean_ctor_set(v___x_1674_, 7, v_expectData_1668_);
lean_ctor_set(v___x_1674_, 8, v___x_1673_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*9, v___x_1672_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*9 + 1, v_handlerDispatched_1669_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1678_, lean_object* v_requestStream_1679_, lean_object* v_keepAliveTimeout_1680_, lean_object* v_currentTimeout_1681_, lean_object* v_headerTimeout_1682_, lean_object* v_response_1683_, lean_object* v_respStream_1684_, lean_object* v_expectData_1685_, lean_object* v_handlerDispatched_1686_, lean_object* v_____r_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v_handlerDispatched_boxed_1689_; lean_object* v_res_1690_; 
v_handlerDispatched_boxed_1689_ = lean_unbox(v_handlerDispatched_1686_);
v_res_1690_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1678_, v_requestStream_1679_, v_keepAliveTimeout_1680_, v_currentTimeout_1681_, v_headerTimeout_1682_, v_response_1683_, v_respStream_1684_, v_expectData_1685_, v_handlerDispatched_boxed_1689_, v_____r_1687_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1691_, lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1692_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v___f_1691_);
v_a_1694_ = lean_ctor_get(v_x_1692_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1692_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_x_1692_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_x_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v_x_1692_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v_x_1692_, 1);
v___x_1704_ = lean_apply_2(v___f_1691_, v_a_1703_, lean_box(0));
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1705_, lean_object* v_x_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1705_, v_x_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1709_, lean_object* v___f_1710_, lean_object* v___f_1711_, lean_object* v_x_1712_){
_start:
{
if (lean_obj_tag(v_x_1712_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v___f_1711_);
lean_dec_ref(v___f_1710_);
lean_dec_ref(v_requestStream_1709_);
v_a_1714_ = lean_ctor_get(v_x_1712_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1716_ = v_x_1712_;
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v_x_1712_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1723_; uint8_t v___x_1724_; 
v_a_1723_ = lean_ctor_get(v_x_1712_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v_x_1712_, 1);
v___x_1724_ = lean_unbox(v_a_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
lean_dec_ref(v___f_1711_);
v___x_1725_ = l_Std_Http_Body_Stream_close(v_requestStream_1709_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
v___x_1728_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1726_, v___x_1727_, v___x_1725_, v___f_1710_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_a_1723_);
lean_dec_ref(v___f_1710_);
lean_dec_ref(v_requestStream_1709_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_apply_2(v___f_1711_, v___x_1729_, lean_box(0));
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1731_, lean_object* v___f_1732_, lean_object* v___f_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1731_, v___f_1732_, v___f_1733_, v_x_1734_);
return v_res_1736_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1737_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1738_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___f_1745_; lean_object* v___f_1746_; 
v___x_1744_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1745_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1746_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1746_, 0, v___f_1745_);
lean_closure_set(v___f_1746_, 1, v___x_1744_);
return v___f_1746_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___f_1756_; lean_object* v___f_1757_; 
v___x_1755_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1756_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1757_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1757_, 0, v___f_1756_);
lean_closure_set(v___f_1757_, 1, v___x_1755_);
return v___f_1757_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1758_; lean_object* v___x_1759_; 
v___f_1758_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1759_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1759_, 0, lean_box(0));
lean_closure_set(v___x_1759_, 1, lean_box(0));
lean_closure_set(v___x_1759_, 2, lean_box(0));
lean_closure_set(v___x_1759_, 3, v___f_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1760_, lean_object* v___f_1761_, lean_object* v_x_1762_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v___f_1761_);
lean_dec_ref(v___y_1760_);
v_a_1764_ = lean_ctor_get(v_x_1762_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_x_1762_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1766_ = v_x_1762_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v_x_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
}
else
{
lean_object* v_machine_1773_; lean_object* v_requestStream_1774_; lean_object* v_keepAliveTimeout_1775_; lean_object* v_currentTimeout_1776_; lean_object* v_headerTimeout_1777_; lean_object* v_response_1778_; lean_object* v_respStream_1779_; lean_object* v_expectData_1780_; uint8_t v_handlerDispatched_1781_; lean_object* v___x_1782_; lean_object* v___f_1783_; lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_4928__overap_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___f_1790_; lean_object* v___f_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref_known(v_x_1762_, 1);
v_machine_1773_ = lean_ctor_get(v___y_1760_, 0);
lean_inc_ref(v_machine_1773_);
v_requestStream_1774_ = lean_ctor_get(v___y_1760_, 1);
lean_inc_ref_n(v_requestStream_1774_, 3);
v_keepAliveTimeout_1775_ = lean_ctor_get(v___y_1760_, 2);
lean_inc(v_keepAliveTimeout_1775_);
v_currentTimeout_1776_ = lean_ctor_get(v___y_1760_, 3);
lean_inc(v_currentTimeout_1776_);
v_headerTimeout_1777_ = lean_ctor_get(v___y_1760_, 4);
lean_inc(v_headerTimeout_1777_);
v_response_1778_ = lean_ctor_get(v___y_1760_, 5);
lean_inc_ref(v_response_1778_);
v_respStream_1779_ = lean_ctor_get(v___y_1760_, 6);
lean_inc(v_respStream_1779_);
v_expectData_1780_ = lean_ctor_get(v___y_1760_, 7);
lean_inc(v_expectData_1780_);
v_handlerDispatched_1781_ = lean_ctor_get_uint8(v___y_1760_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1760_);
v___x_1782_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1783_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1784_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1785_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1786_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1786_, 0, lean_box(0));
lean_closure_set(v___x_1786_, 1, lean_box(0));
lean_closure_set(v___x_1786_, 2, lean_box(0));
lean_closure_set(v___x_1786_, 3, v___x_1782_);
lean_closure_set(v___x_1786_, 4, lean_box(0));
lean_closure_set(v___x_1786_, 5, lean_box(0));
lean_closure_set(v___x_1786_, 6, v___x_1785_);
lean_closure_set(v___x_1786_, 7, v___f_1761_);
v___x_4928__overap_1787_ = l_Std_Mutex_atomically___redArg(v___x_1782_, v___f_1783_, v___f_1784_, v_requestStream_1774_, v___x_1786_);
v___x_1788_ = lean_apply_1(v___x_4928__overap_1787_, lean_box(0));
v___x_1789_ = lean_box(v_handlerDispatched_1781_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1790_, 0, v_machine_1773_);
lean_closure_set(v___f_1790_, 1, v_requestStream_1774_);
lean_closure_set(v___f_1790_, 2, v_keepAliveTimeout_1775_);
lean_closure_set(v___f_1790_, 3, v_currentTimeout_1776_);
lean_closure_set(v___f_1790_, 4, v_headerTimeout_1777_);
lean_closure_set(v___f_1790_, 5, v_response_1778_);
lean_closure_set(v___f_1790_, 6, v_respStream_1779_);
lean_closure_set(v___f_1790_, 7, v_expectData_1780_);
lean_closure_set(v___f_1790_, 8, v___x_1789_);
lean_inc_ref(v___f_1790_);
v___f_1791_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1791_, 0, v___f_1790_);
v___f_1792_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1792_, 0, v_requestStream_1774_);
lean_closure_set(v___f_1792_, 1, v___f_1791_);
lean_closure_set(v___f_1792_, 2, v___f_1790_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = 0;
v___x_1795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1793_, v___x_1794_, v___x_1788_, v___f_1792_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1796_, lean_object* v___f_1797_, lean_object* v_x_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1796_, v___f_1797_, v_x_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1801_, lean_object* v_x_1802_){
_start:
{
if (lean_obj_tag(v_x_1802_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v___y_1801_);
v_a_1804_ = lean_ctor_get(v_x_1802_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1802_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1806_ = v_x_1802_;
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v_x_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
}
else
{
lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1821_; 
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1802_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v_x_1802_, 0);
lean_dec(v_unused_1822_);
v___x_1814_ = v_x_1802_;
v_isShared_1815_ = v_isSharedCheck_1821_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v_x_1802_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1821_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1801_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1823_, lean_object* v_x_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1823_, v_x_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1827_, lean_object* v___f_1828_, lean_object* v___y_1829_, lean_object* v_x_1830_){
_start:
{
if (lean_obj_tag(v_x_1830_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___f_1828_);
lean_dec_ref(v_requestStream_1827_);
v_a_1832_ = lean_ctor_get(v_x_1830_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_x_1830_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v_x_1830_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v_x_1830_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1855_; 
v_a_1841_ = lean_ctor_get(v_x_1830_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_x_1830_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1843_ = v_x_1830_;
v_isShared_1844_ = v_isSharedCheck_1855_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v_x_1830_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1855_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_unbox(v_a_1841_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
lean_del_object(v___x_1843_);
lean_dec_ref(v___y_1829_);
v___x_1846_ = l_Std_Http_Body_Stream_close(v_requestStream_1827_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_unbox(v_a_1841_);
lean_dec(v_a_1841_);
v___x_1849_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1847_, v___x_1848_, v___x_1846_, v___f_1828_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec(v_a_1841_);
lean_dec_ref(v___f_1828_);
lean_dec_ref(v_requestStream_1827_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___y_1829_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1850_);
v___x_1852_ = v___x_1843_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1856_, lean_object* v___f_1857_, lean_object* v___y_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1856_, v___f_1857_, v___y_1858_, v_x_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1862_, lean_object* v_machine_1863_, lean_object* v_a_1864_, uint8_t v_requiresData_1865_, lean_object* v_expectData_1866_, lean_object* v_pendingHead_1867_, lean_object* v_x_1868_){
_start:
{
if (lean_obj_tag(v_x_1868_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_pendingHead_1867_);
lean_dec(v_expectData_1866_);
lean_dec_ref(v_a_1864_);
lean_dec_ref(v_machine_1863_);
v_a_1870_ = lean_ctor_get(v_x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1872_ = v_x_1868_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v_x_1868_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1893_; 
v_a_1879_ = lean_ctor_get(v_x_1868_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1868_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1881_ = v_x_1868_;
v_isShared_1882_ = v_isSharedCheck_1893_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v_x_1868_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1893_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_keepAliveTimeout_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v_keepAliveTimeout_1883_ = lean_ctor_get(v_config_1862_, 5);
lean_inc_n(v_keepAliveTimeout_1883_, 2);
v___x_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_keepAliveTimeout_1883_);
v___x_1885_ = lean_box(0);
v___x_1886_ = 0;
v___x_1887_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1887_, 0, v_machine_1863_);
lean_ctor_set(v___x_1887_, 1, v_a_1864_);
lean_ctor_set(v___x_1887_, 2, v___x_1884_);
lean_ctor_set(v___x_1887_, 3, v_keepAliveTimeout_1883_);
lean_ctor_set(v___x_1887_, 4, v___x_1885_);
lean_ctor_set(v___x_1887_, 5, v_a_1879_);
lean_ctor_set(v___x_1887_, 6, v___x_1885_);
lean_ctor_set(v___x_1887_, 7, v_expectData_1866_);
lean_ctor_set(v___x_1887_, 8, v_pendingHead_1867_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*9, v_requiresData_1865_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*9 + 1, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1888_);
v___x_1890_ = v___x_1881_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1894_, lean_object* v_machine_1895_, lean_object* v_a_1896_, lean_object* v_requiresData_1897_, lean_object* v_expectData_1898_, lean_object* v_pendingHead_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v_requiresData_boxed_1902_; lean_object* v_res_1903_; 
v_requiresData_boxed_1902_ = lean_unbox(v_requiresData_1897_);
v_res_1903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1894_, v_machine_1895_, v_a_1896_, v_requiresData_boxed_1902_, v_expectData_1898_, v_pendingHead_1899_, v_x_1900_);
lean_dec_ref(v_config_1894_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1904_, lean_object* v_machine_1905_, uint8_t v_requiresData_1906_, lean_object* v_expectData_1907_, lean_object* v_pendingHead_1908_, lean_object* v_x_1909_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_pendingHead_1908_);
lean_dec(v_expectData_1907_);
lean_dec_ref(v_machine_1905_);
lean_dec_ref(v_config_1904_);
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
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1935_; 
v_a_1920_ = lean_ctor_get(v_x_1909_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1909_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1922_ = v_x_1909_;
v_isShared_1923_ = v_isSharedCheck_1935_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v_x_1909_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1935_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___f_1927_; lean_object* v___x_1929_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = l_Std_CloseableChannel_new___redArg(v___x_1924_);
v___x_1926_ = lean_box(v_requiresData_1906_);
v___f_1927_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1927_, 0, v_config_1904_);
lean_closure_set(v___f_1927_, 1, v_machine_1905_);
lean_closure_set(v___f_1927_, 2, v_a_1920_);
lean_closure_set(v___f_1927_, 3, v___x_1926_);
lean_closure_set(v___f_1927_, 4, v_expectData_1907_);
lean_closure_set(v___f_1927_, 5, v_pendingHead_1908_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1925_);
v___x_1929_ = v___x_1922_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1925_);
v___x_1929_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = 0;
v___x_1933_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1931_, v___x_1932_, v___x_1930_, v___f_1927_);
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1936_, lean_object* v_machine_1937_, lean_object* v_requiresData_1938_, lean_object* v_expectData_1939_, lean_object* v_pendingHead_1940_, lean_object* v_x_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v_requiresData_boxed_1943_; lean_object* v_res_1944_; 
v_requiresData_boxed_1943_ = lean_unbox(v_requiresData_1938_);
v_res_1944_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1936_, v_machine_1937_, v_requiresData_boxed_1943_, v_expectData_1939_, v_pendingHead_1940_, v_x_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1945_, lean_object* v_____r_1946_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1948_ = l_Std_Http_Body_mkStream();
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = 0;
v___x_1951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1949_, v___x_1950_, v___x_1948_, v___f_1945_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1952_, lean_object* v_____r_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1952_, v_____r_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1956_, lean_object* v_val_1957_, lean_object* v___f_1958_, lean_object* v___f_1959_, lean_object* v_x_1960_){
_start:
{
if (lean_obj_tag(v_x_1960_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v___f_1959_);
lean_dec_ref(v___f_1958_);
lean_dec(v_val_1957_);
lean_dec_ref(v_close_1956_);
v_a_1962_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1964_ = v_x_1960_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v_x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
}
else
{
lean_object* v_a_1971_; uint8_t v___x_1972_; 
v_a_1971_ = lean_ctor_get(v_x_1960_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v_x_1960_, 1);
v___x_1972_ = lean_unbox(v_a_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; 
lean_dec_ref(v___f_1959_);
v___x_1973_ = lean_apply_2(v_close_1956_, v_val_1957_, lean_box(0));
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_unbox(v_a_1971_);
lean_dec(v_a_1971_);
v___x_1976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1974_, v___x_1975_, v___x_1973_, v___f_1958_);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v_a_1971_);
lean_dec_ref(v___f_1958_);
lean_dec(v_val_1957_);
lean_dec_ref(v_close_1956_);
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_apply_2(v___f_1959_, v___x_1977_, lean_box(0));
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1979_, lean_object* v_val_1980_, lean_object* v___f_1981_, lean_object* v___f_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1979_, v_val_1980_, v___f_1981_, v___f_1982_, v_x_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1986_, lean_object* v_inst_1987_, lean_object* v___f_1988_, lean_object* v___f_1989_, lean_object* v_____r_1990_){
_start:
{
if (lean_obj_tag(v_respStream_1986_) == 1)
{
lean_object* v_val_1992_; lean_object* v_close_1993_; lean_object* v_isClosed_1994_; lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v_val_1992_ = lean_ctor_get(v_respStream_1986_, 0);
lean_inc_n(v_val_1992_, 2);
lean_dec_ref_known(v_respStream_1986_, 1);
v_close_1993_ = lean_ctor_get(v_inst_1987_, 1);
lean_inc_ref(v_close_1993_);
v_isClosed_1994_ = lean_ctor_get(v_inst_1987_, 2);
lean_inc_ref(v_isClosed_1994_);
lean_dec_ref(v_inst_1987_);
v___x_1995_ = lean_apply_2(v_isClosed_1994_, v_val_1992_, lean_box(0));
v___f_1996_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1996_, 0, v_close_1993_);
lean_closure_set(v___f_1996_, 1, v_val_1992_);
lean_closure_set(v___f_1996_, 2, v___f_1988_);
lean_closure_set(v___f_1996_, 3, v___f_1989_);
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = 0;
v___x_1999_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1997_, v___x_1998_, v___x_1995_, v___f_1996_);
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v___f_1988_);
lean_dec_ref(v_inst_1987_);
lean_dec(v_respStream_1986_);
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_apply_2(v___f_1989_, v___x_2000_, lean_box(0));
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_2002_, lean_object* v_inst_2003_, lean_object* v___f_2004_, lean_object* v___f_2005_, lean_object* v_____r_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_2002_, v_inst_2003_, v___f_2004_, v___f_2005_, v_____r_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2009_, lean_object* v_keepAliveTimeout_2010_, lean_object* v_currentTimeout_2011_, lean_object* v_headerTimeout_2012_, lean_object* v_response_2013_, lean_object* v_respStream_2014_, uint8_t v_requiresData_2015_, lean_object* v_expectData_2016_, uint8_t v_handlerDispatched_2017_, lean_object* v_pendingHead_2018_, lean_object* v_x_2019_){
_start:
{
if (lean_obj_tag(v_x_2019_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_pendingHead_2018_);
lean_dec(v_expectData_2016_);
lean_dec(v_respStream_2014_);
lean_dec_ref(v_response_2013_);
lean_dec(v_headerTimeout_2012_);
lean_dec(v_currentTimeout_2011_);
lean_dec(v_keepAliveTimeout_2010_);
lean_dec_ref(v_requestStream_2009_);
v_a_2021_ = lean_ctor_get(v_x_2019_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_x_2019_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2023_ = v_x_2019_;
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v_x_2019_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2051_; 
v_a_2030_ = lean_ctor_get(v_x_2019_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2019_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2032_ = v_x_2019_;
v_isShared_2033_ = v_isSharedCheck_2051_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v_x_2019_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2051_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_snd_2034_; uint8_t v___x_2035_; 
v_snd_2034_ = lean_ctor_get(v_a_2030_, 1);
v___x_2035_ = lean_unbox(v_snd_2034_);
if (v___x_2035_ == 0)
{
lean_object* v_fst_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v_fst_2036_ = lean_ctor_get(v_a_2030_, 0);
lean_inc(v_fst_2036_);
lean_dec(v_a_2030_);
v___x_2037_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2037_, 0, v_fst_2036_);
lean_ctor_set(v___x_2037_, 1, v_requestStream_2009_);
lean_ctor_set(v___x_2037_, 2, v_keepAliveTimeout_2010_);
lean_ctor_set(v___x_2037_, 3, v_currentTimeout_2011_);
lean_ctor_set(v___x_2037_, 4, v_headerTimeout_2012_);
lean_ctor_set(v___x_2037_, 5, v_response_2013_);
lean_ctor_set(v___x_2037_, 6, v_respStream_2014_);
lean_ctor_set(v___x_2037_, 7, v_expectData_2016_);
lean_ctor_set(v___x_2037_, 8, v_pendingHead_2018_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*9, v_requiresData_2015_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*9 + 1, v_handlerDispatched_2017_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2038_);
v___x_2040_ = v___x_2032_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
else
{
lean_object* v_fst_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec(v_pendingHead_2018_);
v_fst_2043_ = lean_ctor_get(v_a_2030_, 0);
lean_inc(v_fst_2043_);
lean_dec(v_a_2030_);
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2045_, 0, v_fst_2043_);
lean_ctor_set(v___x_2045_, 1, v_requestStream_2009_);
lean_ctor_set(v___x_2045_, 2, v_keepAliveTimeout_2010_);
lean_ctor_set(v___x_2045_, 3, v_currentTimeout_2011_);
lean_ctor_set(v___x_2045_, 4, v_headerTimeout_2012_);
lean_ctor_set(v___x_2045_, 5, v_response_2013_);
lean_ctor_set(v___x_2045_, 6, v_respStream_2014_);
lean_ctor_set(v___x_2045_, 7, v_expectData_2016_);
lean_ctor_set(v___x_2045_, 8, v___x_2044_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*9, v_requiresData_2015_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*9 + 1, v_handlerDispatched_2017_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2046_);
v___x_2048_ = v___x_2032_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2052_, lean_object* v_keepAliveTimeout_2053_, lean_object* v_currentTimeout_2054_, lean_object* v_headerTimeout_2055_, lean_object* v_response_2056_, lean_object* v_respStream_2057_, lean_object* v_requiresData_2058_, lean_object* v_expectData_2059_, lean_object* v_handlerDispatched_2060_, lean_object* v_pendingHead_2061_, lean_object* v_x_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v_requiresData_boxed_2064_; uint8_t v_handlerDispatched_boxed_2065_; lean_object* v_res_2066_; 
v_requiresData_boxed_2064_ = lean_unbox(v_requiresData_2058_);
v_handlerDispatched_boxed_2065_ = lean_unbox(v_handlerDispatched_2060_);
v_res_2066_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2052_, v_keepAliveTimeout_2053_, v_currentTimeout_2054_, v_headerTimeout_2055_, v_response_2056_, v_respStream_2057_, v_requiresData_boxed_2064_, v_expectData_2059_, v_handlerDispatched_boxed_2065_, v_pendingHead_2061_, v_x_2062_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2079_, lean_object* v_inst_2080_, lean_object* v___f_2081_, lean_object* v_handler_2082_, lean_object* v___f_2083_, lean_object* v___f_2084_, lean_object* v_inst_2085_, lean_object* v_connectionContext_2086_, lean_object* v_a_2087_, lean_object* v_x_2088_, lean_object* v___y_2089_){
_start:
{
switch(lean_obj_tag(v_a_2087_))
{
case 0:
{
lean_object* v_head_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_connectionContext_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v___f_2084_);
lean_dec_ref(v___f_2083_);
lean_dec(v_handler_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v_inst_2080_);
v_head_2091_ = lean_ctor_get(v_a_2087_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_a_2087_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2093_ = v_a_2087_;
v_isShared_2094_ = v_isSharedCheck_2134_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_head_2091_);
lean_dec(v_a_2087_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2134_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_machine_2095_; lean_object* v_requestStream_2096_; lean_object* v_response_2097_; lean_object* v_respStream_2098_; uint8_t v_requiresData_2099_; lean_object* v_expectData_2100_; uint8_t v_handlerDispatched_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2129_; 
v_machine_2095_ = lean_ctor_get(v___y_2089_, 0);
v_requestStream_2096_ = lean_ctor_get(v___y_2089_, 1);
v_response_2097_ = lean_ctor_get(v___y_2089_, 5);
v_respStream_2098_ = lean_ctor_get(v___y_2089_, 6);
v_requiresData_2099_ = lean_ctor_get_uint8(v___y_2089_, sizeof(void*)*9);
v_expectData_2100_ = lean_ctor_get(v___y_2089_, 7);
v_handlerDispatched_2101_ = lean_ctor_get_uint8(v___y_2089_, sizeof(void*)*9 + 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___y_2089_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; 
v_unused_2130_ = lean_ctor_get(v___y_2089_, 8);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v___y_2089_, 4);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v___y_2089_, 3);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v___y_2089_, 2);
lean_dec(v_unused_2133_);
v___x_2103_ = v___y_2089_;
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_expectData_2100_);
lean_inc(v_respStream_2098_);
lean_inc(v_response_2097_);
lean_inc(v_requestStream_2096_);
lean_inc(v_machine_2095_);
lean_dec(v___y_2089_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v_lingeringTimeout_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v_lingeringTimeout_2105_ = lean_ctor_get(v_config_2079_, 4);
lean_inc(v_lingeringTimeout_2105_);
lean_dec_ref(v_config_2079_);
v___x_2106_ = lean_box(0);
lean_inc(v_head_2091_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 1);
v___x_2108_ = v___x_2093_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_head_2091_);
v___x_2108_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
lean_inc_ref(v_requestStream_2096_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 8, v___x_2108_);
lean_ctor_set(v___x_2103_, 4, v___x_2106_);
lean_ctor_set(v___x_2103_, 3, v_lingeringTimeout_2105_);
lean_ctor_set(v___x_2103_, 2, v___x_2106_);
v___x_2110_ = v___x_2103_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_machine_2095_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_requestStream_2096_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_lingeringTimeout_2105_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2127_, 5, v_response_2097_);
lean_ctor_set(v_reuseFailAlloc_2127_, 6, v_respStream_2098_);
lean_ctor_set(v_reuseFailAlloc_2127_, 7, v_expectData_2100_);
lean_ctor_set(v_reuseFailAlloc_2127_, 8, v___x_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*9, v_requiresData_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*9 + 1, v_handlerDispatched_2101_);
v___x_2110_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
uint8_t v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = 0;
v___x_2112_ = 1;
v___x_2113_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2111_, v_head_2091_, v___x_2112_);
lean_dec(v_head_2091_);
if (lean_obj_tag(v___x_2113_) == 1)
{
lean_object* v___f_2114_; lean_object* v___x_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___x_5121__overap_2118_; lean_object* v___x_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
v___f_2114_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2114_, 0, v___x_2113_);
v___x_2115_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2116_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2117_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5121__overap_2118_ = l_Std_Mutex_atomically___redArg(v___x_2115_, v___f_2116_, v___f_2117_, v_requestStream_2096_, v___f_2114_);
v___x_2119_ = lean_apply_1(v___x_5121__overap_2118_, lean_box(0));
v___f_2120_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2120_, 0, v___x_2110_);
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = 0;
v___x_2123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2121_, v___x_2122_, v___x_2119_, v___f_2120_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec(v___x_2113_);
lean_dec_ref(v_requestStream_2096_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2110_);
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_connectionContext_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v___f_2084_);
lean_dec_ref(v___f_2083_);
lean_dec(v_handler_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v_inst_2080_);
lean_dec_ref(v_config_2079_);
v_size_2135_ = lean_ctor_get(v_a_2087_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2087_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2137_ = v_a_2087_;
v_isShared_2138_ = v_isSharedCheck_2162_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_size_2135_);
lean_dec(v_a_2087_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2162_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_machine_2139_; lean_object* v_requestStream_2140_; lean_object* v_keepAliveTimeout_2141_; lean_object* v_currentTimeout_2142_; lean_object* v_headerTimeout_2143_; lean_object* v_response_2144_; lean_object* v_respStream_2145_; uint8_t v_handlerDispatched_2146_; lean_object* v_pendingHead_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2160_; 
v_machine_2139_ = lean_ctor_get(v___y_2089_, 0);
v_requestStream_2140_ = lean_ctor_get(v___y_2089_, 1);
v_keepAliveTimeout_2141_ = lean_ctor_get(v___y_2089_, 2);
v_currentTimeout_2142_ = lean_ctor_get(v___y_2089_, 3);
v_headerTimeout_2143_ = lean_ctor_get(v___y_2089_, 4);
v_response_2144_ = lean_ctor_get(v___y_2089_, 5);
v_respStream_2145_ = lean_ctor_get(v___y_2089_, 6);
v_handlerDispatched_2146_ = lean_ctor_get_uint8(v___y_2089_, sizeof(void*)*9 + 1);
v_pendingHead_2147_ = lean_ctor_get(v___y_2089_, 8);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___y_2089_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___y_2089_, 7);
lean_dec(v_unused_2161_);
v___x_2149_ = v___y_2089_;
v_isShared_2150_ = v_isSharedCheck_2160_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_pendingHead_2147_);
lean_inc(v_respStream_2145_);
lean_inc(v_response_2144_);
lean_inc(v_headerTimeout_2143_);
lean_inc(v_currentTimeout_2142_);
lean_inc(v_keepAliveTimeout_2141_);
lean_inc(v_requestStream_2140_);
lean_inc(v_machine_2139_);
lean_dec(v___y_2089_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2160_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
uint8_t v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = 1;
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 7, v_size_2135_);
v___x_2153_ = v___x_2149_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_machine_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_requestStream_2140_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_keepAliveTimeout_2141_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_currentTimeout_2142_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_headerTimeout_2143_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v_response_2144_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_respStream_2145_);
lean_ctor_set(v_reuseFailAlloc_2159_, 7, v_size_2135_);
lean_ctor_set(v_reuseFailAlloc_2159_, 8, v_pendingHead_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*9 + 1, v_handlerDispatched_2146_);
v___x_2153_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*9, v___x_2151_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2153_);
v___x_2155_ = v___x_2137_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2163_; lean_object* v_onFailure_2164_; lean_object* v___f_2165_; lean_object* v___y_2167_; 
lean_dec_ref(v_connectionContext_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v___f_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v_config_2079_);
v_err_2163_ = lean_ctor_get(v_a_2087_, 0);
lean_inc(v_err_2163_);
lean_dec_ref_known(v_a_2087_, 1);
v_onFailure_2164_ = lean_ctor_get(v_inst_2080_, 2);
lean_inc_ref(v_onFailure_2164_);
lean_dec_ref(v_inst_2080_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2165_, 0, v___y_2089_);
lean_closure_set(v___f_2165_, 1, v___f_2081_);
switch(lean_obj_tag(v_err_2163_))
{
case 0:
{
lean_object* v___x_2173_; 
v___x_2173_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2167_ = v___x_2173_;
goto v___jp_2166_;
}
case 1:
{
lean_object* v___x_2174_; 
v___x_2174_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2167_ = v___x_2174_;
goto v___jp_2166_;
}
case 2:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2167_ = v___x_2175_;
goto v___jp_2166_;
}
case 3:
{
lean_object* v___x_2176_; 
v___x_2176_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2167_ = v___x_2176_;
goto v___jp_2166_;
}
case 4:
{
lean_object* v___x_2177_; 
v___x_2177_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2167_ = v___x_2177_;
goto v___jp_2166_;
}
case 5:
{
lean_object* v___x_2178_; 
v___x_2178_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2167_ = v___x_2178_;
goto v___jp_2166_;
}
case 6:
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2167_ = v___x_2179_;
goto v___jp_2166_;
}
case 7:
{
lean_object* v___x_2180_; 
v___x_2180_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2167_ = v___x_2180_;
goto v___jp_2166_;
}
case 8:
{
lean_object* v___x_2181_; 
v___x_2181_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2167_ = v___x_2181_;
goto v___jp_2166_;
}
case 9:
{
lean_object* v___x_2182_; 
v___x_2182_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2167_ = v___x_2182_;
goto v___jp_2166_;
}
case 10:
{
lean_object* v___x_2183_; 
v___x_2183_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2167_ = v___x_2183_;
goto v___jp_2166_;
}
default: 
{
lean_object* v_message_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_message_2184_ = lean_ctor_get(v_err_2163_, 0);
lean_inc_ref(v_message_2184_);
lean_dec_ref_known(v_err_2163_, 1);
v___x_2185_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2186_ = lean_string_append(v___x_2185_, v_message_2184_);
lean_dec_ref(v_message_2184_);
v___y_2167_ = v___x_2186_;
goto v___jp_2166_;
}
}
v___jp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2168_ = lean_mk_io_user_error(v___y_2167_);
v___x_2169_ = lean_apply_3(v_onFailure_2164_, v_handler_2082_, v___x_2168_, lean_box(0));
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = 0;
v___x_2172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2170_, v___x_2171_, v___x_2169_, v___f_2165_);
return v___x_2172_;
}
}
case 4:
{
lean_object* v_requestStream_2187_; lean_object* v___x_2188_; lean_object* v___f_2189_; lean_object* v___f_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_5177__overap_2193_; lean_object* v___x_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref(v_connectionContext_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v___f_2084_);
lean_dec(v_handler_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v_inst_2080_);
lean_dec_ref(v_config_2079_);
v_requestStream_2187_ = lean_ctor_get(v___y_2089_, 1);
lean_inc_ref_n(v_requestStream_2187_, 2);
v___x_2188_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2189_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2190_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2191_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2192_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2192_, 0, lean_box(0));
lean_closure_set(v___x_2192_, 1, lean_box(0));
lean_closure_set(v___x_2192_, 2, lean_box(0));
lean_closure_set(v___x_2192_, 3, v___x_2188_);
lean_closure_set(v___x_2192_, 4, lean_box(0));
lean_closure_set(v___x_2192_, 5, lean_box(0));
lean_closure_set(v___x_2192_, 6, v___x_2191_);
lean_closure_set(v___x_2192_, 7, v___f_2083_);
v___x_5177__overap_2193_ = l_Std_Mutex_atomically___redArg(v___x_2188_, v___f_2189_, v___f_2190_, v_requestStream_2187_, v___x_2192_);
v___x_2194_ = lean_apply_1(v___x_5177__overap_2193_, lean_box(0));
lean_inc_ref(v___y_2089_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2195_, 0, v___y_2089_);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2196_, 0, v_requestStream_2187_);
lean_closure_set(v___f_2196_, 1, v___f_2195_);
lean_closure_set(v___f_2196_, 2, v___y_2089_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = 0;
v___x_2199_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2197_, v___x_2198_, v___x_2194_, v___f_2196_);
return v___x_2199_;
}
case 6:
{
lean_object* v_machine_2200_; lean_object* v_requestStream_2201_; lean_object* v_respStream_2202_; uint8_t v_requiresData_2203_; lean_object* v_expectData_2204_; lean_object* v_pendingHead_2205_; lean_object* v___x_2206_; lean_object* v___f_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_5198__overap_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___f_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___f_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v_connectionContext_2086_);
lean_dec_ref(v___f_2083_);
lean_dec(v_handler_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v_inst_2080_);
v_machine_2200_ = lean_ctor_get(v___y_2089_, 0);
lean_inc_ref(v_machine_2200_);
v_requestStream_2201_ = lean_ctor_get(v___y_2089_, 1);
lean_inc_ref_n(v_requestStream_2201_, 2);
v_respStream_2202_ = lean_ctor_get(v___y_2089_, 6);
lean_inc(v_respStream_2202_);
v_requiresData_2203_ = lean_ctor_get_uint8(v___y_2089_, sizeof(void*)*9);
v_expectData_2204_ = lean_ctor_get(v___y_2089_, 7);
lean_inc(v_expectData_2204_);
v_pendingHead_2205_ = lean_ctor_get(v___y_2089_, 8);
lean_inc(v_pendingHead_2205_);
lean_dec_ref(v___y_2089_);
v___x_2206_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2207_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2208_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2209_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2210_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2210_, 0, lean_box(0));
lean_closure_set(v___x_2210_, 1, lean_box(0));
lean_closure_set(v___x_2210_, 2, lean_box(0));
lean_closure_set(v___x_2210_, 3, v___x_2206_);
lean_closure_set(v___x_2210_, 4, lean_box(0));
lean_closure_set(v___x_2210_, 5, lean_box(0));
lean_closure_set(v___x_2210_, 6, v___x_2209_);
lean_closure_set(v___x_2210_, 7, v___f_2084_);
v___x_5198__overap_2211_ = l_Std_Mutex_atomically___redArg(v___x_2206_, v___f_2207_, v___f_2208_, v_requestStream_2201_, v___x_2210_);
v___x_2212_ = lean_apply_1(v___x_5198__overap_2211_, lean_box(0));
v___x_2213_ = lean_box(v_requiresData_2203_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2214_, 0, v_config_2079_);
lean_closure_set(v___f_2214_, 1, v_machine_2200_);
lean_closure_set(v___f_2214_, 2, v___x_2213_);
lean_closure_set(v___f_2214_, 3, v_expectData_2204_);
lean_closure_set(v___f_2214_, 4, v_pendingHead_2205_);
v___f_2215_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2215_, 0, v___f_2214_);
lean_inc_ref(v___f_2215_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2216_, 0, v___f_2215_);
v___f_2217_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2217_, 0, v_respStream_2202_);
lean_closure_set(v___f_2217_, 1, v_inst_2085_);
lean_closure_set(v___f_2217_, 2, v___f_2216_);
lean_closure_set(v___f_2217_, 3, v___f_2215_);
lean_inc_ref(v___f_2217_);
v___f_2218_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2218_, 0, v___f_2217_);
v___f_2219_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2219_, 0, v_requestStream_2201_);
lean_closure_set(v___f_2219_, 1, v___f_2218_);
lean_closure_set(v___f_2219_, 2, v___f_2217_);
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = 0;
v___x_2222_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2220_, v___x_2221_, v___x_2212_, v___f_2219_);
return v___x_2222_;
}
case 7:
{
lean_object* v_pendingHead_2223_; 
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v___f_2084_);
lean_dec_ref(v___f_2083_);
lean_dec_ref(v___f_2081_);
v_pendingHead_2223_ = lean_ctor_get(v___y_2089_, 8);
if (lean_obj_tag(v_pendingHead_2223_) == 1)
{
lean_object* v_machine_2224_; lean_object* v_requestStream_2225_; lean_object* v_keepAliveTimeout_2226_; lean_object* v_currentTimeout_2227_; lean_object* v_headerTimeout_2228_; lean_object* v_response_2229_; lean_object* v_respStream_2230_; uint8_t v_requiresData_2231_; lean_object* v_expectData_2232_; uint8_t v_handlerDispatched_2233_; lean_object* v_val_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; 
lean_inc_ref(v_pendingHead_2223_);
v_machine_2224_ = lean_ctor_get(v___y_2089_, 0);
lean_inc_ref(v_machine_2224_);
v_requestStream_2225_ = lean_ctor_get(v___y_2089_, 1);
lean_inc_ref(v_requestStream_2225_);
v_keepAliveTimeout_2226_ = lean_ctor_get(v___y_2089_, 2);
lean_inc(v_keepAliveTimeout_2226_);
v_currentTimeout_2227_ = lean_ctor_get(v___y_2089_, 3);
lean_inc(v_currentTimeout_2227_);
v_headerTimeout_2228_ = lean_ctor_get(v___y_2089_, 4);
lean_inc(v_headerTimeout_2228_);
v_response_2229_ = lean_ctor_get(v___y_2089_, 5);
lean_inc_ref(v_response_2229_);
v_respStream_2230_ = lean_ctor_get(v___y_2089_, 6);
lean_inc(v_respStream_2230_);
v_requiresData_2231_ = lean_ctor_get_uint8(v___y_2089_, sizeof(void*)*9);
v_expectData_2232_ = lean_ctor_get(v___y_2089_, 7);
lean_inc(v_expectData_2232_);
v_handlerDispatched_2233_ = lean_ctor_get_uint8(v___y_2089_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2089_);
v_val_2234_ = lean_ctor_get(v_pendingHead_2223_, 0);
lean_inc(v_val_2234_);
v___x_2235_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2080_, v_handler_2082_, v_machine_2224_, v_val_2234_, v_config_2079_, v_connectionContext_2086_);
v___x_2236_ = lean_box(v_requiresData_2231_);
v___x_2237_ = lean_box(v_handlerDispatched_2233_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2238_, 0, v_requestStream_2225_);
lean_closure_set(v___f_2238_, 1, v_keepAliveTimeout_2226_);
lean_closure_set(v___f_2238_, 2, v_currentTimeout_2227_);
lean_closure_set(v___f_2238_, 3, v_headerTimeout_2228_);
lean_closure_set(v___f_2238_, 4, v_response_2229_);
lean_closure_set(v___f_2238_, 5, v_respStream_2230_);
lean_closure_set(v___f_2238_, 6, v___x_2236_);
lean_closure_set(v___f_2238_, 7, v_expectData_2232_);
lean_closure_set(v___f_2238_, 8, v___x_2237_);
lean_closure_set(v___f_2238_, 9, v_pendingHead_2223_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = 0;
v___x_2241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2239_, v___x_2240_, v___x_2235_, v___f_2238_);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v_connectionContext_2086_);
lean_dec(v_handler_2082_);
lean_dec_ref(v_inst_2080_);
lean_dec_ref(v_config_2079_);
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___y_2089_);
v___x_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
default: 
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec(v_a_2087_);
lean_dec_ref(v_connectionContext_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v___f_2084_);
lean_dec_ref(v___f_2083_);
lean_dec(v_handler_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v_inst_2080_);
lean_dec_ref(v_config_2079_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___y_2089_);
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2248_, lean_object* v_inst_2249_, lean_object* v___f_2250_, lean_object* v_handler_2251_, lean_object* v___f_2252_, lean_object* v___f_2253_, lean_object* v_inst_2254_, lean_object* v_connectionContext_2255_, lean_object* v_a_2256_, lean_object* v_x_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2248_, v_inst_2249_, v___f_2250_, v_handler_2251_, v___f_2252_, v___f_2253_, v_inst_2254_, v_connectionContext_2255_, v_a_2256_, v_x_2257_, v___y_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_x_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_handler_2271_, lean_object* v_config_2272_, lean_object* v_connectionContext_2273_, lean_object* v_events_2274_, lean_object* v_state_2275_){
_start:
{
lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; size_t v_sz_2280_; size_t v___x_2281_; lean_object* v___x_4110__overap_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
v___f_2277_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2278_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2278_, 0, v_config_2272_);
lean_closure_set(v___f_2278_, 1, v_inst_2269_);
lean_closure_set(v___f_2278_, 2, v___f_2277_);
lean_closure_set(v___f_2278_, 3, v_handler_2271_);
lean_closure_set(v___f_2278_, 4, v___f_2277_);
lean_closure_set(v___f_2278_, 5, v___f_2277_);
lean_closure_set(v___f_2278_, 6, v_inst_2270_);
lean_closure_set(v___f_2278_, 7, v_connectionContext_2273_);
v___x_2279_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2280_ = lean_array_size(v_events_2274_);
v___x_2281_ = ((size_t)0ULL);
v___x_4110__overap_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2279_, v_events_2274_, v___f_2278_, v_sz_2280_, v___x_2281_, v_state_2275_);
v___x_2283_ = lean_apply_1(v___x_4110__overap_2282_, lean_box(0));
v___f_2284_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = 0;
v___x_2287_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2285_, v___x_2286_, v___x_2283_, v___f_2284_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_handler_2290_, lean_object* v_config_2291_, lean_object* v_connectionContext_2292_, lean_object* v_events_2293_, lean_object* v_state_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2288_, v_inst_2289_, v_handler_2290_, v_config_2291_, v_connectionContext_2292_, v_events_2293_, v_state_2294_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2297_, lean_object* v_00_u03b2_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_handler_2301_, lean_object* v_config_2302_, lean_object* v_connectionContext_2303_, lean_object* v_events_2304_, lean_object* v_state_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2299_, v_inst_2300_, v_handler_2301_, v_config_2302_, v_connectionContext_2303_, v_events_2304_, v_state_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2308_, lean_object* v_00_u03b2_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_handler_2312_, lean_object* v_config_2313_, lean_object* v_connectionContext_2314_, lean_object* v_events_2315_, lean_object* v_state_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2308_, v_00_u03b2_2309_, v_inst_2310_, v_inst_2311_, v_handler_2312_, v_config_2313_, v_connectionContext_2314_, v_events_2315_, v_state_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2319_){
_start:
{
if (lean_obj_tag(v_x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v_x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v_x_2319_, 1);
v___x_2321_ = lean_task_pure(v_a_2320_);
return v___x_2321_;
}
else
{
lean_object* v_a_2322_; 
v_a_2322_ = lean_ctor_get(v_x_2319_, 0);
lean_inc_ref(v_a_2322_);
lean_dec_ref_known(v_x_2319_, 1);
return v_a_2322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2323_, lean_object* v_requestStream_2324_, lean_object* v_keepAliveTimeout_2325_, lean_object* v_currentTimeout_2326_, lean_object* v_headerTimeout_2327_, lean_object* v_response_2328_, lean_object* v_respStream_2329_, uint8_t v_requiresData_2330_, lean_object* v_expectData_2331_, lean_object* v_x_2332_){
_start:
{
if (lean_obj_tag(v_x_2332_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_expectData_2331_);
lean_dec(v_respStream_2329_);
lean_dec_ref(v_response_2328_);
lean_dec(v_headerTimeout_2327_);
lean_dec(v_currentTimeout_2326_);
lean_dec(v_keepAliveTimeout_2325_);
lean_dec_ref(v_requestStream_2324_);
lean_dec_ref(v_machine_2323_);
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
lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2353_; 
v_isSharedCheck_2353_ = !lean_is_exclusive(v_x_2332_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v_x_2332_, 0);
lean_dec(v_unused_2354_);
v___x_2344_ = v_x_2332_;
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
else
{
lean_dec(v_x_2332_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2346_ = 1;
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2348_, 0, v_machine_2323_);
lean_ctor_set(v___x_2348_, 1, v_requestStream_2324_);
lean_ctor_set(v___x_2348_, 2, v_keepAliveTimeout_2325_);
lean_ctor_set(v___x_2348_, 3, v_currentTimeout_2326_);
lean_ctor_set(v___x_2348_, 4, v_headerTimeout_2327_);
lean_ctor_set(v___x_2348_, 5, v_response_2328_);
lean_ctor_set(v___x_2348_, 6, v_respStream_2329_);
lean_ctor_set(v___x_2348_, 7, v_expectData_2331_);
lean_ctor_set(v___x_2348_, 8, v___x_2347_);
lean_ctor_set_uint8(v___x_2348_, sizeof(void*)*9, v_requiresData_2330_);
lean_ctor_set_uint8(v___x_2348_, sizeof(void*)*9 + 1, v___x_2346_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2348_);
v___x_2350_ = v___x_2344_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2355_, lean_object* v_requestStream_2356_, lean_object* v_keepAliveTimeout_2357_, lean_object* v_currentTimeout_2358_, lean_object* v_headerTimeout_2359_, lean_object* v_response_2360_, lean_object* v_respStream_2361_, lean_object* v_requiresData_2362_, lean_object* v_expectData_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_){
_start:
{
uint8_t v_requiresData_boxed_2366_; lean_object* v_res_2367_; 
v_requiresData_boxed_2366_ = lean_unbox(v_requiresData_2362_);
v_res_2367_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2355_, v_requestStream_2356_, v_keepAliveTimeout_2357_, v_currentTimeout_2358_, v_headerTimeout_2359_, v_response_2360_, v_respStream_2361_, v_requiresData_boxed_2366_, v_expectData_2363_, v_x_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2368_, lean_object* v_response_2369_, lean_object* v___x_2370_, lean_object* v___f_2371_, lean_object* v_x_2372_){
_start:
{
if (lean_obj_tag(v_x_2372_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v___f_2371_);
lean_dec(v___x_2370_);
lean_dec_ref(v_response_2369_);
lean_dec_ref(v_toFunctor_2368_);
v_a_2374_ = lean_ctor_get(v_x_2372_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_x_2372_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2376_ = v_x_2372_;
v_isShared_2377_ = v_isSharedCheck_2382_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v_x_2372_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2382_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2397_; 
v_a_2383_ = lean_ctor_get(v_x_2372_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_x_2372_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2385_ = v_x_2372_;
v_isShared_2386_ = v_isSharedCheck_2397_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v_x_2372_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2397_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2387_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2387_, 0, lean_box(0));
lean_closure_set(v___x_2387_, 1, lean_box(0));
lean_closure_set(v___x_2387_, 2, v_toFunctor_2368_);
v___x_2388_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2388_, 0, lean_box(0));
lean_closure_set(v___x_2388_, 1, v_response_2369_);
v___x_2389_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2389_, 0, lean_box(0));
lean_closure_set(v___x_2389_, 1, lean_box(0));
lean_closure_set(v___x_2389_, 2, lean_box(0));
lean_closure_set(v___x_2389_, 3, v___x_2387_);
lean_closure_set(v___x_2389_, 4, v___x_2388_);
v___x_2390_ = 0;
lean_inc(v___x_2370_);
v___x_2391_ = l_BaseIO_chainTask___redArg(v_a_2383_, v___x_2389_, v___x_2370_, v___x_2390_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2391_);
v___x_2393_ = v___x_2385_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
v___x_2395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2370_, v___x_2390_, v___x_2394_, v___f_2371_);
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2398_, lean_object* v_response_2399_, lean_object* v___x_2400_, lean_object* v___f_2401_, lean_object* v_x_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2398_, v_response_2399_, v___x_2400_, v___f_2401_, v_x_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2406_, lean_object* v_handler_2407_, lean_object* v_extensions_2408_, lean_object* v_connectionContext_2409_, lean_object* v_state_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_toApplicative_2413_; lean_object* v_pendingHead_2414_; 
v___x_2412_ = l_instMonadBaseIO;
v_toApplicative_2413_ = lean_ctor_get(v___x_2412_, 0);
v_pendingHead_2414_ = lean_ctor_get(v_state_2410_, 8);
lean_inc(v_pendingHead_2414_);
if (lean_obj_tag(v_pendingHead_2414_) == 1)
{
lean_object* v_toFunctor_2415_; lean_object* v_machine_2416_; lean_object* v_requestStream_2417_; lean_object* v_keepAliveTimeout_2418_; lean_object* v_currentTimeout_2419_; lean_object* v_headerTimeout_2420_; lean_object* v_response_2421_; lean_object* v_respStream_2422_; uint8_t v_requiresData_2423_; lean_object* v_expectData_2424_; lean_object* v_val_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2447_; 
v_toFunctor_2415_ = lean_ctor_get(v_toApplicative_2413_, 0);
v_machine_2416_ = lean_ctor_get(v_state_2410_, 0);
lean_inc_ref(v_machine_2416_);
v_requestStream_2417_ = lean_ctor_get(v_state_2410_, 1);
lean_inc_ref(v_requestStream_2417_);
v_keepAliveTimeout_2418_ = lean_ctor_get(v_state_2410_, 2);
lean_inc(v_keepAliveTimeout_2418_);
v_currentTimeout_2419_ = lean_ctor_get(v_state_2410_, 3);
lean_inc(v_currentTimeout_2419_);
v_headerTimeout_2420_ = lean_ctor_get(v_state_2410_, 4);
lean_inc(v_headerTimeout_2420_);
v_response_2421_ = lean_ctor_get(v_state_2410_, 5);
lean_inc_ref(v_response_2421_);
v_respStream_2422_ = lean_ctor_get(v_state_2410_, 6);
lean_inc(v_respStream_2422_);
v_requiresData_2423_ = lean_ctor_get_uint8(v_state_2410_, sizeof(void*)*9);
v_expectData_2424_ = lean_ctor_get(v_state_2410_, 7);
lean_inc(v_expectData_2424_);
lean_dec_ref(v_state_2410_);
v_val_2425_ = lean_ctor_get(v_pendingHead_2414_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_pendingHead_2414_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2427_ = v_pendingHead_2414_;
v_isShared_2428_ = v_isSharedCheck_2447_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_val_2425_);
lean_dec(v_pendingHead_2414_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2447_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_onRequest_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; lean_object* v___f_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v_onRequest_2429_ = lean_ctor_get(v_inst_2406_, 1);
lean_inc_ref(v_onRequest_2429_);
lean_dec_ref(v_inst_2406_);
lean_inc_ref(v_requestStream_2417_);
v___x_2430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2430_, 0, v_val_2425_);
lean_ctor_set(v___x_2430_, 1, v_requestStream_2417_);
lean_ctor_set(v___x_2430_, 2, v_extensions_2408_);
v___x_2431_ = lean_apply_3(v_onRequest_2429_, v_handler_2407_, v___x_2430_, v_connectionContext_2409_);
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2433_, 0, lean_box(0));
lean_closure_set(v___x_2433_, 1, v___x_2431_);
v___x_2434_ = lean_io_as_task(v___x_2433_, v___x_2432_);
v___f_2435_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2436_ = lean_box(v_requiresData_2423_);
lean_inc_ref(v_response_2421_);
v___f_2437_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2437_, 0, v_machine_2416_);
lean_closure_set(v___f_2437_, 1, v_requestStream_2417_);
lean_closure_set(v___f_2437_, 2, v_keepAliveTimeout_2418_);
lean_closure_set(v___f_2437_, 3, v_currentTimeout_2419_);
lean_closure_set(v___f_2437_, 4, v_headerTimeout_2420_);
lean_closure_set(v___f_2437_, 5, v_response_2421_);
lean_closure_set(v___f_2437_, 6, v_respStream_2422_);
lean_closure_set(v___f_2437_, 7, v___x_2436_);
lean_closure_set(v___f_2437_, 8, v_expectData_2424_);
lean_inc_ref(v_toFunctor_2415_);
v___f_2438_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2438_, 0, v_toFunctor_2415_);
lean_closure_set(v___f_2438_, 1, v_response_2421_);
lean_closure_set(v___f_2438_, 2, v___x_2432_);
lean_closure_set(v___f_2438_, 3, v___f_2437_);
v___x_2439_ = 1;
v___x_2440_ = lean_task_bind(v___x_2434_, v___f_2435_, v___x_2432_, v___x_2439_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2440_);
v___x_2442_ = v___x_2427_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
v___x_2444_ = 0;
v___x_2445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2432_, v___x_2444_, v___x_2443_, v___f_2438_);
return v___x_2445_;
}
}
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec(v_pendingHead_2414_);
lean_dec_ref(v_connectionContext_2409_);
lean_dec(v_extensions_2408_);
lean_dec(v_handler_2407_);
lean_dec_ref(v_inst_2406_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_state_2410_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2450_, lean_object* v_handler_2451_, lean_object* v_extensions_2452_, lean_object* v_connectionContext_2453_, lean_object* v_state_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2450_, v_handler_2451_, v_extensions_2452_, v_connectionContext_2453_, v_state_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2457_, lean_object* v_inst_2458_, lean_object* v_handler_2459_, lean_object* v_extensions_2460_, lean_object* v_connectionContext_2461_, lean_object* v_state_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2458_, v_handler_2459_, v_extensions_2460_, v_connectionContext_2461_, v_state_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2465_, lean_object* v_inst_2466_, lean_object* v_handler_2467_, lean_object* v_extensions_2468_, lean_object* v_connectionContext_2469_, lean_object* v_state_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2465_, v_inst_2466_, v_handler_2467_, v_extensions_2468_, v_connectionContext_2469_, v_state_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2473_, lean_object* v_____r_2474_){
_start:
{
lean_object* v_writer_2476_; lean_object* v_reader_2477_; lean_object* v_config_2478_; lean_object* v_events_2479_; lean_object* v_error_2480_; lean_object* v_instant_2481_; uint8_t v_keepAlive_2482_; uint8_t v_forcedFlush_2483_; uint8_t v_pullBodyStalled_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2511_; 
v_writer_2476_ = lean_ctor_get(v_machine_2473_, 1);
v_reader_2477_ = lean_ctor_get(v_machine_2473_, 0);
v_config_2478_ = lean_ctor_get(v_machine_2473_, 2);
v_events_2479_ = lean_ctor_get(v_machine_2473_, 3);
v_error_2480_ = lean_ctor_get(v_machine_2473_, 4);
v_instant_2481_ = lean_ctor_get(v_machine_2473_, 5);
v_keepAlive_2482_ = lean_ctor_get_uint8(v_machine_2473_, sizeof(void*)*6);
v_forcedFlush_2483_ = lean_ctor_get_uint8(v_machine_2473_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2484_ = lean_ctor_get_uint8(v_machine_2473_, sizeof(void*)*6 + 2);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_machine_2473_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2486_ = v_machine_2473_;
v_isShared_2487_ = v_isSharedCheck_2511_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_instant_2481_);
lean_inc(v_error_2480_);
lean_inc(v_events_2479_);
lean_inc(v_config_2478_);
lean_inc(v_writer_2476_);
lean_inc(v_reader_2477_);
lean_dec(v_machine_2473_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2511_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v_userData_2488_; lean_object* v_outputData_2489_; lean_object* v_state_2490_; lean_object* v_knownSize_2491_; lean_object* v_messageHead_2492_; uint8_t v_sentMessage_2493_; uint8_t v_omitBody_2494_; lean_object* v_userDataBytes_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2510_; 
v_userData_2488_ = lean_ctor_get(v_writer_2476_, 0);
v_outputData_2489_ = lean_ctor_get(v_writer_2476_, 1);
v_state_2490_ = lean_ctor_get(v_writer_2476_, 2);
v_knownSize_2491_ = lean_ctor_get(v_writer_2476_, 3);
v_messageHead_2492_ = lean_ctor_get(v_writer_2476_, 4);
v_sentMessage_2493_ = lean_ctor_get_uint8(v_writer_2476_, sizeof(void*)*6);
v_omitBody_2494_ = lean_ctor_get_uint8(v_writer_2476_, sizeof(void*)*6 + 2);
v_userDataBytes_2495_ = lean_ctor_get(v_writer_2476_, 5);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_writer_2476_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2497_ = v_writer_2476_;
v_isShared_2498_ = v_isSharedCheck_2510_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_userDataBytes_2495_);
lean_inc(v_messageHead_2492_);
lean_inc(v_knownSize_2491_);
lean_inc(v_state_2490_);
lean_inc(v_outputData_2489_);
lean_inc(v_userData_2488_);
lean_dec(v_writer_2476_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2510_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
uint8_t v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = 1;
if (v_isShared_2498_ == 0)
{
v___x_2501_ = v___x_2497_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_userData_2488_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_outputData_2489_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_state_2490_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_knownSize_2491_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_messageHead_2492_);
lean_ctor_set(v_reuseFailAlloc_2509_, 5, v_userDataBytes_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*6, v_sentMessage_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*6 + 2, v_omitBody_2494_);
v___x_2501_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2503_; 
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*6 + 1, v___x_2499_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___x_2501_);
v___x_2503_ = v___x_2486_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_reader_2477_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_config_2478_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_events_2479_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_error_2480_);
lean_ctor_set(v_reuseFailAlloc_2508_, 5, v_instant_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*6, v_keepAlive_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*6 + 1, v_forcedFlush_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*6 + 2, v_pullBodyStalled_2484_);
v___x_2503_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2512_, lean_object* v_____r_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2512_, v_____r_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2516_, lean_object* v_x2_2517_){
_start:
{
lean_object* v_data_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_data_2518_ = lean_ctor_get(v_x2_2517_, 0);
v___x_2519_ = lean_byte_array_size(v_data_2518_);
v___x_2520_ = lean_nat_add(v_x1_2516_, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2521_, lean_object* v_x2_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2521_, v_x2_2522_);
lean_dec_ref(v_x2_2522_);
lean_dec(v_x1_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2524_, lean_object* v_machine_2525_, lean_object* v_isClosed_2526_, lean_object* v___f_2527_, lean_object* v___f_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v___y_2532_; 
if (lean_obj_tag(v_x_2529_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v_isClosed_2526_);
lean_dec_ref(v_machine_2525_);
lean_dec(v_body_2524_);
v_a_2537_ = lean_ctor_get(v_x_2529_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_x_2529_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2539_ = v_x_2529_;
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v_x_2529_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2613_; 
v_a_2546_ = lean_ctor_get(v_x_2529_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_x_2529_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2548_ = v_x_2529_;
v_isShared_2549_ = v_isSharedCheck_2613_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v_x_2529_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2613_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
if (lean_obj_tag(v_a_2546_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
lean_dec_ref(v___f_2528_);
lean_dec_ref(v___f_2527_);
lean_dec_ref(v_isClosed_2526_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_body_2524_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_machine_2525_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2551_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
else
{
lean_object* v_val_2556_; 
lean_del_object(v___x_2548_);
v_val_2556_ = lean_ctor_get(v_a_2546_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_a_2546_, 1);
if (lean_obj_tag(v_val_2556_) == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; 
lean_dec_ref(v___f_2528_);
lean_dec_ref(v_machine_2525_);
v___x_2557_ = lean_apply_2(v_isClosed_2526_, v_body_2524_, lean_box(0));
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = 0;
v___x_2560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2558_, v___x_2559_, v___x_2557_, v___f_2527_);
return v___x_2560_;
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
lean_dec_ref(v___f_2527_);
lean_dec_ref(v_isClosed_2526_);
v_val_2561_ = lean_ctor_get(v_val_2556_, 0);
lean_inc(v_val_2561_);
lean_dec_ref_known(v_val_2556_, 1);
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = lean_mk_empty_array_with_capacity(v___x_2562_);
v___x_2564_ = lean_array_push(v___x_2563_, v_val_2561_);
v___x_2565_ = lean_array_get_size(v___x_2564_);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = lean_nat_dec_eq(v___x_2565_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v_reader_2568_; lean_object* v_writer_2569_; lean_object* v_config_2570_; lean_object* v_events_2571_; lean_object* v_error_2572_; lean_object* v_instant_2573_; uint8_t v_keepAlive_2574_; uint8_t v_forcedFlush_2575_; uint8_t v_pullBodyStalled_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2612_; 
v_reader_2568_ = lean_ctor_get(v_machine_2525_, 0);
v_writer_2569_ = lean_ctor_get(v_machine_2525_, 1);
v_config_2570_ = lean_ctor_get(v_machine_2525_, 2);
v_events_2571_ = lean_ctor_get(v_machine_2525_, 3);
v_error_2572_ = lean_ctor_get(v_machine_2525_, 4);
v_instant_2573_ = lean_ctor_get(v_machine_2525_, 5);
v_keepAlive_2574_ = lean_ctor_get_uint8(v_machine_2525_, sizeof(void*)*6);
v_forcedFlush_2575_ = lean_ctor_get_uint8(v_machine_2525_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2576_ = lean_ctor_get_uint8(v_machine_2525_, sizeof(void*)*6 + 2);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_machine_2525_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2578_ = v_machine_2525_;
v_isShared_2579_ = v_isSharedCheck_2612_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_instant_2573_);
lean_inc(v_error_2572_);
lean_inc(v_events_2571_);
lean_inc(v_config_2570_);
lean_inc(v_writer_2569_);
lean_inc(v_reader_2568_);
lean_dec(v_machine_2525_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2612_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___y_2581_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2604_ = lean_nat_dec_lt(v___x_2566_, v___x_2565_);
if (v___x_2604_ == 0)
{
lean_dec_ref(v___f_2528_);
v___y_2581_ = v___x_2566_;
goto v___jp_2580_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_le(v___x_2565_, v___x_2565_);
if (v___x_2605_ == 0)
{
if (v___x_2604_ == 0)
{
lean_dec_ref(v___f_2528_);
v___y_2581_ = v___x_2566_;
goto v___jp_2580_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = lean_usize_of_nat(v___x_2565_);
lean_inc_ref(v___x_2564_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2603_, v___f_2528_, v___x_2564_, v___x_2606_, v___x_2607_, v___x_2566_);
v___y_2581_ = v___x_2608_;
goto v___jp_2580_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2565_);
lean_inc_ref(v___x_2564_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2603_, v___f_2528_, v___x_2564_, v___x_2609_, v___x_2610_, v___x_2566_);
v___y_2581_ = v___x_2611_;
goto v___jp_2580_;
}
}
v___jp_2580_:
{
lean_object* v_userData_2582_; lean_object* v_outputData_2583_; lean_object* v_state_2584_; lean_object* v_knownSize_2585_; lean_object* v_messageHead_2586_; uint8_t v_sentMessage_2587_; uint8_t v_userClosedBody_2588_; uint8_t v_omitBody_2589_; lean_object* v_userDataBytes_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2602_; 
v_userData_2582_ = lean_ctor_get(v_writer_2569_, 0);
v_outputData_2583_ = lean_ctor_get(v_writer_2569_, 1);
v_state_2584_ = lean_ctor_get(v_writer_2569_, 2);
v_knownSize_2585_ = lean_ctor_get(v_writer_2569_, 3);
v_messageHead_2586_ = lean_ctor_get(v_writer_2569_, 4);
v_sentMessage_2587_ = lean_ctor_get_uint8(v_writer_2569_, sizeof(void*)*6);
v_userClosedBody_2588_ = lean_ctor_get_uint8(v_writer_2569_, sizeof(void*)*6 + 1);
v_omitBody_2589_ = lean_ctor_get_uint8(v_writer_2569_, sizeof(void*)*6 + 2);
v_userDataBytes_2590_ = lean_ctor_get(v_writer_2569_, 5);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_writer_2569_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2592_ = v_writer_2569_;
v_isShared_2593_ = v_isSharedCheck_2602_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_userDataBytes_2590_);
lean_inc(v_messageHead_2586_);
lean_inc(v_knownSize_2585_);
lean_inc(v_state_2584_);
lean_inc(v_outputData_2583_);
lean_inc(v_userData_2582_);
lean_dec(v_writer_2569_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2602_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2594_ = l_Array_append___redArg(v_userData_2582_, v___x_2564_);
lean_dec_ref(v___x_2564_);
v___x_2595_ = lean_nat_add(v_userDataBytes_2590_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec(v_userDataBytes_2590_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 5, v___x_2595_);
lean_ctor_set(v___x_2592_, 0, v___x_2594_);
v___x_2597_ = v___x_2592_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_outputData_2583_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_state_2584_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_knownSize_2585_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_messageHead_2586_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v___x_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*6, v_sentMessage_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*6 + 1, v_userClosedBody_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*6 + 2, v_omitBody_2589_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2599_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v___x_2597_);
v___x_2599_ = v___x_2578_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_reader_2568_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_config_2570_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_events_2571_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_error_2572_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_instant_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*6, v_keepAlive_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*6 + 1, v_forcedFlush_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*6 + 2, v_pullBodyStalled_2576_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
v___y_2532_ = v___x_2599_;
goto v___jp_2531_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2564_);
lean_dec_ref(v___f_2528_);
v___y_2532_ = v_machine_2525_;
goto v___jp_2531_;
}
}
}
}
}
v___jp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_body_2524_);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2614_, lean_object* v_machine_2615_, lean_object* v_isClosed_2616_, lean_object* v___f_2617_, lean_object* v___f_2618_, lean_object* v_x_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2614_, v_machine_2615_, v_isClosed_2616_, v___f_2617_, v___f_2618_, v_x_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2623_, lean_object* v_machine_2624_, lean_object* v_body_2625_){
_start:
{
lean_object* v_close_2627_; lean_object* v_isClosed_2628_; lean_object* v_tryRecv_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v___f_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; 
v_close_2627_ = lean_ctor_get(v_inst_2623_, 1);
lean_inc_ref(v_close_2627_);
v_isClosed_2628_ = lean_ctor_get(v_inst_2623_, 2);
lean_inc_ref(v_isClosed_2628_);
v_tryRecv_2629_ = lean_ctor_get(v_inst_2623_, 4);
lean_inc_ref(v_tryRecv_2629_);
lean_dec_ref(v_inst_2623_);
lean_inc_n(v_body_2625_, 2);
v___x_2630_ = lean_apply_2(v_tryRecv_2629_, v_body_2625_, lean_box(0));
lean_inc_ref(v_machine_2624_);
v___f_2631_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2631_, 0, v_machine_2624_);
lean_inc_ref(v___f_2631_);
v___f_2632_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2632_, 0, v___f_2631_);
v___f_2633_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2633_, 0, v_close_2627_);
lean_closure_set(v___f_2633_, 1, v_body_2625_);
lean_closure_set(v___f_2633_, 2, v___f_2632_);
lean_closure_set(v___f_2633_, 3, v___f_2631_);
v___f_2634_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2635_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2635_, 0, v_body_2625_);
lean_closure_set(v___f_2635_, 1, v_machine_2624_);
lean_closure_set(v___f_2635_, 2, v_isClosed_2628_);
lean_closure_set(v___f_2635_, 3, v___f_2633_);
lean_closure_set(v___f_2635_, 4, v___f_2634_);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = 0;
v___x_2638_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2636_, v___x_2637_, v___x_2630_, v___f_2635_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2639_, lean_object* v_machine_2640_, lean_object* v_body_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2639_, v_machine_2640_, v_body_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2644_, lean_object* v_inst_2645_, lean_object* v_machine_2646_, lean_object* v_body_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2645_, v_machine_2646_, v_body_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2650_, lean_object* v_inst_2651_, lean_object* v_machine_2652_, lean_object* v_body_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2650_, v_inst_2651_, v_machine_2652_, v_body_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2662_, lean_object* v_____r_2663_, lean_object* v_st_2664_){
_start:
{
lean_object* v_machine_2666_; lean_object* v_requestStream_2667_; lean_object* v_keepAliveTimeout_2668_; lean_object* v_currentTimeout_2669_; lean_object* v_headerTimeout_2670_; lean_object* v_response_2671_; lean_object* v_respStream_2672_; uint8_t v_requiresData_2673_; lean_object* v_expectData_2674_; uint8_t v_handlerDispatched_2675_; lean_object* v_pendingHead_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2758_; 
v_machine_2666_ = lean_ctor_get(v_st_2664_, 0);
v_requestStream_2667_ = lean_ctor_get(v_st_2664_, 1);
v_keepAliveTimeout_2668_ = lean_ctor_get(v_st_2664_, 2);
v_currentTimeout_2669_ = lean_ctor_get(v_st_2664_, 3);
v_headerTimeout_2670_ = lean_ctor_get(v_st_2664_, 4);
v_response_2671_ = lean_ctor_get(v_st_2664_, 5);
v_respStream_2672_ = lean_ctor_get(v_st_2664_, 6);
v_requiresData_2673_ = lean_ctor_get_uint8(v_st_2664_, sizeof(void*)*9);
v_expectData_2674_ = lean_ctor_get(v_st_2664_, 7);
v_handlerDispatched_2675_ = lean_ctor_get_uint8(v_st_2664_, sizeof(void*)*9 + 1);
v_pendingHead_2676_ = lean_ctor_get(v_st_2664_, 8);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_st_2664_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2678_ = v_st_2664_;
v_isShared_2679_ = v_isSharedCheck_2758_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_pendingHead_2676_);
lean_inc(v_expectData_2674_);
lean_inc(v_respStream_2672_);
lean_inc(v_response_2671_);
lean_inc(v_headerTimeout_2670_);
lean_inc(v_currentTimeout_2669_);
lean_inc(v_keepAliveTimeout_2668_);
lean_inc(v_requestStream_2667_);
lean_inc(v_machine_2666_);
lean_dec(v_st_2664_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2758_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___y_2681_; lean_object* v_reader_2690_; lean_object* v_state_2691_; 
v_reader_2690_ = lean_ctor_get(v_machine_2666_, 0);
lean_inc_ref(v_reader_2690_);
v_state_2691_ = lean_ctor_get(v_reader_2690_, 0);
lean_inc(v_state_2691_);
if (lean_obj_tag(v_state_2691_) == 6)
{
lean_dec_ref(v_reader_2690_);
lean_dec_ref(v_val_2662_);
v___y_2681_ = v_machine_2666_;
goto v___jp_2680_;
}
else
{
if (lean_obj_tag(v_state_2691_) == 7)
{
lean_dec_ref_known(v_state_2691_, 1);
lean_dec_ref(v_reader_2690_);
lean_dec_ref(v_val_2662_);
v___y_2681_ = v_machine_2666_;
goto v___jp_2680_;
}
else
{
lean_object* v_input_2692_; lean_object* v_writer_2693_; lean_object* v_config_2694_; lean_object* v_events_2695_; lean_object* v_error_2696_; lean_object* v_instant_2697_; uint8_t v_keepAlive_2698_; uint8_t v_forcedFlush_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2756_; 
v_input_2692_ = lean_ctor_get(v_reader_2690_, 1);
lean_inc_ref(v_input_2692_);
v_writer_2693_ = lean_ctor_get(v_machine_2666_, 1);
v_config_2694_ = lean_ctor_get(v_machine_2666_, 2);
v_events_2695_ = lean_ctor_get(v_machine_2666_, 3);
v_error_2696_ = lean_ctor_get(v_machine_2666_, 4);
v_instant_2697_ = lean_ctor_get(v_machine_2666_, 5);
v_keepAlive_2698_ = lean_ctor_get_uint8(v_machine_2666_, sizeof(void*)*6);
v_forcedFlush_2699_ = lean_ctor_get_uint8(v_machine_2666_, sizeof(void*)*6 + 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_machine_2666_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; 
v_unused_2757_ = lean_ctor_get(v_machine_2666_, 0);
lean_dec(v_unused_2757_);
v___x_2701_ = v_machine_2666_;
v_isShared_2702_ = v_isSharedCheck_2756_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_instant_2697_);
lean_inc(v_error_2696_);
lean_inc(v_events_2695_);
lean_inc(v_config_2694_);
lean_inc(v_writer_2693_);
lean_dec(v_machine_2666_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2756_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v_messageHead_2703_; lean_object* v_messageCount_2704_; lean_object* v_bodyBytesRead_2705_; lean_object* v_headerBytesRead_2706_; uint8_t v_noMoreInput_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2753_; 
v_messageHead_2703_ = lean_ctor_get(v_reader_2690_, 2);
v_messageCount_2704_ = lean_ctor_get(v_reader_2690_, 3);
v_bodyBytesRead_2705_ = lean_ctor_get(v_reader_2690_, 4);
v_headerBytesRead_2706_ = lean_ctor_get(v_reader_2690_, 5);
v_noMoreInput_2707_ = lean_ctor_get_uint8(v_reader_2690_, sizeof(void*)*6);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_reader_2690_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; lean_object* v_unused_2755_; 
v_unused_2754_ = lean_ctor_get(v_reader_2690_, 1);
lean_dec(v_unused_2754_);
v_unused_2755_ = lean_ctor_get(v_reader_2690_, 0);
lean_dec(v_unused_2755_);
v___x_2709_ = v_reader_2690_;
v_isShared_2710_ = v_isSharedCheck_2753_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_headerBytesRead_2706_);
lean_inc(v_bodyBytesRead_2705_);
lean_inc(v_messageCount_2704_);
lean_inc(v_messageHead_2703_);
lean_dec(v_reader_2690_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2753_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_array_2711_; lean_object* v_idx_2712_; uint8_t v___x_2713_; lean_object* v___y_2715_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_array_2711_ = lean_ctor_get(v_input_2692_, 0);
lean_inc_ref(v_array_2711_);
v_idx_2712_ = lean_ctor_get(v_input_2692_, 1);
lean_inc(v_idx_2712_);
lean_dec_ref(v_input_2692_);
v___x_2713_ = 0;
v___x_2744_ = lean_byte_array_size(v_array_2711_);
v___x_2745_ = lean_nat_dec_le(v___x_2744_, v_idx_2712_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2746_ = l_ByteArray_extract(v_array_2711_, v_idx_2712_, v___x_2744_);
lean_dec_ref(v_array_2711_);
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = lean_byte_array_size(v___x_2746_);
v___x_2749_ = lean_byte_array_size(v_val_2662_);
v___x_2750_ = lean_byte_array_copy_slice(v_val_2662_, v___x_2747_, v___x_2746_, v___x_2748_, v___x_2749_, v___x_2745_);
lean_dec_ref(v_val_2662_);
v___x_2751_ = l_ByteArray_mkIterator(v___x_2750_);
v___y_2715_ = v___x_2751_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2752_; 
lean_dec(v_idx_2712_);
lean_dec_ref(v_array_2711_);
v___x_2752_ = l_ByteArray_mkIterator(v_val_2662_);
v___y_2715_ = v___x_2752_;
goto v___jp_2714_;
}
v___jp_2714_:
{
lean_object* v_maxHeaderBytes_2716_; lean_object* v_maxStartLineLength_2717_; lean_object* v_maxChunkLineLength_2718_; lean_object* v_maxBodySize_2719_; lean_object* v_array_2720_; lean_object* v_idx_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v_maxHeaderBytes_2716_ = lean_ctor_get(v_config_2694_, 2);
v_maxStartLineLength_2717_ = lean_ctor_get(v_config_2694_, 5);
v_maxChunkLineLength_2718_ = lean_ctor_get(v_config_2694_, 13);
v_maxBodySize_2719_ = lean_ctor_get(v_config_2694_, 15);
v_array_2720_ = lean_ctor_get(v___y_2715_, 0);
v_idx_2721_ = lean_ctor_get(v___y_2715_, 1);
v___x_2722_ = lean_nat_add(v_maxBodySize_2719_, v_maxHeaderBytes_2716_);
v___x_2723_ = lean_nat_add(v___x_2722_, v_maxStartLineLength_2717_);
lean_dec(v___x_2722_);
v___x_2724_ = lean_nat_add(v___x_2723_, v_maxChunkLineLength_2718_);
lean_dec(v___x_2723_);
v___x_2725_ = lean_byte_array_size(v_array_2720_);
v___x_2726_ = lean_nat_sub(v___x_2725_, v_idx_2721_);
v___x_2727_ = lean_nat_dec_lt(v___x_2724_, v___x_2726_);
lean_dec(v___x_2726_);
lean_dec(v___x_2724_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2729_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 1, v___y_2715_);
v___x_2729_ = v___x_2709_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_state_2691_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___y_2715_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_messageHead_2703_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_messageCount_2704_);
lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_bodyBytesRead_2705_);
lean_ctor_set(v_reuseFailAlloc_2733_, 5, v_headerBytesRead_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2733_, sizeof(void*)*6, v_noMoreInput_2707_);
v___x_2729_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v_machine_2731_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2729_);
v_machine_2731_ = v___x_2701_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_writer_2693_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_config_2694_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_events_2695_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_error_2696_);
lean_ctor_set(v_reuseFailAlloc_2732_, 5, v_instant_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2732_, sizeof(void*)*6, v_keepAlive_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2732_, sizeof(void*)*6 + 1, v_forcedFlush_2699_);
v_machine_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_ctor_set_uint8(v_machine_2731_, sizeof(void*)*6 + 2, v___x_2713_);
v___y_2681_ = v_machine_2731_;
goto v___jp_2680_;
}
}
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec(v_error_2696_);
lean_dec(v_state_2691_);
v___x_2734_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2735_ = lean_array_push(v_events_2695_, v___x_2734_);
v___x_2736_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 1, v___y_2715_);
lean_ctor_set(v___x_2709_, 0, v___x_2736_);
v___x_2738_ = v___x_2709_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___y_2715_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_messageHead_2703_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_messageCount_2704_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_bodyBytesRead_2705_);
lean_ctor_set(v_reuseFailAlloc_2743_, 5, v_headerBytesRead_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2743_, sizeof(void*)*6, v_noMoreInput_2707_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 4, v___x_2739_);
lean_ctor_set(v___x_2701_, 3, v___x_2735_);
lean_ctor_set(v___x_2701_, 0, v___x_2738_);
v___x_2741_ = v___x_2701_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_writer_2693_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_config_2694_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_instant_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2742_, sizeof(void*)*6, v_keepAlive_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2742_, sizeof(void*)*6 + 1, v_forcedFlush_2699_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*6 + 2, v___x_2713_);
v___y_2681_ = v___x_2741_;
goto v___jp_2680_;
}
}
}
}
}
}
}
}
v___jp_2680_:
{
lean_object* v___x_2683_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___y_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___y_2681_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_requestStream_2667_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v_keepAliveTimeout_2668_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v_currentTimeout_2669_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v_headerTimeout_2670_);
lean_ctor_set(v_reuseFailAlloc_2689_, 5, v_response_2671_);
lean_ctor_set(v_reuseFailAlloc_2689_, 6, v_respStream_2672_);
lean_ctor_set(v_reuseFailAlloc_2689_, 7, v_expectData_2674_);
lean_ctor_set(v_reuseFailAlloc_2689_, 8, v_pendingHead_2676_);
lean_ctor_set_uint8(v_reuseFailAlloc_2689_, sizeof(void*)*9, v_requiresData_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2689_, sizeof(void*)*9 + 1, v_handlerDispatched_2675_);
v___x_2683_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2684_ = 0;
v___x_2685_ = lean_box(v___x_2684_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2683_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2759_, lean_object* v_____r_2760_, lean_object* v_st_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2759_, v_____r_2760_, v_st_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2764_, lean_object* v_machine_2765_, lean_object* v_requestStream_2766_, lean_object* v_currentTimeout_2767_, lean_object* v_response_2768_, lean_object* v_respStream_2769_, uint8_t v_requiresData_2770_, lean_object* v_expectData_2771_, uint8_t v_handlerDispatched_2772_, lean_object* v_pendingHead_2773_, lean_object* v___f_2774_, lean_object* v_x_2775_){
_start:
{
if (lean_obj_tag(v_x_2775_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v___f_2774_);
lean_dec(v_pendingHead_2773_);
lean_dec(v_expectData_2771_);
lean_dec(v_respStream_2769_);
lean_dec_ref(v_response_2768_);
lean_dec(v_currentTimeout_2767_);
lean_dec_ref(v_requestStream_2766_);
lean_dec_ref(v_machine_2765_);
v_a_2777_ = lean_ctor_get(v_x_2775_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_x_2775_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2779_ = v_x_2775_;
v_isShared_2780_ = v_isSharedCheck_2785_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v_x_2775_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2785_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v_headerTimeout_2787_; lean_object* v_second_2788_; lean_object* v_nano_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v_second_2793_; lean_object* v_nano_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2786_ = lean_ctor_get(v_x_2775_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v_x_2775_, 1);
v_headerTimeout_2787_ = lean_ctor_get(v_config_2764_, 6);
v_second_2788_ = lean_ctor_get(v_a_2786_, 0);
lean_inc(v_second_2788_);
v_nano_2789_ = lean_ctor_get(v_a_2786_, 1);
lean_inc(v_nano_2789_);
lean_dec(v_a_2786_);
v___x_2790_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2791_ = lean_int_mul(v_headerTimeout_2787_, v___x_2790_);
v___x_2792_ = l_Std_Time_Duration_ofNanoseconds(v___x_2791_);
lean_dec(v___x_2791_);
v_second_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_second_2793_);
v_nano_2794_ = lean_ctor_get(v___x_2792_, 1);
lean_inc(v_nano_2794_);
lean_dec_ref(v___x_2792_);
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2797_ = lean_int_mul(v_second_2788_, v___x_2796_);
lean_dec(v_second_2788_);
v___x_2798_ = lean_int_add(v___x_2797_, v_nano_2789_);
lean_dec(v_nano_2789_);
lean_dec(v___x_2797_);
v___x_2799_ = lean_int_mul(v_second_2793_, v___x_2796_);
lean_dec(v_second_2793_);
v___x_2800_ = lean_int_add(v___x_2799_, v_nano_2794_);
lean_dec(v_nano_2794_);
lean_dec(v___x_2799_);
v___x_2801_ = lean_int_add(v___x_2798_, v___x_2800_);
lean_dec(v___x_2800_);
lean_dec(v___x_2798_);
v___x_2802_ = l_Std_Time_Duration_ofNanoseconds(v___x_2801_);
lean_dec(v___x_2801_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2804_, 0, v_machine_2765_);
lean_ctor_set(v___x_2804_, 1, v_requestStream_2766_);
lean_ctor_set(v___x_2804_, 2, v___x_2795_);
lean_ctor_set(v___x_2804_, 3, v_currentTimeout_2767_);
lean_ctor_set(v___x_2804_, 4, v___x_2803_);
lean_ctor_set(v___x_2804_, 5, v_response_2768_);
lean_ctor_set(v___x_2804_, 6, v_respStream_2769_);
lean_ctor_set(v___x_2804_, 7, v_expectData_2771_);
lean_ctor_set(v___x_2804_, 8, v_pendingHead_2773_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*9, v_requiresData_2770_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*9 + 1, v_handlerDispatched_2772_);
v___x_2805_ = lean_box(0);
v___x_2806_ = lean_apply_3(v___f_2774_, v___x_2805_, v___x_2804_, lean_box(0));
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2807_, lean_object* v_machine_2808_, lean_object* v_requestStream_2809_, lean_object* v_currentTimeout_2810_, lean_object* v_response_2811_, lean_object* v_respStream_2812_, lean_object* v_requiresData_2813_, lean_object* v_expectData_2814_, lean_object* v_handlerDispatched_2815_, lean_object* v_pendingHead_2816_, lean_object* v___f_2817_, lean_object* v_x_2818_, lean_object* v___y_2819_){
_start:
{
uint8_t v_requiresData_boxed_2820_; uint8_t v_handlerDispatched_boxed_2821_; lean_object* v_res_2822_; 
v_requiresData_boxed_2820_ = lean_unbox(v_requiresData_2813_);
v_handlerDispatched_boxed_2821_ = lean_unbox(v_handlerDispatched_2815_);
v_res_2822_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2807_, v_machine_2808_, v_requestStream_2809_, v_currentTimeout_2810_, v_response_2811_, v_respStream_2812_, v_requiresData_boxed_2820_, v_expectData_2814_, v_handlerDispatched_boxed_2821_, v_pendingHead_2816_, v___f_2817_, v_x_2818_);
lean_dec_ref(v_config_2807_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2823_, lean_object* v_requestStream_2824_, lean_object* v_keepAliveTimeout_2825_, lean_object* v_currentTimeout_2826_, lean_object* v_headerTimeout_2827_, lean_object* v_response_2828_, uint8_t v_requiresData_2829_, lean_object* v_expectData_2830_, uint8_t v_handlerDispatched_2831_, lean_object* v_pendingHead_2832_, lean_object* v_____r_2833_){
_start:
{
lean_object* v_writer_2835_; lean_object* v_reader_2836_; lean_object* v_config_2837_; lean_object* v_events_2838_; lean_object* v_error_2839_; lean_object* v_instant_2840_; uint8_t v_keepAlive_2841_; uint8_t v_forcedFlush_2842_; uint8_t v_pullBodyStalled_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2873_; 
v_writer_2835_ = lean_ctor_get(v_machine_2823_, 1);
v_reader_2836_ = lean_ctor_get(v_machine_2823_, 0);
v_config_2837_ = lean_ctor_get(v_machine_2823_, 2);
v_events_2838_ = lean_ctor_get(v_machine_2823_, 3);
v_error_2839_ = lean_ctor_get(v_machine_2823_, 4);
v_instant_2840_ = lean_ctor_get(v_machine_2823_, 5);
v_keepAlive_2841_ = lean_ctor_get_uint8(v_machine_2823_, sizeof(void*)*6);
v_forcedFlush_2842_ = lean_ctor_get_uint8(v_machine_2823_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2843_ = lean_ctor_get_uint8(v_machine_2823_, sizeof(void*)*6 + 2);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_machine_2823_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2845_ = v_machine_2823_;
v_isShared_2846_ = v_isSharedCheck_2873_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_instant_2840_);
lean_inc(v_error_2839_);
lean_inc(v_events_2838_);
lean_inc(v_config_2837_);
lean_inc(v_writer_2835_);
lean_inc(v_reader_2836_);
lean_dec(v_machine_2823_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2873_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_userData_2847_; lean_object* v_outputData_2848_; lean_object* v_state_2849_; lean_object* v_knownSize_2850_; lean_object* v_messageHead_2851_; uint8_t v_sentMessage_2852_; uint8_t v_omitBody_2853_; lean_object* v_userDataBytes_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2872_; 
v_userData_2847_ = lean_ctor_get(v_writer_2835_, 0);
v_outputData_2848_ = lean_ctor_get(v_writer_2835_, 1);
v_state_2849_ = lean_ctor_get(v_writer_2835_, 2);
v_knownSize_2850_ = lean_ctor_get(v_writer_2835_, 3);
v_messageHead_2851_ = lean_ctor_get(v_writer_2835_, 4);
v_sentMessage_2852_ = lean_ctor_get_uint8(v_writer_2835_, sizeof(void*)*6);
v_omitBody_2853_ = lean_ctor_get_uint8(v_writer_2835_, sizeof(void*)*6 + 2);
v_userDataBytes_2854_ = lean_ctor_get(v_writer_2835_, 5);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_writer_2835_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2856_ = v_writer_2835_;
v_isShared_2857_ = v_isSharedCheck_2872_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_userDataBytes_2854_);
lean_inc(v_messageHead_2851_);
lean_inc(v_knownSize_2850_);
lean_inc(v_state_2849_);
lean_inc(v_outputData_2848_);
lean_inc(v_userData_2847_);
lean_dec(v_writer_2835_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2872_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
uint8_t v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = 1;
if (v_isShared_2857_ == 0)
{
v___x_2860_ = v___x_2856_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_userData_2847_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_outputData_2848_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_state_2849_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_knownSize_2850_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_messageHead_2851_);
lean_ctor_set(v_reuseFailAlloc_2871_, 5, v_userDataBytes_2854_);
lean_ctor_set_uint8(v_reuseFailAlloc_2871_, sizeof(void*)*6, v_sentMessage_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2871_, sizeof(void*)*6 + 2, v_omitBody_2853_);
v___x_2860_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*6 + 1, v___x_2858_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___x_2860_);
v___x_2862_ = v___x_2845_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_reader_2836_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_config_2837_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_events_2838_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_error_2839_);
lean_ctor_set(v_reuseFailAlloc_2870_, 5, v_instant_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2870_, sizeof(void*)*6, v_keepAlive_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2870_, sizeof(void*)*6 + 1, v_forcedFlush_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2870_, sizeof(void*)*6 + 2, v_pullBodyStalled_2843_);
v___x_2862_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v_requestStream_2824_);
lean_ctor_set(v___x_2864_, 2, v_keepAliveTimeout_2825_);
lean_ctor_set(v___x_2864_, 3, v_currentTimeout_2826_);
lean_ctor_set(v___x_2864_, 4, v_headerTimeout_2827_);
lean_ctor_set(v___x_2864_, 5, v_response_2828_);
lean_ctor_set(v___x_2864_, 6, v___x_2863_);
lean_ctor_set(v___x_2864_, 7, v_expectData_2830_);
lean_ctor_set(v___x_2864_, 8, v_pendingHead_2832_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*9, v_requiresData_2829_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*9 + 1, v_handlerDispatched_2831_);
v___x_2865_ = 0;
v___x_2866_ = lean_box(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2864_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2874_, lean_object* v_requestStream_2875_, lean_object* v_keepAliveTimeout_2876_, lean_object* v_currentTimeout_2877_, lean_object* v_headerTimeout_2878_, lean_object* v_response_2879_, lean_object* v_requiresData_2880_, lean_object* v_expectData_2881_, lean_object* v_handlerDispatched_2882_, lean_object* v_pendingHead_2883_, lean_object* v_____r_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_requiresData_boxed_2886_; uint8_t v_handlerDispatched_boxed_2887_; lean_object* v_res_2888_; 
v_requiresData_boxed_2886_ = lean_unbox(v_requiresData_2880_);
v_handlerDispatched_boxed_2887_ = lean_unbox(v_handlerDispatched_2882_);
v_res_2888_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2874_, v_requestStream_2875_, v_keepAliveTimeout_2876_, v_currentTimeout_2877_, v_headerTimeout_2878_, v_response_2879_, v_requiresData_boxed_2886_, v_expectData_2881_, v_handlerDispatched_boxed_2887_, v_pendingHead_2883_, v_____r_2884_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2890_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v___f_2889_);
v_a_2892_ = lean_ctor_get(v_x_2890_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_x_2890_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v_x_2890_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v_x_2890_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2902_; 
v_a_2901_ = lean_ctor_get(v_x_2890_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v_x_2890_, 1);
v___x_2902_ = lean_apply_2(v___f_2889_, v_a_2901_, lean_box(0));
return v___x_2902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2903_, lean_object* v_x_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2903_, v_x_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2907_, lean_object* v_val_2908_, lean_object* v___f_2909_, lean_object* v___f_2910_, lean_object* v_x_2911_){
_start:
{
if (lean_obj_tag(v_x_2911_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___f_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v_val_2908_);
lean_dec_ref(v_close_2907_);
v_a_2913_ = lean_ctor_get(v_x_2911_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_x_2911_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2915_ = v_x_2911_;
v_isShared_2916_ = v_isSharedCheck_2921_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v_x_2911_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2921_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
else
{
lean_object* v_a_2922_; uint8_t v___x_2923_; 
v_a_2922_ = lean_ctor_get(v_x_2911_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v_x_2911_, 1);
v___x_2923_ = lean_unbox(v_a_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; 
lean_dec_ref(v___f_2910_);
v___x_2924_ = lean_apply_2(v_close_2907_, v_val_2908_, lean_box(0));
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = lean_unbox(v_a_2922_);
lean_dec(v_a_2922_);
v___x_2927_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2925_, v___x_2926_, v___x_2924_, v___f_2909_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v_a_2922_);
lean_dec_ref(v___f_2909_);
lean_dec(v_val_2908_);
lean_dec_ref(v_close_2907_);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_apply_2(v___f_2910_, v___x_2928_, lean_box(0));
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2930_, lean_object* v_val_2931_, lean_object* v___f_2932_, lean_object* v___f_2933_, lean_object* v_x_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2930_, v_val_2931_, v___f_2932_, v___f_2933_, v_x_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2937_, lean_object* v_handler_2938_, lean_object* v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2939_) == 0)
{
lean_object* v_a_2941_; lean_object* v_onFailure_2942_; lean_object* v___x_2943_; 
v_a_2941_ = lean_ctor_get(v_x_2939_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v_x_2939_, 1);
v_onFailure_2942_ = lean_ctor_get(v_inst_2937_, 2);
lean_inc_ref(v_onFailure_2942_);
lean_dec_ref(v_inst_2937_);
v___x_2943_ = lean_apply_3(v_onFailure_2942_, v_handler_2938_, v_a_2941_, lean_box(0));
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; 
lean_dec(v_handler_2938_);
lean_dec_ref(v_inst_2937_);
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_x_2939_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2945_, lean_object* v_handler_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2945_, v_handler_2946_, v_x_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2950_, lean_object* v_____r_2951_){
_start:
{
uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2953_ = 0;
v___x_2954_ = lean_box(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_st_2950_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2958_, lean_object* v_____r_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2958_, v_____r_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2962_, lean_object* v___f_2963_, lean_object* v___f_2964_, lean_object* v_x_2965_){
_start:
{
if (lean_obj_tag(v_x_2965_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v___f_2964_);
lean_dec_ref(v___f_2963_);
lean_dec_ref(v_requestStream_2962_);
v_a_2967_ = lean_ctor_get(v_x_2965_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_x_2965_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2969_ = v_x_2965_;
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v_x_2965_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
return v___x_2973_;
}
}
}
else
{
lean_object* v_a_2976_; uint8_t v___x_2977_; 
v_a_2976_ = lean_ctor_get(v_x_2965_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v_x_2965_, 1);
v___x_2977_ = lean_unbox(v_a_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; 
lean_dec_ref(v___f_2964_);
v___x_2978_ = l_Std_Http_Body_Stream_close(v_requestStream_2962_);
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_unbox(v_a_2976_);
lean_dec(v_a_2976_);
v___x_2981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2979_, v___x_2980_, v___x_2978_, v___f_2963_);
return v___x_2981_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_dec(v_a_2976_);
lean_dec_ref(v___f_2963_);
lean_dec_ref(v_requestStream_2962_);
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_apply_2(v___f_2964_, v___x_2982_, lean_box(0));
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2984_, lean_object* v___f_2985_, lean_object* v___f_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2984_, v___f_2985_, v___f_2986_, v_x_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2990_, lean_object* v___f_2991_, lean_object* v___f_2992_, lean_object* v_requestStream_2993_, lean_object* v___f_2994_, lean_object* v_x_2995_){
_start:
{
if (lean_obj_tag(v_x_2995_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___f_2994_);
lean_dec_ref(v_requestStream_2993_);
lean_dec_ref(v___f_2992_);
lean_dec_ref(v___f_2991_);
v_a_2997_ = lean_ctor_get(v_x_2995_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2999_ = v_x_2995_;
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v_x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
}
else
{
lean_dec_ref_known(v_x_2995_, 1);
if (v_final_2990_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec_ref(v___f_2994_);
lean_dec_ref(v_requestStream_2993_);
lean_dec_ref(v___f_2992_);
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_apply_2(v___f_2991_, v___x_3006_, lean_box(0));
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_7012__overap_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; 
lean_dec_ref(v___f_2991_);
v___x_3008_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3009_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3010_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3011_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3012_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3012_, 0, lean_box(0));
lean_closure_set(v___x_3012_, 1, lean_box(0));
lean_closure_set(v___x_3012_, 2, lean_box(0));
lean_closure_set(v___x_3012_, 3, v___x_3008_);
lean_closure_set(v___x_3012_, 4, lean_box(0));
lean_closure_set(v___x_3012_, 5, lean_box(0));
lean_closure_set(v___x_3012_, 6, v___x_3011_);
lean_closure_set(v___x_3012_, 7, v___f_2992_);
v___x_7012__overap_3013_ = l_Std_Mutex_atomically___redArg(v___x_3008_, v___f_3009_, v___f_3010_, v_requestStream_2993_, v___x_3012_);
v___x_3014_ = lean_apply_1(v___x_7012__overap_3013_, lean_box(0));
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = 0;
v___x_3017_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3015_, v___x_3016_, v___x_3014_, v___f_2994_);
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3018_, lean_object* v___f_3019_, lean_object* v___f_3020_, lean_object* v_requestStream_3021_, lean_object* v___f_3022_, lean_object* v_x_3023_, lean_object* v___y_3024_){
_start:
{
uint8_t v_final_boxed_3025_; lean_object* v_res_3026_; 
v_final_boxed_3025_ = lean_unbox(v_final_3018_);
v_res_3026_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3025_, v___f_3019_, v___f_3020_, v_requestStream_3021_, v___f_3022_, v_x_3023_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3027_, lean_object* v_x_3028_){
_start:
{
if (lean_obj_tag(v_x_3028_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v_state_3027_);
v_a_3030_ = lean_ctor_get(v_x_3028_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_x_3028_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3032_ = v_x_3028_;
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v_x_3028_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
}
}
else
{
lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3068_; 
v_isSharedCheck_3068_ = !lean_is_exclusive(v_x_3028_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_x_3028_, 0);
lean_dec(v_unused_3069_);
v___x_3040_ = v_x_3028_;
v_isShared_3041_ = v_isSharedCheck_3068_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v_x_3028_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3068_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_machine_3042_; lean_object* v_requestStream_3043_; lean_object* v_keepAliveTimeout_3044_; lean_object* v_currentTimeout_3045_; lean_object* v_headerTimeout_3046_; lean_object* v_response_3047_; lean_object* v_respStream_3048_; uint8_t v_requiresData_3049_; lean_object* v_expectData_3050_; lean_object* v_pendingHead_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3067_; 
v_machine_3042_ = lean_ctor_get(v_state_3027_, 0);
v_requestStream_3043_ = lean_ctor_get(v_state_3027_, 1);
v_keepAliveTimeout_3044_ = lean_ctor_get(v_state_3027_, 2);
v_currentTimeout_3045_ = lean_ctor_get(v_state_3027_, 3);
v_headerTimeout_3046_ = lean_ctor_get(v_state_3027_, 4);
v_response_3047_ = lean_ctor_get(v_state_3027_, 5);
v_respStream_3048_ = lean_ctor_get(v_state_3027_, 6);
v_requiresData_3049_ = lean_ctor_get_uint8(v_state_3027_, sizeof(void*)*9);
v_expectData_3050_ = lean_ctor_get(v_state_3027_, 7);
v_pendingHead_3051_ = lean_ctor_get(v_state_3027_, 8);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_state_3027_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3053_ = v_state_3027_;
v_isShared_3054_ = v_isSharedCheck_3067_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_pendingHead_3051_);
lean_inc(v_expectData_3050_);
lean_inc(v_respStream_3048_);
lean_inc(v_response_3047_);
lean_inc(v_headerTimeout_3046_);
lean_inc(v_currentTimeout_3045_);
lean_inc(v_keepAliveTimeout_3044_);
lean_inc(v_requestStream_3043_);
lean_inc(v_machine_3042_);
lean_dec(v_state_3027_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3067_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3059_; 
v___x_3055_ = lean_box(52);
v___x_3056_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3042_, v___x_3055_);
v___x_3057_ = 0;
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3056_);
v___x_3059_ = v___x_3053_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_requestStream_3043_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v_keepAliveTimeout_3044_);
lean_ctor_set(v_reuseFailAlloc_3066_, 3, v_currentTimeout_3045_);
lean_ctor_set(v_reuseFailAlloc_3066_, 4, v_headerTimeout_3046_);
lean_ctor_set(v_reuseFailAlloc_3066_, 5, v_response_3047_);
lean_ctor_set(v_reuseFailAlloc_3066_, 6, v_respStream_3048_);
lean_ctor_set(v_reuseFailAlloc_3066_, 7, v_expectData_3050_);
lean_ctor_set(v_reuseFailAlloc_3066_, 8, v_pendingHead_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3066_, sizeof(void*)*9, v_requiresData_3049_);
v___x_3059_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*9 + 1, v___x_3057_);
v___x_3060_ = lean_box(v___x_3057_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3061_);
v___x_3063_ = v___x_3040_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3070_, v_x_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3074_, lean_object* v_requestStream_3075_, lean_object* v_keepAliveTimeout_3076_, lean_object* v_currentTimeout_3077_, lean_object* v_headerTimeout_3078_, lean_object* v_response_3079_, lean_object* v_respStream_3080_, uint8_t v_requiresData_3081_, lean_object* v_expectData_3082_, lean_object* v_pendingHead_3083_, lean_object* v_____r_3084_){
_start:
{
uint8_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3086_ = 0;
v___x_3087_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3087_, 0, v_machine_3074_);
lean_ctor_set(v___x_3087_, 1, v_requestStream_3075_);
lean_ctor_set(v___x_3087_, 2, v_keepAliveTimeout_3076_);
lean_ctor_set(v___x_3087_, 3, v_currentTimeout_3077_);
lean_ctor_set(v___x_3087_, 4, v_headerTimeout_3078_);
lean_ctor_set(v___x_3087_, 5, v_response_3079_);
lean_ctor_set(v___x_3087_, 6, v_respStream_3080_);
lean_ctor_set(v___x_3087_, 7, v_expectData_3082_);
lean_ctor_set(v___x_3087_, 8, v_pendingHead_3083_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*9, v_requiresData_3081_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*9 + 1, v___x_3086_);
v___x_3088_ = lean_box(v___x_3086_);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3087_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3092_, lean_object* v_requestStream_3093_, lean_object* v_keepAliveTimeout_3094_, lean_object* v_currentTimeout_3095_, lean_object* v_headerTimeout_3096_, lean_object* v_response_3097_, lean_object* v_respStream_3098_, lean_object* v_requiresData_3099_, lean_object* v_expectData_3100_, lean_object* v_pendingHead_3101_, lean_object* v_____r_3102_, lean_object* v___y_3103_){
_start:
{
uint8_t v_requiresData_boxed_3104_; lean_object* v_res_3105_; 
v_requiresData_boxed_3104_ = lean_unbox(v_requiresData_3099_);
v_res_3105_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3092_, v_requestStream_3093_, v_keepAliveTimeout_3094_, v_currentTimeout_3095_, v_headerTimeout_3096_, v_response_3097_, v_respStream_3098_, v_requiresData_boxed_3104_, v_expectData_3100_, v_pendingHead_3101_, v_____r_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3106_, lean_object* v_body_3107_, lean_object* v___f_3108_, lean_object* v___f_3109_, lean_object* v_x_3110_){
_start:
{
if (lean_obj_tag(v_x_3110_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v___f_3109_);
lean_dec_ref(v___f_3108_);
lean_dec(v_body_3107_);
lean_dec_ref(v_close_3106_);
v_a_3112_ = lean_ctor_get(v_x_3110_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_x_3110_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v_x_3110_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v_x_3110_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; uint8_t v___x_3122_; 
v_a_3121_ = lean_ctor_get(v_x_3110_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v_x_3110_, 1);
v___x_3122_ = lean_unbox(v_a_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v___f_3109_);
v___x_3123_ = lean_apply_2(v_close_3106_, v_body_3107_, lean_box(0));
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = lean_unbox(v_a_3121_);
lean_dec(v_a_3121_);
v___x_3126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3124_, v___x_3125_, v___x_3123_, v___f_3108_);
return v___x_3126_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec(v_a_3121_);
lean_dec_ref(v___f_3108_);
lean_dec(v_body_3107_);
lean_dec_ref(v_close_3106_);
v___x_3127_ = lean_box(0);
v___x_3128_ = lean_apply_2(v___f_3109_, v___x_3127_, lean_box(0));
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3129_, lean_object* v_body_3130_, lean_object* v___f_3131_, lean_object* v___f_3132_, lean_object* v_x_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3129_, v_body_3130_, v___f_3131_, v___f_3132_, v_x_3133_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3136_, lean_object* v_keepAliveTimeout_3137_, lean_object* v_currentTimeout_3138_, lean_object* v_headerTimeout_3139_, lean_object* v_response_3140_, uint8_t v_requiresData_3141_, lean_object* v_expectData_3142_, uint8_t v___x_3143_, lean_object* v_pendingHead_3144_, lean_object* v_____x_3145_){
_start:
{
lean_object* v_fst_3147_; lean_object* v_snd_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3159_; 
v_fst_3147_ = lean_ctor_get(v_____x_3145_, 0);
v_snd_3148_ = lean_ctor_get(v_____x_3145_, 1);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_____x_3145_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3150_ = v_____x_3145_;
v_isShared_3151_ = v_isSharedCheck_3159_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_snd_3148_);
lean_inc(v_fst_3147_);
lean_dec(v_____x_3145_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3159_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3152_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3152_, 0, v_fst_3147_);
lean_ctor_set(v___x_3152_, 1, v_requestStream_3136_);
lean_ctor_set(v___x_3152_, 2, v_keepAliveTimeout_3137_);
lean_ctor_set(v___x_3152_, 3, v_currentTimeout_3138_);
lean_ctor_set(v___x_3152_, 4, v_headerTimeout_3139_);
lean_ctor_set(v___x_3152_, 5, v_response_3140_);
lean_ctor_set(v___x_3152_, 6, v_snd_3148_);
lean_ctor_set(v___x_3152_, 7, v_expectData_3142_);
lean_ctor_set(v___x_3152_, 8, v_pendingHead_3144_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*9, v_requiresData_3141_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*9 + 1, v___x_3143_);
v___x_3153_ = lean_box(v___x_3143_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v___x_3153_);
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3155_ = v___x_3150_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3160_, lean_object* v_keepAliveTimeout_3161_, lean_object* v_currentTimeout_3162_, lean_object* v_headerTimeout_3163_, lean_object* v_response_3164_, lean_object* v_requiresData_3165_, lean_object* v_expectData_3166_, lean_object* v___x_3167_, lean_object* v_pendingHead_3168_, lean_object* v_____x_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_requiresData_boxed_3171_; uint8_t v___x_7768__boxed_3172_; lean_object* v_res_3173_; 
v_requiresData_boxed_3171_ = lean_unbox(v_requiresData_3165_);
v___x_7768__boxed_3172_ = lean_unbox(v___x_3167_);
v_res_3173_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3160_, v_keepAliveTimeout_3161_, v_currentTimeout_3162_, v_headerTimeout_3163_, v_response_3164_, v_requiresData_boxed_3171_, v_expectData_3166_, v___x_7768__boxed_3172_, v_pendingHead_3168_, v_____x_3169_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3174_, lean_object* v_x_3175_){
_start:
{
if (lean_obj_tag(v_x_3175_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v___f_3174_);
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
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_ctor_get(v_x_3175_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v_x_3175_, 1);
v___x_3187_ = lean_apply_2(v___f_3174_, v_a_3186_, lean_box(0));
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3188_, lean_object* v_x_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3188_, v_x_3189_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3192_, lean_object* v___f_3193_, lean_object* v_inst_3194_, lean_object* v___f_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v___f_3195_);
lean_dec_ref(v_inst_3194_);
lean_dec_ref(v___f_3193_);
v_a_3198_ = lean_ctor_get(v_x_3196_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_x_3196_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3200_ = v_x_3196_;
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v_x_3196_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v_snd_3208_; 
v_a_3207_ = lean_ctor_get(v_x_3196_, 0);
v_snd_3208_ = lean_ctor_get(v_a_3207_, 1);
if (lean_obj_tag(v_snd_3208_) == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v___f_3195_);
lean_dec_ref(v_inst_3194_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v_x_3196_);
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3210_, v___x_3192_, v___x_3209_, v___f_3193_);
return v___x_3211_;
}
else
{
lean_object* v_fst_3212_; lean_object* v_val_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_inc_ref(v_snd_3208_);
lean_inc(v_a_3207_);
lean_dec_ref_known(v_x_3196_, 1);
lean_dec_ref(v___f_3193_);
v_fst_3212_ = lean_ctor_get(v_a_3207_, 0);
lean_inc(v_fst_3212_);
lean_dec(v_a_3207_);
v_val_3213_ = lean_ctor_get(v_snd_3208_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v_snd_3208_, 1);
v___x_3214_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3194_, v_fst_3212_, v_val_3213_);
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3215_, v___x_3192_, v___x_3214_, v___f_3195_);
return v___x_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3217_, lean_object* v___f_3218_, lean_object* v_inst_3219_, lean_object* v___f_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v___x_7834__boxed_3223_; lean_object* v_res_3224_; 
v___x_7834__boxed_3223_ = lean_unbox(v___x_3217_);
v_res_3224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7834__boxed_3223_, v___f_3218_, v_inst_3219_, v___f_3220_, v_x_3221_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_state_3225_, lean_object* v_x_3226_){
_start:
{
if (lean_obj_tag(v_x_3226_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3236_; 
lean_dec_ref(v_state_3225_);
v_a_3228_ = lean_ctor_get(v_x_3226_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_x_3226_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3230_ = v_x_3226_;
v_isShared_3231_ = v_isSharedCheck_3236_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v_x_3226_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3236_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
}
}
else
{
lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3266_; 
v_isSharedCheck_3266_ = !lean_is_exclusive(v_x_3226_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v_x_3226_, 0);
lean_dec(v_unused_3267_);
v___x_3238_ = v_x_3226_;
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
else
{
lean_dec(v_x_3226_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v_machine_3240_; lean_object* v_requestStream_3241_; lean_object* v_keepAliveTimeout_3242_; lean_object* v_currentTimeout_3243_; lean_object* v_headerTimeout_3244_; lean_object* v_response_3245_; lean_object* v_respStream_3246_; uint8_t v_requiresData_3247_; lean_object* v_expectData_3248_; lean_object* v_pendingHead_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3265_; 
v_machine_3240_ = lean_ctor_get(v_state_3225_, 0);
v_requestStream_3241_ = lean_ctor_get(v_state_3225_, 1);
v_keepAliveTimeout_3242_ = lean_ctor_get(v_state_3225_, 2);
v_currentTimeout_3243_ = lean_ctor_get(v_state_3225_, 3);
v_headerTimeout_3244_ = lean_ctor_get(v_state_3225_, 4);
v_response_3245_ = lean_ctor_get(v_state_3225_, 5);
v_respStream_3246_ = lean_ctor_get(v_state_3225_, 6);
v_requiresData_3247_ = lean_ctor_get_uint8(v_state_3225_, sizeof(void*)*9);
v_expectData_3248_ = lean_ctor_get(v_state_3225_, 7);
v_pendingHead_3249_ = lean_ctor_get(v_state_3225_, 8);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_state_3225_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3251_ = v_state_3225_;
v_isShared_3252_ = v_isSharedCheck_3265_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_pendingHead_3249_);
lean_inc(v_expectData_3248_);
lean_inc(v_respStream_3246_);
lean_inc(v_response_3245_);
lean_inc(v_headerTimeout_3244_);
lean_inc(v_currentTimeout_3243_);
lean_inc(v_keepAliveTimeout_3242_);
lean_inc(v_requestStream_3241_);
lean_inc(v_machine_3240_);
lean_dec(v_state_3225_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3265_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3257_; 
v___x_3253_ = lean_box(31);
v___x_3254_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3240_, v___x_3253_);
v___x_3255_ = 0;
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3254_);
v___x_3257_ = v___x_3251_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3254_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_requestStream_3241_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_keepAliveTimeout_3242_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v_currentTimeout_3243_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v_headerTimeout_3244_);
lean_ctor_set(v_reuseFailAlloc_3264_, 5, v_response_3245_);
lean_ctor_set(v_reuseFailAlloc_3264_, 6, v_respStream_3246_);
lean_ctor_set(v_reuseFailAlloc_3264_, 7, v_expectData_3248_);
lean_ctor_set(v_reuseFailAlloc_3264_, 8, v_pendingHead_3249_);
lean_ctor_set_uint8(v_reuseFailAlloc_3264_, sizeof(void*)*9, v_requiresData_3247_);
v___x_3257_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*9 + 1, v___x_3255_);
v___x_3258_ = lean_box(v___x_3255_);
v___x_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3259_);
v___x_3261_ = v___x_3238_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_state_3268_, lean_object* v_x_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_state_3268_, v_x_3269_);
return v_res_3271_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3274_ = lean_mk_io_user_error(v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v_handler_3277_, lean_object* v_config_3278_, lean_object* v_event_3279_, lean_object* v_state_3280_){
_start:
{
switch(lean_obj_tag(v_event_3279_))
{
case 0:
{
lean_object* v_x_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v_handler_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
v_x_3282_ = lean_ctor_get(v_event_3279_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_event_3279_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3284_ = v_event_3279_;
v_isShared_3285_ = v_isSharedCheck_3389_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_x_3282_);
lean_dec(v_event_3279_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3389_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
if (lean_obj_tag(v_x_3282_) == 0)
{
lean_object* v_machine_3286_; lean_object* v_reader_3287_; lean_object* v_requestStream_3288_; lean_object* v_keepAliveTimeout_3289_; lean_object* v_currentTimeout_3290_; lean_object* v_headerTimeout_3291_; lean_object* v_response_3292_; lean_object* v_respStream_3293_; uint8_t v_requiresData_3294_; lean_object* v_expectData_3295_; uint8_t v_handlerDispatched_3296_; lean_object* v_pendingHead_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v_config_3278_);
v_machine_3286_ = lean_ctor_get(v_state_3280_, 0);
lean_inc_ref(v_machine_3286_);
v_reader_3287_ = lean_ctor_get(v_machine_3286_, 0);
lean_inc_ref(v_reader_3287_);
v_requestStream_3288_ = lean_ctor_get(v_state_3280_, 1);
v_keepAliveTimeout_3289_ = lean_ctor_get(v_state_3280_, 2);
v_currentTimeout_3290_ = lean_ctor_get(v_state_3280_, 3);
v_headerTimeout_3291_ = lean_ctor_get(v_state_3280_, 4);
v_response_3292_ = lean_ctor_get(v_state_3280_, 5);
v_respStream_3293_ = lean_ctor_get(v_state_3280_, 6);
v_requiresData_3294_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3295_ = lean_ctor_get(v_state_3280_, 7);
v_handlerDispatched_3296_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9 + 1);
v_pendingHead_3297_ = lean_ctor_get(v_state_3280_, 8);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_state_3280_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; 
v_unused_3341_ = lean_ctor_get(v_state_3280_, 0);
lean_dec(v_unused_3341_);
v___x_3299_ = v_state_3280_;
v_isShared_3300_ = v_isSharedCheck_3340_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_pendingHead_3297_);
lean_inc(v_expectData_3295_);
lean_inc(v_respStream_3293_);
lean_inc(v_response_3292_);
lean_inc(v_headerTimeout_3291_);
lean_inc(v_currentTimeout_3290_);
lean_inc(v_keepAliveTimeout_3289_);
lean_inc(v_requestStream_3288_);
lean_dec(v_state_3280_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3340_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_writer_3301_; lean_object* v_config_3302_; lean_object* v_events_3303_; lean_object* v_error_3304_; lean_object* v_instant_3305_; uint8_t v_keepAlive_3306_; uint8_t v_forcedFlush_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3338_; 
v_writer_3301_ = lean_ctor_get(v_machine_3286_, 1);
v_config_3302_ = lean_ctor_get(v_machine_3286_, 2);
v_events_3303_ = lean_ctor_get(v_machine_3286_, 3);
v_error_3304_ = lean_ctor_get(v_machine_3286_, 4);
v_instant_3305_ = lean_ctor_get(v_machine_3286_, 5);
v_keepAlive_3306_ = lean_ctor_get_uint8(v_machine_3286_, sizeof(void*)*6);
v_forcedFlush_3307_ = lean_ctor_get_uint8(v_machine_3286_, sizeof(void*)*6 + 1);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_machine_3286_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_machine_3286_, 0);
lean_dec(v_unused_3339_);
v___x_3309_ = v_machine_3286_;
v_isShared_3310_ = v_isSharedCheck_3338_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_instant_3305_);
lean_inc(v_error_3304_);
lean_inc(v_events_3303_);
lean_inc(v_config_3302_);
lean_inc(v_writer_3301_);
lean_dec(v_machine_3286_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3338_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v_state_3311_; lean_object* v_input_3312_; lean_object* v_messageHead_3313_; lean_object* v_messageCount_3314_; lean_object* v_bodyBytesRead_3315_; lean_object* v_headerBytesRead_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3337_; 
v_state_3311_ = lean_ctor_get(v_reader_3287_, 0);
v_input_3312_ = lean_ctor_get(v_reader_3287_, 1);
v_messageHead_3313_ = lean_ctor_get(v_reader_3287_, 2);
v_messageCount_3314_ = lean_ctor_get(v_reader_3287_, 3);
v_bodyBytesRead_3315_ = lean_ctor_get(v_reader_3287_, 4);
v_headerBytesRead_3316_ = lean_ctor_get(v_reader_3287_, 5);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_reader_3287_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3318_ = v_reader_3287_;
v_isShared_3319_ = v_isSharedCheck_3337_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_headerBytesRead_3316_);
lean_inc(v_bodyBytesRead_3315_);
lean_inc(v_messageCount_3314_);
lean_inc(v_messageHead_3313_);
lean_inc(v_input_3312_);
lean_inc(v_state_3311_);
lean_dec(v_reader_3287_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3337_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
uint8_t v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = 1;
if (v_isShared_3319_ == 0)
{
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_state_3311_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_input_3312_);
lean_ctor_set(v_reuseFailAlloc_3336_, 2, v_messageHead_3313_);
lean_ctor_set(v_reuseFailAlloc_3336_, 3, v_messageCount_3314_);
lean_ctor_set(v_reuseFailAlloc_3336_, 4, v_bodyBytesRead_3315_);
lean_ctor_set(v_reuseFailAlloc_3336_, 5, v_headerBytesRead_3316_);
v___x_3322_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
uint8_t v___x_3323_; lean_object* v___x_3325_; 
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*6, v___x_3320_);
v___x_3323_ = 0;
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3322_);
v___x_3325_ = v___x_3309_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_writer_3301_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_config_3302_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_events_3303_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_error_3304_);
lean_ctor_set(v_reuseFailAlloc_3335_, 5, v_instant_3305_);
lean_ctor_set_uint8(v_reuseFailAlloc_3335_, sizeof(void*)*6, v_keepAlive_3306_);
lean_ctor_set_uint8(v_reuseFailAlloc_3335_, sizeof(void*)*6 + 1, v_forcedFlush_3307_);
v___x_3325_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3327_; 
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*6 + 2, v___x_3323_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3325_);
v___x_3327_ = v___x_3299_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_requestStream_3288_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_keepAliveTimeout_3289_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_currentTimeout_3290_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_headerTimeout_3291_);
lean_ctor_set(v_reuseFailAlloc_3334_, 5, v_response_3292_);
lean_ctor_set(v_reuseFailAlloc_3334_, 6, v_respStream_3293_);
lean_ctor_set(v_reuseFailAlloc_3334_, 7, v_expectData_3295_);
lean_ctor_set(v_reuseFailAlloc_3334_, 8, v_pendingHead_3297_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*9, v_requiresData_3294_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*9 + 1, v_handlerDispatched_3296_);
v___x_3327_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3328_ = lean_box(v___x_3323_);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 1);
lean_ctor_set(v___x_3284_, 0, v___x_3329_);
v___x_3331_ = v___x_3284_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
return v___x_3332_;
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
lean_object* v_val_3342_; lean_object* v_machine_3343_; lean_object* v_requestStream_3344_; lean_object* v_keepAliveTimeout_3345_; lean_object* v_currentTimeout_3346_; lean_object* v_response_3347_; lean_object* v_respStream_3348_; uint8_t v_requiresData_3349_; lean_object* v_expectData_3350_; uint8_t v_handlerDispatched_3351_; lean_object* v_pendingHead_3352_; lean_object* v___f_3353_; 
lean_del_object(v___x_3284_);
v_val_3342_ = lean_ctor_get(v_x_3282_, 0);
lean_inc_n(v_val_3342_, 2);
lean_dec_ref_known(v_x_3282_, 1);
v_machine_3343_ = lean_ctor_get(v_state_3280_, 0);
v_requestStream_3344_ = lean_ctor_get(v_state_3280_, 1);
v_keepAliveTimeout_3345_ = lean_ctor_get(v_state_3280_, 2);
lean_inc(v_keepAliveTimeout_3345_);
v_currentTimeout_3346_ = lean_ctor_get(v_state_3280_, 3);
v_response_3347_ = lean_ctor_get(v_state_3280_, 5);
v_respStream_3348_ = lean_ctor_get(v_state_3280_, 6);
v_requiresData_3349_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3350_ = lean_ctor_get(v_state_3280_, 7);
v_handlerDispatched_3351_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9 + 1);
v_pendingHead_3352_ = lean_ctor_get(v_state_3280_, 8);
v___f_3353_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3353_, 0, v_val_3342_);
if (lean_obj_tag(v_keepAliveTimeout_3345_) == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec_ref(v___f_3353_);
lean_dec_ref(v_config_3278_);
v___x_3354_ = lean_box(0);
v___x_3355_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3342_, v___x_3354_, v_state_3280_);
return v___x_3355_;
}
else
{
lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3387_; 
lean_inc(v_pendingHead_3352_);
lean_inc(v_expectData_3350_);
lean_inc(v_respStream_3348_);
lean_inc_ref(v_response_3347_);
lean_inc(v_currentTimeout_3346_);
lean_inc_ref(v_requestStream_3344_);
lean_inc_ref(v_machine_3343_);
lean_dec(v_val_3342_);
lean_dec_ref(v_state_3280_);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_keepAliveTimeout_3345_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v_keepAliveTimeout_3345_, 0);
lean_dec(v_unused_3388_);
v___x_3357_ = v_keepAliveTimeout_3345_;
v_isShared_3358_ = v_isSharedCheck_3387_;
goto v_resetjp_3356_;
}
else
{
lean_dec(v_keepAliveTimeout_3345_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3387_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; lean_object* v_val_3363_; lean_object* v___x_3370_; 
v___x_3359_ = lean_box(v_requiresData_3349_);
v___x_3360_ = lean_box(v_handlerDispatched_3351_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3361_, 0, v_config_3278_);
lean_closure_set(v___f_3361_, 1, v_machine_3343_);
lean_closure_set(v___f_3361_, 2, v_requestStream_3344_);
lean_closure_set(v___f_3361_, 3, v_currentTimeout_3346_);
lean_closure_set(v___f_3361_, 4, v_response_3347_);
lean_closure_set(v___f_3361_, 5, v_respStream_3348_);
lean_closure_set(v___f_3361_, 6, v___x_3359_);
lean_closure_set(v___f_3361_, 7, v_expectData_3350_);
lean_closure_set(v___f_3361_, 8, v___x_3360_);
lean_closure_set(v___f_3361_, 9, v_pendingHead_3352_);
lean_closure_set(v___f_3361_, 10, v___f_3353_);
v___x_3370_ = lean_get_current_time();
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set_tag(v___x_3373_, 1);
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
v_val_3363_ = v___x_3376_;
goto v___jp_3362_;
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_a_3379_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3370_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3370_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set_tag(v___x_3381_, 0);
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
v_val_3363_ = v___x_3384_;
goto v___jp_3362_;
}
}
}
v___jp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 0);
lean_ctor_set(v___x_3357_, 0, v_val_3363_);
v___x_3365_ = v___x_3357_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_val_3363_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_unsigned_to_nat(0u);
v___x_3367_ = 0;
v___x_3368_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3366_, v___x_3367_, v___x_3365_, v___f_3361_);
return v___x_3368_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_config_3278_);
lean_dec(v_handler_3277_);
lean_dec_ref(v_inst_3275_);
v_x_3390_ = lean_ctor_get(v_event_3279_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_event_3279_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3392_ = v_event_3279_;
v_isShared_3393_ = v_isSharedCheck_3505_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_x_3390_);
lean_dec(v_event_3279_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3505_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
if (lean_obj_tag(v_x_3390_) == 0)
{
lean_object* v_machine_3394_; lean_object* v_requestStream_3395_; lean_object* v_keepAliveTimeout_3396_; lean_object* v_currentTimeout_3397_; lean_object* v_headerTimeout_3398_; lean_object* v_response_3399_; lean_object* v_respStream_3400_; uint8_t v_requiresData_3401_; lean_object* v_expectData_3402_; uint8_t v_handlerDispatched_3403_; lean_object* v_pendingHead_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___f_3407_; 
lean_del_object(v___x_3392_);
v_machine_3394_ = lean_ctor_get(v_state_3280_, 0);
lean_inc_ref_n(v_machine_3394_, 2);
v_requestStream_3395_ = lean_ctor_get(v_state_3280_, 1);
lean_inc_ref_n(v_requestStream_3395_, 2);
v_keepAliveTimeout_3396_ = lean_ctor_get(v_state_3280_, 2);
lean_inc_n(v_keepAliveTimeout_3396_, 2);
v_currentTimeout_3397_ = lean_ctor_get(v_state_3280_, 3);
lean_inc_n(v_currentTimeout_3397_, 2);
v_headerTimeout_3398_ = lean_ctor_get(v_state_3280_, 4);
lean_inc_n(v_headerTimeout_3398_, 2);
v_response_3399_ = lean_ctor_get(v_state_3280_, 5);
lean_inc_ref_n(v_response_3399_, 2);
v_respStream_3400_ = lean_ctor_get(v_state_3280_, 6);
lean_inc(v_respStream_3400_);
v_requiresData_3401_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3402_ = lean_ctor_get(v_state_3280_, 7);
lean_inc_n(v_expectData_3402_, 2);
v_handlerDispatched_3403_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9 + 1);
v_pendingHead_3404_ = lean_ctor_get(v_state_3280_, 8);
lean_inc_n(v_pendingHead_3404_, 2);
lean_dec_ref(v_state_3280_);
v___x_3405_ = lean_box(v_requiresData_3401_);
v___x_3406_ = lean_box(v_handlerDispatched_3403_);
v___f_3407_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3407_, 0, v_machine_3394_);
lean_closure_set(v___f_3407_, 1, v_requestStream_3395_);
lean_closure_set(v___f_3407_, 2, v_keepAliveTimeout_3396_);
lean_closure_set(v___f_3407_, 3, v_currentTimeout_3397_);
lean_closure_set(v___f_3407_, 4, v_headerTimeout_3398_);
lean_closure_set(v___f_3407_, 5, v_response_3399_);
lean_closure_set(v___f_3407_, 6, v___x_3405_);
lean_closure_set(v___f_3407_, 7, v_expectData_3402_);
lean_closure_set(v___f_3407_, 8, v___x_3406_);
lean_closure_set(v___f_3407_, 9, v_pendingHead_3404_);
if (lean_obj_tag(v_respStream_3400_) == 1)
{
lean_object* v_val_3408_; lean_object* v_close_3409_; lean_object* v_isClosed_3410_; lean_object* v___x_3411_; lean_object* v___f_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v_pendingHead_3404_);
lean_dec(v_expectData_3402_);
lean_dec_ref(v_response_3399_);
lean_dec(v_headerTimeout_3398_);
lean_dec(v_currentTimeout_3397_);
lean_dec(v_keepAliveTimeout_3396_);
lean_dec_ref(v_requestStream_3395_);
lean_dec_ref(v_machine_3394_);
v_val_3408_ = lean_ctor_get(v_respStream_3400_, 0);
lean_inc_n(v_val_3408_, 2);
lean_dec_ref_known(v_respStream_3400_, 1);
v_close_3409_ = lean_ctor_get(v_inst_3276_, 1);
lean_inc_ref(v_close_3409_);
v_isClosed_3410_ = lean_ctor_get(v_inst_3276_, 2);
lean_inc_ref(v_isClosed_3410_);
lean_dec_ref(v_inst_3276_);
v___x_3411_ = lean_apply_2(v_isClosed_3410_, v_val_3408_, lean_box(0));
lean_inc_ref(v___f_3407_);
v___f_3412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3412_, 0, v___f_3407_);
v___f_3413_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3413_, 0, v_close_3409_);
lean_closure_set(v___f_3413_, 1, v_val_3408_);
lean_closure_set(v___f_3413_, 2, v___f_3412_);
lean_closure_set(v___f_3413_, 3, v___f_3407_);
v___x_3414_ = lean_unsigned_to_nat(0u);
v___x_3415_ = 0;
v___x_3416_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3414_, v___x_3415_, v___x_3411_, v___f_3413_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v___f_3407_);
lean_dec(v_respStream_3400_);
lean_dec_ref(v_inst_3276_);
v___x_3417_ = lean_box(0);
v___x_3418_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3394_, v_requestStream_3395_, v_keepAliveTimeout_3396_, v_currentTimeout_3397_, v_headerTimeout_3398_, v_response_3399_, v_requiresData_3401_, v_expectData_3402_, v_handlerDispatched_3403_, v_pendingHead_3404_, v___x_3417_);
return v___x_3418_;
}
}
else
{
lean_object* v_val_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_inst_3276_);
v_val_3419_ = lean_ctor_get(v_x_3390_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_x_3390_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3421_ = v_x_3390_;
v_isShared_3422_ = v_isSharedCheck_3504_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_val_3419_);
lean_dec(v_x_3390_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3504_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_machine_3423_; lean_object* v_requestStream_3424_; lean_object* v_keepAliveTimeout_3425_; lean_object* v_currentTimeout_3426_; lean_object* v_headerTimeout_3427_; lean_object* v_response_3428_; lean_object* v_respStream_3429_; uint8_t v_requiresData_3430_; lean_object* v_expectData_3431_; uint8_t v_handlerDispatched_3432_; lean_object* v_pendingHead_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3503_; 
v_machine_3423_ = lean_ctor_get(v_state_3280_, 0);
v_requestStream_3424_ = lean_ctor_get(v_state_3280_, 1);
v_keepAliveTimeout_3425_ = lean_ctor_get(v_state_3280_, 2);
v_currentTimeout_3426_ = lean_ctor_get(v_state_3280_, 3);
v_headerTimeout_3427_ = lean_ctor_get(v_state_3280_, 4);
v_response_3428_ = lean_ctor_get(v_state_3280_, 5);
v_respStream_3429_ = lean_ctor_get(v_state_3280_, 6);
v_requiresData_3430_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3431_ = lean_ctor_get(v_state_3280_, 7);
v_handlerDispatched_3432_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9 + 1);
v_pendingHead_3433_ = lean_ctor_get(v_state_3280_, 8);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_state_3280_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3435_ = v_state_3280_;
v_isShared_3436_ = v_isSharedCheck_3503_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_pendingHead_3433_);
lean_inc(v_expectData_3431_);
lean_inc(v_respStream_3429_);
lean_inc(v_response_3428_);
lean_inc(v_headerTimeout_3427_);
lean_inc(v_currentTimeout_3426_);
lean_inc(v_keepAliveTimeout_3425_);
lean_inc(v_requestStream_3424_);
lean_inc(v_machine_3423_);
lean_dec(v_state_3280_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3503_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___y_3438_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3451_ = lean_unsigned_to_nat(1u);
v___x_3452_ = lean_mk_empty_array_with_capacity(v___x_3451_);
v___x_3453_ = lean_array_push(v___x_3452_, v_val_3419_);
v___x_3454_ = lean_array_get_size(v___x_3453_);
v___x_3455_ = lean_unsigned_to_nat(0u);
v___x_3456_ = lean_nat_dec_eq(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v_reader_3457_; lean_object* v_writer_3458_; lean_object* v_config_3459_; lean_object* v_events_3460_; lean_object* v_error_3461_; lean_object* v_instant_3462_; uint8_t v_keepAlive_3463_; uint8_t v_forcedFlush_3464_; uint8_t v_pullBodyStalled_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3502_; 
v_reader_3457_ = lean_ctor_get(v_machine_3423_, 0);
v_writer_3458_ = lean_ctor_get(v_machine_3423_, 1);
v_config_3459_ = lean_ctor_get(v_machine_3423_, 2);
v_events_3460_ = lean_ctor_get(v_machine_3423_, 3);
v_error_3461_ = lean_ctor_get(v_machine_3423_, 4);
v_instant_3462_ = lean_ctor_get(v_machine_3423_, 5);
v_keepAlive_3463_ = lean_ctor_get_uint8(v_machine_3423_, sizeof(void*)*6);
v_forcedFlush_3464_ = lean_ctor_get_uint8(v_machine_3423_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3465_ = lean_ctor_get_uint8(v_machine_3423_, sizeof(void*)*6 + 2);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_machine_3423_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3467_ = v_machine_3423_;
v_isShared_3468_ = v_isSharedCheck_3502_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_instant_3462_);
lean_inc(v_error_3461_);
lean_inc(v_events_3460_);
lean_inc(v_config_3459_);
lean_inc(v_writer_3458_);
lean_inc(v_reader_3457_);
lean_dec(v_machine_3423_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3502_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___y_3470_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3492_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3493_ = lean_nat_dec_lt(v___x_3455_, v___x_3454_);
if (v___x_3493_ == 0)
{
v___y_3470_ = v___x_3455_;
goto v___jp_3469_;
}
else
{
lean_object* v___f_3494_; uint8_t v___x_3495_; 
v___f_3494_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3495_ = lean_nat_dec_le(v___x_3454_, v___x_3454_);
if (v___x_3495_ == 0)
{
if (v___x_3493_ == 0)
{
v___y_3470_ = v___x_3455_;
goto v___jp_3469_;
}
else
{
size_t v___x_3496_; size_t v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = ((size_t)0ULL);
v___x_3497_ = lean_usize_of_nat(v___x_3454_);
lean_inc_ref(v___x_3453_);
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3492_, v___f_3494_, v___x_3453_, v___x_3496_, v___x_3497_, v___x_3455_);
v___y_3470_ = v___x_3498_;
goto v___jp_3469_;
}
}
else
{
size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = lean_usize_of_nat(v___x_3454_);
lean_inc_ref(v___x_3453_);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3492_, v___f_3494_, v___x_3453_, v___x_3499_, v___x_3500_, v___x_3455_);
v___y_3470_ = v___x_3501_;
goto v___jp_3469_;
}
}
v___jp_3469_:
{
lean_object* v_userData_3471_; lean_object* v_outputData_3472_; lean_object* v_state_3473_; lean_object* v_knownSize_3474_; lean_object* v_messageHead_3475_; uint8_t v_sentMessage_3476_; uint8_t v_userClosedBody_3477_; uint8_t v_omitBody_3478_; lean_object* v_userDataBytes_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3491_; 
v_userData_3471_ = lean_ctor_get(v_writer_3458_, 0);
v_outputData_3472_ = lean_ctor_get(v_writer_3458_, 1);
v_state_3473_ = lean_ctor_get(v_writer_3458_, 2);
v_knownSize_3474_ = lean_ctor_get(v_writer_3458_, 3);
v_messageHead_3475_ = lean_ctor_get(v_writer_3458_, 4);
v_sentMessage_3476_ = lean_ctor_get_uint8(v_writer_3458_, sizeof(void*)*6);
v_userClosedBody_3477_ = lean_ctor_get_uint8(v_writer_3458_, sizeof(void*)*6 + 1);
v_omitBody_3478_ = lean_ctor_get_uint8(v_writer_3458_, sizeof(void*)*6 + 2);
v_userDataBytes_3479_ = lean_ctor_get(v_writer_3458_, 5);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_writer_3458_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3481_ = v_writer_3458_;
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_userDataBytes_3479_);
lean_inc(v_messageHead_3475_);
lean_inc(v_knownSize_3474_);
lean_inc(v_state_3473_);
lean_inc(v_outputData_3472_);
lean_inc(v_userData_3471_);
lean_dec(v_writer_3458_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3483_ = l_Array_append___redArg(v_userData_3471_, v___x_3453_);
lean_dec_ref(v___x_3453_);
v___x_3484_ = lean_nat_add(v_userDataBytes_3479_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec(v_userDataBytes_3479_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 5, v___x_3484_);
lean_ctor_set(v___x_3481_, 0, v___x_3483_);
v___x_3486_ = v___x_3481_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_outputData_3472_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_state_3473_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_knownSize_3474_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_messageHead_3475_);
lean_ctor_set(v_reuseFailAlloc_3490_, 5, v___x_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6, v_sentMessage_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6 + 1, v_userClosedBody_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6 + 2, v_omitBody_3478_);
v___x_3486_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3488_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3486_);
v___x_3488_ = v___x_3467_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_reader_3457_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_config_3459_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_events_3460_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v_error_3461_);
lean_ctor_set(v_reuseFailAlloc_3489_, 5, v_instant_3462_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*6, v_keepAlive_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*6 + 1, v_forcedFlush_3464_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*6 + 2, v_pullBodyStalled_3465_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
v___y_3438_ = v___x_3488_;
goto v___jp_3437_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3453_);
v___y_3438_ = v_machine_3423_;
goto v___jp_3437_;
}
v___jp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___y_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___y_3438_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_requestStream_3424_);
lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_keepAliveTimeout_3425_);
lean_ctor_set(v_reuseFailAlloc_3450_, 3, v_currentTimeout_3426_);
lean_ctor_set(v_reuseFailAlloc_3450_, 4, v_headerTimeout_3427_);
lean_ctor_set(v_reuseFailAlloc_3450_, 5, v_response_3428_);
lean_ctor_set(v_reuseFailAlloc_3450_, 6, v_respStream_3429_);
lean_ctor_set(v_reuseFailAlloc_3450_, 7, v_expectData_3431_);
lean_ctor_set(v_reuseFailAlloc_3450_, 8, v_pendingHead_3433_);
lean_ctor_set_uint8(v_reuseFailAlloc_3450_, sizeof(void*)*9, v_requiresData_3430_);
lean_ctor_set_uint8(v_reuseFailAlloc_3450_, sizeof(void*)*9 + 1, v_handlerDispatched_3432_);
v___x_3440_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
uint8_t v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3441_ = 0;
v___x_3442_ = lean_box(v___x_3441_);
v___x_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3440_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3443_);
v___x_3445_ = v___x_3421_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set_tag(v___x_3392_, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3445_);
v___x_3447_ = v___x_3392_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
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
uint8_t v_x_3506_; 
lean_dec_ref(v_config_3278_);
lean_dec_ref(v_inst_3276_);
v_x_3506_ = lean_ctor_get_uint8(v_event_3279_, 0);
lean_dec_ref_known(v_event_3279_, 0);
if (v_x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec(v_handler_3277_);
lean_dec_ref(v_inst_3275_);
v___x_3507_ = lean_box(v_x_3506_);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_state_3280_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
return v___x_3510_;
}
else
{
lean_object* v_machine_3511_; lean_object* v_requestStream_3512_; lean_object* v_keepAliveTimeout_3513_; lean_object* v_currentTimeout_3514_; lean_object* v_headerTimeout_3515_; lean_object* v_response_3516_; lean_object* v_respStream_3517_; uint8_t v_requiresData_3518_; lean_object* v_expectData_3519_; uint8_t v_handlerDispatched_3520_; lean_object* v_pendingHead_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3571_; 
v_machine_3511_ = lean_ctor_get(v_state_3280_, 0);
v_requestStream_3512_ = lean_ctor_get(v_state_3280_, 1);
v_keepAliveTimeout_3513_ = lean_ctor_get(v_state_3280_, 2);
v_currentTimeout_3514_ = lean_ctor_get(v_state_3280_, 3);
v_headerTimeout_3515_ = lean_ctor_get(v_state_3280_, 4);
v_response_3516_ = lean_ctor_get(v_state_3280_, 5);
v_respStream_3517_ = lean_ctor_get(v_state_3280_, 6);
v_requiresData_3518_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3519_ = lean_ctor_get(v_state_3280_, 7);
v_handlerDispatched_3520_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9 + 1);
v_pendingHead_3521_ = lean_ctor_get(v_state_3280_, 8);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_state_3280_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3523_ = v_state_3280_;
v_isShared_3524_ = v_isSharedCheck_3571_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_pendingHead_3521_);
lean_inc(v_expectData_3519_);
lean_inc(v_respStream_3517_);
lean_inc(v_response_3516_);
lean_inc(v_headerTimeout_3515_);
lean_inc(v_currentTimeout_3514_);
lean_inc(v_keepAliveTimeout_3513_);
lean_inc(v_requestStream_3512_);
lean_inc(v_machine_3511_);
lean_dec(v_state_3280_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3571_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v_reader_3529_; lean_object* v_writer_3530_; lean_object* v_config_3531_; lean_object* v_events_3532_; lean_object* v_error_3533_; lean_object* v_instant_3534_; uint8_t v_keepAlive_3535_; uint8_t v_forcedFlush_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3570_; 
v___x_3525_ = 0;
v___x_3526_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3525_, v_machine_3511_);
v_fst_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_fst_3527_);
v_snd_3528_ = lean_ctor_get(v___x_3526_, 1);
lean_inc(v_snd_3528_);
lean_dec_ref(v___x_3526_);
v_reader_3529_ = lean_ctor_get(v_fst_3527_, 0);
v_writer_3530_ = lean_ctor_get(v_fst_3527_, 1);
v_config_3531_ = lean_ctor_get(v_fst_3527_, 2);
v_events_3532_ = lean_ctor_get(v_fst_3527_, 3);
v_error_3533_ = lean_ctor_get(v_fst_3527_, 4);
v_instant_3534_ = lean_ctor_get(v_fst_3527_, 5);
v_keepAlive_3535_ = lean_ctor_get_uint8(v_fst_3527_, sizeof(void*)*6);
v_forcedFlush_3536_ = lean_ctor_get_uint8(v_fst_3527_, sizeof(void*)*6 + 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_fst_3527_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3538_ = v_fst_3527_;
v_isShared_3539_ = v_isSharedCheck_3570_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_instant_3534_);
lean_inc(v_error_3533_);
lean_inc(v_events_3532_);
lean_inc(v_config_3531_);
lean_inc(v_writer_3530_);
lean_inc(v_reader_3529_);
lean_dec(v_fst_3527_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3570_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___f_3540_; lean_object* v___f_3541_; uint8_t v___y_3543_; 
v___f_3540_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3540_, 0, v_inst_3275_);
lean_closure_set(v___f_3540_, 1, v_handler_3277_);
v___f_3541_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3528_) == 0)
{
uint8_t v_sentMessage_3566_; 
v_sentMessage_3566_ = lean_ctor_get_uint8(v_writer_3530_, sizeof(void*)*6);
if (v_sentMessage_3566_ == 0)
{
lean_object* v_state_3567_; 
v_state_3567_ = lean_ctor_get(v_reader_3529_, 0);
if (lean_obj_tag(v_state_3567_) == 2)
{
v___y_3543_ = v_x_3506_;
goto v___jp_3542_;
}
else
{
v___y_3543_ = v_sentMessage_3566_;
goto v___jp_3542_;
}
}
else
{
uint8_t v___x_3568_; 
v___x_3568_ = 0;
v___y_3543_ = v___x_3568_;
goto v___jp_3542_;
}
}
else
{
uint8_t v___x_3569_; 
v___x_3569_ = 0;
v___y_3543_ = v___x_3569_;
goto v___jp_3542_;
}
v___jp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3539_ == 0)
{
v___x_3545_ = v___x_3538_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_reader_3529_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_writer_3530_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_config_3531_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_events_3532_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_error_3533_);
lean_ctor_set(v_reuseFailAlloc_3565_, 5, v_instant_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*6, v_keepAlive_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*6 + 1, v_forcedFlush_3536_);
v___x_3545_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v_st_3547_; 
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*6 + 2, v___y_3543_);
lean_inc_ref(v_requestStream_3512_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3545_);
v_st_3547_ = v___x_3523_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_requestStream_3512_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_keepAliveTimeout_3513_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_currentTimeout_3514_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_headerTimeout_3515_);
lean_ctor_set(v_reuseFailAlloc_3564_, 5, v_response_3516_);
lean_ctor_set(v_reuseFailAlloc_3564_, 6, v_respStream_3517_);
lean_ctor_set(v_reuseFailAlloc_3564_, 7, v_expectData_3519_);
lean_ctor_set(v_reuseFailAlloc_3564_, 8, v_pendingHead_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*9, v_requiresData_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*9 + 1, v_handlerDispatched_3520_);
v_st_3547_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___f_3548_; 
lean_inc_ref(v_st_3547_);
v___f_3548_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3548_, 0, v_st_3547_);
if (lean_obj_tag(v_snd_3528_) == 1)
{
lean_object* v_val_3549_; uint8_t v_final_3550_; uint8_t v_incomplete_3551_; lean_object* v_chunk_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___f_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; lean_object* v___f_3560_; lean_object* v___x_3561_; 
lean_dec_ref(v_st_3547_);
v_val_3549_ = lean_ctor_get(v_snd_3528_, 0);
lean_inc(v_val_3549_);
lean_dec_ref_known(v_snd_3528_, 1);
v_final_3550_ = lean_ctor_get_uint8(v_val_3549_, sizeof(void*)*1);
v_incomplete_3551_ = lean_ctor_get_uint8(v_val_3549_, sizeof(void*)*1 + 1);
v_chunk_3552_ = lean_ctor_get(v_val_3549_, 0);
lean_inc_ref(v_chunk_3552_);
lean_dec(v_val_3549_);
lean_inc_ref_n(v_requestStream_3512_, 2);
v___x_3553_ = l_Std_Http_Body_Stream_send(v_requestStream_3512_, v_chunk_3552_, v_incomplete_3551_);
v___x_3554_ = lean_unsigned_to_nat(0u);
v___x_3555_ = 0;
v___x_3556_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3554_, v___x_3555_, v___x_3553_, v___f_3540_);
lean_inc_ref_n(v___f_3548_, 2);
v___f_3557_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3557_, 0, v___f_3548_);
v___f_3558_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3558_, 0, v_requestStream_3512_);
lean_closure_set(v___f_3558_, 1, v___f_3557_);
lean_closure_set(v___f_3558_, 2, v___f_3548_);
v___x_3559_ = lean_box(v_final_3550_);
v___f_3560_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3560_, 0, v___x_3559_);
lean_closure_set(v___f_3560_, 1, v___f_3548_);
lean_closure_set(v___f_3560_, 2, v___f_3541_);
lean_closure_set(v___f_3560_, 3, v_requestStream_3512_);
lean_closure_set(v___f_3560_, 4, v___f_3558_);
v___x_3561_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3554_, v___x_3555_, v___x_3556_, v___f_3560_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec_ref(v___f_3548_);
lean_dec_ref(v___f_3540_);
lean_dec(v_snd_3528_);
lean_dec_ref(v_requestStream_3512_);
v___x_3562_ = lean_box(0);
v___x_3563_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3547_, v___x_3562_);
return v___x_3563_;
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
lean_object* v_x_3572_; 
v_x_3572_ = lean_ctor_get(v_event_3279_, 0);
lean_inc_ref(v_x_3572_);
lean_dec_ref_known(v_event_3279_, 1);
if (lean_obj_tag(v_x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v_onFailure_3574_; lean_object* v___x_3575_; lean_object* v___f_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; 
lean_dec_ref(v_config_3278_);
lean_dec_ref(v_inst_3276_);
v_a_3573_ = lean_ctor_get(v_x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v_x_3572_, 1);
v_onFailure_3574_ = lean_ctor_get(v_inst_3275_, 2);
lean_inc_ref(v_onFailure_3574_);
lean_dec_ref(v_inst_3275_);
v___x_3575_ = lean_apply_3(v_onFailure_3574_, v_handler_3277_, v_a_3573_, lean_box(0));
v___f_3576_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3576_, 0, v_state_3280_);
v___x_3577_ = lean_unsigned_to_nat(0u);
v___x_3578_ = 0;
v___x_3579_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3577_, v___x_3578_, v___x_3575_, v___f_3576_);
return v___x_3579_;
}
else
{
lean_object* v_machine_3580_; lean_object* v_reader_3581_; lean_object* v_state_3582_; 
lean_dec(v_handler_3277_);
lean_dec_ref(v_inst_3275_);
v_machine_3580_ = lean_ctor_get(v_state_3280_, 0);
lean_inc_ref(v_machine_3580_);
v_reader_3581_ = lean_ctor_get(v_machine_3580_, 0);
v_state_3582_ = lean_ctor_get(v_reader_3581_, 0);
if (lean_obj_tag(v_state_3582_) == 7)
{
lean_object* v_a_3583_; lean_object* v_requestStream_3584_; lean_object* v_keepAliveTimeout_3585_; lean_object* v_currentTimeout_3586_; lean_object* v_headerTimeout_3587_; lean_object* v_response_3588_; lean_object* v_respStream_3589_; uint8_t v_requiresData_3590_; lean_object* v_expectData_3591_; lean_object* v_pendingHead_3592_; lean_object* v_close_3593_; lean_object* v_isClosed_3594_; lean_object* v_body_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___f_3598_; lean_object* v___f_3599_; lean_object* v___f_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v_config_3278_);
v_a_3583_ = lean_ctor_get(v_x_3572_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v_x_3572_, 1);
v_requestStream_3584_ = lean_ctor_get(v_state_3280_, 1);
lean_inc_ref(v_requestStream_3584_);
v_keepAliveTimeout_3585_ = lean_ctor_get(v_state_3280_, 2);
lean_inc(v_keepAliveTimeout_3585_);
v_currentTimeout_3586_ = lean_ctor_get(v_state_3280_, 3);
lean_inc(v_currentTimeout_3586_);
v_headerTimeout_3587_ = lean_ctor_get(v_state_3280_, 4);
lean_inc(v_headerTimeout_3587_);
v_response_3588_ = lean_ctor_get(v_state_3280_, 5);
lean_inc_ref(v_response_3588_);
v_respStream_3589_ = lean_ctor_get(v_state_3280_, 6);
lean_inc(v_respStream_3589_);
v_requiresData_3590_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3591_ = lean_ctor_get(v_state_3280_, 7);
lean_inc(v_expectData_3591_);
v_pendingHead_3592_ = lean_ctor_get(v_state_3280_, 8);
lean_inc(v_pendingHead_3592_);
lean_dec_ref(v_state_3280_);
v_close_3593_ = lean_ctor_get(v_inst_3276_, 1);
lean_inc_ref(v_close_3593_);
v_isClosed_3594_ = lean_ctor_get(v_inst_3276_, 2);
lean_inc_ref(v_isClosed_3594_);
lean_dec_ref(v_inst_3276_);
v_body_3595_ = lean_ctor_get(v_a_3583_, 1);
lean_inc_n(v_body_3595_, 2);
lean_dec(v_a_3583_);
v___x_3596_ = lean_apply_2(v_isClosed_3594_, v_body_3595_, lean_box(0));
v___x_3597_ = lean_box(v_requiresData_3590_);
v___f_3598_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3598_, 0, v_machine_3580_);
lean_closure_set(v___f_3598_, 1, v_requestStream_3584_);
lean_closure_set(v___f_3598_, 2, v_keepAliveTimeout_3585_);
lean_closure_set(v___f_3598_, 3, v_currentTimeout_3586_);
lean_closure_set(v___f_3598_, 4, v_headerTimeout_3587_);
lean_closure_set(v___f_3598_, 5, v_response_3588_);
lean_closure_set(v___f_3598_, 6, v_respStream_3589_);
lean_closure_set(v___f_3598_, 7, v___x_3597_);
lean_closure_set(v___f_3598_, 8, v_expectData_3591_);
lean_closure_set(v___f_3598_, 9, v_pendingHead_3592_);
lean_inc_ref(v___f_3598_);
v___f_3599_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3599_, 0, v___f_3598_);
v___f_3600_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3600_, 0, v_close_3593_);
lean_closure_set(v___f_3600_, 1, v_body_3595_);
lean_closure_set(v___f_3600_, 2, v___f_3599_);
lean_closure_set(v___f_3600_, 3, v___f_3598_);
v___x_3601_ = lean_unsigned_to_nat(0u);
v___x_3602_ = 0;
v___x_3603_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3601_, v___x_3602_, v___x_3596_, v___f_3600_);
return v___x_3603_;
}
else
{
lean_object* v_a_3604_; lean_object* v_requestStream_3605_; lean_object* v_keepAliveTimeout_3606_; lean_object* v_currentTimeout_3607_; lean_object* v_headerTimeout_3608_; lean_object* v_response_3609_; uint8_t v_requiresData_3610_; lean_object* v_expectData_3611_; lean_object* v_pendingHead_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___f_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_a_3604_ = lean_ctor_get(v_x_3572_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v_x_3572_, 1);
v_requestStream_3605_ = lean_ctor_get(v_state_3280_, 1);
lean_inc_ref(v_requestStream_3605_);
v_keepAliveTimeout_3606_ = lean_ctor_get(v_state_3280_, 2);
lean_inc(v_keepAliveTimeout_3606_);
v_currentTimeout_3607_ = lean_ctor_get(v_state_3280_, 3);
lean_inc(v_currentTimeout_3607_);
v_headerTimeout_3608_ = lean_ctor_get(v_state_3280_, 4);
lean_inc(v_headerTimeout_3608_);
v_response_3609_ = lean_ctor_get(v_state_3280_, 5);
lean_inc_ref(v_response_3609_);
v_requiresData_3610_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3611_ = lean_ctor_get(v_state_3280_, 7);
lean_inc(v_expectData_3611_);
v_pendingHead_3612_ = lean_ctor_get(v_state_3280_, 8);
lean_inc(v_pendingHead_3612_);
lean_dec_ref(v_state_3280_);
lean_inc_ref(v_inst_3276_);
v___x_3613_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3276_, v_config_3278_, v_machine_3580_, v_a_3604_);
v___x_3614_ = 0;
v___x_3615_ = lean_box(v_requiresData_3610_);
v___x_3616_ = lean_box(v___x_3614_);
v___f_3617_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3617_, 0, v_requestStream_3605_);
lean_closure_set(v___f_3617_, 1, v_keepAliveTimeout_3606_);
lean_closure_set(v___f_3617_, 2, v_currentTimeout_3607_);
lean_closure_set(v___f_3617_, 3, v_headerTimeout_3608_);
lean_closure_set(v___f_3617_, 4, v_response_3609_);
lean_closure_set(v___f_3617_, 5, v___x_3615_);
lean_closure_set(v___f_3617_, 6, v_expectData_3611_);
lean_closure_set(v___f_3617_, 7, v___x_3616_);
lean_closure_set(v___f_3617_, 8, v_pendingHead_3612_);
v___f_3618_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3618_, 0, v___f_3617_);
v___x_3619_ = lean_box(v___x_3614_);
lean_inc_ref(v___f_3618_);
v___f_3620_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 6, 4);
lean_closure_set(v___f_3620_, 0, v___x_3619_);
lean_closure_set(v___f_3620_, 1, v___f_3618_);
lean_closure_set(v___f_3620_, 2, v_inst_3276_);
lean_closure_set(v___f_3620_, 3, v___f_3618_);
v___x_3621_ = lean_unsigned_to_nat(0u);
v___x_3622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3621_, v___x_3614_, v___x_3613_, v___f_3620_);
return v___x_3622_;
}
}
}
case 4:
{
lean_object* v_onFailure_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; 
lean_dec_ref(v_config_3278_);
lean_dec_ref(v_inst_3276_);
v_onFailure_3623_ = lean_ctor_get(v_inst_3275_, 2);
lean_inc_ref(v_onFailure_3623_);
lean_dec_ref(v_inst_3275_);
v___x_3624_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_3625_ = lean_apply_3(v_onFailure_3623_, v_handler_3277_, v___x_3624_, lean_box(0));
v___f_3626_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 3, 1);
lean_closure_set(v___f_3626_, 0, v_state_3280_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = 0;
v___x_3629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3627_, v___x_3628_, v___x_3625_, v___f_3626_);
return v___x_3629_;
}
case 5:
{
lean_object* v_machine_3630_; lean_object* v_requestStream_3631_; lean_object* v_keepAliveTimeout_3632_; lean_object* v_currentTimeout_3633_; lean_object* v_headerTimeout_3634_; lean_object* v_response_3635_; lean_object* v_respStream_3636_; uint8_t v_requiresData_3637_; lean_object* v_expectData_3638_; lean_object* v_pendingHead_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v_config_3278_);
lean_dec(v_handler_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
v_machine_3630_ = lean_ctor_get(v_state_3280_, 0);
v_requestStream_3631_ = lean_ctor_get(v_state_3280_, 1);
v_keepAliveTimeout_3632_ = lean_ctor_get(v_state_3280_, 2);
v_currentTimeout_3633_ = lean_ctor_get(v_state_3280_, 3);
v_headerTimeout_3634_ = lean_ctor_get(v_state_3280_, 4);
v_response_3635_ = lean_ctor_get(v_state_3280_, 5);
v_respStream_3636_ = lean_ctor_get(v_state_3280_, 6);
v_requiresData_3637_ = lean_ctor_get_uint8(v_state_3280_, sizeof(void*)*9);
v_expectData_3638_ = lean_ctor_get(v_state_3280_, 7);
v_pendingHead_3639_ = lean_ctor_get(v_state_3280_, 8);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_state_3280_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3641_ = v_state_3280_;
v_isShared_3642_ = v_isSharedCheck_3653_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_pendingHead_3639_);
lean_inc(v_expectData_3638_);
lean_inc(v_respStream_3636_);
lean_inc(v_response_3635_);
lean_inc(v_headerTimeout_3634_);
lean_inc(v_currentTimeout_3633_);
lean_inc(v_keepAliveTimeout_3632_);
lean_inc(v_requestStream_3631_);
lean_inc(v_machine_3630_);
lean_dec(v_state_3280_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3653_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; lean_object* v___x_3647_; 
v___x_3643_ = lean_box(55);
v___x_3644_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3630_, v___x_3643_);
v___x_3645_ = 0;
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3644_);
v___x_3647_ = v___x_3641_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_requestStream_3631_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_keepAliveTimeout_3632_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_currentTimeout_3633_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v_headerTimeout_3634_);
lean_ctor_set(v_reuseFailAlloc_3652_, 5, v_response_3635_);
lean_ctor_set(v_reuseFailAlloc_3652_, 6, v_respStream_3636_);
lean_ctor_set(v_reuseFailAlloc_3652_, 7, v_expectData_3638_);
lean_ctor_set(v_reuseFailAlloc_3652_, 8, v_pendingHead_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3652_, sizeof(void*)*9, v_requiresData_3637_);
v___x_3647_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*9 + 1, v___x_3645_);
v___x_3648_ = lean_box(v___x_3645_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
}
}
default: 
{
uint8_t v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
lean_dec_ref(v_config_3278_);
lean_dec(v_handler_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
v___x_3654_ = 1;
v___x_3655_ = lean_box(v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v_state_3280_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
v___x_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
return v___x_3658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_handler_3661_, lean_object* v_config_3662_, lean_object* v_event_3663_, lean_object* v_state_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3659_, v_inst_3660_, v_handler_3661_, v_config_3662_, v_event_3663_, v_state_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3667_, lean_object* v_00_u03b2_3668_, lean_object* v_inst_3669_, lean_object* v_inst_3670_, lean_object* v_handler_3671_, lean_object* v_config_3672_, lean_object* v_event_3673_, lean_object* v_state_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3669_, v_inst_3670_, v_handler_3671_, v_config_3672_, v_event_3673_, v_state_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3677_, lean_object* v_00_u03b2_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_handler_3681_, lean_object* v_config_3682_, lean_object* v_event_3683_, lean_object* v_state_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3677_, v_00_u03b2_3678_, v_inst_3679_, v_inst_3680_, v_handler_3681_, v_config_3682_, v_event_3683_, v_state_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3687_, uint8_t v_handlerDispatched_3688_, lean_object* v_headerTimeout_3689_, lean_object* v_keepAliveTimeout_3690_, lean_object* v_currentTimeout_3691_, lean_object* v_respStream_3692_, lean_object* v_expectData_3693_, lean_object* v_response_3694_, lean_object* v_socket_3695_, uint8_t v_requiresData_3696_, uint8_t v_sentMessage_3697_, lean_object* v_reader_3698_, uint8_t v_requestBodyInterested_3699_, lean_object* v_requestBody_3700_){
_start:
{
lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3714_; 
if (v_requiresData_3696_ == 0)
{
if (v_handlerDispatched_3688_ == 0)
{
goto v___jp_3717_;
}
else
{
if (lean_obj_tag(v_respStream_3692_) == 0)
{
if (v_sentMessage_3697_ == 0)
{
lean_object* v_state_3721_; 
v_state_3721_ = lean_ctor_get(v_reader_3698_, 0);
if (lean_obj_tag(v_state_3721_) == 2)
{
if (v_requestBodyInterested_3699_ == 0)
{
lean_dec(v_socket_3695_);
goto v___jp_3719_;
}
else
{
goto v___jp_3717_;
}
}
else
{
lean_dec(v_socket_3695_);
goto v___jp_3719_;
}
}
else
{
goto v___jp_3717_;
}
}
else
{
goto v___jp_3717_;
}
}
}
else
{
goto v___jp_3717_;
}
v___jp_3702_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3710_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3710_, 0, v___y_3704_);
lean_ctor_set(v___x_3710_, 1, v___y_3708_);
lean_ctor_set(v___x_3710_, 2, v___y_3709_);
lean_ctor_set(v___x_3710_, 3, v___y_3707_);
lean_ctor_set(v___x_3710_, 4, v_requestBody_3700_);
lean_ctor_set(v___x_3710_, 5, v___y_3706_);
lean_ctor_set(v___x_3710_, 6, v___y_3705_);
lean_ctor_set(v___x_3710_, 7, v___y_3703_);
lean_ctor_set(v___x_3710_, 8, v_connectionContext_3687_);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
v___jp_3713_:
{
if (v_handlerDispatched_3688_ == 0)
{
lean_object* v___x_3715_; 
lean_dec_ref(v_response_3694_);
v___x_3715_ = lean_box(0);
v___y_3703_ = v_headerTimeout_3689_;
v___y_3704_ = v___y_3714_;
v___y_3705_ = v_keepAliveTimeout_3690_;
v___y_3706_ = v_currentTimeout_3691_;
v___y_3707_ = v_respStream_3692_;
v___y_3708_ = v_expectData_3693_;
v___y_3709_ = v___x_3715_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_response_3694_);
v___y_3703_ = v_headerTimeout_3689_;
v___y_3704_ = v___y_3714_;
v___y_3705_ = v_keepAliveTimeout_3690_;
v___y_3706_ = v_currentTimeout_3691_;
v___y_3707_ = v_respStream_3692_;
v___y_3708_ = v_expectData_3693_;
v___y_3709_ = v___x_3716_;
goto v___jp_3702_;
}
}
v___jp_3717_:
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v_socket_3695_);
v___y_3714_ = v___x_3718_;
goto v___jp_3713_;
}
v___jp_3719_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_box(0);
v___y_3714_ = v___x_3720_;
goto v___jp_3713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3722_, lean_object* v_handlerDispatched_3723_, lean_object* v_headerTimeout_3724_, lean_object* v_keepAliveTimeout_3725_, lean_object* v_currentTimeout_3726_, lean_object* v_respStream_3727_, lean_object* v_expectData_3728_, lean_object* v_response_3729_, lean_object* v_socket_3730_, lean_object* v_requiresData_3731_, lean_object* v_sentMessage_3732_, lean_object* v_reader_3733_, lean_object* v_requestBodyInterested_3734_, lean_object* v_requestBody_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v_handlerDispatched_boxed_3737_; uint8_t v_requiresData_boxed_3738_; uint8_t v_sentMessage_boxed_3739_; uint8_t v_requestBodyInterested_boxed_3740_; lean_object* v_res_3741_; 
v_handlerDispatched_boxed_3737_ = lean_unbox(v_handlerDispatched_3723_);
v_requiresData_boxed_3738_ = lean_unbox(v_requiresData_3731_);
v_sentMessage_boxed_3739_ = lean_unbox(v_sentMessage_3732_);
v_requestBodyInterested_boxed_3740_ = lean_unbox(v_requestBodyInterested_3734_);
v_res_3741_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3722_, v_handlerDispatched_boxed_3737_, v_headerTimeout_3724_, v_keepAliveTimeout_3725_, v_currentTimeout_3726_, v_respStream_3727_, v_expectData_3728_, v_response_3729_, v_socket_3730_, v_requiresData_boxed_3738_, v_sentMessage_boxed_3739_, v_reader_3733_, v_requestBodyInterested_boxed_3740_, v_requestBody_3735_);
lean_dec_ref(v_reader_3733_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3742_, lean_object* v_x_3743_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v___f_3742_);
v_a_3745_ = lean_ctor_get(v_x_3743_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_x_3743_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3747_ = v_x_3743_;
v_isShared_3748_ = v_isSharedCheck_3753_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v_x_3743_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3753_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3755_; 
v_a_3754_ = lean_ctor_get(v_x_3743_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v_x_3743_, 1);
v___x_3755_ = lean_apply_2(v___f_3742_, v_a_3754_, lean_box(0));
return v___x_3755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3756_, v_x_3757_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3764_, uint8_t v_handlerDispatched_3765_, lean_object* v_headerTimeout_3766_, lean_object* v_keepAliveTimeout_3767_, lean_object* v_currentTimeout_3768_, lean_object* v_respStream_3769_, lean_object* v_expectData_3770_, lean_object* v_response_3771_, lean_object* v_socket_3772_, uint8_t v_requiresData_3773_, uint8_t v_sentMessage_3774_, lean_object* v_reader_3775_, uint8_t v_pullBodyStalled_3776_, uint8_t v_requestBodyOpen_3777_, lean_object* v_requestStream_3778_, uint8_t v_requestBodyInterested_3779_){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___f_3785_; lean_object* v___f_3786_; 
v___x_3781_ = lean_box(v_handlerDispatched_3765_);
v___x_3782_ = lean_box(v_requiresData_3773_);
v___x_3783_ = lean_box(v_sentMessage_3774_);
v___x_3784_ = lean_box(v_requestBodyInterested_3779_);
lean_inc_ref(v_reader_3775_);
v___f_3785_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3785_, 0, v_connectionContext_3764_);
lean_closure_set(v___f_3785_, 1, v___x_3781_);
lean_closure_set(v___f_3785_, 2, v_headerTimeout_3766_);
lean_closure_set(v___f_3785_, 3, v_keepAliveTimeout_3767_);
lean_closure_set(v___f_3785_, 4, v_currentTimeout_3768_);
lean_closure_set(v___f_3785_, 5, v_respStream_3769_);
lean_closure_set(v___f_3785_, 6, v_expectData_3770_);
lean_closure_set(v___f_3785_, 7, v_response_3771_);
lean_closure_set(v___f_3785_, 8, v_socket_3772_);
lean_closure_set(v___f_3785_, 9, v___x_3782_);
lean_closure_set(v___f_3785_, 10, v___x_3783_);
lean_closure_set(v___f_3785_, 11, v_reader_3775_);
lean_closure_set(v___f_3785_, 12, v___x_3784_);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3786_, 0, v___f_3785_);
if (v_sentMessage_3774_ == 0)
{
lean_object* v_state_3792_; 
v_state_3792_ = lean_ctor_get(v_reader_3775_, 0);
lean_inc(v_state_3792_);
lean_dec_ref(v_reader_3775_);
if (lean_obj_tag(v_state_3792_) == 2)
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3803_; 
v_isSharedCheck_3803_ = !lean_is_exclusive(v_state_3792_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; 
v_unused_3804_ = lean_ctor_get(v_state_3792_, 0);
lean_dec(v_unused_3804_);
v___x_3794_ = v_state_3792_;
v_isShared_3795_ = v_isSharedCheck_3803_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v_state_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3803_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
if (v_pullBodyStalled_3776_ == 0)
{
if (v_requestBodyOpen_3777_ == 0)
{
lean_del_object(v___x_3794_);
lean_dec_ref(v_requestStream_3778_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 1);
lean_ctor_set(v___x_3794_, 0, v_requestStream_3778_);
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_requestStream_3778_);
v___x_3797_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
v___x_3800_ = lean_unsigned_to_nat(0u);
v___x_3801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3800_, v_pullBodyStalled_3776_, v___x_3799_, v___f_3786_);
return v___x_3801_;
}
}
}
else
{
lean_del_object(v___x_3794_);
lean_dec_ref(v_requestStream_3778_);
goto v___jp_3787_;
}
}
}
else
{
lean_dec(v_state_3792_);
lean_dec_ref(v_requestStream_3778_);
goto v___jp_3787_;
}
}
else
{
lean_dec_ref(v_requestStream_3778_);
lean_dec_ref(v_reader_3775_);
goto v___jp_3787_;
}
v___jp_3787_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; lean_object* v___x_3791_; 
v___x_3788_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3789_ = lean_unsigned_to_nat(0u);
v___x_3790_ = 0;
v___x_3791_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3789_, v___x_3790_, v___x_3788_, v___f_3786_);
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3805_ = _args[0];
lean_object* v_handlerDispatched_3806_ = _args[1];
lean_object* v_headerTimeout_3807_ = _args[2];
lean_object* v_keepAliveTimeout_3808_ = _args[3];
lean_object* v_currentTimeout_3809_ = _args[4];
lean_object* v_respStream_3810_ = _args[5];
lean_object* v_expectData_3811_ = _args[6];
lean_object* v_response_3812_ = _args[7];
lean_object* v_socket_3813_ = _args[8];
lean_object* v_requiresData_3814_ = _args[9];
lean_object* v_sentMessage_3815_ = _args[10];
lean_object* v_reader_3816_ = _args[11];
lean_object* v_pullBodyStalled_3817_ = _args[12];
lean_object* v_requestBodyOpen_3818_ = _args[13];
lean_object* v_requestStream_3819_ = _args[14];
lean_object* v_requestBodyInterested_3820_ = _args[15];
lean_object* v___y_3821_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3822_; uint8_t v_requiresData_boxed_3823_; uint8_t v_sentMessage_boxed_3824_; uint8_t v_pullBodyStalled_boxed_3825_; uint8_t v_requestBodyOpen_boxed_3826_; uint8_t v_requestBodyInterested_boxed_3827_; lean_object* v_res_3828_; 
v_handlerDispatched_boxed_3822_ = lean_unbox(v_handlerDispatched_3806_);
v_requiresData_boxed_3823_ = lean_unbox(v_requiresData_3814_);
v_sentMessage_boxed_3824_ = lean_unbox(v_sentMessage_3815_);
v_pullBodyStalled_boxed_3825_ = lean_unbox(v_pullBodyStalled_3817_);
v_requestBodyOpen_boxed_3826_ = lean_unbox(v_requestBodyOpen_3818_);
v_requestBodyInterested_boxed_3827_ = lean_unbox(v_requestBodyInterested_3820_);
v_res_3828_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3805_, v_handlerDispatched_boxed_3822_, v_headerTimeout_3807_, v_keepAliveTimeout_3808_, v_currentTimeout_3809_, v_respStream_3810_, v_expectData_3811_, v_response_3812_, v_socket_3813_, v_requiresData_boxed_3823_, v_sentMessage_boxed_3824_, v_reader_3816_, v_pullBodyStalled_boxed_3825_, v_requestBodyOpen_boxed_3826_, v_requestStream_3819_, v_requestBodyInterested_boxed_3827_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3829_, lean_object* v_x_3830_){
_start:
{
if (lean_obj_tag(v_x_3830_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v___f_3829_);
v_a_3832_ = lean_ctor_get(v_x_3830_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_x_3830_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3834_ = v_x_3830_;
v_isShared_3835_ = v_isSharedCheck_3840_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v_x_3830_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3840_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v_x_3830_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v_x_3830_, 1);
v___x_3842_ = lean_apply_2(v___f_3829_, v_a_3841_, lean_box(0));
return v___x_3842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3843_, lean_object* v_x_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3843_, v_x_3844_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3852_, uint8_t v_handlerDispatched_3853_, lean_object* v_headerTimeout_3854_, lean_object* v_keepAliveTimeout_3855_, lean_object* v_currentTimeout_3856_, lean_object* v_respStream_3857_, lean_object* v_expectData_3858_, lean_object* v_response_3859_, lean_object* v_socket_3860_, uint8_t v_requiresData_3861_, uint8_t v_sentMessage_3862_, lean_object* v_reader_3863_, uint8_t v_pullBodyStalled_3864_, lean_object* v_requestStream_3865_, uint8_t v_requestBodyOpen_3866_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; 
v___x_3868_ = lean_box(v_handlerDispatched_3853_);
v___x_3869_ = lean_box(v_requiresData_3861_);
v___x_3870_ = lean_box(v_sentMessage_3862_);
v___x_3871_ = lean_box(v_pullBodyStalled_3864_);
v___x_3872_ = lean_box(v_requestBodyOpen_3866_);
lean_inc_ref(v_requestStream_3865_);
lean_inc_ref(v_reader_3863_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3873_, 0, v_connectionContext_3852_);
lean_closure_set(v___f_3873_, 1, v___x_3868_);
lean_closure_set(v___f_3873_, 2, v_headerTimeout_3854_);
lean_closure_set(v___f_3873_, 3, v_keepAliveTimeout_3855_);
lean_closure_set(v___f_3873_, 4, v_currentTimeout_3856_);
lean_closure_set(v___f_3873_, 5, v_respStream_3857_);
lean_closure_set(v___f_3873_, 6, v_expectData_3858_);
lean_closure_set(v___f_3873_, 7, v_response_3859_);
lean_closure_set(v___f_3873_, 8, v_socket_3860_);
lean_closure_set(v___f_3873_, 9, v___x_3869_);
lean_closure_set(v___f_3873_, 10, v___x_3870_);
lean_closure_set(v___f_3873_, 11, v_reader_3863_);
lean_closure_set(v___f_3873_, 12, v___x_3871_);
lean_closure_set(v___f_3873_, 13, v___x_3872_);
lean_closure_set(v___f_3873_, 14, v_requestStream_3865_);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3874_, 0, v___f_3873_);
if (v_sentMessage_3862_ == 0)
{
lean_object* v_state_3880_; 
v_state_3880_ = lean_ctor_get(v_reader_3863_, 0);
lean_inc(v_state_3880_);
lean_dec_ref(v_reader_3863_);
if (lean_obj_tag(v_state_3880_) == 2)
{
lean_dec_ref_known(v_state_3880_, 1);
if (v_requestBodyOpen_3866_ == 0)
{
lean_dec_ref(v_requestStream_3865_);
goto v___jp_3875_;
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3865_);
v___x_3882_ = lean_unsigned_to_nat(0u);
v___x_3883_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3882_, v_sentMessage_3862_, v___x_3881_, v___f_3874_);
return v___x_3883_;
}
}
else
{
lean_dec(v_state_3880_);
lean_dec_ref(v_requestStream_3865_);
goto v___jp_3875_;
}
}
else
{
lean_dec_ref(v_requestStream_3865_);
lean_dec_ref(v_reader_3863_);
goto v___jp_3875_;
}
v___jp_3875_:
{
uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3876_ = 0;
v___x_3877_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3878_ = lean_unsigned_to_nat(0u);
v___x_3879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3878_, v___x_3876_, v___x_3877_, v___f_3874_);
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3884_, lean_object* v_handlerDispatched_3885_, lean_object* v_headerTimeout_3886_, lean_object* v_keepAliveTimeout_3887_, lean_object* v_currentTimeout_3888_, lean_object* v_respStream_3889_, lean_object* v_expectData_3890_, lean_object* v_response_3891_, lean_object* v_socket_3892_, lean_object* v_requiresData_3893_, lean_object* v_sentMessage_3894_, lean_object* v_reader_3895_, lean_object* v_pullBodyStalled_3896_, lean_object* v_requestStream_3897_, lean_object* v_requestBodyOpen_3898_, lean_object* v___y_3899_){
_start:
{
uint8_t v_handlerDispatched_boxed_3900_; uint8_t v_requiresData_boxed_3901_; uint8_t v_sentMessage_boxed_3902_; uint8_t v_pullBodyStalled_boxed_3903_; uint8_t v_requestBodyOpen_boxed_3904_; lean_object* v_res_3905_; 
v_handlerDispatched_boxed_3900_ = lean_unbox(v_handlerDispatched_3885_);
v_requiresData_boxed_3901_ = lean_unbox(v_requiresData_3893_);
v_sentMessage_boxed_3902_ = lean_unbox(v_sentMessage_3894_);
v_pullBodyStalled_boxed_3903_ = lean_unbox(v_pullBodyStalled_3896_);
v_requestBodyOpen_boxed_3904_ = lean_unbox(v_requestBodyOpen_3898_);
v_res_3905_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3884_, v_handlerDispatched_boxed_3900_, v_headerTimeout_3886_, v_keepAliveTimeout_3887_, v_currentTimeout_3888_, v_respStream_3889_, v_expectData_3890_, v_response_3891_, v_socket_3892_, v_requiresData_boxed_3901_, v_sentMessage_boxed_3902_, v_reader_3895_, v_pullBodyStalled_boxed_3903_, v_requestStream_3897_, v_requestBodyOpen_boxed_3904_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3906_, lean_object* v___f_3907_, uint8_t v___x_3908_, lean_object* v_x_3909_){
_start:
{
uint8_t v___y_3912_; 
if (lean_obj_tag(v_x_3909_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3926_; 
lean_dec_ref(v___f_3907_);
v_a_3918_ = lean_ctor_get(v_x_3909_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_x_3909_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3920_ = v_x_3909_;
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v_x_3909_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
else
{
lean_object* v_a_3927_; uint8_t v___x_3928_; 
v_a_3927_ = lean_ctor_get(v_x_3909_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v_x_3909_, 1);
v___x_3928_ = lean_unbox(v_a_3927_);
lean_dec(v_a_3927_);
if (v___x_3928_ == 0)
{
v___y_3912_ = v___x_3908_;
goto v___jp_3911_;
}
else
{
v___y_3912_ = v_sentMessage_3906_;
goto v___jp_3911_;
}
}
v___jp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3913_ = lean_box(v___y_3912_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___x_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
v___x_3916_ = lean_unsigned_to_nat(0u);
v___x_3917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3916_, v_sentMessage_3906_, v___x_3915_, v___f_3907_);
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3929_, lean_object* v___f_3930_, lean_object* v___x_3931_, lean_object* v_x_3932_, lean_object* v___y_3933_){
_start:
{
uint8_t v_sentMessage_boxed_3934_; uint8_t v___x_3791__boxed_3935_; lean_object* v_res_3936_; 
v_sentMessage_boxed_3934_ = lean_unbox(v_sentMessage_3929_);
v___x_3791__boxed_3935_ = lean_unbox(v___x_3931_);
v_res_3936_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3934_, v___f_3930_, v___x_3791__boxed_3935_, v_x_3932_);
return v_res_3936_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___f_3937_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3938_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3939_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3940_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_3940_, 0, lean_box(0));
lean_closure_set(v___x_3940_, 1, lean_box(0));
lean_closure_set(v___x_3940_, 2, lean_box(0));
lean_closure_set(v___x_3940_, 3, v___x_3939_);
lean_closure_set(v___x_3940_, 4, lean_box(0));
lean_closure_set(v___x_3940_, 5, lean_box(0));
lean_closure_set(v___x_3940_, 6, v___x_3938_);
lean_closure_set(v___x_3940_, 7, v___f_3937_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3941_, lean_object* v_connectionContext_3942_, lean_object* v_state_3943_){
_start:
{
lean_object* v_machine_3945_; lean_object* v_writer_3946_; lean_object* v_requestStream_3947_; lean_object* v_keepAliveTimeout_3948_; lean_object* v_currentTimeout_3949_; lean_object* v_headerTimeout_3950_; lean_object* v_response_3951_; lean_object* v_respStream_3952_; uint8_t v_requiresData_3953_; lean_object* v_expectData_3954_; uint8_t v_handlerDispatched_3955_; lean_object* v_reader_3956_; uint8_t v_pullBodyStalled_3957_; uint8_t v_sentMessage_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___f_3963_; lean_object* v___f_3964_; uint8_t v___y_3966_; 
v_machine_3945_ = lean_ctor_get(v_state_3943_, 0);
lean_inc_ref(v_machine_3945_);
v_writer_3946_ = lean_ctor_get(v_machine_3945_, 1);
lean_inc_ref(v_writer_3946_);
v_requestStream_3947_ = lean_ctor_get(v_state_3943_, 1);
lean_inc_ref_n(v_requestStream_3947_, 2);
v_keepAliveTimeout_3948_ = lean_ctor_get(v_state_3943_, 2);
lean_inc(v_keepAliveTimeout_3948_);
v_currentTimeout_3949_ = lean_ctor_get(v_state_3943_, 3);
lean_inc(v_currentTimeout_3949_);
v_headerTimeout_3950_ = lean_ctor_get(v_state_3943_, 4);
lean_inc(v_headerTimeout_3950_);
v_response_3951_ = lean_ctor_get(v_state_3943_, 5);
lean_inc_ref(v_response_3951_);
v_respStream_3952_ = lean_ctor_get(v_state_3943_, 6);
lean_inc(v_respStream_3952_);
v_requiresData_3953_ = lean_ctor_get_uint8(v_state_3943_, sizeof(void*)*9);
v_expectData_3954_ = lean_ctor_get(v_state_3943_, 7);
lean_inc(v_expectData_3954_);
v_handlerDispatched_3955_ = lean_ctor_get_uint8(v_state_3943_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3943_);
v_reader_3956_ = lean_ctor_get(v_machine_3945_, 0);
lean_inc_ref_n(v_reader_3956_, 2);
v_pullBodyStalled_3957_ = lean_ctor_get_uint8(v_machine_3945_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3945_);
v_sentMessage_3958_ = lean_ctor_get_uint8(v_writer_3946_, sizeof(void*)*6);
lean_dec_ref(v_writer_3946_);
v___x_3959_ = lean_box(v_handlerDispatched_3955_);
v___x_3960_ = lean_box(v_requiresData_3953_);
v___x_3961_ = lean_box(v_sentMessage_3958_);
v___x_3962_ = lean_box(v_pullBodyStalled_3957_);
v___f_3963_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3963_, 0, v_connectionContext_3942_);
lean_closure_set(v___f_3963_, 1, v___x_3959_);
lean_closure_set(v___f_3963_, 2, v_headerTimeout_3950_);
lean_closure_set(v___f_3963_, 3, v_keepAliveTimeout_3948_);
lean_closure_set(v___f_3963_, 4, v_currentTimeout_3949_);
lean_closure_set(v___f_3963_, 5, v_respStream_3952_);
lean_closure_set(v___f_3963_, 6, v_expectData_3954_);
lean_closure_set(v___f_3963_, 7, v_response_3951_);
lean_closure_set(v___f_3963_, 8, v_socket_3941_);
lean_closure_set(v___f_3963_, 9, v___x_3960_);
lean_closure_set(v___f_3963_, 10, v___x_3961_);
lean_closure_set(v___f_3963_, 11, v_reader_3956_);
lean_closure_set(v___f_3963_, 12, v___x_3962_);
lean_closure_set(v___f_3963_, 13, v_requestStream_3947_);
v___f_3964_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3964_, 0, v___f_3963_);
if (v_sentMessage_3958_ == 0)
{
lean_object* v_state_3972_; 
v_state_3972_ = lean_ctor_get(v_reader_3956_, 0);
lean_inc(v_state_3972_);
lean_dec_ref(v_reader_3956_);
if (lean_obj_tag(v_state_3972_) == 2)
{
lean_object* v___x_3973_; lean_object* v___f_3974_; lean_object* v___f_3975_; lean_object* v___x_3976_; lean_object* v___x_3305__overap_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___f_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_dec_ref_known(v_state_3972_, 1);
v___x_3973_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3974_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3975_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3976_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3305__overap_3977_ = l_Std_Mutex_atomically___redArg(v___x_3973_, v___f_3974_, v___f_3975_, v_requestStream_3947_, v___x_3976_);
v___x_3978_ = lean_apply_1(v___x_3305__overap_3977_, lean_box(0));
v___x_3979_ = 1;
v___x_3980_ = lean_box(v_sentMessage_3958_);
v___x_3981_ = lean_box(v___x_3979_);
v___f_3982_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3982_, 0, v___x_3980_);
lean_closure_set(v___f_3982_, 1, v___f_3964_);
lean_closure_set(v___f_3982_, 2, v___x_3981_);
v___x_3983_ = lean_unsigned_to_nat(0u);
v___x_3984_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3983_, v_sentMessage_3958_, v___x_3978_, v___f_3982_);
return v___x_3984_;
}
else
{
lean_dec(v_state_3972_);
lean_dec_ref(v_requestStream_3947_);
v___y_3966_ = v_sentMessage_3958_;
goto v___jp_3965_;
}
}
else
{
uint8_t v___x_3985_; 
lean_dec_ref(v_reader_3956_);
lean_dec_ref(v_requestStream_3947_);
v___x_3985_ = 0;
v___y_3966_ = v___x_3985_;
goto v___jp_3965_;
}
v___jp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3967_ = lean_box(v___y_3966_);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3970_, v___y_3966_, v___x_3969_, v___f_3964_);
return v___x_3971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3986_, lean_object* v_connectionContext_3987_, lean_object* v_state_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3986_, v_connectionContext_3987_, v_state_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3991_, lean_object* v_00_u03b2_3992_, lean_object* v_inst_3993_, lean_object* v_socket_3994_, lean_object* v_connectionContext_3995_, lean_object* v_state_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3994_, v_connectionContext_3995_, v_state_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_3999_, lean_object* v_00_u03b2_4000_, lean_object* v_inst_4001_, lean_object* v_socket_4002_, lean_object* v_connectionContext_4003_, lean_object* v_state_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_3999_, v_00_u03b2_4000_, v_inst_4001_, v_socket_4002_, v_connectionContext_4003_, v_state_4004_);
lean_dec_ref(v_inst_4001_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4007_){
_start:
{
if (lean_obj_tag(v_x_4007_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4017_; 
v_a_4009_ = lean_ctor_get(v_x_4007_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_x_4007_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4011_ = v_x_4007_;
v_isShared_4012_ = v_isSharedCheck_4017_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v_x_4007_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4017_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4009_);
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
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4036_; 
v_a_4018_ = lean_ctor_get(v_x_4007_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_x_4007_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4020_ = v_x_4007_;
v_isShared_4021_ = v_isSharedCheck_4036_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v_x_4007_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4036_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v_snd_4022_; uint8_t v___x_4023_; 
v_snd_4022_ = lean_ctor_get(v_a_4018_, 1);
v___x_4023_ = lean_unbox(v_snd_4022_);
if (v___x_4023_ == 0)
{
lean_object* v_fst_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v_fst_4024_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_fst_4024_);
lean_dec(v_a_4018_);
v___x_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_fst_4024_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4025_);
v___x_4027_ = v___x_4020_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4025_);
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
else
{
lean_object* v_fst_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v_fst_4030_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_fst_4030_);
lean_dec(v_a_4018_);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v_fst_4030_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4031_);
v___x_4033_ = v___x_4020_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4037_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4040_){
_start:
{
if (lean_obj_tag(v_x_4040_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4050_; 
v_a_4042_ = lean_ctor_get(v_x_4040_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_x_4040_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4044_ = v_x_4040_;
v_isShared_4045_ = v_isSharedCheck_4050_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v_x_4040_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4050_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4060_; 
v_a_4051_ = lean_ctor_get(v_x_4040_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_x_4040_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4053_ = v_x_4040_;
v_isShared_4054_ = v_isSharedCheck_4060_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v_x_4040_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4060_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_a_4051_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4055_);
v___x_4057_ = v___x_4053_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
return v___x_4058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4068_){
_start:
{
if (lean_obj_tag(v_x_4068_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4078_; 
v_a_4070_ = lean_ctor_get(v_x_4068_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_x_4068_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4072_ = v_x_4068_;
v_isShared_4073_ = v_isSharedCheck_4078_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v_x_4068_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4078_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; 
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
}
}
else
{
lean_object* v___x_4079_; 
lean_dec_ref_known(v_x_4068_, 1);
v___x_4079_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4080_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4083_, lean_object* v_handler_4084_, lean_object* v___f_4085_, lean_object* v_x_4086_){
_start:
{
if (lean_obj_tag(v_x_4086_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; 
v_a_4088_ = lean_ctor_get(v_x_4086_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v_x_4086_, 1);
v___x_4089_ = lean_apply_3(v_onFailure_4083_, v_handler_4084_, v_a_4088_, lean_box(0));
v___x_4090_ = lean_unsigned_to_nat(0u);
v___x_4091_ = 0;
v___x_4092_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4090_, v___x_4091_, v___x_4089_, v___f_4085_);
return v___x_4092_;
}
else
{
lean_object* v___x_4093_; 
lean_dec_ref(v___f_4085_);
lean_dec(v_handler_4084_);
lean_dec_ref(v_onFailure_4083_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_x_4086_);
return v___x_4093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4094_, lean_object* v_handler_4095_, lean_object* v___f_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4094_, v_handler_4095_, v___f_4096_, v_x_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4100_, lean_object* v_socket_4101_, lean_object* v_____r_4102_){
_start:
{
lean_object* v_val_4105_; lean_object* v_close_4107_; lean_object* v___x_4108_; 
v_close_4107_ = lean_ctor_get(v_inst_4100_, 3);
lean_inc_ref(v_close_4107_);
lean_dec_ref(v_inst_4100_);
v___x_4108_ = lean_apply_2(v_close_4107_, v_socket_4101_, lean_box(0));
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
lean_ctor_set_tag(v___x_4111_, 1);
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
v_val_4105_ = v___x_4114_;
goto v___jp_4104_;
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
v_a_4117_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4108_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4108_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
lean_ctor_set_tag(v___x_4119_, 0);
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
v_val_4105_ = v___x_4122_;
goto v___jp_4104_;
}
}
}
v___jp_4104_:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_val_4105_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4125_, lean_object* v_socket_4126_, lean_object* v_____r_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4125_, v_socket_4126_, v_____r_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4130_, lean_object* v_x_4131_){
_start:
{
if (lean_obj_tag(v_x_4131_) == 0)
{
lean_object* v___x_4133_; 
lean_dec_ref(v___f_4130_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_x_4131_);
return v___x_4133_;
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4135_; 
v_a_4134_ = lean_ctor_get(v_x_4131_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v_x_4131_, 1);
v___x_4135_ = lean_apply_2(v___f_4130_, v_a_4134_, lean_box(0));
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4136_, v_x_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4140_, lean_object* v_val_4141_, lean_object* v___f_4142_, lean_object* v___f_4143_, lean_object* v_x_4144_){
_start:
{
if (lean_obj_tag(v_x_4144_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4154_; 
lean_dec_ref(v___f_4143_);
lean_dec_ref(v___f_4142_);
lean_dec(v_val_4141_);
lean_dec_ref(v_close_4140_);
v_a_4146_ = lean_ctor_get(v_x_4144_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_x_4144_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4148_ = v_x_4144_;
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v_x_4144_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; 
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
}
else
{
lean_object* v_a_4155_; uint8_t v___x_4156_; 
v_a_4155_ = lean_ctor_get(v_x_4144_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v_x_4144_, 1);
v___x_4156_ = lean_unbox(v_a_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; lean_object* v___x_4160_; 
lean_dec_ref(v___f_4143_);
v___x_4157_ = lean_apply_2(v_close_4140_, v_val_4141_, lean_box(0));
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = lean_unbox(v_a_4155_);
lean_dec(v_a_4155_);
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4158_, v___x_4159_, v___x_4157_, v___f_4142_);
return v___x_4160_;
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec(v_a_4155_);
lean_dec_ref(v___f_4142_);
lean_dec(v_val_4141_);
lean_dec_ref(v_close_4140_);
v___x_4161_ = lean_box(0);
v___x_4162_ = lean_apply_2(v___f_4143_, v___x_4161_, lean_box(0));
return v___x_4162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4163_, lean_object* v_val_4164_, lean_object* v___f_4165_, lean_object* v___f_4166_, lean_object* v_x_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4163_, v_val_4164_, v___f_4165_, v___f_4166_, v_x_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4170_, lean_object* v_responseBodyInstance_4171_, lean_object* v___f_4172_, lean_object* v___f_4173_, lean_object* v_____r_4174_){
_start:
{
if (lean_obj_tag(v_respStream_4170_) == 1)
{
lean_object* v_val_4176_; lean_object* v_close_4177_; lean_object* v_isClosed_4178_; lean_object* v___x_4179_; lean_object* v___f_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; lean_object* v___x_4183_; 
v_val_4176_ = lean_ctor_get(v_respStream_4170_, 0);
lean_inc_n(v_val_4176_, 2);
lean_dec_ref_known(v_respStream_4170_, 1);
v_close_4177_ = lean_ctor_get(v_responseBodyInstance_4171_, 1);
lean_inc_ref(v_close_4177_);
v_isClosed_4178_ = lean_ctor_get(v_responseBodyInstance_4171_, 2);
lean_inc_ref(v_isClosed_4178_);
lean_dec_ref(v_responseBodyInstance_4171_);
v___x_4179_ = lean_apply_2(v_isClosed_4178_, v_val_4176_, lean_box(0));
v___f_4180_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4180_, 0, v_close_4177_);
lean_closure_set(v___f_4180_, 1, v_val_4176_);
lean_closure_set(v___f_4180_, 2, v___f_4172_);
lean_closure_set(v___f_4180_, 3, v___f_4173_);
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = 0;
v___x_4183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4181_, v___x_4182_, v___x_4179_, v___f_4180_);
return v___x_4183_;
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec_ref(v___f_4172_);
lean_dec_ref(v_responseBodyInstance_4171_);
lean_dec(v_respStream_4170_);
v___x_4184_ = lean_box(0);
v___x_4185_ = lean_apply_2(v___f_4173_, v___x_4184_, lean_box(0));
return v___x_4185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4186_, lean_object* v_responseBodyInstance_4187_, lean_object* v___f_4188_, lean_object* v___f_4189_, lean_object* v_____r_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4186_, v_responseBodyInstance_4187_, v___f_4188_, v___f_4189_, v_____r_4190_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4193_, lean_object* v___f_4194_, lean_object* v___f_4195_, lean_object* v_x_4196_){
_start:
{
if (lean_obj_tag(v_x_4196_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4206_; 
lean_dec_ref(v___f_4195_);
lean_dec_ref(v___f_4194_);
lean_dec_ref(v_requestStream_4193_);
v_a_4198_ = lean_ctor_get(v_x_4196_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_x_4196_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4200_ = v_x_4196_;
v_isShared_4201_ = v_isSharedCheck_4206_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v_x_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4206_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
}
else
{
lean_object* v_a_4207_; uint8_t v___x_4208_; 
v_a_4207_ = lean_ctor_get(v_x_4196_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v_x_4196_, 1);
v___x_4208_ = lean_unbox(v_a_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; 
lean_dec_ref(v___f_4195_);
v___x_4209_ = l_Std_Http_Body_Stream_close(v_requestStream_4193_);
v___x_4210_ = lean_unsigned_to_nat(0u);
v___x_4211_ = lean_unbox(v_a_4207_);
lean_dec(v_a_4207_);
v___x_4212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4210_, v___x_4211_, v___x_4209_, v___f_4194_);
return v___x_4212_;
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_dec(v_a_4207_);
lean_dec_ref(v___f_4194_);
lean_dec_ref(v_requestStream_4193_);
v___x_4213_ = lean_box(0);
v___x_4214_ = lean_apply_2(v___f_4195_, v___x_4213_, lean_box(0));
return v___x_4214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4215_, lean_object* v___f_4216_, lean_object* v___f_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4215_, v___f_4216_, v___f_4217_, v_x_4218_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4221_, lean_object* v_responseBodyInstance_4222_, lean_object* v___f_4223_, lean_object* v___f_4224_, lean_object* v_x_4225_){
_start:
{
if (lean_obj_tag(v_x_4225_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4235_; 
lean_dec_ref(v___f_4224_);
lean_dec_ref(v___f_4223_);
lean_dec_ref(v_responseBodyInstance_4222_);
lean_dec_ref(v___f_4221_);
v_a_4227_ = lean_ctor_get(v_x_4225_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_x_4225_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4229_ = v_x_4225_;
v_isShared_4230_ = v_isSharedCheck_4235_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v_x_4225_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4235_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v_requestStream_4237_; lean_object* v_respStream_4238_; lean_object* v___x_4239_; lean_object* v___f_4240_; lean_object* v___f_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_5017__overap_4244_; lean_object* v___x_4245_; lean_object* v___f_4246_; lean_object* v___f_4247_; lean_object* v___f_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; lean_object* v___x_4251_; 
v_a_4236_ = lean_ctor_get(v_x_4225_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v_x_4225_, 1);
v_requestStream_4237_ = lean_ctor_get(v_a_4236_, 1);
lean_inc_ref_n(v_requestStream_4237_, 2);
v_respStream_4238_ = lean_ctor_get(v_a_4236_, 6);
lean_inc(v_respStream_4238_);
lean_dec(v_a_4236_);
v___x_4239_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4240_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4241_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4242_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4243_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_4243_, 0, lean_box(0));
lean_closure_set(v___x_4243_, 1, lean_box(0));
lean_closure_set(v___x_4243_, 2, lean_box(0));
lean_closure_set(v___x_4243_, 3, v___x_4239_);
lean_closure_set(v___x_4243_, 4, lean_box(0));
lean_closure_set(v___x_4243_, 5, lean_box(0));
lean_closure_set(v___x_4243_, 6, v___x_4242_);
lean_closure_set(v___x_4243_, 7, v___f_4221_);
v___x_5017__overap_4244_ = l_Std_Mutex_atomically___redArg(v___x_4239_, v___f_4240_, v___f_4241_, v_requestStream_4237_, v___x_4243_);
v___x_4245_ = lean_apply_1(v___x_5017__overap_4244_, lean_box(0));
v___f_4246_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4246_, 0, v_respStream_4238_);
lean_closure_set(v___f_4246_, 1, v_responseBodyInstance_4222_);
lean_closure_set(v___f_4246_, 2, v___f_4223_);
lean_closure_set(v___f_4246_, 3, v___f_4224_);
lean_inc_ref(v___f_4246_);
v___f_4247_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4247_, 0, v___f_4246_);
v___f_4248_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4248_, 0, v_requestStream_4237_);
lean_closure_set(v___f_4248_, 1, v___f_4247_);
lean_closure_set(v___f_4248_, 2, v___f_4246_);
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = 0;
v___x_4251_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4249_, v___x_4250_, v___x_4245_, v___f_4248_);
return v___x_4251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4252_, lean_object* v_responseBodyInstance_4253_, lean_object* v___f_4254_, lean_object* v___f_4255_, lean_object* v_x_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4252_, v_responseBodyInstance_4253_, v___f_4254_, v___f_4255_, v_x_4256_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4259_, lean_object* v_responseBodyInstance_4260_, lean_object* v_handler_4261_, lean_object* v_config_4262_, lean_object* v___x_4263_, uint8_t v___x_4264_, lean_object* v___f_4265_, lean_object* v_x_4266_){
_start:
{
if (lean_obj_tag(v_x_4266_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v___f_4265_);
lean_dec_ref(v___x_4263_);
lean_dec_ref(v_config_4262_);
lean_dec(v_handler_4261_);
lean_dec_ref(v_responseBodyInstance_4260_);
lean_dec_ref(v_h_4259_);
v_a_4268_ = lean_ctor_get(v_x_4266_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_x_4266_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4270_ = v_x_4266_;
v_isShared_4271_ = v_isSharedCheck_4276_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v_x_4266_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4276_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v___x_4274_; 
v___x_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
return v___x_4274_;
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v_a_4277_ = lean_ctor_get(v_x_4266_, 0);
lean_inc(v_a_4277_);
lean_dec_ref_known(v_x_4266_, 1);
v___x_4278_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4259_, v_responseBodyInstance_4260_, v_handler_4261_, v_config_4262_, v_a_4277_, v___x_4263_);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4279_, v___x_4264_, v___x_4278_, v___f_4265_);
return v___x_4280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4281_, lean_object* v_responseBodyInstance_4282_, lean_object* v_handler_4283_, lean_object* v_config_4284_, lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v___f_4287_, lean_object* v_x_4288_, lean_object* v___y_4289_){
_start:
{
uint8_t v___x_5688__boxed_4290_; lean_object* v_res_4291_; 
v___x_5688__boxed_4290_ = lean_unbox(v___x_4286_);
v_res_4291_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4281_, v_responseBodyInstance_4282_, v_handler_4283_, v_config_4284_, v___x_4285_, v___x_5688__boxed_4290_, v___f_4287_, v_x_4288_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4292_, lean_object* v_h_4293_, lean_object* v_responseBodyInstance_4294_, lean_object* v_config_4295_, lean_object* v_handler_4296_, uint8_t v___x_4297_, lean_object* v___f_4298_, lean_object* v_x_4299_){
_start:
{
if (lean_obj_tag(v_x_4299_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4309_; 
lean_dec_ref(v___f_4298_);
lean_dec(v_handler_4296_);
lean_dec_ref(v_config_4295_);
lean_dec_ref(v_responseBodyInstance_4294_);
lean_dec_ref(v_h_4293_);
lean_dec_ref(v_inst_4292_);
v_a_4301_ = lean_ctor_get(v_x_4299_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_x_4299_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4303_ = v_x_4299_;
v_isShared_4304_ = v_isSharedCheck_4309_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v_x_4299_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4309_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
return v___x_4307_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_a_4310_ = lean_ctor_get(v_x_4299_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v_x_4299_, 1);
v___x_4311_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4292_, v_h_4293_, v_responseBodyInstance_4294_, v_config_4295_, v_handler_4296_, v_a_4310_);
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4312_, v___x_4297_, v___x_4311_, v___f_4298_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4314_, lean_object* v_h_4315_, lean_object* v_responseBodyInstance_4316_, lean_object* v_config_4317_, lean_object* v_handler_4318_, lean_object* v___x_4319_, lean_object* v___f_4320_, lean_object* v_x_4321_, lean_object* v___y_4322_){
_start:
{
uint8_t v___x_5729__boxed_4323_; lean_object* v_res_4324_; 
v___x_5729__boxed_4323_ = lean_unbox(v___x_4319_);
v_res_4324_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4314_, v_h_4315_, v_responseBodyInstance_4316_, v_config_4317_, v_handler_4318_, v___x_5729__boxed_4323_, v___f_4320_, v_x_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4325_, lean_object* v_socket_4326_, lean_object* v_connectionContext_4327_, lean_object* v_h_4328_, lean_object* v_responseBodyInstance_4329_, lean_object* v_handler_4330_, lean_object* v_config_4331_, lean_object* v___f_4332_, lean_object* v_inst_4333_, lean_object* v_x_4334_){
_start:
{
if (lean_obj_tag(v_x_4334_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4344_; 
lean_dec_ref(v_inst_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v_config_4331_);
lean_dec(v_handler_4330_);
lean_dec_ref(v_responseBodyInstance_4329_);
lean_dec_ref(v_h_4328_);
lean_dec_ref(v_connectionContext_4327_);
lean_dec(v_socket_4326_);
v_a_4336_ = lean_ctor_get(v_x_4334_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_x_4334_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4338_ = v_x_4334_;
v_isShared_4339_ = v_isSharedCheck_4344_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v_x_4334_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4344_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4342_; 
v___x_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
return v___x_4342_;
}
}
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4379_; 
v_a_4345_ = lean_ctor_get(v_x_4334_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v_x_4334_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4347_ = v_x_4334_;
v_isShared_4348_ = v_isSharedCheck_4379_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v_x_4334_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4379_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v_machine_4355_; lean_object* v_requestStream_4356_; lean_object* v_keepAliveTimeout_4357_; lean_object* v_currentTimeout_4358_; lean_object* v_headerTimeout_4359_; lean_object* v_response_4360_; lean_object* v_respStream_4361_; uint8_t v_requiresData_4362_; lean_object* v_expectData_4363_; uint8_t v_handlerDispatched_4364_; lean_object* v_pendingHead_4365_; 
v_machine_4355_ = lean_ctor_get(v_a_4345_, 0);
v_requestStream_4356_ = lean_ctor_get(v_a_4345_, 1);
v_keepAliveTimeout_4357_ = lean_ctor_get(v_a_4345_, 2);
v_currentTimeout_4358_ = lean_ctor_get(v_a_4345_, 3);
v_headerTimeout_4359_ = lean_ctor_get(v_a_4345_, 4);
v_response_4360_ = lean_ctor_get(v_a_4345_, 5);
v_respStream_4361_ = lean_ctor_get(v_a_4345_, 6);
v_requiresData_4362_ = lean_ctor_get_uint8(v_a_4345_, sizeof(void*)*9);
v_expectData_4363_ = lean_ctor_get(v_a_4345_, 7);
v_handlerDispatched_4364_ = lean_ctor_get_uint8(v_a_4345_, sizeof(void*)*9 + 1);
v_pendingHead_4365_ = lean_ctor_get(v_a_4345_, 8);
if (v_requiresData_4362_ == 0)
{
if (v_handlerDispatched_4364_ == 0)
{
if (lean_obj_tag(v_respStream_4361_) == 0)
{
lean_object* v_writer_4375_; uint8_t v_sentMessage_4376_; 
v_writer_4375_ = lean_ctor_get(v_machine_4355_, 1);
v_sentMessage_4376_ = lean_ctor_get_uint8(v_writer_4375_, sizeof(void*)*6);
if (v_sentMessage_4376_ == 0)
{
lean_object* v_reader_4377_; lean_object* v_state_4378_; 
v_reader_4377_ = lean_ctor_get(v_machine_4355_, 0);
v_state_4378_ = lean_ctor_get(v_reader_4377_, 0);
if (lean_obj_tag(v_state_4378_) == 2)
{
lean_inc(v_respStream_4361_);
lean_inc(v_pendingHead_4365_);
lean_inc(v_expectData_4363_);
lean_inc_ref(v_response_4360_);
lean_inc(v_headerTimeout_4359_);
lean_inc(v_currentTimeout_4358_);
lean_inc(v_keepAliveTimeout_4357_);
lean_inc_ref(v_requestStream_4356_);
lean_inc_ref(v_machine_4355_);
lean_del_object(v___x_4347_);
lean_dec(v_a_4345_);
goto v___jp_4366_;
}
else
{
lean_dec_ref(v_inst_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v_config_4331_);
lean_dec(v_handler_4330_);
lean_dec_ref(v_responseBodyInstance_4329_);
lean_dec_ref(v_h_4328_);
lean_dec_ref(v_connectionContext_4327_);
lean_dec(v_socket_4326_);
goto v___jp_4349_;
}
}
else
{
lean_dec_ref(v_inst_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v_config_4331_);
lean_dec(v_handler_4330_);
lean_dec_ref(v_responseBodyInstance_4329_);
lean_dec_ref(v_h_4328_);
lean_dec_ref(v_connectionContext_4327_);
lean_dec(v_socket_4326_);
goto v___jp_4349_;
}
}
else
{
lean_inc_ref(v_respStream_4361_);
lean_inc(v_pendingHead_4365_);
lean_inc(v_expectData_4363_);
lean_inc_ref(v_response_4360_);
lean_inc(v_headerTimeout_4359_);
lean_inc(v_currentTimeout_4358_);
lean_inc(v_keepAliveTimeout_4357_);
lean_inc_ref(v_requestStream_4356_);
lean_inc_ref(v_machine_4355_);
lean_del_object(v___x_4347_);
lean_dec(v_a_4345_);
goto v___jp_4366_;
}
}
else
{
lean_inc(v_pendingHead_4365_);
lean_inc(v_expectData_4363_);
lean_inc(v_respStream_4361_);
lean_inc_ref(v_response_4360_);
lean_inc(v_headerTimeout_4359_);
lean_inc(v_currentTimeout_4358_);
lean_inc(v_keepAliveTimeout_4357_);
lean_inc_ref(v_requestStream_4356_);
lean_inc_ref(v_machine_4355_);
lean_del_object(v___x_4347_);
lean_dec(v_a_4345_);
goto v___jp_4366_;
}
}
else
{
lean_inc(v_pendingHead_4365_);
lean_inc(v_expectData_4363_);
lean_inc(v_respStream_4361_);
lean_inc_ref(v_response_4360_);
lean_inc(v_headerTimeout_4359_);
lean_inc(v_currentTimeout_4358_);
lean_inc(v_keepAliveTimeout_4357_);
lean_inc_ref(v_requestStream_4356_);
lean_inc_ref(v_machine_4355_);
lean_del_object(v___x_4347_);
lean_dec(v_a_4345_);
goto v___jp_4366_;
}
v___jp_4349_:
{
lean_object* v___x_4350_; lean_object* v___x_4352_; 
v___x_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4350_, 0, v_a_4345_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4350_);
v___x_4352_ = v___x_4347_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4350_);
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
v___jp_4366_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; lean_object* v___f_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4367_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4367_, 0, v_machine_4355_);
lean_ctor_set(v___x_4367_, 1, v_requestStream_4356_);
lean_ctor_set(v___x_4367_, 2, v_keepAliveTimeout_4357_);
lean_ctor_set(v___x_4367_, 3, v_currentTimeout_4358_);
lean_ctor_set(v___x_4367_, 4, v_headerTimeout_4359_);
lean_ctor_set(v___x_4367_, 5, v_response_4360_);
lean_ctor_set(v___x_4367_, 6, v_respStream_4361_);
lean_ctor_set(v___x_4367_, 7, v_expectData_4363_);
lean_ctor_set(v___x_4367_, 8, v_pendingHead_4365_);
lean_ctor_set_uint8(v___x_4367_, sizeof(void*)*9, v___x_4325_);
lean_ctor_set_uint8(v___x_4367_, sizeof(void*)*9 + 1, v_handlerDispatched_4364_);
lean_inc_ref(v___x_4367_);
v___x_4368_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4326_, v_connectionContext_4327_, v___x_4367_);
v___x_4369_ = lean_box(v___x_4325_);
lean_inc_ref(v_config_4331_);
lean_inc(v_handler_4330_);
lean_inc_ref(v_responseBodyInstance_4329_);
lean_inc_ref(v_h_4328_);
v___f_4370_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4370_, 0, v_h_4328_);
lean_closure_set(v___f_4370_, 1, v_responseBodyInstance_4329_);
lean_closure_set(v___f_4370_, 2, v_handler_4330_);
lean_closure_set(v___f_4370_, 3, v_config_4331_);
lean_closure_set(v___f_4370_, 4, v___x_4367_);
lean_closure_set(v___f_4370_, 5, v___x_4369_);
lean_closure_set(v___f_4370_, 6, v___f_4332_);
v___x_4371_ = lean_box(v___x_4325_);
v___f_4372_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4372_, 0, v_inst_4333_);
lean_closure_set(v___f_4372_, 1, v_h_4328_);
lean_closure_set(v___f_4372_, 2, v_responseBodyInstance_4329_);
lean_closure_set(v___f_4372_, 3, v_config_4331_);
lean_closure_set(v___f_4372_, 4, v_handler_4330_);
lean_closure_set(v___f_4372_, 5, v___x_4371_);
lean_closure_set(v___f_4372_, 6, v___f_4370_);
v___x_4373_ = lean_unsigned_to_nat(0u);
v___x_4374_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4373_, v___x_4325_, v___x_4368_, v___f_4372_);
return v___x_4374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4380_, lean_object* v_socket_4381_, lean_object* v_connectionContext_4382_, lean_object* v_h_4383_, lean_object* v_responseBodyInstance_4384_, lean_object* v_handler_4385_, lean_object* v_config_4386_, lean_object* v___f_4387_, lean_object* v_inst_4388_, lean_object* v_x_4389_, lean_object* v___y_4390_){
_start:
{
uint8_t v___x_5769__boxed_4391_; lean_object* v_res_4392_; 
v___x_5769__boxed_4391_ = lean_unbox(v___x_4380_);
v_res_4392_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5769__boxed_4391_, v_socket_4381_, v_connectionContext_4382_, v_h_4383_, v_responseBodyInstance_4384_, v_handler_4385_, v_config_4386_, v___f_4387_, v_inst_4388_, v_x_4389_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4393_, lean_object* v_handler_4394_, lean_object* v_extensions_4395_, lean_object* v_connectionContext_4396_, uint8_t v___x_4397_, lean_object* v___f_4398_, lean_object* v_x_4399_){
_start:
{
if (lean_obj_tag(v_x_4399_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4409_; 
lean_dec_ref(v___f_4398_);
lean_dec_ref(v_connectionContext_4396_);
lean_dec(v_extensions_4395_);
lean_dec(v_handler_4394_);
lean_dec_ref(v_h_4393_);
v_a_4401_ = lean_ctor_get(v_x_4399_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v_x_4399_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4403_ = v_x_4399_;
v_isShared_4404_ = v_isSharedCheck_4409_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v_x_4399_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4409_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_a_4410_ = lean_ctor_get(v_x_4399_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v_x_4399_, 1);
v___x_4411_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4393_, v_handler_4394_, v_extensions_4395_, v_connectionContext_4396_, v_a_4410_);
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4412_, v___x_4397_, v___x_4411_, v___f_4398_);
return v___x_4413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4414_, lean_object* v_handler_4415_, lean_object* v_extensions_4416_, lean_object* v_connectionContext_4417_, lean_object* v___x_4418_, lean_object* v___f_4419_, lean_object* v_x_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v___x_5844__boxed_4422_; lean_object* v_res_4423_; 
v___x_5844__boxed_4422_ = lean_unbox(v___x_4418_);
v_res_4423_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4414_, v_handler_4415_, v_extensions_4416_, v_connectionContext_4417_, v___x_5844__boxed_4422_, v___f_4419_, v_x_4420_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4424_, lean_object* v_responseBodyInstance_4425_, lean_object* v_handler_4426_, lean_object* v_config_4427_, lean_object* v_connectionContext_4428_, lean_object* v_events_4429_, lean_object* v___x_4430_, uint8_t v___x_4431_, lean_object* v___f_4432_, lean_object* v_____r_4433_){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4424_, v_responseBodyInstance_4425_, v_handler_4426_, v_config_4427_, v_connectionContext_4428_, v_events_4429_, v___x_4430_);
v___x_4436_ = lean_unsigned_to_nat(0u);
v___x_4437_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4436_, v___x_4431_, v___x_4435_, v___f_4432_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4438_, lean_object* v_responseBodyInstance_4439_, lean_object* v_handler_4440_, lean_object* v_config_4441_, lean_object* v_connectionContext_4442_, lean_object* v_events_4443_, lean_object* v___x_4444_, lean_object* v___x_4445_, lean_object* v___f_4446_, lean_object* v_____r_4447_, lean_object* v___y_4448_){
_start:
{
uint8_t v___x_5883__boxed_4449_; lean_object* v_res_4450_; 
v___x_5883__boxed_4449_ = lean_unbox(v___x_4445_);
v_res_4450_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4438_, v_responseBodyInstance_4439_, v_handler_4440_, v_config_4441_, v_connectionContext_4442_, v_events_4443_, v___x_4444_, v___x_5883__boxed_4449_, v___f_4446_, v_____r_4447_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4451_, lean_object* v___f_4452_, lean_object* v_x_4453_){
_start:
{
if (lean_obj_tag(v_x_4453_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4463_; 
lean_dec_ref(v___f_4452_);
lean_dec_ref(v___x_4451_);
v_a_4455_ = lean_ctor_get(v_x_4453_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_x_4453_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4457_ = v_x_4453_;
v_isShared_4458_ = v_isSharedCheck_4463_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v_x_4453_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4463_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4475_; 
v_a_4464_ = lean_ctor_get(v_x_4453_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_x_4453_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4466_ = v_x_4453_;
v_isShared_4467_ = v_isSharedCheck_4475_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v_x_4453_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4475_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
if (lean_obj_tag(v_a_4464_) == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4470_; 
lean_dec_ref(v___f_4452_);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4451_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 0, v___x_4468_);
v___x_4470_ = v___x_4466_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
else
{
lean_object* v_val_4473_; lean_object* v___x_4474_; 
lean_del_object(v___x_4466_);
lean_dec_ref(v___x_4451_);
v_val_4473_ = lean_ctor_get(v_a_4464_, 0);
lean_inc(v_val_4473_);
lean_dec_ref_known(v_a_4464_, 1);
v___x_4474_ = lean_apply_2(v___f_4452_, v_val_4473_, lean_box(0));
return v___x_4474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4476_, lean_object* v___f_4477_, lean_object* v_x_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4476_, v___f_4477_, v_x_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4481_, lean_object* v_responseBodyInstance_4482_, lean_object* v_handler_4483_, lean_object* v_config_4484_, lean_object* v_connectionContext_4485_, uint8_t v___x_4486_, lean_object* v___f_4487_, lean_object* v_inst_4488_, lean_object* v_socket_4489_, lean_object* v___f_4490_, lean_object* v___f_4491_, lean_object* v_x_4492_, lean_object* v_____s_4493_){
_start:
{
lean_object* v_machine_4495_; lean_object* v_reader_4496_; lean_object* v_requestStream_4497_; lean_object* v_keepAliveTimeout_4498_; lean_object* v_currentTimeout_4499_; lean_object* v_headerTimeout_4500_; lean_object* v_response_4501_; lean_object* v_respStream_4502_; uint8_t v_requiresData_4503_; lean_object* v_expectData_4504_; uint8_t v_handlerDispatched_4505_; lean_object* v_pendingHead_4506_; lean_object* v_writer_4507_; lean_object* v_state_4508_; uint8_t v___x_4509_; 
v_machine_4495_ = lean_ctor_get(v_____s_4493_, 0);
v_reader_4496_ = lean_ctor_get(v_machine_4495_, 0);
v_requestStream_4497_ = lean_ctor_get(v_____s_4493_, 1);
v_keepAliveTimeout_4498_ = lean_ctor_get(v_____s_4493_, 2);
v_currentTimeout_4499_ = lean_ctor_get(v_____s_4493_, 3);
v_headerTimeout_4500_ = lean_ctor_get(v_____s_4493_, 4);
v_response_4501_ = lean_ctor_get(v_____s_4493_, 5);
v_respStream_4502_ = lean_ctor_get(v_____s_4493_, 6);
v_requiresData_4503_ = lean_ctor_get_uint8(v_____s_4493_, sizeof(void*)*9);
v_expectData_4504_ = lean_ctor_get(v_____s_4493_, 7);
v_handlerDispatched_4505_ = lean_ctor_get_uint8(v_____s_4493_, sizeof(void*)*9 + 1);
v_pendingHead_4506_ = lean_ctor_get(v_____s_4493_, 8);
v_writer_4507_ = lean_ctor_get(v_machine_4495_, 1);
v_state_4508_ = lean_ctor_get(v_reader_4496_, 0);
v___x_4509_ = 0;
if (lean_obj_tag(v_state_4508_) == 6)
{
lean_object* v_state_4531_; 
v_state_4531_ = lean_ctor_get(v_writer_4507_, 2);
if (lean_obj_tag(v_state_4531_) == 7)
{
lean_object* v_outputData_4532_; lean_object* v_size_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v_outputData_4532_ = lean_ctor_get(v_writer_4507_, 1);
v_size_4533_ = lean_ctor_get(v_outputData_4532_, 1);
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = lean_nat_dec_eq(v_size_4533_, v___x_4534_);
if (v___x_4535_ == 0)
{
lean_inc(v_pendingHead_4506_);
lean_inc(v_expectData_4504_);
lean_inc(v_respStream_4502_);
lean_inc_ref(v_response_4501_);
lean_inc(v_headerTimeout_4500_);
lean_inc(v_currentTimeout_4499_);
lean_inc(v_keepAliveTimeout_4498_);
lean_inc_ref(v_requestStream_4497_);
lean_inc_ref(v_machine_4495_);
lean_dec_ref(v_____s_4493_);
goto v___jp_4510_;
}
else
{
if (v___x_4535_ == 0)
{
lean_inc(v_pendingHead_4506_);
lean_inc(v_expectData_4504_);
lean_inc(v_respStream_4502_);
lean_inc_ref(v_response_4501_);
lean_inc(v_headerTimeout_4500_);
lean_inc(v_currentTimeout_4499_);
lean_inc(v_keepAliveTimeout_4498_);
lean_inc_ref(v_requestStream_4497_);
lean_inc_ref(v_machine_4495_);
lean_dec_ref(v_____s_4493_);
goto v___jp_4510_;
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
lean_dec_ref(v___f_4491_);
lean_dec_ref(v___f_4490_);
lean_dec(v_socket_4489_);
lean_dec_ref(v_inst_4488_);
lean_dec_ref(v___f_4487_);
lean_dec_ref(v_connectionContext_4485_);
lean_dec_ref(v_config_4484_);
lean_dec(v_handler_4483_);
lean_dec_ref(v_responseBodyInstance_4482_);
lean_dec_ref(v_h_4481_);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_____s_4493_);
v___x_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
return v___x_4538_;
}
}
}
else
{
lean_inc(v_pendingHead_4506_);
lean_inc(v_expectData_4504_);
lean_inc(v_respStream_4502_);
lean_inc_ref(v_response_4501_);
lean_inc(v_headerTimeout_4500_);
lean_inc(v_currentTimeout_4499_);
lean_inc(v_keepAliveTimeout_4498_);
lean_inc_ref(v_requestStream_4497_);
lean_inc_ref(v_machine_4495_);
lean_dec_ref(v_____s_4493_);
goto v___jp_4510_;
}
}
else
{
lean_inc(v_pendingHead_4506_);
lean_inc(v_expectData_4504_);
lean_inc(v_respStream_4502_);
lean_inc_ref(v_response_4501_);
lean_inc(v_headerTimeout_4500_);
lean_inc(v_currentTimeout_4499_);
lean_inc(v_keepAliveTimeout_4498_);
lean_inc_ref(v_requestStream_4497_);
lean_inc_ref(v_machine_4495_);
lean_dec_ref(v_____s_4493_);
goto v___jp_4510_;
}
v___jp_4510_:
{
lean_object* v___x_4511_; lean_object* v_snd_4512_; lean_object* v_output_4513_; lean_object* v_fst_4514_; lean_object* v_events_4515_; lean_object* v_data_4516_; lean_object* v_size_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___f_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4511_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4509_, v_machine_4495_);
v_snd_4512_ = lean_ctor_get(v___x_4511_, 1);
lean_inc(v_snd_4512_);
v_output_4513_ = lean_ctor_get(v_snd_4512_, 1);
lean_inc_ref(v_output_4513_);
v_fst_4514_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_fst_4514_);
lean_dec_ref(v___x_4511_);
v_events_4515_ = lean_ctor_get(v_snd_4512_, 0);
lean_inc_ref_n(v_events_4515_, 2);
lean_dec(v_snd_4512_);
v_data_4516_ = lean_ctor_get(v_output_4513_, 0);
lean_inc_ref(v_data_4516_);
v_size_4517_ = lean_ctor_get(v_output_4513_, 1);
lean_inc(v_size_4517_);
lean_dec_ref(v_output_4513_);
v___x_4518_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4518_, 0, v_fst_4514_);
lean_ctor_set(v___x_4518_, 1, v_requestStream_4497_);
lean_ctor_set(v___x_4518_, 2, v_keepAliveTimeout_4498_);
lean_ctor_set(v___x_4518_, 3, v_currentTimeout_4499_);
lean_ctor_set(v___x_4518_, 4, v_headerTimeout_4500_);
lean_ctor_set(v___x_4518_, 5, v_response_4501_);
lean_ctor_set(v___x_4518_, 6, v_respStream_4502_);
lean_ctor_set(v___x_4518_, 7, v_expectData_4504_);
lean_ctor_set(v___x_4518_, 8, v_pendingHead_4506_);
lean_ctor_set_uint8(v___x_4518_, sizeof(void*)*9, v_requiresData_4503_);
lean_ctor_set_uint8(v___x_4518_, sizeof(void*)*9 + 1, v_handlerDispatched_4505_);
v___x_4519_ = lean_box(v___x_4486_);
lean_inc_ref(v___f_4487_);
lean_inc_ref(v___x_4518_);
lean_inc_ref(v_connectionContext_4485_);
lean_inc_ref(v_config_4484_);
lean_inc(v_handler_4483_);
lean_inc_ref(v_responseBodyInstance_4482_);
lean_inc_ref(v_h_4481_);
v___f_4520_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4520_, 0, v_h_4481_);
lean_closure_set(v___f_4520_, 1, v_responseBodyInstance_4482_);
lean_closure_set(v___f_4520_, 2, v_handler_4483_);
lean_closure_set(v___f_4520_, 3, v_config_4484_);
lean_closure_set(v___f_4520_, 4, v_connectionContext_4485_);
lean_closure_set(v___f_4520_, 5, v_events_4515_);
lean_closure_set(v___f_4520_, 6, v___x_4518_);
lean_closure_set(v___f_4520_, 7, v___x_4519_);
lean_closure_set(v___f_4520_, 8, v___f_4487_);
v___x_4521_ = lean_unsigned_to_nat(0u);
v___x_4522_ = lean_nat_dec_lt(v___x_4521_, v_size_4517_);
lean_dec(v_size_4517_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_dec_ref(v___f_4520_);
lean_dec_ref(v_data_4516_);
lean_dec_ref(v___f_4491_);
lean_dec_ref(v___f_4490_);
lean_dec(v_socket_4489_);
lean_dec_ref(v_inst_4488_);
v___x_4523_ = lean_box(0);
v___x_4524_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4481_, v_responseBodyInstance_4482_, v_handler_4483_, v_config_4484_, v_connectionContext_4485_, v_events_4515_, v___x_4518_, v___x_4486_, v___f_4487_, v___x_4523_);
return v___x_4524_;
}
else
{
lean_object* v_sendAll_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___f_4529_; lean_object* v___x_4530_; 
lean_dec_ref(v_events_4515_);
lean_dec_ref(v___f_4487_);
lean_dec_ref(v_connectionContext_4485_);
lean_dec_ref(v_config_4484_);
lean_dec(v_handler_4483_);
lean_dec_ref(v_responseBodyInstance_4482_);
lean_dec_ref(v_h_4481_);
v_sendAll_4525_ = lean_ctor_get(v_inst_4488_, 1);
lean_inc_ref(v_sendAll_4525_);
lean_dec_ref(v_inst_4488_);
v___x_4526_ = lean_apply_3(v_sendAll_4525_, v_socket_4489_, v_data_4516_, lean_box(0));
v___x_4527_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4521_, v___x_4486_, v___x_4526_, v___f_4490_);
v___x_4528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4521_, v___x_4486_, v___x_4527_, v___f_4491_);
v___f_4529_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4529_, 0, v___x_4518_);
lean_closure_set(v___f_4529_, 1, v___f_4520_);
v___x_4530_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4521_, v___x_4486_, v___x_4528_, v___f_4529_);
return v___x_4530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4539_, lean_object* v_responseBodyInstance_4540_, lean_object* v_handler_4541_, lean_object* v_config_4542_, lean_object* v_connectionContext_4543_, lean_object* v___x_4544_, lean_object* v___f_4545_, lean_object* v_inst_4546_, lean_object* v_socket_4547_, lean_object* v___f_4548_, lean_object* v___f_4549_, lean_object* v_x_4550_, lean_object* v_____s_4551_, lean_object* v___y_4552_){
_start:
{
uint8_t v___x_5957__boxed_4553_; lean_object* v_res_4554_; 
v___x_5957__boxed_4553_ = lean_unbox(v___x_4544_);
v_res_4554_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4539_, v_responseBodyInstance_4540_, v_handler_4541_, v_config_4542_, v_connectionContext_4543_, v___x_5957__boxed_4553_, v___f_4545_, v_inst_4546_, v_socket_4547_, v___f_4548_, v___f_4549_, v_x_4550_, v_____s_4551_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4555_, lean_object* v_x_4556_){
_start:
{
if (lean_obj_tag(v_x_4556_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4566_; 
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
lean_object* v___x_4567_; lean_object* v___x_4568_; 
lean_dec_ref_known(v_x_4556_, 1);
v___x_4567_ = l_IO_Promise_result_x21___redArg(v_a_4555_);
v___x_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4569_, lean_object* v_x_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4569_, v_x_4570_);
lean_dec(v_a_4569_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4573_, lean_object* v___x_4574_, lean_object* v___x_4575_, uint8_t v___x_4576_, lean_object* v_x_4577_){
_start:
{
if (lean_obj_tag(v_x_4577_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4587_; 
lean_dec_ref(v___x_4575_);
lean_dec(v___x_4574_);
lean_dec_ref(v___f_4573_);
v_a_4579_ = lean_ctor_get(v_x_4577_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4581_ = v_x_4577_;
v_isShared_4582_ = v_isSharedCheck_4587_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v_x_4577_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4587_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4599_; 
v_a_4588_ = lean_ctor_get(v_x_4577_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4590_ = v_x_4577_;
v_isShared_4591_ = v_isSharedCheck_4599_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v_x_4577_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4599_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v___f_4593_; lean_object* v___x_4595_; 
lean_inc(v_a_4588_);
lean_inc(v___x_4574_);
v___x_4592_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4573_, v___x_4574_, v_a_4588_, v___x_4575_);
v___f_4593_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4593_, 0, v_a_4588_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4592_);
v___x_4595_ = v___x_4590_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4592_);
v___x_4595_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
v___x_4597_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4574_, v___x_4576_, v___x_4596_, v___f_4593_);
return v___x_4597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4600_, lean_object* v___x_4601_, lean_object* v___x_4602_, lean_object* v___x_4603_, lean_object* v_x_4604_, lean_object* v___y_4605_){
_start:
{
uint8_t v___x_6060__boxed_4606_; lean_object* v_res_4607_; 
v___x_6060__boxed_4606_ = lean_unbox(v___x_4603_);
v_res_4607_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4600_, v___x_4601_, v___x_4602_, v___x_6060__boxed_4606_, v_x_4604_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4608_, lean_object* v_machine_4609_, lean_object* v_a_4610_, lean_object* v___x_4611_, lean_object* v_socket_4612_, lean_object* v_connectionContext_4613_, lean_object* v_h_4614_, lean_object* v_responseBodyInstance_4615_, lean_object* v_handler_4616_, lean_object* v___f_4617_, lean_object* v_inst_4618_, lean_object* v_extensions_4619_, lean_object* v___f_4620_, lean_object* v___f_4621_, lean_object* v___f_4622_, lean_object* v_x_4623_){
_start:
{
if (lean_obj_tag(v_x_4623_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4633_; 
lean_dec_ref(v___f_4622_);
lean_dec_ref(v___f_4621_);
lean_dec_ref(v___f_4620_);
lean_dec(v_extensions_4619_);
lean_dec_ref(v_inst_4618_);
lean_dec_ref(v___f_4617_);
lean_dec(v_handler_4616_);
lean_dec_ref(v_responseBodyInstance_4615_);
lean_dec_ref(v_h_4614_);
lean_dec_ref(v_connectionContext_4613_);
lean_dec(v_socket_4612_);
lean_dec(v___x_4611_);
lean_dec_ref(v_a_4610_);
lean_dec_ref(v_machine_4609_);
lean_dec_ref(v_config_4608_);
v_a_4625_ = lean_ctor_get(v_x_4623_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_x_4623_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4627_ = v_x_4623_;
v_isShared_4628_ = v_isSharedCheck_4633_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v_x_4623_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4633_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
return v___x_4631_;
}
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4659_; 
v_a_4634_ = lean_ctor_get(v_x_4623_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v_x_4623_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4636_ = v_x_4623_;
v_isShared_4637_ = v_isSharedCheck_4659_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v_x_4623_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4659_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v_keepAliveTimeout_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; uint8_t v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___f_4645_; lean_object* v___x_4646_; lean_object* v___f_4647_; lean_object* v___x_4648_; lean_object* v___f_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___f_4652_; lean_object* v___x_4654_; 
v_keepAliveTimeout_4638_ = lean_ctor_get(v_config_4608_, 5);
lean_inc_n(v_keepAliveTimeout_4638_, 2);
v___x_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4639_, 0, v_keepAliveTimeout_4638_);
v___x_4640_ = lean_box(0);
v___x_4641_ = 0;
v___x_4642_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4642_, 0, v_machine_4609_);
lean_ctor_set(v___x_4642_, 1, v_a_4610_);
lean_ctor_set(v___x_4642_, 2, v___x_4639_);
lean_ctor_set(v___x_4642_, 3, v_keepAliveTimeout_4638_);
lean_ctor_set(v___x_4642_, 4, v___x_4640_);
lean_ctor_set(v___x_4642_, 5, v_a_4634_);
lean_ctor_set(v___x_4642_, 6, v___x_4640_);
lean_ctor_set(v___x_4642_, 7, v___x_4611_);
lean_ctor_set(v___x_4642_, 8, v___x_4640_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*9, v___x_4641_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*9 + 1, v___x_4641_);
v___x_4643_ = lean_io_promise_new();
v___x_4644_ = lean_box(v___x_4641_);
lean_inc_ref(v_inst_4618_);
lean_inc_ref(v_config_4608_);
lean_inc_n(v_handler_4616_, 2);
lean_inc_ref(v_responseBodyInstance_4615_);
lean_inc_ref_n(v_h_4614_, 2);
lean_inc_ref_n(v_connectionContext_4613_, 2);
lean_inc(v_socket_4612_);
v___f_4645_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4645_, 0, v___x_4644_);
lean_closure_set(v___f_4645_, 1, v_socket_4612_);
lean_closure_set(v___f_4645_, 2, v_connectionContext_4613_);
lean_closure_set(v___f_4645_, 3, v_h_4614_);
lean_closure_set(v___f_4645_, 4, v_responseBodyInstance_4615_);
lean_closure_set(v___f_4645_, 5, v_handler_4616_);
lean_closure_set(v___f_4645_, 6, v_config_4608_);
lean_closure_set(v___f_4645_, 7, v___f_4617_);
lean_closure_set(v___f_4645_, 8, v_inst_4618_);
v___x_4646_ = lean_box(v___x_4641_);
v___f_4647_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4647_, 0, v_h_4614_);
lean_closure_set(v___f_4647_, 1, v_handler_4616_);
lean_closure_set(v___f_4647_, 2, v_extensions_4619_);
lean_closure_set(v___f_4647_, 3, v_connectionContext_4613_);
lean_closure_set(v___f_4647_, 4, v___x_4646_);
lean_closure_set(v___f_4647_, 5, v___f_4645_);
v___x_4648_ = lean_box(v___x_4641_);
v___f_4649_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4649_, 0, v_h_4614_);
lean_closure_set(v___f_4649_, 1, v_responseBodyInstance_4615_);
lean_closure_set(v___f_4649_, 2, v_handler_4616_);
lean_closure_set(v___f_4649_, 3, v_config_4608_);
lean_closure_set(v___f_4649_, 4, v_connectionContext_4613_);
lean_closure_set(v___f_4649_, 5, v___x_4648_);
lean_closure_set(v___f_4649_, 6, v___f_4647_);
lean_closure_set(v___f_4649_, 7, v_inst_4618_);
lean_closure_set(v___f_4649_, 8, v_socket_4612_);
lean_closure_set(v___f_4649_, 9, v___f_4620_);
lean_closure_set(v___f_4649_, 10, v___f_4621_);
v___x_4650_ = lean_unsigned_to_nat(0u);
v___x_4651_ = lean_box(v___x_4641_);
v___f_4652_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4652_, 0, v___f_4649_);
lean_closure_set(v___f_4652_, 1, v___x_4650_);
lean_closure_set(v___f_4652_, 2, v___x_4642_);
lean_closure_set(v___f_4652_, 3, v___x_4651_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v___x_4643_);
v___x_4654_ = v___x_4636_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4643_);
v___x_4654_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
v___x_4656_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4650_, v___x_4641_, v___x_4655_, v___f_4652_);
v___x_4657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4650_, v___x_4641_, v___x_4656_, v___f_4622_);
return v___x_4657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4660_ = _args[0];
lean_object* v_machine_4661_ = _args[1];
lean_object* v_a_4662_ = _args[2];
lean_object* v___x_4663_ = _args[3];
lean_object* v_socket_4664_ = _args[4];
lean_object* v_connectionContext_4665_ = _args[5];
lean_object* v_h_4666_ = _args[6];
lean_object* v_responseBodyInstance_4667_ = _args[7];
lean_object* v_handler_4668_ = _args[8];
lean_object* v___f_4669_ = _args[9];
lean_object* v_inst_4670_ = _args[10];
lean_object* v_extensions_4671_ = _args[11];
lean_object* v___f_4672_ = _args[12];
lean_object* v___f_4673_ = _args[13];
lean_object* v___f_4674_ = _args[14];
lean_object* v_x_4675_ = _args[15];
lean_object* v___y_4676_ = _args[16];
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4660_, v_machine_4661_, v_a_4662_, v___x_4663_, v_socket_4664_, v_connectionContext_4665_, v_h_4666_, v_responseBodyInstance_4667_, v_handler_4668_, v___f_4669_, v_inst_4670_, v_extensions_4671_, v___f_4672_, v___f_4673_, v___f_4674_, v_x_4675_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4678_, lean_object* v_machine_4679_, lean_object* v_socket_4680_, lean_object* v_connectionContext_4681_, lean_object* v_h_4682_, lean_object* v_responseBodyInstance_4683_, lean_object* v_handler_4684_, lean_object* v___f_4685_, lean_object* v_inst_4686_, lean_object* v_extensions_4687_, lean_object* v___f_4688_, lean_object* v___f_4689_, lean_object* v___f_4690_, lean_object* v_x_4691_){
_start:
{
if (lean_obj_tag(v_x_4691_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v___f_4690_);
lean_dec_ref(v___f_4689_);
lean_dec_ref(v___f_4688_);
lean_dec(v_extensions_4687_);
lean_dec_ref(v_inst_4686_);
lean_dec_ref(v___f_4685_);
lean_dec(v_handler_4684_);
lean_dec_ref(v_responseBodyInstance_4683_);
lean_dec_ref(v_h_4682_);
lean_dec_ref(v_connectionContext_4681_);
lean_dec(v_socket_4680_);
lean_dec_ref(v_machine_4679_);
lean_dec_ref(v_config_4678_);
v_a_4693_ = lean_ctor_get(v_x_4691_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v_x_4691_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4695_ = v_x_4691_;
v_isShared_4696_ = v_isSharedCheck_4701_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v_x_4691_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4701_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
lean_object* v___x_4699_; 
v___x_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
return v___x_4699_;
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4716_; 
v_a_4702_ = lean_ctor_get(v_x_4691_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v_x_4691_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4704_ = v_x_4691_;
v_isShared_4705_ = v_isSharedCheck_4716_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v_x_4691_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4716_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___f_4708_; lean_object* v___x_4710_; 
v___x_4706_ = lean_box(0);
v___x_4707_ = l_Std_CloseableChannel_new___redArg(v___x_4706_);
v___f_4708_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4708_, 0, v_config_4678_);
lean_closure_set(v___f_4708_, 1, v_machine_4679_);
lean_closure_set(v___f_4708_, 2, v_a_4702_);
lean_closure_set(v___f_4708_, 3, v___x_4706_);
lean_closure_set(v___f_4708_, 4, v_socket_4680_);
lean_closure_set(v___f_4708_, 5, v_connectionContext_4681_);
lean_closure_set(v___f_4708_, 6, v_h_4682_);
lean_closure_set(v___f_4708_, 7, v_responseBodyInstance_4683_);
lean_closure_set(v___f_4708_, 8, v_handler_4684_);
lean_closure_set(v___f_4708_, 9, v___f_4685_);
lean_closure_set(v___f_4708_, 10, v_inst_4686_);
lean_closure_set(v___f_4708_, 11, v_extensions_4687_);
lean_closure_set(v___f_4708_, 12, v___f_4688_);
lean_closure_set(v___f_4708_, 13, v___f_4689_);
lean_closure_set(v___f_4708_, 14, v___f_4690_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v___x_4707_);
v___x_4710_ = v___x_4704_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4707_);
v___x_4710_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; lean_object* v___x_4714_; 
v___x_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4710_);
v___x_4712_ = lean_unsigned_to_nat(0u);
v___x_4713_ = 0;
v___x_4714_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4712_, v___x_4713_, v___x_4711_, v___f_4708_);
return v___x_4714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4717_, lean_object* v_machine_4718_, lean_object* v_socket_4719_, lean_object* v_connectionContext_4720_, lean_object* v_h_4721_, lean_object* v_responseBodyInstance_4722_, lean_object* v_handler_4723_, lean_object* v___f_4724_, lean_object* v_inst_4725_, lean_object* v_extensions_4726_, lean_object* v___f_4727_, lean_object* v___f_4728_, lean_object* v___f_4729_, lean_object* v_x_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4717_, v_machine_4718_, v_socket_4719_, v_connectionContext_4720_, v_h_4721_, v_responseBodyInstance_4722_, v_handler_4723_, v___f_4724_, v_inst_4725_, v_extensions_4726_, v___f_4727_, v___f_4728_, v___f_4729_, v_x_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4736_, lean_object* v_h_4737_, lean_object* v_connection_4738_, lean_object* v_config_4739_, lean_object* v_connectionContext_4740_, lean_object* v_handler_4741_){
_start:
{
lean_object* v_responseBodyInstance_4743_; lean_object* v_onFailure_4744_; lean_object* v___x_4745_; lean_object* v_socket_4746_; lean_object* v_machine_4747_; lean_object* v_extensions_4748_; lean_object* v___f_4749_; lean_object* v___f_4750_; lean_object* v___f_4751_; lean_object* v___f_4752_; lean_object* v___f_4753_; lean_object* v___f_4754_; lean_object* v___f_4755_; lean_object* v___f_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; 
v_responseBodyInstance_4743_ = lean_ctor_get(v_h_4737_, 0);
lean_inc_ref_n(v_responseBodyInstance_4743_, 2);
v_onFailure_4744_ = lean_ctor_get(v_h_4737_, 2);
v___x_4745_ = l_Std_Http_Body_mkStream();
v_socket_4746_ = lean_ctor_get(v_connection_4738_, 0);
lean_inc_n(v_socket_4746_, 2);
v_machine_4747_ = lean_ctor_get(v_connection_4738_, 1);
lean_inc_ref(v_machine_4747_);
v_extensions_4748_ = lean_ctor_get(v_connection_4738_, 2);
lean_inc(v_extensions_4748_);
lean_dec_ref(v_connection_4738_);
v___f_4749_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4750_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4751_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4752_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4741_);
lean_inc_ref(v_onFailure_4744_);
v___f_4753_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4753_, 0, v_onFailure_4744_);
lean_closure_set(v___f_4753_, 1, v_handler_4741_);
lean_closure_set(v___f_4753_, 2, v___f_4752_);
lean_inc_ref(v_inst_4736_);
v___f_4754_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4754_, 0, v_inst_4736_);
lean_closure_set(v___f_4754_, 1, v_socket_4746_);
lean_inc_ref(v___f_4754_);
v___f_4755_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4755_, 0, v___f_4754_);
v___f_4756_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4756_, 0, v___f_4749_);
lean_closure_set(v___f_4756_, 1, v_responseBodyInstance_4743_);
lean_closure_set(v___f_4756_, 2, v___f_4755_);
lean_closure_set(v___f_4756_, 3, v___f_4754_);
v___f_4757_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4757_, 0, v_config_4739_);
lean_closure_set(v___f_4757_, 1, v_machine_4747_);
lean_closure_set(v___f_4757_, 2, v_socket_4746_);
lean_closure_set(v___f_4757_, 3, v_connectionContext_4740_);
lean_closure_set(v___f_4757_, 4, v_h_4737_);
lean_closure_set(v___f_4757_, 5, v_responseBodyInstance_4743_);
lean_closure_set(v___f_4757_, 6, v_handler_4741_);
lean_closure_set(v___f_4757_, 7, v___f_4750_);
lean_closure_set(v___f_4757_, 8, v_inst_4736_);
lean_closure_set(v___f_4757_, 9, v_extensions_4748_);
lean_closure_set(v___f_4757_, 10, v___f_4751_);
lean_closure_set(v___f_4757_, 11, v___f_4753_);
lean_closure_set(v___f_4757_, 12, v___f_4756_);
v___x_4758_ = lean_unsigned_to_nat(0u);
v___x_4759_ = 0;
v___x_4760_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4758_, v___x_4759_, v___x_4745_, v___f_4757_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4761_, lean_object* v_h_4762_, lean_object* v_connection_4763_, lean_object* v_config_4764_, lean_object* v_connectionContext_4765_, lean_object* v_handler_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4761_, v_h_4762_, v_connection_4763_, v_config_4764_, v_connectionContext_4765_, v_handler_4766_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4769_, lean_object* v_00_u03c3_4770_, lean_object* v_inst_4771_, lean_object* v_h_4772_, lean_object* v_connection_4773_, lean_object* v_config_4774_, lean_object* v_connectionContext_4775_, lean_object* v_handler_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4771_, v_h_4772_, v_connection_4773_, v_config_4774_, v_connectionContext_4775_, v_handler_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4779_, lean_object* v_00_u03c3_4780_, lean_object* v_inst_4781_, lean_object* v_h_4782_, lean_object* v_connection_4783_, lean_object* v_config_4784_, lean_object* v_connectionContext_4785_, lean_object* v_handler_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4779_, v_00_u03c3_4780_, v_inst_4781_, v_h_4782_, v_connection_4783_, v_config_4784_, v_connectionContext_4785_, v_handler_4786_);
return v_res_4788_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4789_; lean_object* v___x_4790_; 
v___x_4789_ = 0;
v___x_4790_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4789_);
return v___x_4790_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_unsigned_to_nat(4096u);
v___x_4792_ = lean_mk_empty_byte_array(v___x_4791_);
return v___x_4792_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4793_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4794_ = l_ByteArray_mkIterator(v___x_4793_);
return v___x_4794_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4795_ = 0;
v___x_4796_ = lean_unsigned_to_nat(0u);
v___x_4797_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4798_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4799_ = lean_box(0);
v___x_4800_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
lean_ctor_set(v___x_4800_, 1, v___x_4798_);
lean_ctor_set(v___x_4800_, 2, v___x_4797_);
lean_ctor_set(v___x_4800_, 3, v___x_4796_);
lean_ctor_set(v___x_4800_, 4, v___x_4796_);
lean_ctor_set(v___x_4800_, 5, v___x_4796_);
lean_ctor_set_uint8(v___x_4800_, sizeof(void*)*6, v___x_4795_);
return v___x_4800_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = 1;
v___x_4809_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4808_);
return v___x_4809_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4810_; uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4810_ = lean_unsigned_to_nat(0u);
v___x_4811_ = 0;
v___x_4812_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4813_ = lean_box(0);
v___x_4814_ = lean_box(0);
v___x_4815_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4816_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4817_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
lean_ctor_set(v___x_4817_, 1, v___x_4815_);
lean_ctor_set(v___x_4817_, 2, v___x_4814_);
lean_ctor_set(v___x_4817_, 3, v___x_4813_);
lean_ctor_set(v___x_4817_, 4, v___x_4812_);
lean_ctor_set(v___x_4817_, 5, v___x_4810_);
lean_ctor_set_uint8(v___x_4817_, sizeof(void*)*6, v___x_4811_);
lean_ctor_set_uint8(v___x_4817_, sizeof(void*)*6 + 1, v___x_4811_);
lean_ctor_set_uint8(v___x_4817_, sizeof(void*)*6 + 2, v___x_4811_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4818_, lean_object* v_client_4819_, lean_object* v_extensions_4820_, lean_object* v_inst_4821_, lean_object* v_inst_4822_, lean_object* v_handler_4823_, lean_object* v_x_4824_){
_start:
{
if (lean_obj_tag(v_x_4824_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4834_; 
lean_dec(v_handler_4823_);
lean_dec_ref(v_inst_4822_);
lean_dec_ref(v_inst_4821_);
lean_dec(v_extensions_4820_);
lean_dec(v_client_4819_);
lean_dec_ref(v_config_4818_);
v_a_4826_ = lean_ctor_get(v_x_4824_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v_x_4824_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4828_ = v_x_4824_;
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v_x_4824_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4831_);
return v___x_4832_;
}
}
}
else
{
lean_object* v_a_4835_; uint8_t v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; uint8_t v_enableKeepAlive_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v_a_4835_ = lean_ctor_get(v_x_4824_, 0);
lean_inc(v_a_4835_);
lean_dec_ref_known(v_x_4824_, 1);
v___x_4836_ = 0;
v___x_4837_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4838_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4839_ = lean_box(0);
v___x_4840_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4841_ = l_Std_Http_Config_toH1Config(v_config_4818_);
v_enableKeepAlive_4842_ = lean_ctor_get_uint8(v___x_4841_, sizeof(void*)*18);
v___x_4843_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4843_, 0, v___x_4837_);
lean_ctor_set(v___x_4843_, 1, v___x_4840_);
lean_ctor_set(v___x_4843_, 2, v___x_4841_);
lean_ctor_set(v___x_4843_, 3, v___x_4838_);
lean_ctor_set(v___x_4843_, 4, v___x_4839_);
lean_ctor_set(v___x_4843_, 5, v___x_4839_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*6, v_enableKeepAlive_4842_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*6 + 1, v___x_4836_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*6 + 2, v___x_4836_);
v___x_4844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4844_, 0, v_client_4819_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
lean_ctor_set(v___x_4844_, 2, v_extensions_4820_);
v___x_4845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4821_, v_inst_4822_, v___x_4844_, v_config_4818_, v_a_4835_, v_handler_4823_);
return v___x_4845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4846_, lean_object* v_client_4847_, lean_object* v_extensions_4848_, lean_object* v_inst_4849_, lean_object* v_inst_4850_, lean_object* v_handler_4851_, lean_object* v_x_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4846_, v_client_4847_, v_extensions_4848_, v_inst_4849_, v_inst_4850_, v_handler_4851_, v_x_4852_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4855_, lean_object* v_inst_4856_, lean_object* v_client_4857_, lean_object* v_handler_4858_, lean_object* v_config_4859_, lean_object* v_extensions_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v___f_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; 
v___f_4863_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4863_, 0, v_config_4859_);
lean_closure_set(v___f_4863_, 1, v_client_4857_);
lean_closure_set(v___f_4863_, 2, v_extensions_4860_);
lean_closure_set(v___f_4863_, 3, v_inst_4855_);
lean_closure_set(v___f_4863_, 4, v_inst_4856_);
lean_closure_set(v___f_4863_, 5, v_handler_4858_);
lean_inc_ref(v_a_4861_);
v___x_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4864_, 0, v_a_4861_);
v___x_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = 0;
v___x_4868_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4866_, v___x_4867_, v___x_4865_, v___f_4863_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4869_, lean_object* v_inst_4870_, lean_object* v_client_4871_, lean_object* v_handler_4872_, lean_object* v_config_4873_, lean_object* v_extensions_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4869_, v_inst_4870_, v_client_4871_, v_handler_4872_, v_config_4873_, v_extensions_4874_, v_a_4875_);
lean_dec_ref(v_a_4875_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4878_, lean_object* v_00_u03c3_4879_, lean_object* v_inst_4880_, lean_object* v_inst_4881_, lean_object* v_client_4882_, lean_object* v_handler_4883_, lean_object* v_config_4884_, lean_object* v_extensions_4885_, lean_object* v_a_4886_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4880_, v_inst_4881_, v_client_4882_, v_handler_4883_, v_config_4884_, v_extensions_4885_, v_a_4886_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4889_, lean_object* v_00_u03c3_4890_, lean_object* v_inst_4891_, lean_object* v_inst_4892_, lean_object* v_client_4893_, lean_object* v_handler_4894_, lean_object* v_config_4895_, lean_object* v_extensions_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Std_Http_Server_serveConnection(v_t_4889_, v_00_u03c3_4890_, v_inst_4891_, v_inst_4892_, v_client_4893_, v_handler_4894_, v_config_4895_, v_extensions_4896_, v_a_4897_);
lean_dec_ref(v_a_4897_);
return v_res_4899_;
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
