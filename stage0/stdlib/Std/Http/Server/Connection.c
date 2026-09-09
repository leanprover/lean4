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
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_date;
lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
lean_object* lean_io_promise_new();
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t v_x_3719__boxed_223_; lean_object* v_res_224_; 
v_x_3719__boxed_223_ = lean_unbox(v_x_221_);
v_res_224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3719__boxed_223_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v_x_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v_x_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_x_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v___f_253_, lean_object* v_response_254_, lean_object* v___x_255_, lean_object* v___f_256_, lean_object* v_requestBody_257_, lean_object* v___f_258_, lean_object* v_responseBody_259_, lean_object* v_inst_260_, lean_object* v___f_261_, lean_object* v_____r_262_, lean_object* v_selectables_263_){
_start:
{
lean_object* v_selectables_266_; lean_object* v_selectables_272_; lean_object* v_selectables_278_; 
if (lean_obj_tag(v_responseBody_259_) == 1)
{
lean_object* v_val_283_; lean_object* v_recvSelector_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_selectables_287_; 
v_val_283_ = lean_ctor_get(v_responseBody_259_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v_responseBody_259_, 1);
v_recvSelector_284_ = lean_ctor_get(v_inst_260_, 3);
lean_inc_ref(v_recvSelector_284_);
lean_dec_ref(v_inst_260_);
v___x_285_ = lean_apply_1(v_recvSelector_284_, v_val_283_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___f_261_);
v_selectables_287_ = lean_array_push(v_selectables_263_, v___x_286_);
v_selectables_278_ = v_selectables_287_;
goto v___jp_277_;
}
else
{
lean_dec_ref(v___f_261_);
lean_dec_ref(v_inst_260_);
lean_dec(v_responseBody_259_);
v_selectables_278_ = v_selectables_263_;
goto v___jp_277_;
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; 
v___x_267_ = l_Std_Async_Selectable_one___redArg(v_selectables_266_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = 0;
v___x_270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_268_, v___x_269_, v___x_267_, v___f_253_);
return v___x_270_;
}
v___jp_271_:
{
if (lean_obj_tag(v_response_254_) == 1)
{
lean_object* v_val_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_selectables_276_; 
v_val_273_ = lean_ctor_get(v_response_254_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_response_254_, 1);
v___x_274_ = l_Std_Channel_recvSelector___redArg(v___x_255_, v_val_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___f_256_);
v_selectables_276_ = lean_array_push(v_selectables_272_, v___x_275_);
v_selectables_266_ = v_selectables_276_;
goto v___jp_265_;
}
else
{
lean_dec_ref(v___f_256_);
lean_dec_ref(v___x_255_);
lean_dec(v_response_254_);
v_selectables_266_ = v_selectables_272_;
goto v___jp_265_;
}
}
v___jp_277_:
{
if (lean_obj_tag(v_requestBody_257_) == 1)
{
lean_object* v_val_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_selectables_282_; 
v_val_279_ = lean_ctor_get(v_requestBody_257_, 0);
lean_inc(v_val_279_);
lean_dec_ref_known(v_requestBody_257_, 1);
v___x_280_ = l_Std_Http_Body_Stream_interestSelector(v_val_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___f_258_);
v_selectables_282_ = lean_array_push(v_selectables_278_, v___x_281_);
v_selectables_272_ = v_selectables_282_;
goto v___jp_271_;
}
else
{
lean_dec_ref(v___f_258_);
lean_dec(v_requestBody_257_);
v_selectables_272_ = v_selectables_278_;
goto v___jp_271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v___f_288_, lean_object* v_response_289_, lean_object* v___x_290_, lean_object* v___f_291_, lean_object* v_requestBody_292_, lean_object* v___f_293_, lean_object* v_responseBody_294_, lean_object* v_inst_295_, lean_object* v___f_296_, lean_object* v_____r_297_, lean_object* v_selectables_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_288_, v_response_289_, v___x_290_, v___f_291_, v_requestBody_292_, v___f_293_, v_responseBody_294_, v_inst_295_, v___f_296_, v_____r_297_, v_selectables_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v_token_301_, lean_object* v___f_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; 
v___x_305_ = l_Std_CancellationToken_getCancellationReason(v_token_301_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = 0;
v___x_310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_308_, v___x_309_, v___x_307_, v___f_302_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v_token_311_, lean_object* v___f_312_, lean_object* v_x_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v_token_311_, v___f_312_, v_x_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v___f_316_, lean_object* v_selectables_317_, lean_object* v___f_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v___f_318_);
lean_dec_ref(v_selectables_317_);
lean_dec_ref(v___f_316_);
v_a_321_ = lean_ctor_get(v_x_319_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v_x_319_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v_x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_330_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v_x_319_, 1);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_a_330_);
lean_ctor_set(v___x_331_, 1, v___f_316_);
v___x_332_ = lean_array_push(v_selectables_317_, v___x_331_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_3(v___f_318_, v___x_333_, v___x_332_, lean_box(0));
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v___f_335_, lean_object* v_selectables_336_, lean_object* v___f_337_, lean_object* v_x_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v___f_335_, v_selectables_336_, v___f_337_, v_x_338_);
return v_res_340_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1000000000u);
v___x_342_ = lean_nat_to_int(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1000u);
v___x_344_ = lean_nat_to_int(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(1000000u);
v___x_346_ = lean_nat_to_int(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object* v_val_347_, lean_object* v___f_348_, lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___f_348_);
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
lean_object* v_a_360_; lean_object* v_second_361_; lean_object* v_nano_362_; lean_object* v_second_363_; lean_object* v_nano_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_second_374_; lean_object* v_nano_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_millis_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v_a_360_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v_x_349_, 1);
v_second_361_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_second_361_);
v_nano_362_ = lean_ctor_get(v_a_360_, 1);
lean_inc(v_nano_362_);
lean_dec(v_a_360_);
v_second_363_ = lean_ctor_get(v_val_347_, 0);
v_nano_364_ = lean_ctor_get(v_val_347_, 1);
v___x_365_ = lean_int_neg(v_second_361_);
lean_dec(v_second_361_);
v___x_366_ = lean_int_neg(v_nano_362_);
lean_dec(v_nano_362_);
v___x_367_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_368_ = lean_int_mul(v_second_363_, v___x_367_);
v___x_369_ = lean_int_add(v___x_368_, v_nano_364_);
lean_dec(v___x_368_);
v___x_370_ = lean_int_mul(v___x_365_, v___x_367_);
lean_dec(v___x_365_);
v___x_371_ = lean_int_add(v___x_370_, v___x_366_);
lean_dec(v___x_366_);
lean_dec(v___x_370_);
v___x_372_ = lean_int_add(v___x_369_, v___x_371_);
lean_dec(v___x_371_);
lean_dec(v___x_369_);
v___x_373_ = l_Std_Time_Duration_ofNanoseconds(v___x_372_);
lean_dec(v___x_372_);
v_second_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_second_374_);
v_nano_375_ = lean_ctor_get(v___x_373_, 1);
lean_inc(v_nano_375_);
lean_dec_ref(v___x_373_);
v___x_376_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1);
v___x_377_ = lean_int_mul(v_second_374_, v___x_376_);
lean_dec(v_second_374_);
v___x_378_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_379_ = lean_int_ediv(v_nano_375_, v___x_378_);
lean_dec(v_nano_375_);
v_millis_380_ = lean_int_add(v___x_377_, v___x_379_);
lean_dec(v___x_379_);
lean_dec(v___x_377_);
v___x_381_ = l_Std_Async_Selector_sleep(v_millis_380_);
lean_dec(v_millis_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = 0;
v___x_384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_382_, v___x_383_, v___x_381_, v___f_348_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object* v_val_385_, lean_object* v___f_386_, lean_object* v_x_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(v_val_385_, v___f_386_, v_x_387_);
lean_dec_ref(v_val_385_);
return v_res_389_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = l_instInhabitedError;
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_config_403_, lean_object* v_handler_404_, lean_object* v_sources_405_){
_start:
{
lean_object* v___y_408_; lean_object* v_val_409_; lean_object* v_socket_414_; lean_object* v_expect_415_; lean_object* v_response_416_; lean_object* v_responseBody_417_; lean_object* v_requestBody_418_; lean_object* v_timeout_419_; lean_object* v_keepAliveTimeout_420_; lean_object* v_headerTimeout_421_; lean_object* v_connectionContext_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___y_435_; lean_object* v___y_483_; 
v_socket_414_ = lean_ctor_get(v_sources_405_, 0);
lean_inc(v_socket_414_);
v_expect_415_ = lean_ctor_get(v_sources_405_, 1);
lean_inc(v_expect_415_);
v_response_416_ = lean_ctor_get(v_sources_405_, 2);
lean_inc_n(v_response_416_, 2);
v_responseBody_417_ = lean_ctor_get(v_sources_405_, 3);
lean_inc_n(v_responseBody_417_, 2);
v_requestBody_418_ = lean_ctor_get(v_sources_405_, 4);
lean_inc_n(v_requestBody_418_, 2);
v_timeout_419_ = lean_ctor_get(v_sources_405_, 5);
lean_inc(v_timeout_419_);
v_keepAliveTimeout_420_ = lean_ctor_get(v_sources_405_, 6);
lean_inc(v_keepAliveTimeout_420_);
v_headerTimeout_421_ = lean_ctor_get(v_sources_405_, 7);
lean_inc(v_headerTimeout_421_);
v_connectionContext_422_ = lean_ctor_get(v_sources_405_, 8);
lean_inc_ref(v_connectionContext_422_);
lean_dec_ref(v_sources_405_);
v___f_423_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_424_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_425_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_425_, 0, v_inst_401_);
lean_closure_set(v___f_425_, 1, v_handler_404_);
lean_closure_set(v___f_425_, 2, v___f_424_);
v___f_426_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_427_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_428_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_429_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_430_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___f_431_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7));
v___x_432_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8);
lean_inc_ref(v_inst_402_);
lean_inc_ref(v___f_425_);
v___f_433_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 12, 9);
lean_closure_set(v___f_433_, 0, v___f_425_);
lean_closure_set(v___f_433_, 1, v_response_416_);
lean_closure_set(v___f_433_, 2, v___x_432_);
lean_closure_set(v___f_433_, 3, v___f_426_);
lean_closure_set(v___f_433_, 4, v_requestBody_418_);
lean_closure_set(v___f_433_, 5, v___f_427_);
lean_closure_set(v___f_433_, 6, v_responseBody_417_);
lean_closure_set(v___f_433_, 7, v_inst_402_);
lean_closure_set(v___f_433_, 8, v___f_428_);
if (lean_obj_tag(v_expect_415_) == 0)
{
lean_object* v_defaultPayloadBytes_486_; 
v_defaultPayloadBytes_486_ = lean_ctor_get(v_config_403_, 8);
lean_inc(v_defaultPayloadBytes_486_);
v___y_483_ = v_defaultPayloadBytes_486_;
goto v___jp_482_;
}
else
{
lean_object* v_val_487_; 
v_val_487_ = lean_ctor_get(v_expect_415_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v_expect_415_, 1);
v___y_483_ = v_val_487_;
goto v___jp_482_;
}
v___jp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_val_409_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = 0;
v___x_413_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_411_, v___x_412_, v___x_410_, v___y_408_);
return v___x_413_;
}
v___jp_434_:
{
lean_object* v_token_436_; lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_selectables_442_; 
v_token_436_ = lean_ctor_get(v_connectionContext_422_, 1);
lean_inc_ref_n(v_token_436_, 2);
lean_dec_ref(v_connectionContext_422_);
v___f_437_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_437_, 0, v_token_436_);
lean_closure_set(v___f_437_, 1, v___f_423_);
v___x_438_ = l_Std_CancellationToken_selector(v_token_436_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___f_437_);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_mk_empty_array_with_capacity(v___x_440_);
v_selectables_442_ = lean_array_push(v___x_441_, v___x_439_);
if (lean_obj_tag(v_socket_414_) == 1)
{
lean_object* v_val_443_; lean_object* v_recvSelector_444_; uint64_t v_expectedBytes_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_selectables_449_; 
lean_dec_ref(v___f_425_);
lean_dec(v_requestBody_418_);
lean_dec(v_responseBody_417_);
lean_dec(v_response_416_);
lean_dec_ref(v_inst_402_);
v_val_443_ = lean_ctor_get(v_socket_414_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v_socket_414_, 1);
v_recvSelector_444_ = lean_ctor_get(v_inst_400_, 2);
lean_inc_ref(v_recvSelector_444_);
lean_dec_ref(v_inst_400_);
v_expectedBytes_445_ = lean_uint64_of_nat(v___y_435_);
lean_dec(v___y_435_);
v___x_446_ = lean_box_uint64(v_expectedBytes_445_);
v___x_447_ = lean_apply_2(v_recvSelector_444_, v_val_443_, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___f_429_);
v_selectables_449_ = lean_array_push(v_selectables_442_, v___x_448_);
if (lean_obj_tag(v_keepAliveTimeout_420_) == 0)
{
if (lean_obj_tag(v_headerTimeout_421_) == 1)
{
lean_object* v_val_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___x_453_; 
lean_dec(v_timeout_419_);
v_val_450_ = lean_ctor_get(v_headerTimeout_421_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v_headerTimeout_421_, 1);
v___f_451_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_451_, 0, v___f_430_);
lean_closure_set(v___f_451_, 1, v_selectables_449_);
lean_closure_set(v___f_451_, 2, v___f_433_);
v___f_452_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_452_, 0, v_val_450_);
lean_closure_set(v___f_452_, 1, v___f_451_);
v___x_453_ = lean_get_current_time();
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 1);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_408_ = v___f_452_;
v_val_409_ = v___x_459_;
goto v___jp_407_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_453_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_453_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 0);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v___y_408_ = v___f_452_;
v_val_409_ = v___x_467_;
goto v___jp_407_;
}
}
}
}
else
{
lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
lean_dec(v_headerTimeout_421_);
v___x_470_ = l_Std_Async_Selector_sleep(v_timeout_419_);
lean_dec(v_timeout_419_);
v___f_471_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_471_, 0, v___f_430_);
lean_closure_set(v___f_471_, 1, v_selectables_449_);
lean_closure_set(v___f_471_, 2, v___f_433_);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = 0;
v___x_474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_472_, v___x_473_, v___x_470_, v___f_471_);
return v___x_474_;
}
}
else
{
lean_object* v___x_475_; lean_object* v___f_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref_known(v_keepAliveTimeout_420_, 1);
lean_dec(v_headerTimeout_421_);
v___x_475_ = l_Std_Async_Selector_sleep(v_timeout_419_);
lean_dec(v_timeout_419_);
v___f_476_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_476_, 0, v___f_431_);
lean_closure_set(v___f_476_, 1, v_selectables_449_);
lean_closure_set(v___f_476_, 2, v___f_433_);
v___x_477_ = 0;
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_478_, v___x_477_, v___x_475_, v___f_476_);
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v___y_435_);
lean_dec_ref(v___f_433_);
lean_dec(v_headerTimeout_421_);
lean_dec(v_keepAliveTimeout_420_);
lean_dec(v_timeout_419_);
lean_dec(v_socket_414_);
lean_dec_ref(v_inst_400_);
v___x_480_ = lean_box(0);
v___x_481_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_425_, v_response_416_, v___x_432_, v___f_426_, v_requestBody_418_, v___f_427_, v_responseBody_417_, v_inst_402_, v___f_428_, v___x_480_, v_selectables_442_);
return v___x_481_;
}
}
v___jp_482_:
{
lean_object* v_maximumRecvSize_484_; uint8_t v___x_485_; 
v_maximumRecvSize_484_ = lean_ctor_get(v_config_403_, 7);
lean_inc(v_maximumRecvSize_484_);
lean_dec_ref(v_config_403_);
v___x_485_ = lean_nat_dec_le(v___y_483_, v_maximumRecvSize_484_);
if (v___x_485_ == 0)
{
lean_dec(v___y_483_);
v___y_435_ = v_maximumRecvSize_484_;
goto v___jp_434_;
}
else
{
lean_dec(v_maximumRecvSize_484_);
v___y_435_ = v___y_483_;
goto v___jp_434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_config_491_, lean_object* v_handler_492_, lean_object* v_sources_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_config_491_, v_handler_492_, v_sources_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_496_, lean_object* v_00_u03c3_497_, lean_object* v_00_u03b2_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_config_502_, lean_object* v_handler_503_, lean_object* v_sources_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_499_, v_inst_500_, v_inst_501_, v_config_502_, v_handler_503_, v_sources_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_507_, lean_object* v_00_u03c3_508_, lean_object* v_00_u03b2_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_config_513_, lean_object* v_handler_514_, lean_object* v_sources_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_507_, v_00_u03c3_508_, v_00_u03b2_509_, v_inst_510_, v_inst_511_, v_inst_512_, v_config_513_, v_handler_514_, v_sources_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___y_522_; uint8_t v___y_523_; 
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_machine_518_);
v_a_528_ = lean_ctor_get(v_x_519_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_519_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v_x_519_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v_x_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___y_539_; uint8_t v___x_545_; 
v_a_537_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v_x_519_, 1);
v___x_545_ = lean_unbox(v_a_537_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(40);
v___y_539_ = v___x_546_;
goto v___jp_538_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
v___y_539_ = v___x_547_;
goto v___jp_538_;
}
v___jp_538_:
{
uint8_t v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = 0;
lean_inc(v___y_539_);
v___x_541_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_540_, v_machine_518_, v___y_539_);
v___x_542_ = lean_unbox(v_a_537_);
lean_dec(v_a_537_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; 
v___x_543_ = 1;
v___y_522_ = v___x_541_;
v___y_523_ = v___x_543_;
goto v___jp_521_;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = 0;
v___y_522_ = v___x_541_;
v___y_523_ = v___x_544_;
goto v___jp_521_;
}
}
}
v___jp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_box(v___y_523_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_522_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_548_, lean_object* v_x_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_548_, v_x_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_box(v___y_552_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___y_1371__boxed_559_; lean_object* v_res_560_; 
v___y_1371__boxed_559_ = lean_unbox(v___y_557_);
v_res_560_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1371__boxed_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; 
v_a_562_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v_x_561_, 1);
v___x_563_ = lean_task_pure(v_a_562_);
return v___x_563_;
}
else
{
lean_object* v_a_564_; 
v_a_564_ = lean_ctor_get(v_x_561_, 0);
lean_inc_ref(v_a_564_);
lean_dec_ref_known(v_x_561_, 1);
return v_a_564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref_known(v_x_566_, 1);
v___x_568_ = 0;
v___x_569_ = lean_box(v___x_568_);
v___x_570_ = l_Std_Channel_send___redArg(v_a_565_, v___x_569_);
lean_dec_ref(v___x_570_);
v___x_571_ = lean_box(0);
return v___x_571_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_572_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v_x_566_, 1);
v___x_573_ = l_Std_Channel_send___redArg(v_a_565_, v_a_572_);
lean_dec_ref(v___x_573_);
v___x_574_ = lean_box(0);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_575_, lean_object* v_x_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_575_, v_x_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_box(v___x_579_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_585_, lean_object* v_x_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_1415__boxed_588_; lean_object* v_res_589_; 
v___x_1415__boxed_588_ = lean_unbox(v___x_585_);
v_res_589_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1415__boxed_588_, v_x_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_590_, uint8_t v___x_591_, lean_object* v_a_592_, lean_object* v___f_593_, lean_object* v___f_594_, lean_object* v___x_595_, uint8_t v___x_596_, lean_object* v___f_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v___f_597_);
lean_dec(v___x_595_);
lean_dec_ref(v___f_594_);
lean_dec_ref(v___f_593_);
lean_dec_ref(v_a_592_);
lean_dec_ref(v_connectionContext_590_);
v_a_600_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_608_ == 0)
{
v___x_602_ = v_x_598_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v_x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
else
{
lean_object* v_a_609_; lean_object* v_token_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_609_ = lean_ctor_get(v_x_598_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v_x_598_, 1);
v_token_610_ = lean_ctor_get(v_connectionContext_590_, 1);
lean_inc_ref(v_token_610_);
lean_dec_ref(v_connectionContext_590_);
v___x_611_ = lean_box(v___x_591_);
v___x_612_ = l_Std_Channel_recvSelector___redArg(v___x_611_, v_a_592_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___f_593_);
v___x_614_ = l_Std_CancellationToken_selector(v_token_610_);
lean_inc_ref(v___f_594_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___f_594_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_a_609_);
lean_ctor_set(v___x_616_, 1, v___f_594_);
v___x_617_ = lean_unsigned_to_nat(3u);
v___x_618_ = lean_mk_empty_array_with_capacity(v___x_617_);
v___x_619_ = lean_array_push(v___x_618_, v___x_613_);
v___x_620_ = lean_array_push(v___x_619_, v___x_615_);
v___x_621_ = lean_array_push(v___x_620_, v___x_616_);
v___x_622_ = l_Std_Async_Selectable_one___redArg(v___x_621_);
v___x_623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_595_, v___x_596_, v___x_622_, v___f_597_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_624_, lean_object* v___x_625_, lean_object* v_a_626_, lean_object* v___f_627_, lean_object* v___f_628_, lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v___f_631_, lean_object* v_x_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_1430__boxed_634_; uint8_t v___x_1435__boxed_635_; lean_object* v_res_636_; 
v___x_1430__boxed_634_ = lean_unbox(v___x_625_);
v___x_1435__boxed_635_ = lean_unbox(v___x_630_);
v_res_636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_624_, v___x_1430__boxed_634_, v_a_626_, v___f_627_, v___f_628_, v___x_629_, v___x_1435__boxed_635_, v___f_631_, v_x_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_637_, lean_object* v___x_638_, uint8_t v___x_639_, lean_object* v___f_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v___f_640_);
lean_dec(v___x_638_);
v_a_643_ = lean_ctor_get(v_x_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_x_641_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v_x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_650_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
else
{
lean_object* v_lingeringTimeout_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v_x_641_, 1);
v_lingeringTimeout_652_ = lean_ctor_get(v_config_637_, 4);
v___x_653_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_652_);
v___x_654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_638_, v___x_639_, v___x_653_, v___f_640_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_655_, lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v___f_658_, lean_object* v_x_659_, lean_object* v___y_660_){
_start:
{
uint8_t v___x_1504__boxed_661_; lean_object* v_res_662_; 
v___x_1504__boxed_661_ = lean_unbox(v___x_657_);
v_res_662_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_655_, v___x_656_, v___x_1504__boxed_661_, v___f_658_, v_x_659_);
lean_dec_ref(v_config_655_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v___f_666_, lean_object* v___x_667_, lean_object* v_connectionContext_668_, uint8_t v___x_669_, lean_object* v_a_670_, lean_object* v___f_671_, lean_object* v___f_672_, lean_object* v_config_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_674_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_config_673_);
lean_dec_ref(v___f_672_);
lean_dec_ref(v___f_671_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v_connectionContext_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___f_666_);
v_a_676_ = lean_ctor_get(v_x_674_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_674_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_x_674_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v_x_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_683_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_702_; 
v_a_685_ = lean_ctor_get(v_x_674_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_674_);
if (v_isSharedCheck_702_ == 0)
{
v___x_687_ = v_x_674_;
v_isShared_688_ = v_isSharedCheck_702_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v_x_674_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_702_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v___f_696_; lean_object* v___x_698_; 
v___x_689_ = 0;
lean_inc_n(v___x_667_, 3);
v___x_690_ = l_BaseIO_chainTask___redArg(v_a_685_, v___f_666_, v___x_667_, v___x_689_);
v___f_691_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_692_ = lean_box(v___x_669_);
v___x_693_ = lean_box(v___x_689_);
v___f_694_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_694_, 0, v_connectionContext_668_);
lean_closure_set(v___f_694_, 1, v___x_692_);
lean_closure_set(v___f_694_, 2, v_a_670_);
lean_closure_set(v___f_694_, 3, v___f_671_);
lean_closure_set(v___f_694_, 4, v___f_691_);
lean_closure_set(v___f_694_, 5, v___x_667_);
lean_closure_set(v___f_694_, 6, v___x_693_);
lean_closure_set(v___f_694_, 7, v___f_672_);
v___x_695_ = lean_box(v___x_689_);
v___f_696_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_696_, 0, v_config_673_);
lean_closure_set(v___f_696_, 1, v___x_667_);
lean_closure_set(v___f_696_, 2, v___x_695_);
lean_closure_set(v___f_696_, 3, v___f_694_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_698_ = v___x_687_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_690_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
v___x_700_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_667_, v___x_689_, v___x_699_, v___f_696_);
return v___x_700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v___f_703_, lean_object* v___x_704_, lean_object* v_connectionContext_705_, lean_object* v___x_706_, lean_object* v_a_707_, lean_object* v___f_708_, lean_object* v___f_709_, lean_object* v_config_710_, lean_object* v_x_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_1546__boxed_713_; lean_object* v_res_714_; 
v___x_1546__boxed_713_ = lean_unbox(v___x_706_);
v_res_714_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v___f_703_, v___x_704_, v_connectionContext_705_, v___x_1546__boxed_713_, v_a_707_, v___f_708_, v___f_709_, v_config_710_, v_x_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_715_, lean_object* v_handler_716_, lean_object* v_head_717_, lean_object* v_connectionContext_718_, uint8_t v___x_719_, lean_object* v___f_720_, lean_object* v___f_721_, lean_object* v_config_722_, lean_object* v___f_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___f_723_);
lean_dec_ref(v_config_722_);
lean_dec_ref(v___f_721_);
lean_dec_ref(v___f_720_);
lean_dec_ref(v_connectionContext_718_);
lean_dec_ref(v_head_717_);
lean_dec(v_handler_716_);
lean_dec_ref(v_inst_715_);
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
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_755_; 
v_a_735_ = lean_ctor_get(v_x_724_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_755_ == 0)
{
v___x_737_ = v_x_724_;
v_isShared_738_ = v_isSharedCheck_755_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v_x_724_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_755_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_onContinue_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___f_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v_onContinue_739_ = lean_ctor_get(v_inst_715_, 3);
lean_inc_ref(v_onContinue_739_);
lean_dec_ref(v_inst_715_);
v___x_740_ = lean_apply_2(v_onContinue_739_, v_handler_716_, v_head_717_);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_742_, 0, lean_box(0));
lean_closure_set(v___x_742_, 1, v___x_740_);
v___x_743_ = lean_io_as_task(v___x_742_, v___x_741_);
lean_inc(v_a_735_);
v___f_744_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_744_, 0, v_a_735_);
v___x_745_ = lean_box(v___x_719_);
v___f_746_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_746_, 0, v___f_744_);
lean_closure_set(v___f_746_, 1, v___x_741_);
lean_closure_set(v___f_746_, 2, v_connectionContext_718_);
lean_closure_set(v___f_746_, 3, v___x_745_);
lean_closure_set(v___f_746_, 4, v_a_735_);
lean_closure_set(v___f_746_, 5, v___f_720_);
lean_closure_set(v___f_746_, 6, v___f_721_);
lean_closure_set(v___f_746_, 7, v_config_722_);
v___x_747_ = 1;
v___x_748_ = lean_task_bind(v___x_743_, v___f_723_, v___x_741_, v___x_747_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_748_);
v___x_750_ = v___x_737_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
v___x_752_ = 0;
v___x_753_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_741_, v___x_752_, v___x_751_, v___f_746_);
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_756_, lean_object* v_handler_757_, lean_object* v_head_758_, lean_object* v_connectionContext_759_, lean_object* v___x_760_, lean_object* v___f_761_, lean_object* v___f_762_, lean_object* v_config_763_, lean_object* v___f_764_, lean_object* v_x_765_, lean_object* v___y_766_){
_start:
{
uint8_t v___x_1627__boxed_767_; lean_object* v_res_768_; 
v___x_1627__boxed_767_ = lean_unbox(v___x_760_);
v_res_768_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_756_, v_handler_757_, v_head_758_, v_connectionContext_759_, v___x_1627__boxed_767_, v___f_761_, v___f_762_, v_config_763_, v___f_764_, v_x_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_771_, lean_object* v_handler_772_, lean_object* v_machine_773_, lean_object* v_head_774_, lean_object* v_config_775_, lean_object* v_connectionContext_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___f_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_778_ = lean_box(0);
v___x_779_ = l_Std_CloseableChannel_new___redArg(v___x_778_);
v___f_780_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_780_, 0, v_machine_773_);
v___f_781_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_782_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_783_ = 0;
v___x_784_ = lean_box(v___x_783_);
v___f_785_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_785_, 0, v_inst_771_);
lean_closure_set(v___f_785_, 1, v_handler_772_);
lean_closure_set(v___f_785_, 2, v_head_774_);
lean_closure_set(v___f_785_, 3, v_connectionContext_776_);
lean_closure_set(v___f_785_, 4, v___x_784_);
lean_closure_set(v___f_785_, 5, v___f_781_);
lean_closure_set(v___f_785_, 6, v___f_780_);
lean_closure_set(v___f_785_, 7, v_config_775_);
lean_closure_set(v___f_785_, 8, v___f_782_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_779_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_788_, v___x_783_, v___x_787_, v___f_785_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_790_, lean_object* v_handler_791_, lean_object* v_machine_792_, lean_object* v_head_793_, lean_object* v_config_794_, lean_object* v_connectionContext_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_790_, v_handler_791_, v_machine_792_, v_head_793_, v_config_794_, v_connectionContext_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_798_, lean_object* v_inst_799_, lean_object* v_handler_800_, lean_object* v_machine_801_, lean_object* v_head_802_, lean_object* v_config_803_, lean_object* v_connectionContext_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_799_, v_handler_800_, v_machine_801_, v_head_802_, v_config_803_, v_connectionContext_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_807_, lean_object* v_inst_808_, lean_object* v_handler_809_, lean_object* v_machine_810_, lean_object* v_head_811_, lean_object* v_config_812_, lean_object* v_connectionContext_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_807_, v_inst_808_, v_handler_809_, v_machine_810_, v_head_811_, v_config_812_, v_connectionContext_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
return v_x_816_;
}
else
{
lean_object* v_key_818_; lean_object* v_value_819_; lean_object* v_tail_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_843_; 
v_key_818_ = lean_ctor_get(v_x_817_, 0);
v_value_819_ = lean_ctor_get(v_x_817_, 1);
v_tail_820_ = lean_ctor_get(v_x_817_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_817_);
if (v_isSharedCheck_843_ == 0)
{
v___x_822_ = v_x_817_;
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_tail_820_);
lean_inc(v_value_819_);
lean_inc(v_key_818_);
lean_dec(v_x_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v_fold_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_824_ = lean_array_get_size(v_x_816_);
v___x_825_ = lean_string_hash(v_key_818_);
v___x_826_ = 32ULL;
v___x_827_ = lean_uint64_shift_right(v___x_825_, v___x_826_);
v_fold_828_ = lean_uint64_xor(v___x_825_, v___x_827_);
v___x_829_ = 16ULL;
v___x_830_ = lean_uint64_shift_right(v_fold_828_, v___x_829_);
v___x_831_ = lean_uint64_xor(v_fold_828_, v___x_830_);
v___x_832_ = lean_uint64_to_usize(v___x_831_);
v___x_833_ = lean_usize_of_nat(v___x_824_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_usize_land(v___x_832_, v___x_835_);
v___x_837_ = lean_array_uget_borrowed(v_x_816_, v___x_836_);
lean_inc(v___x_837_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v___x_837_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_key_818_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_value_819_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v___x_837_);
v___x_839_ = v_reuseFailAlloc_842_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_array_uset(v_x_816_, v___x_836_, v___x_839_);
v_x_816_ = v___x_840_;
v_x_817_ = v_tail_820_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(lean_object* v_i_844_, lean_object* v_source_845_, lean_object* v_target_846_){
_start:
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_array_get_size(v_source_845_);
v___x_848_ = lean_nat_dec_lt(v_i_844_, v___x_847_);
if (v___x_848_ == 0)
{
lean_dec_ref(v_source_845_);
lean_dec(v_i_844_);
return v_target_846_;
}
else
{
lean_object* v_es_849_; lean_object* v___x_850_; lean_object* v_source_851_; lean_object* v_target_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_es_849_ = lean_array_fget(v_source_845_, v_i_844_);
v___x_850_ = lean_box(0);
v_source_851_ = lean_array_fset(v_source_845_, v_i_844_, v___x_850_);
v_target_852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_target_846_, v_es_849_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_i_844_, v___x_853_);
lean_dec(v_i_844_);
v_i_844_ = v___x_854_;
v_source_845_ = v_source_851_;
v_target_846_ = v_target_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object* v_data_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_nbuckets_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_857_ = lean_array_get_size(v_data_856_);
v___x_858_ = lean_unsigned_to_nat(2u);
v_nbuckets_859_ = lean_nat_mul(v___x_857_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_box(0);
v___x_862_ = lean_mk_array(v_nbuckets_859_, v___x_861_);
v___x_863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v___x_860_, v_data_856_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_mk_empty_array_with_capacity(v___x_866_);
v___x_868_ = lean_array_push(v___x_867_, v_i_864_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
v_val_870_ = lean_ctor_get(v_x_865_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_878_ == 0)
{
v___x_872_ = v_x_865_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v_x_865_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_array_push(v_val_870_, v_i_864_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_879_, lean_object* v_a_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_val_884_; lean_object* v___x_885_; 
v___x_882_ = lean_box(0);
v___x_883_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_879_, v___x_882_);
v_val_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_val_884_);
lean_dec(v___x_883_);
v___x_885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_885_, 0, v_a_880_);
lean_ctor_set(v___x_885_, 1, v_val_884_);
lean_ctor_set(v___x_885_, 2, v_x_881_);
return v___x_885_;
}
else
{
lean_object* v_key_886_; lean_object* v_value_887_; lean_object* v_tail_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_903_; 
v_key_886_ = lean_ctor_get(v_x_881_, 0);
v_value_887_ = lean_ctor_get(v_x_881_, 1);
v_tail_888_ = lean_ctor_get(v_x_881_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_903_ == 0)
{
v___x_890_ = v_x_881_;
v_isShared_891_ = v_isSharedCheck_903_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_tail_888_);
lean_inc(v_value_887_);
lean_inc(v_key_886_);
lean_dec(v_x_881_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_903_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
uint8_t v___x_892_; 
v___x_892_ = lean_string_dec_eq(v_key_886_, v_a_880_);
if (v___x_892_ == 0)
{
lean_object* v_tail_893_; lean_object* v___x_895_; 
v_tail_893_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_879_, v_a_880_, v_tail_888_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 2, v_tail_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_key_886_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_value_887_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_tail_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_val_899_; lean_object* v___x_901_; 
lean_dec(v_key_886_);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_value_887_);
v___x_898_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_879_, v___x_897_);
v_val_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_val_899_);
lean_dec(v___x_898_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_val_899_);
lean_ctor_set(v___x_890_, 0, v_a_880_);
v___x_901_ = v___x_890_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_880_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_val_899_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_tail_888_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
uint8_t v___x_906_; 
v___x_906_ = 0;
return v___x_906_;
}
else
{
lean_object* v_key_907_; lean_object* v_tail_908_; uint8_t v___x_909_; 
v_key_907_ = lean_ctor_get(v_x_905_, 0);
v_tail_908_ = lean_ctor_get(v_x_905_, 2);
v___x_909_ = lean_string_dec_eq(v_key_907_, v_a_904_);
if (v___x_909_ == 0)
{
v_x_905_ = v_tail_908_;
goto _start;
}
else
{
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_911_, lean_object* v_x_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_911_, v_x_912_);
lean_dec(v_x_912_);
lean_dec_ref(v_a_911_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_915_, lean_object* v_m_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_size_918_; lean_object* v_buckets_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_969_; 
v_size_918_ = lean_ctor_get(v_m_916_, 0);
v_buckets_919_ = lean_ctor_get(v_m_916_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_m_916_);
if (v_isSharedCheck_969_ == 0)
{
v___x_921_ = v_m_916_;
v_isShared_922_ = v_isSharedCheck_969_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_buckets_919_);
lean_inc(v_size_918_);
lean_dec(v_m_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_969_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; uint64_t v___x_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v_fold_927_; uint64_t v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v___x_935_; lean_object* v_bkt_936_; uint8_t v___x_937_; 
v___x_923_ = lean_array_get_size(v_buckets_919_);
v___x_924_ = lean_string_hash(v_a_917_);
v___x_925_ = 32ULL;
v___x_926_ = lean_uint64_shift_right(v___x_924_, v___x_925_);
v_fold_927_ = lean_uint64_xor(v___x_924_, v___x_926_);
v___x_928_ = 16ULL;
v___x_929_ = lean_uint64_shift_right(v_fold_927_, v___x_928_);
v___x_930_ = lean_uint64_xor(v_fold_927_, v___x_929_);
v___x_931_ = lean_uint64_to_usize(v___x_930_);
v___x_932_ = lean_usize_of_nat(v___x_923_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_sub(v___x_932_, v___x_933_);
v___x_935_ = lean_usize_land(v___x_931_, v___x_934_);
v_bkt_936_ = lean_array_uget_borrowed(v_buckets_919_, v___x_935_);
v___x_937_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_917_, v_bkt_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_size_x27_941_; lean_object* v___x_942_; lean_object* v_buckets_x27_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___x_940_ = lean_array_push(v___x_939_, v_i_915_);
v_size_x27_941_ = lean_nat_add(v_size_918_, v___x_938_);
lean_dec(v_size_918_);
lean_inc(v_bkt_936_);
v___x_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_942_, 0, v_a_917_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
lean_ctor_set(v___x_942_, 2, v_bkt_936_);
v_buckets_x27_943_ = lean_array_uset(v_buckets_919_, v___x_935_, v___x_942_);
v___x_944_ = lean_unsigned_to_nat(4u);
v___x_945_ = lean_nat_mul(v_size_x27_941_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(3u);
v___x_947_ = lean_nat_div(v___x_945_, v___x_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_array_get_size(v_buckets_x27_943_);
v___x_949_ = lean_nat_dec_le(v___x_947_, v___x_948_);
lean_dec(v___x_947_);
if (v___x_949_ == 0)
{
lean_object* v_val_950_; lean_object* v___x_952_; 
v_val_950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_943_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v_val_950_);
lean_ctor_set(v___x_921_, 0, v_size_x27_941_);
v___x_952_ = v___x_921_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_size_x27_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_val_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v___x_955_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v_buckets_x27_943_);
lean_ctor_set(v___x_921_, 0, v_size_x27_941_);
v___x_955_ = v___x_921_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_size_x27_941_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_buckets_x27_943_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v___x_957_; lean_object* v_buckets_x27_958_; lean_object* v_bkt_x27_959_; lean_object* v___y_961_; uint8_t v___x_966_; 
lean_inc(v_bkt_936_);
v___x_957_ = lean_box(0);
v_buckets_x27_958_ = lean_array_uset(v_buckets_919_, v___x_935_, v___x_957_);
lean_inc_ref(v_a_917_);
v_bkt_x27_959_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_915_, v_a_917_, v_bkt_936_);
v___x_966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_917_, v_bkt_x27_959_);
lean_dec_ref(v_a_917_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_sub(v_size_918_, v___x_967_);
lean_dec(v_size_918_);
v___y_961_ = v___x_968_;
goto v___jp_960_;
}
else
{
v___y_961_ = v_size_918_;
goto v___jp_960_;
}
v___jp_960_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_array_uset(v_buckets_x27_958_, v___x_935_, v_bkt_x27_959_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_962_);
lean_ctor_set(v___x_921_, 0, v___y_961_);
v___x_964_ = v___x_921_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___y_961_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_970_, lean_object* v___x_971_, lean_object* v_indexes_972_, lean_object* v_status_973_, uint8_t v_version_974_, lean_object* v_x_975_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_status_973_);
lean_dec_ref(v_indexes_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v_entries_970_);
v_a_977_ = lean_ctor_get(v_x_975_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_985_ == 0)
{
v___x_979_ = v_x_975_;
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v_x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_984_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1002_; 
v_a_986_ = lean_ctor_get(v_x_975_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_988_ = v_x_975_;
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v_x_975_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_i_992_; lean_object* v___x_993_; lean_object* v_entries_994_; lean_object* v_indexes_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_990_ = l_Std_Time_DateTime_toRFC822String(v_a_986_);
v___x_991_ = l_Std_Http_Header_Value_ofString_x21(v___x_990_);
v_i_992_ = lean_array_get_size(v_entries_970_);
lean_inc_ref(v___x_971_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_971_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
v_entries_994_ = lean_array_push(v_entries_970_, v___x_993_);
v_indexes_995_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_992_, v_indexes_972_, v___x_971_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v_entries_994_);
lean_ctor_set(v___x_996_, 1, v_indexes_995_);
v___x_997_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_997_, 0, v_status_973_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*2, v_version_974_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_997_);
v___x_999_ = v___x_988_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_1003_, lean_object* v___x_1004_, lean_object* v_indexes_1005_, lean_object* v_status_1006_, lean_object* v_version_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_){
_start:
{
uint8_t v_version_boxed_1010_; lean_object* v_res_1011_; 
v_version_boxed_1010_ = lean_unbox(v_version_1007_);
v_res_1011_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_1003_, v___x_1004_, v_indexes_1005_, v_status_1006_, v_version_boxed_1010_, v_x_1008_);
return v_res_1011_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_nat_to_int(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1014_, lean_object* v_a_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_offset_1017_; lean_object* v_second_1018_; lean_object* v_nano_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_offset_1017_ = lean_ctor_get(v_tz_1014_, 0);
v_second_1018_ = lean_ctor_get(v_a_1015_, 0);
v_nano_1019_ = lean_ctor_get(v_a_1015_, 1);
v___x_1020_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_1021_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_1022_ = lean_int_mul(v_second_1018_, v___x_1021_);
v___x_1023_ = lean_int_add(v___x_1022_, v_nano_1019_);
lean_dec(v___x_1022_);
v___x_1024_ = lean_int_mul(v_offset_1017_, v___x_1021_);
v___x_1025_ = lean_int_add(v___x_1024_, v___x_1020_);
lean_dec(v___x_1024_);
v___x_1026_ = lean_int_add(v___x_1023_, v___x_1025_);
lean_dec(v___x_1025_);
lean_dec(v___x_1023_);
v___x_1027_ = l_Std_Time_Duration_ofNanoseconds(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1028_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1029_, lean_object* v_a_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1029_, v_a_1030_, v_x_1031_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v_tz_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object* v_m_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_buckets_1035_; lean_object* v___x_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v_fold_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_buckets_1035_ = lean_ctor_get(v_m_1033_, 1);
v___x_1036_ = lean_array_get_size(v_buckets_1035_);
v___x_1037_ = lean_string_hash(v_a_1034_);
v___x_1038_ = 32ULL;
v___x_1039_ = lean_uint64_shift_right(v___x_1037_, v___x_1038_);
v_fold_1040_ = lean_uint64_xor(v___x_1037_, v___x_1039_);
v___x_1041_ = 16ULL;
v___x_1042_ = lean_uint64_shift_right(v_fold_1040_, v___x_1041_);
v___x_1043_ = lean_uint64_xor(v_fold_1040_, v___x_1042_);
v___x_1044_ = lean_uint64_to_usize(v___x_1043_);
v___x_1045_ = lean_usize_of_nat(v___x_1036_);
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_sub(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_usize_land(v___x_1044_, v___x_1047_);
v___x_1049_ = lean_array_uget_borrowed(v_buckets_1035_, v___x_1048_);
v___x_1050_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1034_, v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object* v_m_1051_, lean_object* v_a_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1051_, v_a_1052_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_m_1051_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1056_, lean_object* v_head_1057_){
_start:
{
lean_object* v_headers_1062_; uint8_t v_generateDate_1063_; lean_object* v_status_1064_; uint8_t v_version_1065_; lean_object* v_entries_1066_; lean_object* v_indexes_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v_val_1072_; lean_object* v_a_1078_; uint8_t v___y_1081_; uint8_t v___x_1100_; 
v_headers_1062_ = lean_ctor_get(v_head_1057_, 1);
v_generateDate_1063_ = lean_ctor_get_uint8(v_config_1056_, sizeof(void*)*24 + 1);
v_status_1064_ = lean_ctor_get(v_head_1057_, 0);
v_version_1065_ = lean_ctor_get_uint8(v_head_1057_, sizeof(void*)*2);
v_entries_1066_ = lean_ctor_get(v_headers_1062_, 0);
v_indexes_1067_ = lean_ctor_get(v_headers_1062_, 1);
v___x_1068_ = l_Std_Http_Header_Name_date;
v___x_1069_ = lean_box(v_version_1065_);
lean_inc(v_status_1064_);
lean_inc_ref(v_indexes_1067_);
lean_inc_ref(v_entries_1066_);
v___f_1070_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1070_, 0, v_entries_1066_);
lean_closure_set(v___f_1070_, 1, v___x_1068_);
lean_closure_set(v___f_1070_, 2, v_indexes_1067_);
lean_closure_set(v___f_1070_, 3, v_status_1064_);
lean_closure_set(v___f_1070_, 4, v___x_1069_);
v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_1067_, v___x_1068_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
v___x_1101_ = 1;
v___y_1081_ = v___x_1101_;
goto v___jp_1080_;
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = 0;
v___y_1081_ = v___x_1102_;
goto v___jp_1080_;
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_head_1057_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
v___jp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_val_1072_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = 0;
v___x_1076_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1074_, v___x_1075_, v___x_1073_, v___f_1070_);
return v___x_1076_;
}
v___jp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_a_1078_);
v_val_1072_ = v___x_1079_;
goto v___jp_1071_;
}
v___jp_1080_:
{
if (v_generateDate_1063_ == 0)
{
lean_dec_ref(v___f_1070_);
goto v___jp_1059_;
}
else
{
if (v___y_1081_ == 0)
{
lean_dec_ref(v___f_1070_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1082_; 
lean_dec_ref(v_head_1057_);
v___x_1082_ = lean_get_current_time();
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1085_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1084_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1097_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1097_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1097_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_tz_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_inc(v_a_1086_);
v_tz_1090_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1086_, v_a_1083_);
lean_inc(v_a_1083_);
lean_inc_ref(v_tz_1090_);
v___f_1091_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1091_, 0, v_tz_1090_);
lean_closure_set(v___f_1091_, 1, v_a_1083_);
v___x_1092_ = lean_mk_thunk(v___f_1091_);
v___x_1093_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_a_1083_);
lean_ctor_set(v___x_1093_, 2, v_a_1086_);
lean_ctor_set(v___x_1093_, 3, v_tz_1090_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
lean_ctor_set(v___x_1088_, 0, v___x_1093_);
v___x_1095_ = v___x_1088_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v_val_1072_ = v___x_1095_;
goto v___jp_1071_;
}
}
}
else
{
lean_object* v_a_1098_; 
lean_dec(v_a_1083_);
v_a_1098_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1085_, 1);
v_a_1078_ = v_a_1098_;
goto v___jp_1077_;
}
}
else
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1082_, 1);
v_a_1078_ = v_a_1099_;
goto v___jp_1077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1103_, lean_object* v_head_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1103_, v_head_1104_);
lean_dec_ref(v_config_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1108_, v_a_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(v_00_u03b2_1111_, v_m_1112_, v_a_1113_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_m_1112_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__5(lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_nat_to_int(v_a_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_nat_to_int(v_a_1118_);
v___x_1120_ = l_Rat_ofInt(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1121_, lean_object* v_a_1122_, lean_object* v_x_1123_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1125_, lean_object* v_a_1126_, lean_object* v_x_1127_){
_start:
{
uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_res_1128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1125_, v_a_1126_, v_x_1127_);
lean_dec(v_x_1127_);
lean_dec_ref(v_a_1126_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1130_, lean_object* v_data_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1133_, lean_object* v_i_1134_, lean_object* v_source_1135_, lean_object* v_target_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v_i_1134_, v_source_1135_, v_target_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1139_, v_x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1142_, lean_object* v_____r_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___y_1142_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1149_, lean_object* v_____r_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1149_, v_____r_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1153_, lean_object* v_x_1154_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v___f_1153_);
v_a_1156_ = lean_ctor_get(v_x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1158_ = v_x_1154_;
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v_x_1154_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1166_; 
v_a_1165_ = lean_ctor_get(v_x_1154_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v_x_1154_, 1);
v___x_1166_ = lean_apply_2(v___f_1153_, v_a_1165_, lean_box(0));
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1167_, v_x_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1171_, lean_object* v_body_1172_, lean_object* v___f_1173_, lean_object* v___f_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v___f_1174_);
lean_dec_ref(v___f_1173_);
lean_dec(v_body_1172_);
lean_dec_ref(v_close_1171_);
v_a_1177_ = lean_ctor_get(v_x_1175_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v_x_1175_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v_x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; uint8_t v___x_1187_; 
v_a_1186_ = lean_ctor_get(v_x_1175_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v_x_1175_, 1);
v___x_1187_ = lean_unbox(v_a_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v___f_1174_);
v___x_1188_ = lean_apply_2(v_close_1171_, v_body_1172_, lean_box(0));
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_unbox(v_a_1186_);
lean_dec(v_a_1186_);
v___x_1191_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1189_, v___x_1190_, v___x_1188_, v___f_1173_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec(v_a_1186_);
lean_dec_ref(v___f_1173_);
lean_dec(v_body_1172_);
lean_dec_ref(v_close_1171_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_apply_2(v___f_1174_, v___x_1192_, lean_box(0));
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1194_, lean_object* v_body_1195_, lean_object* v___f_1196_, lean_object* v___f_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1194_, v_body_1195_, v___f_1196_, v___f_1197_, v_x_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1201_, lean_object* v___f_1202_, lean_object* v___f_1203_, lean_object* v_x1_1204_, lean_object* v_x2_1205_){
_start:
{
lean_object* v_fst_1206_; uint8_t v___x_1207_; 
v_fst_1206_ = lean_ctor_get(v_x2_1205_, 0);
lean_inc(v_fst_1206_);
v___x_1207_ = lean_string_dec_eq(v___x_1201_, v_fst_1206_);
if (v___x_1207_ == 0)
{
lean_object* v_entries_1208_; lean_object* v_indexes_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1220_; 
v_entries_1208_ = lean_ctor_get(v_x1_1204_, 0);
v_indexes_1209_ = lean_ctor_get(v_x1_1204_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x1_1204_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1211_ = v_x1_1204_;
v_isShared_1212_ = v_isSharedCheck_1220_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_indexes_1209_);
lean_inc(v_entries_1208_);
lean_dec(v_x1_1204_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1220_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_i_1213_; lean_object* v_f_1214_; lean_object* v_entries_1215_; lean_object* v_indexes_1216_; lean_object* v___x_1218_; 
v_i_1213_ = lean_array_get_size(v_entries_1208_);
v_f_1214_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1214_, 0, v_i_1213_);
v_entries_1215_ = lean_array_push(v_entries_1208_, v_x2_1205_);
v_indexes_1216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1202_, v___f_1203_, v_indexes_1209_, v_fst_1206_, v_f_1214_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v_indexes_1216_);
lean_ctor_set(v___x_1211_, 0, v_entries_1215_);
v___x_1218_ = v___x_1211_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_entries_1215_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_indexes_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_dec(v_fst_1206_);
lean_dec_ref(v_x2_1205_);
lean_dec_ref(v___f_1203_);
lean_dec_ref(v___f_1202_);
return v_x1_1204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1221_, lean_object* v___f_1222_, lean_object* v___f_1223_, lean_object* v_x1_1224_, lean_object* v_x2_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1221_, v___f_1222_, v___f_1223_, v_x1_1224_, v_x2_1225_);
lean_dec_ref(v___x_1221_);
return v_res_1226_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2(void){
_start:
{
lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; 
v___f_1229_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1230_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1231_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1230_, v___f_1229_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___f_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; lean_object* v___f_1254_; 
v___f_1251_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1252_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1253_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1254_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1254_, 0, v___x_1253_);
lean_closure_set(v___f_1254_, 1, v___f_1252_);
lean_closure_set(v___f_1254_, 2, v___f_1251_);
return v___f_1254_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14(void){
_start:
{
lean_object* v___f_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; 
v___f_1255_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1256_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1257_ = l_Std_Http_Header_Name_contentLength;
v___f_1258_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1258_, 0, v___x_1257_);
lean_closure_set(v___f_1258_, 1, v___f_1256_);
lean_closure_set(v___f_1258_, 2, v___f_1255_);
return v___f_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1259_, lean_object* v_body_1260_, lean_object* v_isClosed_1261_, lean_object* v_close_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___y_1266_; uint8_t v_omitBody_1267_; lean_object* v___y_1280_; 
if (lean_obj_tag(v_x_1263_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_close_1262_);
lean_dec_ref(v_isClosed_1261_);
lean_dec(v_body_1260_);
lean_dec_ref(v___y_1259_);
v_a_1314_ = lean_ctor_get(v_x_1263_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_x_1263_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1316_ = v_x_1263_;
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v_x_1263_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___y_1325_; uint8_t v___y_1326_; uint8_t v___y_1327_; uint8_t v___y_1328_; uint8_t v___y_1329_; uint8_t v___y_1330_; lean_object* v_writer_1338_; lean_object* v_reader_1339_; lean_object* v_config_1340_; lean_object* v_events_1341_; lean_object* v_error_1342_; lean_object* v_instant_1343_; uint8_t v_keepAlive_1344_; uint8_t v_forcedFlush_1345_; uint8_t v_pullBodyStalled_1346_; lean_object* v_userData_1347_; lean_object* v_outputData_1348_; lean_object* v_state_1349_; lean_object* v_knownSize_1350_; lean_object* v_messageHead_1351_; uint8_t v_sentMessage_1352_; uint8_t v_userClosedBody_1353_; uint8_t v_omitBody_1354_; lean_object* v_userDataBytes_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1438_; 
v_a_1323_ = lean_ctor_get(v_x_1263_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v_x_1263_, 1);
v_writer_1338_ = lean_ctor_get(v___y_1259_, 1);
lean_inc_ref(v_writer_1338_);
v_reader_1339_ = lean_ctor_get(v___y_1259_, 0);
v_config_1340_ = lean_ctor_get(v___y_1259_, 2);
v_events_1341_ = lean_ctor_get(v___y_1259_, 3);
v_error_1342_ = lean_ctor_get(v___y_1259_, 4);
v_instant_1343_ = lean_ctor_get(v___y_1259_, 5);
v_keepAlive_1344_ = lean_ctor_get_uint8(v___y_1259_, sizeof(void*)*6);
v_forcedFlush_1345_ = lean_ctor_get_uint8(v___y_1259_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1346_ = lean_ctor_get_uint8(v___y_1259_, sizeof(void*)*6 + 2);
v_userData_1347_ = lean_ctor_get(v_writer_1338_, 0);
v_outputData_1348_ = lean_ctor_get(v_writer_1338_, 1);
v_state_1349_ = lean_ctor_get(v_writer_1338_, 2);
v_knownSize_1350_ = lean_ctor_get(v_writer_1338_, 3);
v_messageHead_1351_ = lean_ctor_get(v_writer_1338_, 4);
v_sentMessage_1352_ = lean_ctor_get_uint8(v_writer_1338_, sizeof(void*)*6);
v_userClosedBody_1353_ = lean_ctor_get_uint8(v_writer_1338_, sizeof(void*)*6 + 1);
v_omitBody_1354_ = lean_ctor_get_uint8(v_writer_1338_, sizeof(void*)*6 + 2);
v_userDataBytes_1355_ = lean_ctor_get(v_writer_1338_, 5);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_writer_1338_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1357_ = v_writer_1338_;
v_isShared_1358_ = v_isSharedCheck_1438_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_userDataBytes_1355_);
lean_inc(v_messageHead_1351_);
lean_inc(v_knownSize_1350_);
lean_inc(v_state_1349_);
lean_inc(v_outputData_1348_);
lean_inc(v_userData_1347_);
lean_dec(v_writer_1338_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1438_;
goto v_resetjp_1356_;
}
v___jp_1324_:
{
lean_object* v_headerSize_1331_; lean_object* v_machine_1332_; lean_object* v_machine_1333_; lean_object* v_reader_1334_; lean_object* v_state_1335_; 
v_headerSize_1331_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1329_, v_a_1323_, v___y_1326_);
v_machine_1332_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1327_, v___y_1325_, v_headerSize_1331_, v___y_1330_);
v_machine_1333_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1327_, v_machine_1332_, v_a_1323_);
lean_dec(v_a_1323_);
v_reader_1334_ = lean_ctor_get(v_machine_1333_, 0);
lean_inc_ref(v_reader_1334_);
v_state_1335_ = lean_ctor_get(v_reader_1334_, 0);
lean_inc(v_state_1335_);
lean_dec_ref(v_reader_1334_);
if (lean_obj_tag(v_state_1335_) == 7)
{
lean_dec_ref_known(v_state_1335_, 1);
if (v___y_1328_ == 0)
{
lean_object* v_writer_1336_; uint8_t v_omitBody_1337_; 
v_writer_1336_ = lean_ctor_get(v_machine_1333_, 1);
lean_inc_ref(v_writer_1336_);
v_omitBody_1337_ = lean_ctor_get_uint8(v_writer_1336_, sizeof(void*)*6 + 2);
lean_dec_ref(v_writer_1336_);
v___y_1266_ = v_machine_1333_;
v_omitBody_1267_ = v_omitBody_1337_;
goto v___jp_1265_;
}
else
{
v___y_1280_ = v_machine_1333_;
goto v___jp_1279_;
}
}
else
{
lean_dec(v_state_1335_);
v___y_1280_ = v_machine_1333_;
goto v___jp_1279_;
}
}
v_resetjp_1356_:
{
uint8_t v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1387_; uint8_t v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1403_; uint8_t v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1424_; lean_object* v___x_1432_; uint8_t v___x_1433_; uint8_t v___y_1435_; 
v___x_1432_ = lean_box(1);
v___x_1433_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1349_, v___x_1432_);
if (v_sentMessage_1352_ == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = 1;
v___y_1435_ = v___x_1436_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = 0;
v___y_1435_ = v___x_1437_;
goto v___jp_1434_;
}
v___jp_1359_:
{
lean_object* v_message_1362_; lean_object* v___x_2263__overap_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v_message_1362_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1360_, v_a_1323_, v___y_1361_);
v___x_2263__overap_1363_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1360_);
v___x_1364_ = lean_apply_2(v___x_2263__overap_1363_, v_outputData_1348_, v_message_1362_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v___x_1364_);
v___x_1366_ = v___x_1357_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_userData_1347_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_state_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_knownSize_1350_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_messageHead_1351_);
lean_ctor_set(v_reuseFailAlloc_1368_, 5, v_userDataBytes_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*6, v_sentMessage_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*6 + 1, v_userClosedBody_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*6 + 2, v_omitBody_1354_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1367_, 0, v_reader_1339_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
lean_ctor_set(v___x_1367_, 2, v_config_1340_);
lean_ctor_set(v___x_1367_, 3, v_events_1341_);
lean_ctor_set(v___x_1367_, 4, v_error_1342_);
lean_ctor_set(v___x_1367_, 5, v_instant_1343_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*6, v_keepAlive_1344_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*6 + 1, v_forcedFlush_1345_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*6 + 2, v_pullBodyStalled_1346_);
v___y_1266_ = v___x_1367_;
v_omitBody_1267_ = v_omitBody_1354_;
goto v___jp_1265_;
}
}
v___jp_1369_:
{
lean_object* v___x_1372_; lean_object* v___f_1373_; lean_object* v___f_1374_; uint8_t v___x_1375_; 
v___x_1372_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1373_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1374_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1375_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1373_, v___f_1374_, v___x_1372_, v___y_1371_);
if (v___x_1375_ == 0)
{
v___y_1360_ = v___y_1370_;
v___y_1361_ = v___y_1371_;
goto v___jp_1359_;
}
else
{
lean_object* v_entries_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_entries_1376_ = lean_ctor_get(v___y_1371_, 0);
lean_inc_ref(v_entries_1376_);
lean_dec_ref(v___y_1371_);
v___x_1377_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_array_get_size(v_entries_1376_);
v___x_1380_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1381_ = lean_nat_dec_lt(v___x_1378_, v___x_1379_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v_entries_1376_);
v___y_1360_ = v___y_1370_;
v___y_1361_ = v___x_1377_;
goto v___jp_1359_;
}
else
{
lean_object* v___f_1382_; size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___f_1382_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13);
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = lean_usize_of_nat(v___x_1379_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1380_, v___f_1382_, v_entries_1376_, v___x_1383_, v___x_1384_, v___x_1377_);
v___y_1360_ = v___y_1370_;
v___y_1361_ = v___x_1385_;
goto v___jp_1359_;
}
}
}
v___jp_1386_:
{
uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v_indexes_1393_; lean_object* v___x_1394_; lean_object* v_machine_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___f_1398_; uint8_t v___x_1399_; 
v___x_1391_ = 1;
v___x_1392_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1391_, v_a_1323_);
v_indexes_1393_ = lean_ctor_get(v___x_1392_, 1);
lean_inc_ref(v_indexes_1393_);
lean_dec_ref(v___x_1392_);
lean_inc(v_a_1323_);
v___x_1394_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1394_, 0, v_userData_1347_);
lean_ctor_set(v___x_1394_, 1, v_outputData_1348_);
lean_ctor_set(v___x_1394_, 2, v_state_1349_);
lean_ctor_set(v___x_1394_, 3, v_knownSize_1350_);
lean_ctor_set(v___x_1394_, 4, v_a_1323_);
lean_ctor_set(v___x_1394_, 5, v_userDataBytes_1355_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*6, v___y_1388_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*6 + 1, v_userClosedBody_1353_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*6 + 2, v_omitBody_1354_);
v_machine_1395_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1395_, 0, v_reader_1339_);
lean_ctor_set(v_machine_1395_, 1, v___x_1394_);
lean_ctor_set(v_machine_1395_, 2, v_config_1340_);
lean_ctor_set(v_machine_1395_, 3, v_events_1341_);
lean_ctor_set(v_machine_1395_, 4, v_error_1342_);
lean_ctor_set(v_machine_1395_, 5, v_instant_1343_);
lean_ctor_set_uint8(v_machine_1395_, sizeof(void*)*6, v_keepAlive_1344_);
lean_ctor_set_uint8(v_machine_1395_, sizeof(void*)*6 + 1, v_forcedFlush_1345_);
lean_ctor_set_uint8(v_machine_1395_, sizeof(void*)*6 + 2, v_pullBodyStalled_1346_);
v___x_1396_ = l_Std_Http_Header_Name_contentLength;
v___f_1397_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1398_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1397_, v___f_1398_, v_indexes_1393_, v___x_1396_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1401_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1397_, v___f_1398_, v_indexes_1393_, v___x_1400_);
lean_dec_ref(v_indexes_1393_);
v___y_1325_ = v_machine_1395_;
v___y_1326_ = v___y_1387_;
v___y_1327_ = v___y_1389_;
v___y_1328_ = v___y_1390_;
v___y_1329_ = v___x_1391_;
v___y_1330_ = v___x_1401_;
goto v___jp_1324_;
}
else
{
lean_dec_ref(v_indexes_1393_);
v___y_1325_ = v_machine_1395_;
v___y_1326_ = v___y_1387_;
v___y_1327_ = v___y_1389_;
v___y_1328_ = v___y_1390_;
v___y_1329_ = v___x_1391_;
v___y_1330_ = v___x_1399_;
goto v___jp_1324_;
}
}
v___jp_1402_:
{
if (v___y_1405_ == 0)
{
lean_object* v_state_1406_; 
lean_del_object(v___x_1357_);
lean_dec(v_messageHead_1351_);
v_state_1406_ = lean_ctor_get(v_reader_1339_, 0);
if (lean_obj_tag(v_state_1406_) == 7)
{
v___y_1387_ = v___y_1405_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___y_1404_;
v___y_1390_ = v___y_1403_;
goto v___jp_1386_;
}
else
{
v___y_1387_ = v___y_1405_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___y_1404_;
v___y_1390_ = v___y_1405_;
goto v___jp_1386_;
}
}
else
{
uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___f_1411_; uint8_t v___x_1412_; 
v___x_1407_ = 1;
v___x_1408_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1407_, v_a_1323_);
v___x_1409_ = l_Std_Http_Header_Name_contentLength;
v___f_1410_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1411_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1412_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1410_, v___f_1411_, v___x_1409_, v___x_1408_);
if (v___x_1412_ == 0)
{
v___y_1370_ = v___x_1407_;
v___y_1371_ = v___x_1408_;
goto v___jp_1369_;
}
else
{
lean_object* v_entries_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_entries_1413_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_entries_1413_);
lean_dec_ref(v___x_1408_);
v___x_1414_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_entries_1413_);
v___x_1417_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1418_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v_entries_1413_);
v___y_1370_ = v___x_1407_;
v___y_1371_ = v___x_1414_;
goto v___jp_1369_;
}
else
{
lean_object* v___f_1419_; size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___f_1419_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1416_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1417_, v___f_1419_, v_entries_1413_, v___x_1420_, v___x_1421_, v___x_1414_);
v___y_1370_ = v___x_1407_;
v___y_1371_ = v___x_1422_;
goto v___jp_1369_;
}
}
}
}
v___jp_1423_:
{
if (v___y_1424_ == 0)
{
lean_del_object(v___x_1357_);
lean_dec(v_userDataBytes_1355_);
lean_dec(v_messageHead_1351_);
lean_dec(v_knownSize_1350_);
lean_dec(v_state_1349_);
lean_dec_ref(v_outputData_1348_);
lean_dec_ref(v_userData_1347_);
lean_dec(v_a_1323_);
v___y_1266_ = v___y_1259_;
v_omitBody_1267_ = v_omitBody_1354_;
goto v___jp_1265_;
}
else
{
lean_object* v_status_1425_; uint8_t v___x_1426_; uint16_t v___x_1427_; uint16_t v___x_1428_; uint8_t v___x_1429_; 
lean_inc(v_instant_1343_);
lean_inc(v_error_1342_);
lean_inc_ref(v_events_1341_);
lean_inc_ref(v_config_1340_);
lean_inc_ref(v_reader_1339_);
lean_dec_ref(v___y_1259_);
v_status_1425_ = lean_ctor_get(v_a_1323_, 0);
v___x_1426_ = 0;
v___x_1427_ = 100;
v___x_1428_ = l_Std_Http_Status_toCode(v_status_1425_);
v___x_1429_ = lean_uint16_dec_le(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
v___y_1403_ = v___y_1424_;
v___y_1404_ = v___x_1426_;
v___y_1405_ = v___x_1429_;
goto v___jp_1402_;
}
else
{
uint16_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = 200;
v___x_1431_ = lean_uint16_dec_lt(v___x_1428_, v___x_1430_);
v___y_1403_ = v___y_1424_;
v___y_1404_ = v___x_1426_;
v___y_1405_ = v___x_1431_;
goto v___jp_1402_;
}
}
}
v___jp_1434_:
{
if (v___x_1433_ == 0)
{
v___y_1424_ = v___x_1433_;
goto v___jp_1423_;
}
else
{
v___y_1424_ = v___y_1435_;
goto v___jp_1423_;
}
}
}
}
v___jp_1265_:
{
if (v_omitBody_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_close_1262_);
lean_dec_ref(v_isClosed_1261_);
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_body_1260_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___y_1266_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
lean_inc(v_body_1260_);
v___x_1272_ = lean_apply_2(v_isClosed_1261_, v_body_1260_, lean_box(0));
v___f_1273_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1273_, 0, v___y_1266_);
lean_inc_ref(v___f_1273_);
v___f_1274_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1274_, 0, v___f_1273_);
v___f_1275_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1275_, 0, v_close_1262_);
lean_closure_set(v___f_1275_, 1, v_body_1260_);
lean_closure_set(v___f_1275_, 2, v___f_1274_);
lean_closure_set(v___f_1275_, 3, v___f_1273_);
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = 0;
v___x_1278_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1276_, v___x_1277_, v___x_1272_, v___f_1275_);
return v___x_1278_;
}
}
v___jp_1279_:
{
lean_object* v_writer_1281_; lean_object* v_reader_1282_; lean_object* v_config_1283_; lean_object* v_events_1284_; lean_object* v_error_1285_; lean_object* v_instant_1286_; uint8_t v_keepAlive_1287_; uint8_t v_forcedFlush_1288_; uint8_t v_pullBodyStalled_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1313_; 
v_writer_1281_ = lean_ctor_get(v___y_1280_, 1);
v_reader_1282_ = lean_ctor_get(v___y_1280_, 0);
v_config_1283_ = lean_ctor_get(v___y_1280_, 2);
v_events_1284_ = lean_ctor_get(v___y_1280_, 3);
v_error_1285_ = lean_ctor_get(v___y_1280_, 4);
v_instant_1286_ = lean_ctor_get(v___y_1280_, 5);
v_keepAlive_1287_ = lean_ctor_get_uint8(v___y_1280_, sizeof(void*)*6);
v_forcedFlush_1288_ = lean_ctor_get_uint8(v___y_1280_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1289_ = lean_ctor_get_uint8(v___y_1280_, sizeof(void*)*6 + 2);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___y_1280_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1291_ = v___y_1280_;
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_instant_1286_);
lean_inc(v_error_1285_);
lean_inc(v_events_1284_);
lean_inc(v_config_1283_);
lean_inc(v_writer_1281_);
lean_inc(v_reader_1282_);
lean_dec(v___y_1280_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_userData_1293_; lean_object* v_outputData_1294_; lean_object* v_knownSize_1295_; lean_object* v_messageHead_1296_; uint8_t v_sentMessage_1297_; uint8_t v_userClosedBody_1298_; uint8_t v_omitBody_1299_; lean_object* v_userDataBytes_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1311_; 
v_userData_1293_ = lean_ctor_get(v_writer_1281_, 0);
v_outputData_1294_ = lean_ctor_get(v_writer_1281_, 1);
v_knownSize_1295_ = lean_ctor_get(v_writer_1281_, 3);
v_messageHead_1296_ = lean_ctor_get(v_writer_1281_, 4);
v_sentMessage_1297_ = lean_ctor_get_uint8(v_writer_1281_, sizeof(void*)*6);
v_userClosedBody_1298_ = lean_ctor_get_uint8(v_writer_1281_, sizeof(void*)*6 + 1);
v_omitBody_1299_ = lean_ctor_get_uint8(v_writer_1281_, sizeof(void*)*6 + 2);
v_userDataBytes_1300_ = lean_ctor_get(v_writer_1281_, 5);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_writer_1281_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_writer_1281_, 2);
lean_dec(v_unused_1312_);
v___x_1302_ = v_writer_1281_;
v_isShared_1303_ = v_isSharedCheck_1311_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_userDataBytes_1300_);
lean_inc(v_messageHead_1296_);
lean_inc(v_knownSize_1295_);
lean_inc(v_outputData_1294_);
lean_inc(v_userData_1293_);
lean_dec(v_writer_1281_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1311_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_box(2);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_userData_1293_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_outputData_1294_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_knownSize_1295_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_messageHead_1296_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_userDataBytes_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6, v_sentMessage_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6 + 1, v_userClosedBody_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6 + 2, v_omitBody_1299_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v___x_1306_);
v___x_1308_ = v___x_1291_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_reader_1282_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_config_1283_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_events_1284_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_error_1285_);
lean_ctor_set(v_reuseFailAlloc_1309_, 5, v_instant_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*6, v_keepAlive_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*6 + 1, v_forcedFlush_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*6 + 2, v_pullBodyStalled_1289_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v___y_1266_ = v___x_1308_;
v_omitBody_1267_ = v_omitBody_1299_;
goto v___jp_1265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1439_, lean_object* v_body_1440_, lean_object* v_isClosed_1441_, lean_object* v_close_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1439_, v_body_1440_, v_isClosed_1441_, v_close_1442_, v_x_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_config_1446_, lean_object* v_line_1447_, lean_object* v_body_1448_, lean_object* v_isClosed_1449_, lean_object* v_close_1450_, lean_object* v_machine_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v___y_1455_; 
if (lean_obj_tag(v_x_1452_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_machine_1451_);
lean_dec_ref(v_close_1450_);
lean_dec_ref(v_isClosed_1449_);
lean_dec(v_body_1448_);
lean_dec_ref(v_line_1447_);
v_a_1461_ = lean_ctor_get(v_x_1452_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v_x_1452_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v_x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v_x_1452_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v_x_1452_, 1);
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_writer_1471_; lean_object* v_reader_1472_; lean_object* v_config_1473_; lean_object* v_events_1474_; lean_object* v_error_1475_; lean_object* v_instant_1476_; uint8_t v_keepAlive_1477_; uint8_t v_forcedFlush_1478_; uint8_t v_pullBodyStalled_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1502_; 
v_writer_1471_ = lean_ctor_get(v_machine_1451_, 1);
v_reader_1472_ = lean_ctor_get(v_machine_1451_, 0);
v_config_1473_ = lean_ctor_get(v_machine_1451_, 2);
v_events_1474_ = lean_ctor_get(v_machine_1451_, 3);
v_error_1475_ = lean_ctor_get(v_machine_1451_, 4);
v_instant_1476_ = lean_ctor_get(v_machine_1451_, 5);
v_keepAlive_1477_ = lean_ctor_get_uint8(v_machine_1451_, sizeof(void*)*6);
v_forcedFlush_1478_ = lean_ctor_get_uint8(v_machine_1451_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1479_ = lean_ctor_get_uint8(v_machine_1451_, sizeof(void*)*6 + 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_machine_1451_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1481_ = v_machine_1451_;
v_isShared_1482_ = v_isSharedCheck_1502_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_instant_1476_);
lean_inc(v_error_1475_);
lean_inc(v_events_1474_);
lean_inc(v_config_1473_);
lean_inc(v_writer_1471_);
lean_inc(v_reader_1472_);
lean_dec(v_machine_1451_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1502_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_userData_1483_; lean_object* v_outputData_1484_; lean_object* v_state_1485_; lean_object* v_messageHead_1486_; uint8_t v_sentMessage_1487_; uint8_t v_userClosedBody_1488_; uint8_t v_omitBody_1489_; lean_object* v_userDataBytes_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1500_; 
v_userData_1483_ = lean_ctor_get(v_writer_1471_, 0);
v_outputData_1484_ = lean_ctor_get(v_writer_1471_, 1);
v_state_1485_ = lean_ctor_get(v_writer_1471_, 2);
v_messageHead_1486_ = lean_ctor_get(v_writer_1471_, 4);
v_sentMessage_1487_ = lean_ctor_get_uint8(v_writer_1471_, sizeof(void*)*6);
v_userClosedBody_1488_ = lean_ctor_get_uint8(v_writer_1471_, sizeof(void*)*6 + 1);
v_omitBody_1489_ = lean_ctor_get_uint8(v_writer_1471_, sizeof(void*)*6 + 2);
v_userDataBytes_1490_ = lean_ctor_get(v_writer_1471_, 5);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_writer_1471_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_writer_1471_, 3);
lean_dec(v_unused_1501_);
v___x_1492_ = v_writer_1471_;
v_isShared_1493_ = v_isSharedCheck_1500_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_userDataBytes_1490_);
lean_inc(v_messageHead_1486_);
lean_inc(v_state_1485_);
lean_inc(v_outputData_1484_);
lean_inc(v_userData_1483_);
lean_dec(v_writer_1471_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1500_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 3, v_a_1470_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_userData_1483_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_outputData_1484_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_state_1485_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_a_1470_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_messageHead_1486_);
lean_ctor_set(v_reuseFailAlloc_1499_, 5, v_userDataBytes_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*6, v_sentMessage_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*6 + 1, v_userClosedBody_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*6 + 2, v_omitBody_1489_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 1, v___x_1495_);
v___x_1497_ = v___x_1481_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_reader_1472_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_config_1473_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_events_1474_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_error_1475_);
lean_ctor_set(v_reuseFailAlloc_1498_, 5, v_instant_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1498_, sizeof(void*)*6, v_keepAlive_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1498_, sizeof(void*)*6 + 1, v_forcedFlush_1478_);
lean_ctor_set_uint8(v_reuseFailAlloc_1498_, sizeof(void*)*6 + 2, v_pullBodyStalled_1479_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v___y_1455_ = v___x_1497_;
goto v___jp_1454_;
}
}
}
}
}
else
{
lean_dec(v_a_1470_);
v___y_1455_ = v_machine_1451_;
goto v___jp_1454_;
}
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1456_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1446_, v_line_1447_);
v___f_1457_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1457_, 0, v___y_1455_);
lean_closure_set(v___f_1457_, 1, v_body_1448_);
lean_closure_set(v___f_1457_, 2, v_isClosed_1449_);
lean_closure_set(v___f_1457_, 3, v_close_1450_);
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = 0;
v___x_1460_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1458_, v___x_1459_, v___x_1456_, v___f_1457_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_config_1503_, lean_object* v_line_1504_, lean_object* v_body_1505_, lean_object* v_isClosed_1506_, lean_object* v_close_1507_, lean_object* v_machine_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_config_1503_, v_line_1504_, v_body_1505_, v_isClosed_1506_, v_close_1507_, v_machine_1508_, v_x_1509_);
lean_dec_ref(v_config_1503_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1512_, lean_object* v_config_1513_, lean_object* v_machine_1514_, lean_object* v_res_1515_){
_start:
{
lean_object* v_close_1517_; lean_object* v_isClosed_1518_; lean_object* v_getKnownSize_1519_; lean_object* v_line_1520_; lean_object* v_body_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_close_1517_ = lean_ctor_get(v_inst_1512_, 1);
lean_inc_ref(v_close_1517_);
v_isClosed_1518_ = lean_ctor_get(v_inst_1512_, 2);
lean_inc_ref(v_isClosed_1518_);
v_getKnownSize_1519_ = lean_ctor_get(v_inst_1512_, 5);
lean_inc_ref(v_getKnownSize_1519_);
lean_dec_ref(v_inst_1512_);
v_line_1520_ = lean_ctor_get(v_res_1515_, 0);
lean_inc_ref(v_line_1520_);
v_body_1521_ = lean_ctor_get(v_res_1515_, 1);
lean_inc_n(v_body_1521_, 2);
lean_dec_ref(v_res_1515_);
v___x_1522_ = lean_apply_2(v_getKnownSize_1519_, v_body_1521_, lean_box(0));
v___f_1523_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1523_, 0, v_config_1513_);
lean_closure_set(v___f_1523_, 1, v_line_1520_);
lean_closure_set(v___f_1523_, 2, v_body_1521_);
lean_closure_set(v___f_1523_, 3, v_isClosed_1518_);
lean_closure_set(v___f_1523_, 4, v_close_1517_);
lean_closure_set(v___f_1523_, 5, v_machine_1514_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = 0;
v___x_1526_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1524_, v___x_1525_, v___x_1522_, v___f_1523_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1527_, lean_object* v_config_1528_, lean_object* v_machine_1529_, lean_object* v_res_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1527_, v_config_1528_, v_machine_1529_, v_res_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1533_, lean_object* v_inst_1534_, lean_object* v_config_1535_, lean_object* v_machine_1536_, lean_object* v_res_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1534_, v_config_1535_, v_machine_1536_, v_res_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1540_, lean_object* v_inst_1541_, lean_object* v_config_1542_, lean_object* v_machine_1543_, lean_object* v_res_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1540_, v_inst_1541_, v_config_1542_, v_machine_1543_, v_res_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v_closed_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_closed_1550_ = lean_ctor_get_uint8(v_____do__lift_1547_, sizeof(void*)*6);
v___x_1551_ = lean_box(v_closed_1550_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v_____do__lift_1554_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v_pendingProducer_1566_; lean_object* v_pendingConsumer_1567_; lean_object* v_interestWaiter_1568_; uint8_t v_closed_1569_; lean_object* v_pendingIncompleteChunk_1570_; lean_object* v_closeError_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1580_; 
v___x_1565_ = lean_st_ref_take(v___y_1563_);
v_pendingProducer_1566_ = lean_ctor_get(v___x_1565_, 0);
v_pendingConsumer_1567_ = lean_ctor_get(v___x_1565_, 1);
v_interestWaiter_1568_ = lean_ctor_get(v___x_1565_, 2);
v_closed_1569_ = lean_ctor_get_uint8(v___x_1565_, sizeof(void*)*6);
v_pendingIncompleteChunk_1570_ = lean_ctor_get(v___x_1565_, 4);
v_closeError_1571_ = lean_ctor_get(v___x_1565_, 5);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1565_, 3);
lean_dec(v_unused_1581_);
v___x_1573_ = v___x_1565_;
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_closeError_1571_);
lean_inc(v_pendingIncompleteChunk_1570_);
lean_inc(v_interestWaiter_1568_);
lean_inc(v_pendingConsumer_1567_);
lean_inc(v_pendingProducer_1566_);
lean_dec(v___x_1565_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 3, v___x_1562_);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_pendingProducer_1566_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_pendingConsumer_1567_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_interestWaiter_1568_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_pendingIncompleteChunk_1570_);
lean_ctor_set(v_reuseFailAlloc_1579_, 5, v_closeError_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1579_, sizeof(void*)*6, v_closed_1569_);
v___x_1576_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_st_ref_put(v___y_1563_, v___x_1576_);
v___x_1578_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1582_, v___y_1583_);
lean_dec(v___y_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v___x_1586_);
v_a_1589_ = lean_ctor_get(v_x_1587_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1591_ = v_x_1587_;
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v_x_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
}
}
else
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_x_1587_, 0);
lean_dec(v_unused_1607_);
v___x_1599_ = v_x_1587_;
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v_x_1587_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1586_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1608_, v_x_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1612_, lean_object* v_requestStream_1613_, lean_object* v_keepAliveTimeout_1614_, lean_object* v_currentTimeout_1615_, lean_object* v_headerTimeout_1616_, lean_object* v_response_1617_, lean_object* v_respStream_1618_, lean_object* v_expectData_1619_, uint8_t v_handlerDispatched_1620_, lean_object* v_____r_1621_){
_start:
{
uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1623_ = 0;
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1625_, 0, v_machine_1612_);
lean_ctor_set(v___x_1625_, 1, v_requestStream_1613_);
lean_ctor_set(v___x_1625_, 2, v_keepAliveTimeout_1614_);
lean_ctor_set(v___x_1625_, 3, v_currentTimeout_1615_);
lean_ctor_set(v___x_1625_, 4, v_headerTimeout_1616_);
lean_ctor_set(v___x_1625_, 5, v_response_1617_);
lean_ctor_set(v___x_1625_, 6, v_respStream_1618_);
lean_ctor_set(v___x_1625_, 7, v_expectData_1619_);
lean_ctor_set(v___x_1625_, 8, v___x_1624_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*9, v___x_1623_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*9 + 1, v_handlerDispatched_1620_);
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1629_, lean_object* v_requestStream_1630_, lean_object* v_keepAliveTimeout_1631_, lean_object* v_currentTimeout_1632_, lean_object* v_headerTimeout_1633_, lean_object* v_response_1634_, lean_object* v_respStream_1635_, lean_object* v_expectData_1636_, lean_object* v_handlerDispatched_1637_, lean_object* v_____r_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v_handlerDispatched_boxed_1640_; lean_object* v_res_1641_; 
v_handlerDispatched_boxed_1640_ = lean_unbox(v_handlerDispatched_1637_);
v_res_1641_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1629_, v_requestStream_1630_, v_keepAliveTimeout_1631_, v_currentTimeout_1632_, v_headerTimeout_1633_, v_response_1634_, v_respStream_1635_, v_expectData_1636_, v_handlerDispatched_boxed_1640_, v_____r_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v___f_1642_);
v_a_1645_ = lean_ctor_get(v_x_1643_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1643_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1647_ = v_x_1643_;
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v_x_1643_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v_x_1643_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v_x_1643_, 1);
v___x_1655_ = lean_apply_2(v___f_1642_, v_a_1654_, lean_box(0));
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1656_, lean_object* v_x_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1656_, v_x_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1660_, lean_object* v___f_1661_, lean_object* v___f_1662_, lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v___f_1662_);
lean_dec_ref(v___f_1661_);
lean_dec_ref(v_requestStream_1660_);
v_a_1665_ = lean_ctor_get(v_x_1663_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1667_ = v_x_1663_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v_x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1674_; uint8_t v___x_1675_; 
v_a_1674_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v_x_1663_, 1);
v___x_1675_ = lean_unbox(v_a_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
lean_dec_ref(v___f_1662_);
v___x_1676_ = l_Std_Http_Body_Stream_close(v_requestStream_1660_);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_unbox(v_a_1674_);
lean_dec(v_a_1674_);
v___x_1679_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1677_, v___x_1678_, v___x_1676_, v___f_1661_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec(v_a_1674_);
lean_dec_ref(v___f_1661_);
lean_dec_ref(v_requestStream_1660_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_apply_2(v___f_1662_, v___x_1680_, lean_box(0));
return v___x_1681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1682_, lean_object* v___f_1683_, lean_object* v___f_1684_, lean_object* v_x_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1682_, v___f_1683_, v___f_1684_, v_x_1685_);
return v_res_1687_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1688_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1689_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; 
v___x_1695_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1696_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1697_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1697_, 0, v___f_1696_);
lean_closure_set(v___f_1697_, 1, v___x_1695_);
return v___f_1697_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; 
v___x_1706_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1707_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1708_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1708_, 0, v___f_1707_);
lean_closure_set(v___f_1708_, 1, v___x_1706_);
return v___f_1708_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1709_; lean_object* v___x_1710_; 
v___f_1709_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1710_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1710_, 0, lean_box(0));
lean_closure_set(v___x_1710_, 1, lean_box(0));
lean_closure_set(v___x_1710_, 2, lean_box(0));
lean_closure_set(v___x_1710_, 3, v___f_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1711_, lean_object* v___f_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v___f_1712_);
lean_dec_ref(v___y_1711_);
v_a_1715_ = lean_ctor_get(v_x_1713_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_x_1713_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v_x_1713_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v_x_1713_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
}
else
{
lean_object* v_machine_1724_; lean_object* v_requestStream_1725_; lean_object* v_keepAliveTimeout_1726_; lean_object* v_currentTimeout_1727_; lean_object* v_headerTimeout_1728_; lean_object* v_response_1729_; lean_object* v_respStream_1730_; lean_object* v_expectData_1731_; uint8_t v_handlerDispatched_1732_; lean_object* v___x_1733_; lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_4846__overap_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; 
lean_dec_ref_known(v_x_1713_, 1);
v_machine_1724_ = lean_ctor_get(v___y_1711_, 0);
lean_inc_ref(v_machine_1724_);
v_requestStream_1725_ = lean_ctor_get(v___y_1711_, 1);
lean_inc_ref_n(v_requestStream_1725_, 3);
v_keepAliveTimeout_1726_ = lean_ctor_get(v___y_1711_, 2);
lean_inc(v_keepAliveTimeout_1726_);
v_currentTimeout_1727_ = lean_ctor_get(v___y_1711_, 3);
lean_inc(v_currentTimeout_1727_);
v_headerTimeout_1728_ = lean_ctor_get(v___y_1711_, 4);
lean_inc(v_headerTimeout_1728_);
v_response_1729_ = lean_ctor_get(v___y_1711_, 5);
lean_inc_ref(v_response_1729_);
v_respStream_1730_ = lean_ctor_get(v___y_1711_, 6);
lean_inc(v_respStream_1730_);
v_expectData_1731_ = lean_ctor_get(v___y_1711_, 7);
lean_inc(v_expectData_1731_);
v_handlerDispatched_1732_ = lean_ctor_get_uint8(v___y_1711_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1711_);
v___x_1733_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1734_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1735_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1736_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1737_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1737_, 0, lean_box(0));
lean_closure_set(v___x_1737_, 1, lean_box(0));
lean_closure_set(v___x_1737_, 2, v___x_1733_);
lean_closure_set(v___x_1737_, 3, lean_box(0));
lean_closure_set(v___x_1737_, 4, lean_box(0));
lean_closure_set(v___x_1737_, 5, v___x_1736_);
lean_closure_set(v___x_1737_, 6, v___f_1712_);
v___x_4846__overap_1738_ = l_Std_Mutex_atomically___redArg(v___x_1733_, v___f_1734_, v___f_1735_, v_requestStream_1725_, v___x_1737_);
v___x_1739_ = lean_apply_1(v___x_4846__overap_1738_, lean_box(0));
v___x_1740_ = lean_box(v_handlerDispatched_1732_);
v___f_1741_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1741_, 0, v_machine_1724_);
lean_closure_set(v___f_1741_, 1, v_requestStream_1725_);
lean_closure_set(v___f_1741_, 2, v_keepAliveTimeout_1726_);
lean_closure_set(v___f_1741_, 3, v_currentTimeout_1727_);
lean_closure_set(v___f_1741_, 4, v_headerTimeout_1728_);
lean_closure_set(v___f_1741_, 5, v_response_1729_);
lean_closure_set(v___f_1741_, 6, v_respStream_1730_);
lean_closure_set(v___f_1741_, 7, v_expectData_1731_);
lean_closure_set(v___f_1741_, 8, v___x_1740_);
lean_inc_ref(v___f_1741_);
v___f_1742_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1742_, 0, v___f_1741_);
v___f_1743_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1743_, 0, v_requestStream_1725_);
lean_closure_set(v___f_1743_, 1, v___f_1742_);
lean_closure_set(v___f_1743_, 2, v___f_1741_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = 0;
v___x_1746_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1744_, v___x_1745_, v___x_1739_, v___f_1743_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1747_, lean_object* v___f_1748_, lean_object* v_x_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1747_, v___f_1748_, v_x_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1752_, lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v___y_1752_);
v_a_1755_ = lean_ctor_get(v_x_1753_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1757_ = v_x_1753_;
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v_x_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
}
else
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1772_; 
v_isSharedCheck_1772_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v_x_1753_, 0);
lean_dec(v_unused_1773_);
v___x_1765_ = v_x_1753_;
v_isShared_1766_ = v_isSharedCheck_1772_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v_x_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1772_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___y_1752_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1767_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1774_, v_x_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1778_, lean_object* v___f_1779_, lean_object* v___y_1780_, lean_object* v_x_1781_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___f_1779_);
lean_dec_ref(v_requestStream_1778_);
v_a_1783_ = lean_ctor_get(v_x_1781_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1785_ = v_x_1781_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v_x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1806_; 
v_a_1792_ = lean_ctor_get(v_x_1781_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1794_ = v_x_1781_;
v_isShared_1795_ = v_isSharedCheck_1806_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v_x_1781_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1806_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_unbox(v_a_1792_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; 
lean_del_object(v___x_1794_);
lean_dec_ref(v___y_1780_);
v___x_1797_ = l_Std_Http_Body_Stream_close(v_requestStream_1778_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_unbox(v_a_1792_);
lean_dec(v_a_1792_);
v___x_1800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1798_, v___x_1799_, v___x_1797_, v___f_1779_);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec(v_a_1792_);
lean_dec_ref(v___f_1779_);
lean_dec_ref(v_requestStream_1778_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___y_1780_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1801_);
v___x_1803_ = v___x_1794_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1807_, lean_object* v___f_1808_, lean_object* v___y_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1807_, v___f_1808_, v___y_1809_, v_x_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1813_, lean_object* v_machine_1814_, lean_object* v_a_1815_, uint8_t v_requiresData_1816_, lean_object* v_expectData_1817_, lean_object* v_pendingHead_1818_, lean_object* v_x_1819_){
_start:
{
if (lean_obj_tag(v_x_1819_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_pendingHead_1818_);
lean_dec(v_expectData_1817_);
lean_dec_ref(v_a_1815_);
lean_dec_ref(v_machine_1814_);
v_a_1821_ = lean_ctor_get(v_x_1819_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_x_1819_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1823_ = v_x_1819_;
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v_x_1819_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1844_; 
v_a_1830_ = lean_ctor_get(v_x_1819_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_x_1819_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1832_ = v_x_1819_;
v_isShared_1833_ = v_isSharedCheck_1844_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v_x_1819_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1844_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_keepAliveTimeout_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v_keepAliveTimeout_1834_ = lean_ctor_get(v_config_1813_, 5);
lean_inc_n(v_keepAliveTimeout_1834_, 2);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_keepAliveTimeout_1834_);
v___x_1836_ = lean_box(0);
v___x_1837_ = 0;
v___x_1838_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1838_, 0, v_machine_1814_);
lean_ctor_set(v___x_1838_, 1, v_a_1815_);
lean_ctor_set(v___x_1838_, 2, v___x_1835_);
lean_ctor_set(v___x_1838_, 3, v_keepAliveTimeout_1834_);
lean_ctor_set(v___x_1838_, 4, v___x_1836_);
lean_ctor_set(v___x_1838_, 5, v_a_1830_);
lean_ctor_set(v___x_1838_, 6, v___x_1836_);
lean_ctor_set(v___x_1838_, 7, v_expectData_1817_);
lean_ctor_set(v___x_1838_, 8, v_pendingHead_1818_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*9, v_requiresData_1816_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*9 + 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1845_, lean_object* v_machine_1846_, lean_object* v_a_1847_, lean_object* v_requiresData_1848_, lean_object* v_expectData_1849_, lean_object* v_pendingHead_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_){
_start:
{
uint8_t v_requiresData_boxed_1853_; lean_object* v_res_1854_; 
v_requiresData_boxed_1853_ = lean_unbox(v_requiresData_1848_);
v_res_1854_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1845_, v_machine_1846_, v_a_1847_, v_requiresData_boxed_1853_, v_expectData_1849_, v_pendingHead_1850_, v_x_1851_);
lean_dec_ref(v_config_1845_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1855_, lean_object* v_machine_1856_, uint8_t v_requiresData_1857_, lean_object* v_expectData_1858_, lean_object* v_pendingHead_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_pendingHead_1859_);
lean_dec(v_expectData_1858_);
lean_dec_ref(v_machine_1856_);
lean_dec_ref(v_config_1855_);
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
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1886_; 
v_a_1871_ = lean_ctor_get(v_x_1860_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1873_ = v_x_1860_;
v_isShared_1874_ = v_isSharedCheck_1886_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v_x_1860_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1886_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___f_1878_; lean_object* v___x_1880_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Std_CloseableChannel_new___redArg(v___x_1875_);
v___x_1877_ = lean_box(v_requiresData_1857_);
v___f_1878_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1878_, 0, v_config_1855_);
lean_closure_set(v___f_1878_, 1, v_machine_1856_);
lean_closure_set(v___f_1878_, 2, v_a_1871_);
lean_closure_set(v___f_1878_, 3, v___x_1877_);
lean_closure_set(v___f_1878_, 4, v_expectData_1858_);
lean_closure_set(v___f_1878_, 5, v_pendingHead_1859_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1880_ = v___x_1873_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1876_);
v___x_1880_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = 0;
v___x_1884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1882_, v___x_1883_, v___x_1881_, v___f_1878_);
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1887_, lean_object* v_machine_1888_, lean_object* v_requiresData_1889_, lean_object* v_expectData_1890_, lean_object* v_pendingHead_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_requiresData_boxed_1894_; lean_object* v_res_1895_; 
v_requiresData_boxed_1894_ = lean_unbox(v_requiresData_1889_);
v_res_1895_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1887_, v_machine_1888_, v_requiresData_boxed_1894_, v_expectData_1890_, v_pendingHead_1891_, v_x_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1896_, lean_object* v_____r_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = l_Std_Http_Body_mkStream();
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = 0;
v___x_1902_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1900_, v___x_1901_, v___x_1899_, v___f_1896_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1903_, lean_object* v_____r_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1903_, v_____r_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1907_, lean_object* v_val_1908_, lean_object* v___f_1909_, lean_object* v___f_1910_, lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___f_1910_);
lean_dec_ref(v___f_1909_);
lean_dec(v_val_1908_);
lean_dec_ref(v_close_1907_);
v_a_1913_ = lean_ctor_get(v_x_1911_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1911_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1915_ = v_x_1911_;
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v_x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
}
else
{
lean_object* v_a_1922_; uint8_t v___x_1923_; 
v_a_1922_ = lean_ctor_get(v_x_1911_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v_x_1911_, 1);
v___x_1923_ = lean_unbox(v_a_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref(v___f_1910_);
v___x_1924_ = lean_apply_2(v_close_1907_, v_val_1908_, lean_box(0));
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_unbox(v_a_1922_);
lean_dec(v_a_1922_);
v___x_1927_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1925_, v___x_1926_, v___x_1924_, v___f_1909_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_a_1922_);
lean_dec_ref(v___f_1909_);
lean_dec(v_val_1908_);
lean_dec_ref(v_close_1907_);
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_apply_2(v___f_1910_, v___x_1928_, lean_box(0));
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1930_, lean_object* v_val_1931_, lean_object* v___f_1932_, lean_object* v___f_1933_, lean_object* v_x_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1930_, v_val_1931_, v___f_1932_, v___f_1933_, v_x_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1937_, lean_object* v_inst_1938_, lean_object* v___f_1939_, lean_object* v___f_1940_, lean_object* v_____r_1941_){
_start:
{
if (lean_obj_tag(v_respStream_1937_) == 1)
{
lean_object* v_val_1943_; lean_object* v_close_1944_; lean_object* v_isClosed_1945_; lean_object* v___x_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v_val_1943_ = lean_ctor_get(v_respStream_1937_, 0);
lean_inc_n(v_val_1943_, 2);
lean_dec_ref_known(v_respStream_1937_, 1);
v_close_1944_ = lean_ctor_get(v_inst_1938_, 1);
lean_inc_ref(v_close_1944_);
v_isClosed_1945_ = lean_ctor_get(v_inst_1938_, 2);
lean_inc_ref(v_isClosed_1945_);
lean_dec_ref(v_inst_1938_);
v___x_1946_ = lean_apply_2(v_isClosed_1945_, v_val_1943_, lean_box(0));
v___f_1947_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1947_, 0, v_close_1944_);
lean_closure_set(v___f_1947_, 1, v_val_1943_);
lean_closure_set(v___f_1947_, 2, v___f_1939_);
lean_closure_set(v___f_1947_, 3, v___f_1940_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = 0;
v___x_1950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1948_, v___x_1949_, v___x_1946_, v___f_1947_);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec_ref(v___f_1939_);
lean_dec_ref(v_inst_1938_);
lean_dec(v_respStream_1937_);
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_apply_2(v___f_1940_, v___x_1951_, lean_box(0));
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1953_, lean_object* v_inst_1954_, lean_object* v___f_1955_, lean_object* v___f_1956_, lean_object* v_____r_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1953_, v_inst_1954_, v___f_1955_, v___f_1956_, v_____r_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1960_, lean_object* v_keepAliveTimeout_1961_, lean_object* v_currentTimeout_1962_, lean_object* v_headerTimeout_1963_, lean_object* v_response_1964_, lean_object* v_respStream_1965_, uint8_t v_requiresData_1966_, lean_object* v_expectData_1967_, uint8_t v_handlerDispatched_1968_, lean_object* v_pendingHead_1969_, lean_object* v_x_1970_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_pendingHead_1969_);
lean_dec(v_expectData_1967_);
lean_dec(v_respStream_1965_);
lean_dec_ref(v_response_1964_);
lean_dec(v_headerTimeout_1963_);
lean_dec(v_currentTimeout_1962_);
lean_dec(v_keepAliveTimeout_1961_);
lean_dec_ref(v_requestStream_1960_);
v_a_1972_ = lean_ctor_get(v_x_1970_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_x_1970_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v_x_1970_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v_x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2002_; 
v_a_1981_ = lean_ctor_get(v_x_1970_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1970_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1983_ = v_x_1970_;
v_isShared_1984_ = v_isSharedCheck_2002_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v_x_1970_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2002_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_snd_1985_; uint8_t v___x_1986_; 
v_snd_1985_ = lean_ctor_get(v_a_1981_, 1);
v___x_1986_ = lean_unbox(v_snd_1985_);
if (v___x_1986_ == 0)
{
lean_object* v_fst_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v_fst_1987_ = lean_ctor_get(v_a_1981_, 0);
lean_inc(v_fst_1987_);
lean_dec(v_a_1981_);
v___x_1988_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1988_, 0, v_fst_1987_);
lean_ctor_set(v___x_1988_, 1, v_requestStream_1960_);
lean_ctor_set(v___x_1988_, 2, v_keepAliveTimeout_1961_);
lean_ctor_set(v___x_1988_, 3, v_currentTimeout_1962_);
lean_ctor_set(v___x_1988_, 4, v_headerTimeout_1963_);
lean_ctor_set(v___x_1988_, 5, v_response_1964_);
lean_ctor_set(v___x_1988_, 6, v_respStream_1965_);
lean_ctor_set(v___x_1988_, 7, v_expectData_1967_);
lean_ctor_set(v___x_1988_, 8, v_pendingHead_1969_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*9, v_requiresData_1966_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*9 + 1, v_handlerDispatched_1968_);
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1989_);
v___x_1991_ = v___x_1983_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
else
{
lean_object* v_fst_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_dec(v_pendingHead_1969_);
v_fst_1994_ = lean_ctor_get(v_a_1981_, 0);
lean_inc(v_fst_1994_);
lean_dec(v_a_1981_);
v___x_1995_ = lean_box(0);
v___x_1996_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1996_, 0, v_fst_1994_);
lean_ctor_set(v___x_1996_, 1, v_requestStream_1960_);
lean_ctor_set(v___x_1996_, 2, v_keepAliveTimeout_1961_);
lean_ctor_set(v___x_1996_, 3, v_currentTimeout_1962_);
lean_ctor_set(v___x_1996_, 4, v_headerTimeout_1963_);
lean_ctor_set(v___x_1996_, 5, v_response_1964_);
lean_ctor_set(v___x_1996_, 6, v_respStream_1965_);
lean_ctor_set(v___x_1996_, 7, v_expectData_1967_);
lean_ctor_set(v___x_1996_, 8, v___x_1995_);
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*9, v_requiresData_1966_);
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*9 + 1, v_handlerDispatched_1968_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1997_);
v___x_1999_ = v___x_1983_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2003_, lean_object* v_keepAliveTimeout_2004_, lean_object* v_currentTimeout_2005_, lean_object* v_headerTimeout_2006_, lean_object* v_response_2007_, lean_object* v_respStream_2008_, lean_object* v_requiresData_2009_, lean_object* v_expectData_2010_, lean_object* v_handlerDispatched_2011_, lean_object* v_pendingHead_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_requiresData_boxed_2015_; uint8_t v_handlerDispatched_boxed_2016_; lean_object* v_res_2017_; 
v_requiresData_boxed_2015_ = lean_unbox(v_requiresData_2009_);
v_handlerDispatched_boxed_2016_ = lean_unbox(v_handlerDispatched_2011_);
v_res_2017_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2003_, v_keepAliveTimeout_2004_, v_currentTimeout_2005_, v_headerTimeout_2006_, v_response_2007_, v_respStream_2008_, v_requiresData_boxed_2015_, v_expectData_2010_, v_handlerDispatched_boxed_2016_, v_pendingHead_2012_, v_x_2013_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2030_, lean_object* v_inst_2031_, lean_object* v___f_2032_, lean_object* v_handler_2033_, lean_object* v___f_2034_, lean_object* v___f_2035_, lean_object* v_inst_2036_, lean_object* v_connectionContext_2037_, lean_object* v_a_2038_, lean_object* v_x_2039_, lean_object* v___y_2040_){
_start:
{
switch(lean_obj_tag(v_a_2038_))
{
case 0:
{
lean_object* v_head_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_connectionContext_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2034_);
lean_dec(v_handler_2033_);
lean_dec_ref(v___f_2032_);
lean_dec_ref(v_inst_2031_);
v_head_2042_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2044_ = v_a_2038_;
v_isShared_2045_ = v_isSharedCheck_2085_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_head_2042_);
lean_dec(v_a_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2085_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_machine_2046_; lean_object* v_requestStream_2047_; lean_object* v_response_2048_; lean_object* v_respStream_2049_; uint8_t v_requiresData_2050_; lean_object* v_expectData_2051_; uint8_t v_handlerDispatched_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2080_; 
v_machine_2046_ = lean_ctor_get(v___y_2040_, 0);
v_requestStream_2047_ = lean_ctor_get(v___y_2040_, 1);
v_response_2048_ = lean_ctor_get(v___y_2040_, 5);
v_respStream_2049_ = lean_ctor_get(v___y_2040_, 6);
v_requiresData_2050_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*9);
v_expectData_2051_ = lean_ctor_get(v___y_2040_, 7);
v_handlerDispatched_2052_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*9 + 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___y_2040_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2081_ = lean_ctor_get(v___y_2040_, 8);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v___y_2040_, 4);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v___y_2040_, 3);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v___y_2040_, 2);
lean_dec(v_unused_2084_);
v___x_2054_ = v___y_2040_;
v_isShared_2055_ = v_isSharedCheck_2080_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_expectData_2051_);
lean_inc(v_respStream_2049_);
lean_inc(v_response_2048_);
lean_inc(v_requestStream_2047_);
lean_inc(v_machine_2046_);
lean_dec(v___y_2040_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2080_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_lingeringTimeout_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v_lingeringTimeout_2056_ = lean_ctor_get(v_config_2030_, 4);
lean_inc(v_lingeringTimeout_2056_);
lean_dec_ref(v_config_2030_);
v___x_2057_ = lean_box(0);
lean_inc(v_head_2042_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
v___x_2059_ = v___x_2044_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_head_2042_);
v___x_2059_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
lean_inc_ref(v_requestStream_2047_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 8, v___x_2059_);
lean_ctor_set(v___x_2054_, 4, v___x_2057_);
lean_ctor_set(v___x_2054_, 3, v_lingeringTimeout_2056_);
lean_ctor_set(v___x_2054_, 2, v___x_2057_);
v___x_2061_ = v___x_2054_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_machine_2046_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_requestStream_2047_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_lingeringTimeout_2056_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2078_, 5, v_response_2048_);
lean_ctor_set(v_reuseFailAlloc_2078_, 6, v_respStream_2049_);
lean_ctor_set(v_reuseFailAlloc_2078_, 7, v_expectData_2051_);
lean_ctor_set(v_reuseFailAlloc_2078_, 8, v___x_2059_);
lean_ctor_set_uint8(v_reuseFailAlloc_2078_, sizeof(void*)*9, v_requiresData_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2078_, sizeof(void*)*9 + 1, v_handlerDispatched_2052_);
v___x_2061_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
uint8_t v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = 0;
v___x_2063_ = 1;
v___x_2064_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2062_, v_head_2042_, v___x_2063_);
lean_dec(v_head_2042_);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___f_2068_; lean_object* v___x_5039__overap_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___f_2065_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2065_, 0, v___x_2064_);
v___x_2066_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2067_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2068_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5039__overap_2069_ = l_Std_Mutex_atomically___redArg(v___x_2066_, v___f_2067_, v___f_2068_, v_requestStream_2047_, v___f_2065_);
v___x_2070_ = lean_apply_1(v___x_5039__overap_2069_, lean_box(0));
v___f_2071_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2071_, 0, v___x_2061_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = 0;
v___x_2074_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2072_, v___x_2073_, v___x_2070_, v___f_2071_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v___x_2064_);
lean_dec_ref(v_requestStream_2047_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2061_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v_connectionContext_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2034_);
lean_dec(v_handler_2033_);
lean_dec_ref(v___f_2032_);
lean_dec_ref(v_inst_2031_);
lean_dec_ref(v_config_2030_);
v_size_2086_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2088_ = v_a_2038_;
v_isShared_2089_ = v_isSharedCheck_2113_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_size_2086_);
lean_dec(v_a_2038_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2113_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_machine_2090_; lean_object* v_requestStream_2091_; lean_object* v_keepAliveTimeout_2092_; lean_object* v_currentTimeout_2093_; lean_object* v_headerTimeout_2094_; lean_object* v_response_2095_; lean_object* v_respStream_2096_; uint8_t v_handlerDispatched_2097_; lean_object* v_pendingHead_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2111_; 
v_machine_2090_ = lean_ctor_get(v___y_2040_, 0);
v_requestStream_2091_ = lean_ctor_get(v___y_2040_, 1);
v_keepAliveTimeout_2092_ = lean_ctor_get(v___y_2040_, 2);
v_currentTimeout_2093_ = lean_ctor_get(v___y_2040_, 3);
v_headerTimeout_2094_ = lean_ctor_get(v___y_2040_, 4);
v_response_2095_ = lean_ctor_get(v___y_2040_, 5);
v_respStream_2096_ = lean_ctor_get(v___y_2040_, 6);
v_handlerDispatched_2097_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*9 + 1);
v_pendingHead_2098_ = lean_ctor_get(v___y_2040_, 8);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___y_2040_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___y_2040_, 7);
lean_dec(v_unused_2112_);
v___x_2100_ = v___y_2040_;
v_isShared_2101_ = v_isSharedCheck_2111_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_pendingHead_2098_);
lean_inc(v_respStream_2096_);
lean_inc(v_response_2095_);
lean_inc(v_headerTimeout_2094_);
lean_inc(v_currentTimeout_2093_);
lean_inc(v_keepAliveTimeout_2092_);
lean_inc(v_requestStream_2091_);
lean_inc(v_machine_2090_);
lean_dec(v___y_2040_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2111_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
uint8_t v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = 1;
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 7, v_size_2086_);
v___x_2104_ = v___x_2100_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_machine_2090_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_requestStream_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_keepAliveTimeout_2092_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_currentTimeout_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_headerTimeout_2094_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_response_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_respStream_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v_size_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v_pendingHead_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*9 + 1, v_handlerDispatched_2097_);
v___x_2104_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*9, v___x_2102_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2104_);
v___x_2106_ = v___x_2088_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2114_; lean_object* v_onFailure_2115_; lean_object* v___f_2116_; lean_object* v___y_2118_; 
lean_dec_ref(v_connectionContext_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2034_);
lean_dec_ref(v_config_2030_);
v_err_2114_ = lean_ctor_get(v_a_2038_, 0);
lean_inc(v_err_2114_);
lean_dec_ref_known(v_a_2038_, 1);
v_onFailure_2115_ = lean_ctor_get(v_inst_2031_, 2);
lean_inc_ref(v_onFailure_2115_);
lean_dec_ref(v_inst_2031_);
v___f_2116_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2116_, 0, v___y_2040_);
lean_closure_set(v___f_2116_, 1, v___f_2032_);
switch(lean_obj_tag(v_err_2114_))
{
case 0:
{
lean_object* v___x_2124_; 
v___x_2124_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2118_ = v___x_2124_;
goto v___jp_2117_;
}
case 1:
{
lean_object* v___x_2125_; 
v___x_2125_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2118_ = v___x_2125_;
goto v___jp_2117_;
}
case 2:
{
lean_object* v___x_2126_; 
v___x_2126_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2118_ = v___x_2126_;
goto v___jp_2117_;
}
case 3:
{
lean_object* v___x_2127_; 
v___x_2127_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2118_ = v___x_2127_;
goto v___jp_2117_;
}
case 4:
{
lean_object* v___x_2128_; 
v___x_2128_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2118_ = v___x_2128_;
goto v___jp_2117_;
}
case 5:
{
lean_object* v___x_2129_; 
v___x_2129_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2118_ = v___x_2129_;
goto v___jp_2117_;
}
case 6:
{
lean_object* v___x_2130_; 
v___x_2130_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2118_ = v___x_2130_;
goto v___jp_2117_;
}
case 7:
{
lean_object* v___x_2131_; 
v___x_2131_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2118_ = v___x_2131_;
goto v___jp_2117_;
}
case 8:
{
lean_object* v___x_2132_; 
v___x_2132_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2118_ = v___x_2132_;
goto v___jp_2117_;
}
case 9:
{
lean_object* v___x_2133_; 
v___x_2133_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2118_ = v___x_2133_;
goto v___jp_2117_;
}
case 10:
{
lean_object* v___x_2134_; 
v___x_2134_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2118_ = v___x_2134_;
goto v___jp_2117_;
}
default: 
{
lean_object* v_message_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_message_2135_ = lean_ctor_get(v_err_2114_, 0);
lean_inc_ref(v_message_2135_);
lean_dec_ref_known(v_err_2114_, 1);
v___x_2136_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2137_ = lean_string_append(v___x_2136_, v_message_2135_);
lean_dec_ref(v_message_2135_);
v___y_2118_ = v___x_2137_;
goto v___jp_2117_;
}
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2119_ = lean_mk_io_user_error(v___y_2118_);
v___x_2120_ = lean_apply_3(v_onFailure_2115_, v_handler_2033_, v___x_2119_, lean_box(0));
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = 0;
v___x_2123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2121_, v___x_2122_, v___x_2120_, v___f_2116_);
return v___x_2123_;
}
}
case 4:
{
lean_object* v_requestStream_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_5095__overap_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v_connectionContext_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec(v_handler_2033_);
lean_dec_ref(v___f_2032_);
lean_dec_ref(v_inst_2031_);
lean_dec_ref(v_config_2030_);
v_requestStream_2138_ = lean_ctor_get(v___y_2040_, 1);
lean_inc_ref_n(v_requestStream_2138_, 2);
v___x_2139_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2140_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2141_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2142_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2143_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2143_, 0, lean_box(0));
lean_closure_set(v___x_2143_, 1, lean_box(0));
lean_closure_set(v___x_2143_, 2, v___x_2139_);
lean_closure_set(v___x_2143_, 3, lean_box(0));
lean_closure_set(v___x_2143_, 4, lean_box(0));
lean_closure_set(v___x_2143_, 5, v___x_2142_);
lean_closure_set(v___x_2143_, 6, v___f_2034_);
v___x_5095__overap_2144_ = l_Std_Mutex_atomically___redArg(v___x_2139_, v___f_2140_, v___f_2141_, v_requestStream_2138_, v___x_2143_);
v___x_2145_ = lean_apply_1(v___x_5095__overap_2144_, lean_box(0));
lean_inc_ref(v___y_2040_);
v___f_2146_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2146_, 0, v___y_2040_);
v___f_2147_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2147_, 0, v_requestStream_2138_);
lean_closure_set(v___f_2147_, 1, v___f_2146_);
lean_closure_set(v___f_2147_, 2, v___y_2040_);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = 0;
v___x_2150_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2148_, v___x_2149_, v___x_2145_, v___f_2147_);
return v___x_2150_;
}
case 6:
{
lean_object* v_machine_2151_; lean_object* v_requestStream_2152_; lean_object* v_respStream_2153_; uint8_t v_requiresData_2154_; lean_object* v_expectData_2155_; lean_object* v_pendingHead_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_5116__overap_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_connectionContext_2037_);
lean_dec_ref(v___f_2034_);
lean_dec(v_handler_2033_);
lean_dec_ref(v___f_2032_);
lean_dec_ref(v_inst_2031_);
v_machine_2151_ = lean_ctor_get(v___y_2040_, 0);
lean_inc_ref(v_machine_2151_);
v_requestStream_2152_ = lean_ctor_get(v___y_2040_, 1);
lean_inc_ref_n(v_requestStream_2152_, 2);
v_respStream_2153_ = lean_ctor_get(v___y_2040_, 6);
lean_inc(v_respStream_2153_);
v_requiresData_2154_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*9);
v_expectData_2155_ = lean_ctor_get(v___y_2040_, 7);
lean_inc(v_expectData_2155_);
v_pendingHead_2156_ = lean_ctor_get(v___y_2040_, 8);
lean_inc(v_pendingHead_2156_);
lean_dec_ref(v___y_2040_);
v___x_2157_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2158_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2159_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2160_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2161_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2161_, 0, lean_box(0));
lean_closure_set(v___x_2161_, 1, lean_box(0));
lean_closure_set(v___x_2161_, 2, v___x_2157_);
lean_closure_set(v___x_2161_, 3, lean_box(0));
lean_closure_set(v___x_2161_, 4, lean_box(0));
lean_closure_set(v___x_2161_, 5, v___x_2160_);
lean_closure_set(v___x_2161_, 6, v___f_2035_);
v___x_5116__overap_2162_ = l_Std_Mutex_atomically___redArg(v___x_2157_, v___f_2158_, v___f_2159_, v_requestStream_2152_, v___x_2161_);
v___x_2163_ = lean_apply_1(v___x_5116__overap_2162_, lean_box(0));
v___x_2164_ = lean_box(v_requiresData_2154_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2165_, 0, v_config_2030_);
lean_closure_set(v___f_2165_, 1, v_machine_2151_);
lean_closure_set(v___f_2165_, 2, v___x_2164_);
lean_closure_set(v___f_2165_, 3, v_expectData_2155_);
lean_closure_set(v___f_2165_, 4, v_pendingHead_2156_);
v___f_2166_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2166_, 0, v___f_2165_);
lean_inc_ref(v___f_2166_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2167_, 0, v___f_2166_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2168_, 0, v_respStream_2153_);
lean_closure_set(v___f_2168_, 1, v_inst_2036_);
lean_closure_set(v___f_2168_, 2, v___f_2167_);
lean_closure_set(v___f_2168_, 3, v___f_2166_);
lean_inc_ref(v___f_2168_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2169_, 0, v___f_2168_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2170_, 0, v_requestStream_2152_);
lean_closure_set(v___f_2170_, 1, v___f_2169_);
lean_closure_set(v___f_2170_, 2, v___f_2168_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = 0;
v___x_2173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2171_, v___x_2172_, v___x_2163_, v___f_2170_);
return v___x_2173_;
}
case 7:
{
lean_object* v_pendingHead_2174_; 
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2034_);
lean_dec_ref(v___f_2032_);
v_pendingHead_2174_ = lean_ctor_get(v___y_2040_, 8);
if (lean_obj_tag(v_pendingHead_2174_) == 1)
{
lean_object* v_machine_2175_; lean_object* v_requestStream_2176_; lean_object* v_keepAliveTimeout_2177_; lean_object* v_currentTimeout_2178_; lean_object* v_headerTimeout_2179_; lean_object* v_response_2180_; lean_object* v_respStream_2181_; uint8_t v_requiresData_2182_; lean_object* v_expectData_2183_; uint8_t v_handlerDispatched_2184_; lean_object* v_val_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; 
lean_inc_ref(v_pendingHead_2174_);
v_machine_2175_ = lean_ctor_get(v___y_2040_, 0);
lean_inc_ref(v_machine_2175_);
v_requestStream_2176_ = lean_ctor_get(v___y_2040_, 1);
lean_inc_ref(v_requestStream_2176_);
v_keepAliveTimeout_2177_ = lean_ctor_get(v___y_2040_, 2);
lean_inc(v_keepAliveTimeout_2177_);
v_currentTimeout_2178_ = lean_ctor_get(v___y_2040_, 3);
lean_inc(v_currentTimeout_2178_);
v_headerTimeout_2179_ = lean_ctor_get(v___y_2040_, 4);
lean_inc(v_headerTimeout_2179_);
v_response_2180_ = lean_ctor_get(v___y_2040_, 5);
lean_inc_ref(v_response_2180_);
v_respStream_2181_ = lean_ctor_get(v___y_2040_, 6);
lean_inc(v_respStream_2181_);
v_requiresData_2182_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*9);
v_expectData_2183_ = lean_ctor_get(v___y_2040_, 7);
lean_inc(v_expectData_2183_);
v_handlerDispatched_2184_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2040_);
v_val_2185_ = lean_ctor_get(v_pendingHead_2174_, 0);
lean_inc(v_val_2185_);
v___x_2186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2031_, v_handler_2033_, v_machine_2175_, v_val_2185_, v_config_2030_, v_connectionContext_2037_);
v___x_2187_ = lean_box(v_requiresData_2182_);
v___x_2188_ = lean_box(v_handlerDispatched_2184_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2189_, 0, v_requestStream_2176_);
lean_closure_set(v___f_2189_, 1, v_keepAliveTimeout_2177_);
lean_closure_set(v___f_2189_, 2, v_currentTimeout_2178_);
lean_closure_set(v___f_2189_, 3, v_headerTimeout_2179_);
lean_closure_set(v___f_2189_, 4, v_response_2180_);
lean_closure_set(v___f_2189_, 5, v_respStream_2181_);
lean_closure_set(v___f_2189_, 6, v___x_2187_);
lean_closure_set(v___f_2189_, 7, v_expectData_2183_);
lean_closure_set(v___f_2189_, 8, v___x_2188_);
lean_closure_set(v___f_2189_, 9, v_pendingHead_2174_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = 0;
v___x_2192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2190_, v___x_2191_, v___x_2186_, v___f_2189_);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec_ref(v_connectionContext_2037_);
lean_dec(v_handler_2033_);
lean_dec_ref(v_inst_2031_);
lean_dec_ref(v_config_2030_);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___y_2040_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
default: 
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_connectionContext_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2034_);
lean_dec(v_handler_2033_);
lean_dec_ref(v___f_2032_);
lean_dec_ref(v_inst_2031_);
lean_dec_ref(v_config_2030_);
v___x_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___y_2040_);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2199_, lean_object* v_inst_2200_, lean_object* v___f_2201_, lean_object* v_handler_2202_, lean_object* v___f_2203_, lean_object* v___f_2204_, lean_object* v_inst_2205_, lean_object* v_connectionContext_2206_, lean_object* v_a_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2199_, v_inst_2200_, v___f_2201_, v_handler_2202_, v___f_2203_, v___f_2204_, v_inst_2205_, v_connectionContext_2206_, v_a_2207_, v_x_2208_, v___y_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_x_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_handler_2222_, lean_object* v_config_2223_, lean_object* v_connectionContext_2224_, lean_object* v_events_2225_, lean_object* v_state_2226_){
_start:
{
lean_object* v___f_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; size_t v_sz_2231_; size_t v___x_2232_; lean_object* v___x_4070__overap_2233_; lean_object* v___x_2234_; lean_object* v___f_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; 
v___f_2228_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2229_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2229_, 0, v_config_2223_);
lean_closure_set(v___f_2229_, 1, v_inst_2220_);
lean_closure_set(v___f_2229_, 2, v___f_2228_);
lean_closure_set(v___f_2229_, 3, v_handler_2222_);
lean_closure_set(v___f_2229_, 4, v___f_2228_);
lean_closure_set(v___f_2229_, 5, v___f_2228_);
lean_closure_set(v___f_2229_, 6, v_inst_2221_);
lean_closure_set(v___f_2229_, 7, v_connectionContext_2224_);
v___x_2230_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2231_ = lean_array_size(v_events_2225_);
v___x_2232_ = ((size_t)0ULL);
v___x_4070__overap_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2230_, v_events_2225_, v___f_2229_, v_sz_2231_, v___x_2232_, v_state_2226_);
v___x_2234_ = lean_apply_1(v___x_4070__overap_2233_, lean_box(0));
v___f_2235_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = 0;
v___x_2238_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2236_, v___x_2237_, v___x_2234_, v___f_2235_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_handler_2241_, lean_object* v_config_2242_, lean_object* v_connectionContext_2243_, lean_object* v_events_2244_, lean_object* v_state_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2239_, v_inst_2240_, v_handler_2241_, v_config_2242_, v_connectionContext_2243_, v_events_2244_, v_state_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_handler_2252_, lean_object* v_config_2253_, lean_object* v_connectionContext_2254_, lean_object* v_events_2255_, lean_object* v_state_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2250_, v_inst_2251_, v_handler_2252_, v_config_2253_, v_connectionContext_2254_, v_events_2255_, v_state_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2259_, lean_object* v_00_u03b2_2260_, lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_handler_2263_, lean_object* v_config_2264_, lean_object* v_connectionContext_2265_, lean_object* v_events_2266_, lean_object* v_state_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2259_, v_00_u03b2_2260_, v_inst_2261_, v_inst_2262_, v_handler_2263_, v_config_2264_, v_connectionContext_2265_, v_events_2266_, v_state_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; 
v_a_2271_ = lean_ctor_get(v_x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_x_2270_, 1);
v___x_2272_ = lean_task_pure(v_a_2271_);
return v___x_2272_;
}
else
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v_x_2270_, 0);
lean_inc_ref(v_a_2273_);
lean_dec_ref_known(v_x_2270_, 1);
return v_a_2273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2274_, lean_object* v_requestStream_2275_, lean_object* v_keepAliveTimeout_2276_, lean_object* v_currentTimeout_2277_, lean_object* v_headerTimeout_2278_, lean_object* v_response_2279_, lean_object* v_respStream_2280_, uint8_t v_requiresData_2281_, lean_object* v_expectData_2282_, lean_object* v_x_2283_){
_start:
{
if (lean_obj_tag(v_x_2283_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_expectData_2282_);
lean_dec(v_respStream_2280_);
lean_dec_ref(v_response_2279_);
lean_dec(v_headerTimeout_2278_);
lean_dec(v_currentTimeout_2277_);
lean_dec(v_keepAliveTimeout_2276_);
lean_dec_ref(v_requestStream_2275_);
lean_dec_ref(v_machine_2274_);
v_a_2285_ = lean_ctor_get(v_x_2283_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2283_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2287_ = v_x_2283_;
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v_x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
}
}
else
{
lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2304_; 
v_isSharedCheck_2304_ = !lean_is_exclusive(v_x_2283_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v_x_2283_, 0);
lean_dec(v_unused_2305_);
v___x_2295_ = v_x_2283_;
v_isShared_2296_ = v_isSharedCheck_2304_;
goto v_resetjp_2294_;
}
else
{
lean_dec(v_x_2283_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2304_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2297_ = 1;
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2299_, 0, v_machine_2274_);
lean_ctor_set(v___x_2299_, 1, v_requestStream_2275_);
lean_ctor_set(v___x_2299_, 2, v_keepAliveTimeout_2276_);
lean_ctor_set(v___x_2299_, 3, v_currentTimeout_2277_);
lean_ctor_set(v___x_2299_, 4, v_headerTimeout_2278_);
lean_ctor_set(v___x_2299_, 5, v_response_2279_);
lean_ctor_set(v___x_2299_, 6, v_respStream_2280_);
lean_ctor_set(v___x_2299_, 7, v_expectData_2282_);
lean_ctor_set(v___x_2299_, 8, v___x_2298_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*9, v_requiresData_2281_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*9 + 1, v___x_2297_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2299_);
v___x_2301_ = v___x_2295_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2306_, lean_object* v_requestStream_2307_, lean_object* v_keepAliveTimeout_2308_, lean_object* v_currentTimeout_2309_, lean_object* v_headerTimeout_2310_, lean_object* v_response_2311_, lean_object* v_respStream_2312_, lean_object* v_requiresData_2313_, lean_object* v_expectData_2314_, lean_object* v_x_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v_requiresData_boxed_2317_; lean_object* v_res_2318_; 
v_requiresData_boxed_2317_ = lean_unbox(v_requiresData_2313_);
v_res_2318_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2306_, v_requestStream_2307_, v_keepAliveTimeout_2308_, v_currentTimeout_2309_, v_headerTimeout_2310_, v_response_2311_, v_respStream_2312_, v_requiresData_boxed_2317_, v_expectData_2314_, v_x_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2319_, lean_object* v_response_2320_, lean_object* v___x_2321_, lean_object* v___f_2322_, lean_object* v_x_2323_){
_start:
{
if (lean_obj_tag(v_x_2323_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v___f_2322_);
lean_dec(v___x_2321_);
lean_dec_ref(v_response_2320_);
lean_dec_ref(v_toFunctor_2319_);
v_a_2325_ = lean_ctor_get(v_x_2323_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_x_2323_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v_x_2323_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v_x_2323_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2348_; 
v_a_2334_ = lean_ctor_get(v_x_2323_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2323_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2336_ = v_x_2323_;
v_isShared_2337_ = v_isSharedCheck_2348_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v_x_2323_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2348_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2338_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2338_, 0, lean_box(0));
lean_closure_set(v___x_2338_, 1, lean_box(0));
lean_closure_set(v___x_2338_, 2, v_toFunctor_2319_);
v___x_2339_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2339_, 0, lean_box(0));
lean_closure_set(v___x_2339_, 1, v_response_2320_);
v___x_2340_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2340_, 0, lean_box(0));
lean_closure_set(v___x_2340_, 1, lean_box(0));
lean_closure_set(v___x_2340_, 2, lean_box(0));
lean_closure_set(v___x_2340_, 3, v___x_2338_);
lean_closure_set(v___x_2340_, 4, v___x_2339_);
v___x_2341_ = 0;
lean_inc(v___x_2321_);
v___x_2342_ = l_BaseIO_chainTask___redArg(v_a_2334_, v___x_2340_, v___x_2321_, v___x_2341_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2342_);
v___x_2344_ = v___x_2336_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2321_, v___x_2341_, v___x_2345_, v___f_2322_);
return v___x_2346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2349_, lean_object* v_response_2350_, lean_object* v___x_2351_, lean_object* v___f_2352_, lean_object* v_x_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2349_, v_response_2350_, v___x_2351_, v___f_2352_, v_x_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2357_, lean_object* v_handler_2358_, lean_object* v_extensions_2359_, lean_object* v_connectionContext_2360_, lean_object* v_state_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v_toApplicative_2364_; lean_object* v_pendingHead_2365_; 
v___x_2363_ = l_instMonadBaseIO;
v_toApplicative_2364_ = lean_ctor_get(v___x_2363_, 0);
v_pendingHead_2365_ = lean_ctor_get(v_state_2361_, 8);
lean_inc(v_pendingHead_2365_);
if (lean_obj_tag(v_pendingHead_2365_) == 1)
{
lean_object* v_toFunctor_2366_; lean_object* v_machine_2367_; lean_object* v_requestStream_2368_; lean_object* v_keepAliveTimeout_2369_; lean_object* v_currentTimeout_2370_; lean_object* v_headerTimeout_2371_; lean_object* v_response_2372_; lean_object* v_respStream_2373_; uint8_t v_requiresData_2374_; lean_object* v_expectData_2375_; lean_object* v_val_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2398_; 
v_toFunctor_2366_ = lean_ctor_get(v_toApplicative_2364_, 0);
v_machine_2367_ = lean_ctor_get(v_state_2361_, 0);
lean_inc_ref(v_machine_2367_);
v_requestStream_2368_ = lean_ctor_get(v_state_2361_, 1);
lean_inc_ref(v_requestStream_2368_);
v_keepAliveTimeout_2369_ = lean_ctor_get(v_state_2361_, 2);
lean_inc(v_keepAliveTimeout_2369_);
v_currentTimeout_2370_ = lean_ctor_get(v_state_2361_, 3);
lean_inc(v_currentTimeout_2370_);
v_headerTimeout_2371_ = lean_ctor_get(v_state_2361_, 4);
lean_inc(v_headerTimeout_2371_);
v_response_2372_ = lean_ctor_get(v_state_2361_, 5);
lean_inc_ref(v_response_2372_);
v_respStream_2373_ = lean_ctor_get(v_state_2361_, 6);
lean_inc(v_respStream_2373_);
v_requiresData_2374_ = lean_ctor_get_uint8(v_state_2361_, sizeof(void*)*9);
v_expectData_2375_ = lean_ctor_get(v_state_2361_, 7);
lean_inc(v_expectData_2375_);
lean_dec_ref(v_state_2361_);
v_val_2376_ = lean_ctor_get(v_pendingHead_2365_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_pendingHead_2365_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2378_ = v_pendingHead_2365_;
v_isShared_2379_ = v_isSharedCheck_2398_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_val_2376_);
lean_dec(v_pendingHead_2365_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2398_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v_onRequest_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v___f_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v_onRequest_2380_ = lean_ctor_get(v_inst_2357_, 1);
lean_inc_ref(v_onRequest_2380_);
lean_dec_ref(v_inst_2357_);
lean_inc_ref(v_requestStream_2368_);
v___x_2381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2381_, 0, v_val_2376_);
lean_ctor_set(v___x_2381_, 1, v_requestStream_2368_);
lean_ctor_set(v___x_2381_, 2, v_extensions_2359_);
v___x_2382_ = lean_apply_3(v_onRequest_2380_, v_handler_2358_, v___x_2381_, v_connectionContext_2360_);
v___x_2383_ = lean_unsigned_to_nat(0u);
v___x_2384_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2384_, 0, lean_box(0));
lean_closure_set(v___x_2384_, 1, v___x_2382_);
v___x_2385_ = lean_io_as_task(v___x_2384_, v___x_2383_);
v___f_2386_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2387_ = lean_box(v_requiresData_2374_);
lean_inc_ref(v_response_2372_);
v___f_2388_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2388_, 0, v_machine_2367_);
lean_closure_set(v___f_2388_, 1, v_requestStream_2368_);
lean_closure_set(v___f_2388_, 2, v_keepAliveTimeout_2369_);
lean_closure_set(v___f_2388_, 3, v_currentTimeout_2370_);
lean_closure_set(v___f_2388_, 4, v_headerTimeout_2371_);
lean_closure_set(v___f_2388_, 5, v_response_2372_);
lean_closure_set(v___f_2388_, 6, v_respStream_2373_);
lean_closure_set(v___f_2388_, 7, v___x_2387_);
lean_closure_set(v___f_2388_, 8, v_expectData_2375_);
lean_inc_ref(v_toFunctor_2366_);
v___f_2389_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2389_, 0, v_toFunctor_2366_);
lean_closure_set(v___f_2389_, 1, v_response_2372_);
lean_closure_set(v___f_2389_, 2, v___x_2383_);
lean_closure_set(v___f_2389_, 3, v___f_2388_);
v___x_2390_ = 1;
v___x_2391_ = lean_task_bind(v___x_2385_, v___f_2386_, v___x_2383_, v___x_2390_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2391_);
v___x_2393_ = v___x_2378_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
v___x_2395_ = 0;
v___x_2396_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2383_, v___x_2395_, v___x_2394_, v___f_2389_);
return v___x_2396_;
}
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec(v_pendingHead_2365_);
lean_dec_ref(v_connectionContext_2360_);
lean_dec(v_extensions_2359_);
lean_dec(v_handler_2358_);
lean_dec_ref(v_inst_2357_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_state_2361_);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2401_, lean_object* v_handler_2402_, lean_object* v_extensions_2403_, lean_object* v_connectionContext_2404_, lean_object* v_state_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2401_, v_handler_2402_, v_extensions_2403_, v_connectionContext_2404_, v_state_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2408_, lean_object* v_inst_2409_, lean_object* v_handler_2410_, lean_object* v_extensions_2411_, lean_object* v_connectionContext_2412_, lean_object* v_state_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2409_, v_handler_2410_, v_extensions_2411_, v_connectionContext_2412_, v_state_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2416_, lean_object* v_inst_2417_, lean_object* v_handler_2418_, lean_object* v_extensions_2419_, lean_object* v_connectionContext_2420_, lean_object* v_state_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2416_, v_inst_2417_, v_handler_2418_, v_extensions_2419_, v_connectionContext_2420_, v_state_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2424_, lean_object* v_____r_2425_){
_start:
{
lean_object* v_writer_2427_; lean_object* v_reader_2428_; lean_object* v_config_2429_; lean_object* v_events_2430_; lean_object* v_error_2431_; lean_object* v_instant_2432_; uint8_t v_keepAlive_2433_; uint8_t v_forcedFlush_2434_; uint8_t v_pullBodyStalled_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2462_; 
v_writer_2427_ = lean_ctor_get(v_machine_2424_, 1);
v_reader_2428_ = lean_ctor_get(v_machine_2424_, 0);
v_config_2429_ = lean_ctor_get(v_machine_2424_, 2);
v_events_2430_ = lean_ctor_get(v_machine_2424_, 3);
v_error_2431_ = lean_ctor_get(v_machine_2424_, 4);
v_instant_2432_ = lean_ctor_get(v_machine_2424_, 5);
v_keepAlive_2433_ = lean_ctor_get_uint8(v_machine_2424_, sizeof(void*)*6);
v_forcedFlush_2434_ = lean_ctor_get_uint8(v_machine_2424_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2435_ = lean_ctor_get_uint8(v_machine_2424_, sizeof(void*)*6 + 2);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_machine_2424_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2437_ = v_machine_2424_;
v_isShared_2438_ = v_isSharedCheck_2462_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_instant_2432_);
lean_inc(v_error_2431_);
lean_inc(v_events_2430_);
lean_inc(v_config_2429_);
lean_inc(v_writer_2427_);
lean_inc(v_reader_2428_);
lean_dec(v_machine_2424_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2462_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_userData_2439_; lean_object* v_outputData_2440_; lean_object* v_state_2441_; lean_object* v_knownSize_2442_; lean_object* v_messageHead_2443_; uint8_t v_sentMessage_2444_; uint8_t v_omitBody_2445_; lean_object* v_userDataBytes_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2461_; 
v_userData_2439_ = lean_ctor_get(v_writer_2427_, 0);
v_outputData_2440_ = lean_ctor_get(v_writer_2427_, 1);
v_state_2441_ = lean_ctor_get(v_writer_2427_, 2);
v_knownSize_2442_ = lean_ctor_get(v_writer_2427_, 3);
v_messageHead_2443_ = lean_ctor_get(v_writer_2427_, 4);
v_sentMessage_2444_ = lean_ctor_get_uint8(v_writer_2427_, sizeof(void*)*6);
v_omitBody_2445_ = lean_ctor_get_uint8(v_writer_2427_, sizeof(void*)*6 + 2);
v_userDataBytes_2446_ = lean_ctor_get(v_writer_2427_, 5);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_writer_2427_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2448_ = v_writer_2427_;
v_isShared_2449_ = v_isSharedCheck_2461_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_userDataBytes_2446_);
lean_inc(v_messageHead_2443_);
lean_inc(v_knownSize_2442_);
lean_inc(v_state_2441_);
lean_inc(v_outputData_2440_);
lean_inc(v_userData_2439_);
lean_dec(v_writer_2427_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2461_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = 1;
if (v_isShared_2449_ == 0)
{
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_userData_2439_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_outputData_2440_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_state_2441_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_knownSize_2442_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_messageHead_2443_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v_userDataBytes_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, sizeof(void*)*6, v_sentMessage_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, sizeof(void*)*6 + 2, v_omitBody_2445_);
v___x_2452_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
lean_ctor_set_uint8(v___x_2452_, sizeof(void*)*6 + 1, v___x_2450_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v___x_2452_);
v___x_2454_ = v___x_2437_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_reader_2428_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_config_2429_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_events_2430_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_error_2431_);
lean_ctor_set(v_reuseFailAlloc_2459_, 5, v_instant_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2459_, sizeof(void*)*6, v_keepAlive_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2459_, sizeof(void*)*6 + 1, v_forcedFlush_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2459_, sizeof(void*)*6 + 2, v_pullBodyStalled_2435_);
v___x_2454_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2463_, lean_object* v_____r_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2463_, v_____r_2464_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2467_, lean_object* v_x2_2468_){
_start:
{
lean_object* v_data_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_data_2469_ = lean_ctor_get(v_x2_2468_, 0);
v___x_2470_ = lean_byte_array_size(v_data_2469_);
v___x_2471_ = lean_nat_add(v_x1_2467_, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2472_, lean_object* v_x2_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2472_, v_x2_2473_);
lean_dec_ref(v_x2_2473_);
lean_dec(v_x1_2472_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2475_, lean_object* v_machine_2476_, lean_object* v_isClosed_2477_, lean_object* v___f_2478_, lean_object* v___f_2479_, lean_object* v_x_2480_){
_start:
{
lean_object* v___y_2483_; 
if (lean_obj_tag(v_x_2480_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v___f_2479_);
lean_dec_ref(v___f_2478_);
lean_dec_ref(v_isClosed_2477_);
lean_dec_ref(v_machine_2476_);
lean_dec(v_body_2475_);
v_a_2488_ = lean_ctor_get(v_x_2480_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2490_ = v_x_2480_;
v_isShared_2491_ = v_isSharedCheck_2496_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v_x_2480_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2496_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2488_);
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
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2560_; 
v_a_2497_ = lean_ctor_get(v_x_2480_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2499_ = v_x_2480_;
v_isShared_2500_ = v_isSharedCheck_2560_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v_x_2480_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2560_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
if (lean_obj_tag(v_a_2497_) == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_dec_ref(v___f_2479_);
lean_dec_ref(v___f_2478_);
lean_dec_ref(v_isClosed_2477_);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_body_2475_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_machine_2476_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2502_);
v___x_2504_ = v___x_2499_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
else
{
lean_object* v_val_2507_; 
lean_del_object(v___x_2499_);
v_val_2507_ = lean_ctor_get(v_a_2497_, 0);
lean_inc(v_val_2507_);
lean_dec_ref_known(v_a_2497_, 1);
if (lean_obj_tag(v_val_2507_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; 
lean_dec_ref(v___f_2479_);
lean_dec_ref(v_machine_2476_);
v___x_2508_ = lean_apply_2(v_isClosed_2477_, v_body_2475_, lean_box(0));
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = 0;
v___x_2511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2509_, v___x_2510_, v___x_2508_, v___f_2478_);
return v___x_2511_;
}
else
{
lean_object* v_val_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
lean_dec_ref(v___f_2478_);
lean_dec_ref(v_isClosed_2477_);
v_val_2512_ = lean_ctor_get(v_val_2507_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v_val_2507_, 1);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2513_);
v___x_2515_ = lean_array_push(v___x_2514_, v_val_2512_);
v___x_2516_ = lean_array_get_size(v___x_2515_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_nat_dec_eq(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v_reader_2519_; lean_object* v_writer_2520_; lean_object* v_config_2521_; lean_object* v_events_2522_; lean_object* v_error_2523_; lean_object* v_instant_2524_; uint8_t v_keepAlive_2525_; uint8_t v_forcedFlush_2526_; uint8_t v_pullBodyStalled_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2559_; 
v_reader_2519_ = lean_ctor_get(v_machine_2476_, 0);
v_writer_2520_ = lean_ctor_get(v_machine_2476_, 1);
v_config_2521_ = lean_ctor_get(v_machine_2476_, 2);
v_events_2522_ = lean_ctor_get(v_machine_2476_, 3);
v_error_2523_ = lean_ctor_get(v_machine_2476_, 4);
v_instant_2524_ = lean_ctor_get(v_machine_2476_, 5);
v_keepAlive_2525_ = lean_ctor_get_uint8(v_machine_2476_, sizeof(void*)*6);
v_forcedFlush_2526_ = lean_ctor_get_uint8(v_machine_2476_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2527_ = lean_ctor_get_uint8(v_machine_2476_, sizeof(void*)*6 + 2);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_machine_2476_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2529_ = v_machine_2476_;
v_isShared_2530_ = v_isSharedCheck_2559_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_instant_2524_);
lean_inc(v_error_2523_);
lean_inc(v_events_2522_);
lean_inc(v_config_2521_);
lean_inc(v_writer_2520_);
lean_inc(v_reader_2519_);
lean_dec(v_machine_2476_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2559_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___y_2532_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_2555_ = lean_nat_dec_lt(v___x_2517_, v___x_2516_);
if (v___x_2555_ == 0)
{
lean_dec_ref(v___f_2479_);
v___y_2532_ = v___x_2517_;
goto v___jp_2531_;
}
else
{
size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = lean_usize_of_nat(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2554_, v___f_2479_, v___x_2515_, v___x_2556_, v___x_2557_, v___x_2517_);
v___y_2532_ = v___x_2558_;
goto v___jp_2531_;
}
v___jp_2531_:
{
lean_object* v_userData_2533_; lean_object* v_outputData_2534_; lean_object* v_state_2535_; lean_object* v_knownSize_2536_; lean_object* v_messageHead_2537_; uint8_t v_sentMessage_2538_; uint8_t v_userClosedBody_2539_; uint8_t v_omitBody_2540_; lean_object* v_userDataBytes_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2553_; 
v_userData_2533_ = lean_ctor_get(v_writer_2520_, 0);
v_outputData_2534_ = lean_ctor_get(v_writer_2520_, 1);
v_state_2535_ = lean_ctor_get(v_writer_2520_, 2);
v_knownSize_2536_ = lean_ctor_get(v_writer_2520_, 3);
v_messageHead_2537_ = lean_ctor_get(v_writer_2520_, 4);
v_sentMessage_2538_ = lean_ctor_get_uint8(v_writer_2520_, sizeof(void*)*6);
v_userClosedBody_2539_ = lean_ctor_get_uint8(v_writer_2520_, sizeof(void*)*6 + 1);
v_omitBody_2540_ = lean_ctor_get_uint8(v_writer_2520_, sizeof(void*)*6 + 2);
v_userDataBytes_2541_ = lean_ctor_get(v_writer_2520_, 5);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_writer_2520_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2543_ = v_writer_2520_;
v_isShared_2544_ = v_isSharedCheck_2553_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_userDataBytes_2541_);
lean_inc(v_messageHead_2537_);
lean_inc(v_knownSize_2536_);
lean_inc(v_state_2535_);
lean_inc(v_outputData_2534_);
lean_inc(v_userData_2533_);
lean_dec(v_writer_2520_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2553_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2545_ = l_Array_append___redArg(v_userData_2533_, v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2546_ = lean_nat_add(v_userDataBytes_2541_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec(v_userDataBytes_2541_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 5, v___x_2546_);
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2548_ = v___x_2543_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_outputData_2534_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_state_2535_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_knownSize_2536_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_messageHead_2537_);
lean_ctor_set(v_reuseFailAlloc_2552_, 5, v___x_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*6, v_sentMessage_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*6 + 1, v_userClosedBody_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*6 + 2, v_omitBody_2540_);
v___x_2548_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2550_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2548_);
v___x_2550_ = v___x_2529_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_reader_2519_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_config_2521_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_events_2522_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_error_2523_);
lean_ctor_set(v_reuseFailAlloc_2551_, 5, v_instant_2524_);
lean_ctor_set_uint8(v_reuseFailAlloc_2551_, sizeof(void*)*6, v_keepAlive_2525_);
lean_ctor_set_uint8(v_reuseFailAlloc_2551_, sizeof(void*)*6 + 1, v_forcedFlush_2526_);
lean_ctor_set_uint8(v_reuseFailAlloc_2551_, sizeof(void*)*6 + 2, v_pullBodyStalled_2527_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
v___y_2483_ = v___x_2550_;
goto v___jp_2482_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___f_2479_);
v___y_2483_ = v_machine_2476_;
goto v___jp_2482_;
}
}
}
}
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_body_2475_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___y_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2561_, lean_object* v_machine_2562_, lean_object* v_isClosed_2563_, lean_object* v___f_2564_, lean_object* v___f_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2561_, v_machine_2562_, v_isClosed_2563_, v___f_2564_, v___f_2565_, v_x_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2570_, lean_object* v_machine_2571_, lean_object* v_body_2572_){
_start:
{
lean_object* v_close_2574_; lean_object* v_isClosed_2575_; lean_object* v_tryRecv_2576_; lean_object* v___x_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
v_close_2574_ = lean_ctor_get(v_inst_2570_, 1);
lean_inc_ref(v_close_2574_);
v_isClosed_2575_ = lean_ctor_get(v_inst_2570_, 2);
lean_inc_ref(v_isClosed_2575_);
v_tryRecv_2576_ = lean_ctor_get(v_inst_2570_, 4);
lean_inc_ref(v_tryRecv_2576_);
lean_dec_ref(v_inst_2570_);
lean_inc_n(v_body_2572_, 2);
v___x_2577_ = lean_apply_2(v_tryRecv_2576_, v_body_2572_, lean_box(0));
lean_inc_ref(v_machine_2571_);
v___f_2578_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2578_, 0, v_machine_2571_);
lean_inc_ref(v___f_2578_);
v___f_2579_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2579_, 0, v___f_2578_);
v___f_2580_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2580_, 0, v_close_2574_);
lean_closure_set(v___f_2580_, 1, v_body_2572_);
lean_closure_set(v___f_2580_, 2, v___f_2579_);
lean_closure_set(v___f_2580_, 3, v___f_2578_);
v___f_2581_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2582_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2582_, 0, v_body_2572_);
lean_closure_set(v___f_2582_, 1, v_machine_2571_);
lean_closure_set(v___f_2582_, 2, v_isClosed_2575_);
lean_closure_set(v___f_2582_, 3, v___f_2580_);
lean_closure_set(v___f_2582_, 4, v___f_2581_);
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = 0;
v___x_2585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2583_, v___x_2584_, v___x_2577_, v___f_2582_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2586_, lean_object* v_machine_2587_, lean_object* v_body_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2586_, v_machine_2587_, v_body_2588_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2591_, lean_object* v_inst_2592_, lean_object* v_machine_2593_, lean_object* v_body_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2592_, v_machine_2593_, v_body_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2597_, lean_object* v_inst_2598_, lean_object* v_machine_2599_, lean_object* v_body_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2597_, v_inst_2598_, v_machine_2599_, v_body_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2609_, lean_object* v_____r_2610_, lean_object* v_st_2611_){
_start:
{
lean_object* v_machine_2613_; lean_object* v_requestStream_2614_; lean_object* v_keepAliveTimeout_2615_; lean_object* v_currentTimeout_2616_; lean_object* v_headerTimeout_2617_; lean_object* v_response_2618_; lean_object* v_respStream_2619_; uint8_t v_requiresData_2620_; lean_object* v_expectData_2621_; uint8_t v_handlerDispatched_2622_; lean_object* v_pendingHead_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2708_; 
v_machine_2613_ = lean_ctor_get(v_st_2611_, 0);
v_requestStream_2614_ = lean_ctor_get(v_st_2611_, 1);
v_keepAliveTimeout_2615_ = lean_ctor_get(v_st_2611_, 2);
v_currentTimeout_2616_ = lean_ctor_get(v_st_2611_, 3);
v_headerTimeout_2617_ = lean_ctor_get(v_st_2611_, 4);
v_response_2618_ = lean_ctor_get(v_st_2611_, 5);
v_respStream_2619_ = lean_ctor_get(v_st_2611_, 6);
v_requiresData_2620_ = lean_ctor_get_uint8(v_st_2611_, sizeof(void*)*9);
v_expectData_2621_ = lean_ctor_get(v_st_2611_, 7);
v_handlerDispatched_2622_ = lean_ctor_get_uint8(v_st_2611_, sizeof(void*)*9 + 1);
v_pendingHead_2623_ = lean_ctor_get(v_st_2611_, 8);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_st_2611_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2625_ = v_st_2611_;
v_isShared_2626_ = v_isSharedCheck_2708_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_pendingHead_2623_);
lean_inc(v_expectData_2621_);
lean_inc(v_respStream_2619_);
lean_inc(v_response_2618_);
lean_inc(v_headerTimeout_2617_);
lean_inc(v_currentTimeout_2616_);
lean_inc(v_keepAliveTimeout_2615_);
lean_inc(v_requestStream_2614_);
lean_inc(v_machine_2613_);
lean_dec(v_st_2611_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2708_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___y_2628_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; uint8_t v___y_2646_; lean_object* v___y_2647_; uint8_t v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v_reader_2673_; lean_object* v_writer_2674_; lean_object* v_config_2675_; lean_object* v_events_2676_; lean_object* v_error_2677_; lean_object* v_instant_2678_; uint8_t v_keepAlive_2679_; uint8_t v_forcedFlush_2680_; lean_object* v_state_2681_; lean_object* v_input_2682_; lean_object* v_messageHead_2683_; lean_object* v_messageCount_2684_; lean_object* v_bodyBytesRead_2685_; lean_object* v_headerBytesRead_2686_; uint8_t v_noMoreInput_2687_; uint8_t v___y_2689_; uint8_t v___y_2690_; uint8_t v___y_2703_; 
v_reader_2673_ = lean_ctor_get(v_machine_2613_, 0);
v_writer_2674_ = lean_ctor_get(v_machine_2613_, 1);
v_config_2675_ = lean_ctor_get(v_machine_2613_, 2);
v_events_2676_ = lean_ctor_get(v_machine_2613_, 3);
v_error_2677_ = lean_ctor_get(v_machine_2613_, 4);
v_instant_2678_ = lean_ctor_get(v_machine_2613_, 5);
v_keepAlive_2679_ = lean_ctor_get_uint8(v_machine_2613_, sizeof(void*)*6);
v_forcedFlush_2680_ = lean_ctor_get_uint8(v_machine_2613_, sizeof(void*)*6 + 1);
v_state_2681_ = lean_ctor_get(v_reader_2673_, 0);
v_input_2682_ = lean_ctor_get(v_reader_2673_, 1);
v_messageHead_2683_ = lean_ctor_get(v_reader_2673_, 2);
v_messageCount_2684_ = lean_ctor_get(v_reader_2673_, 3);
v_bodyBytesRead_2685_ = lean_ctor_get(v_reader_2673_, 4);
v_headerBytesRead_2686_ = lean_ctor_get(v_reader_2673_, 5);
v_noMoreInput_2687_ = lean_ctor_get_uint8(v_reader_2673_, sizeof(void*)*6);
if (lean_obj_tag(v_state_2681_) == 6)
{
uint8_t v___x_2706_; 
v___x_2706_ = 1;
v___y_2703_ = v___x_2706_;
goto v___jp_2702_;
}
else
{
uint8_t v___x_2707_; 
v___x_2707_ = 0;
v___y_2703_ = v___x_2707_;
goto v___jp_2702_;
}
v___jp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___y_2628_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___y_2628_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_requestStream_2614_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_keepAliveTimeout_2615_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_currentTimeout_2616_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_headerTimeout_2617_);
lean_ctor_set(v_reuseFailAlloc_2636_, 5, v_response_2618_);
lean_ctor_set(v_reuseFailAlloc_2636_, 6, v_respStream_2619_);
lean_ctor_set(v_reuseFailAlloc_2636_, 7, v_expectData_2621_);
lean_ctor_set(v_reuseFailAlloc_2636_, 8, v_pendingHead_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2636_, sizeof(void*)*9, v_requiresData_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2636_, sizeof(void*)*9 + 1, v_handlerDispatched_2622_);
v___x_2630_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2631_ = 0;
v___x_2632_ = lean_box(v___x_2631_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2630_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
v___jp_2637_:
{
lean_object* v_maxHeaderBytes_2653_; lean_object* v_maxStartLineLength_2654_; lean_object* v_maxChunkLineLength_2655_; lean_object* v_maxBodySize_2656_; lean_object* v_array_2657_; lean_object* v_idx_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v_maxHeaderBytes_2653_ = lean_ctor_get(v___y_2638_, 2);
v_maxStartLineLength_2654_ = lean_ctor_get(v___y_2638_, 5);
v_maxChunkLineLength_2655_ = lean_ctor_get(v___y_2638_, 13);
v_maxBodySize_2656_ = lean_ctor_get(v___y_2638_, 15);
v_array_2657_ = lean_ctor_get(v___y_2652_, 0);
v_idx_2658_ = lean_ctor_get(v___y_2652_, 1);
v___x_2659_ = lean_nat_add(v_maxBodySize_2656_, v_maxHeaderBytes_2653_);
v___x_2660_ = lean_nat_add(v___x_2659_, v_maxStartLineLength_2654_);
lean_dec(v___x_2659_);
v___x_2661_ = lean_nat_add(v___x_2660_, v_maxChunkLineLength_2655_);
lean_dec(v___x_2660_);
v___x_2662_ = lean_byte_array_size(v_array_2657_);
v___x_2663_ = lean_nat_sub(v___x_2662_, v_idx_2658_);
v___x_2664_ = lean_nat_dec_lt(v___x_2661_, v___x_2663_);
lean_dec(v___x_2663_);
lean_dec(v___x_2661_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v_machine_2666_; 
v___x_2665_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2665_, 0, v___y_2651_);
lean_ctor_set(v___x_2665_, 1, v___y_2652_);
lean_ctor_set(v___x_2665_, 2, v___y_2649_);
lean_ctor_set(v___x_2665_, 3, v___y_2643_);
lean_ctor_set(v___x_2665_, 4, v___y_2647_);
lean_ctor_set(v___x_2665_, 5, v___y_2645_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*6, v___y_2646_);
v_machine_2666_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_2666_, 0, v___x_2665_);
lean_ctor_set(v_machine_2666_, 1, v___y_2650_);
lean_ctor_set(v_machine_2666_, 2, v___y_2638_);
lean_ctor_set(v_machine_2666_, 3, v___y_2641_);
lean_ctor_set(v_machine_2666_, 4, v___y_2644_);
lean_ctor_set(v_machine_2666_, 5, v___y_2639_);
lean_ctor_set_uint8(v_machine_2666_, sizeof(void*)*6, v___y_2648_);
lean_ctor_set_uint8(v_machine_2666_, sizeof(void*)*6 + 1, v___y_2642_);
lean_ctor_set_uint8(v_machine_2666_, sizeof(void*)*6 + 2, v___y_2640_);
v___y_2628_ = v_machine_2666_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec(v___y_2651_);
lean_dec(v___y_2644_);
v___x_2667_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2668_ = lean_array_push(v___y_2641_, v___x_2667_);
v___x_2669_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
v___x_2670_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___y_2652_);
lean_ctor_set(v___x_2670_, 2, v___y_2649_);
lean_ctor_set(v___x_2670_, 3, v___y_2643_);
lean_ctor_set(v___x_2670_, 4, v___y_2647_);
lean_ctor_set(v___x_2670_, 5, v___y_2645_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*6, v___y_2646_);
v___x_2671_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
v___x_2672_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___y_2650_);
lean_ctor_set(v___x_2672_, 2, v___y_2638_);
lean_ctor_set(v___x_2672_, 3, v___x_2668_);
lean_ctor_set(v___x_2672_, 4, v___x_2671_);
lean_ctor_set(v___x_2672_, 5, v___y_2639_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*6, v___y_2648_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*6 + 1, v___y_2642_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*6 + 2, v___y_2640_);
v___y_2628_ = v___x_2672_;
goto v___jp_2627_;
}
}
v___jp_2688_:
{
if (v___y_2689_ == 0)
{
if (v___y_2690_ == 0)
{
lean_object* v_array_2691_; lean_object* v_idx_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
lean_inc(v_headerBytesRead_2686_);
lean_inc(v_bodyBytesRead_2685_);
lean_inc(v_messageCount_2684_);
lean_inc(v_messageHead_2683_);
lean_inc_ref(v_input_2682_);
lean_inc(v_state_2681_);
lean_inc(v_instant_2678_);
lean_inc(v_error_2677_);
lean_inc_ref(v_events_2676_);
lean_inc_ref(v_config_2675_);
lean_inc_ref(v_writer_2674_);
lean_dec_ref(v_machine_2613_);
v_array_2691_ = lean_ctor_get(v_input_2682_, 0);
lean_inc_ref(v_array_2691_);
v_idx_2692_ = lean_ctor_get(v_input_2682_, 1);
lean_inc(v_idx_2692_);
lean_dec_ref(v_input_2682_);
v___x_2693_ = lean_byte_array_size(v_array_2691_);
v___x_2694_ = lean_nat_dec_le(v___x_2693_, v_idx_2692_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2695_ = l_ByteArray_extract(v_array_2691_, v_idx_2692_, v___x_2693_);
lean_dec_ref(v_array_2691_);
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = lean_byte_array_size(v___x_2695_);
v___x_2698_ = lean_byte_array_size(v_val_2609_);
v___x_2699_ = lean_byte_array_copy_slice(v_val_2609_, v___x_2696_, v___x_2695_, v___x_2697_, v___x_2698_, v___x_2694_);
lean_dec_ref(v_val_2609_);
v___x_2700_ = l_ByteArray_mkIterator(v___x_2699_);
v___y_2638_ = v_config_2675_;
v___y_2639_ = v_instant_2678_;
v___y_2640_ = v___y_2690_;
v___y_2641_ = v_events_2676_;
v___y_2642_ = v_forcedFlush_2680_;
v___y_2643_ = v_messageCount_2684_;
v___y_2644_ = v_error_2677_;
v___y_2645_ = v_headerBytesRead_2686_;
v___y_2646_ = v_noMoreInput_2687_;
v___y_2647_ = v_bodyBytesRead_2685_;
v___y_2648_ = v_keepAlive_2679_;
v___y_2649_ = v_messageHead_2683_;
v___y_2650_ = v_writer_2674_;
v___y_2651_ = v_state_2681_;
v___y_2652_ = v___x_2700_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2701_; 
lean_dec(v_idx_2692_);
lean_dec_ref(v_array_2691_);
v___x_2701_ = l_ByteArray_mkIterator(v_val_2609_);
v___y_2638_ = v_config_2675_;
v___y_2639_ = v_instant_2678_;
v___y_2640_ = v___y_2690_;
v___y_2641_ = v_events_2676_;
v___y_2642_ = v_forcedFlush_2680_;
v___y_2643_ = v_messageCount_2684_;
v___y_2644_ = v_error_2677_;
v___y_2645_ = v_headerBytesRead_2686_;
v___y_2646_ = v_noMoreInput_2687_;
v___y_2647_ = v_bodyBytesRead_2685_;
v___y_2648_ = v_keepAlive_2679_;
v___y_2649_ = v_messageHead_2683_;
v___y_2650_ = v_writer_2674_;
v___y_2651_ = v_state_2681_;
v___y_2652_ = v___x_2701_;
goto v___jp_2637_;
}
}
else
{
lean_dec_ref(v_val_2609_);
v___y_2628_ = v_machine_2613_;
goto v___jp_2627_;
}
}
else
{
lean_dec_ref(v_val_2609_);
v___y_2628_ = v_machine_2613_;
goto v___jp_2627_;
}
}
v___jp_2702_:
{
if (lean_obj_tag(v_state_2681_) == 7)
{
uint8_t v___x_2704_; 
v___x_2704_ = 1;
v___y_2689_ = v___y_2703_;
v___y_2690_ = v___x_2704_;
goto v___jp_2688_;
}
else
{
uint8_t v___x_2705_; 
v___x_2705_ = 0;
v___y_2689_ = v___y_2703_;
v___y_2690_ = v___x_2705_;
goto v___jp_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2709_, lean_object* v_____r_2710_, lean_object* v_st_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2709_, v_____r_2710_, v_st_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2714_, lean_object* v_machine_2715_, lean_object* v_requestStream_2716_, lean_object* v_currentTimeout_2717_, lean_object* v_response_2718_, lean_object* v_respStream_2719_, uint8_t v_requiresData_2720_, lean_object* v_expectData_2721_, uint8_t v_handlerDispatched_2722_, lean_object* v_pendingHead_2723_, lean_object* v___f_2724_, lean_object* v_x_2725_){
_start:
{
if (lean_obj_tag(v_x_2725_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v___f_2724_);
lean_dec(v_pendingHead_2723_);
lean_dec(v_expectData_2721_);
lean_dec(v_respStream_2719_);
lean_dec_ref(v_response_2718_);
lean_dec(v_currentTimeout_2717_);
lean_dec_ref(v_requestStream_2716_);
lean_dec_ref(v_machine_2715_);
v_a_2727_ = lean_ctor_get(v_x_2725_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_x_2725_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2729_ = v_x_2725_;
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v_x_2725_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v_headerTimeout_2737_; lean_object* v_second_2738_; lean_object* v_nano_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v_second_2743_; lean_object* v_nano_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_a_2736_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v_x_2725_, 1);
v_headerTimeout_2737_ = lean_ctor_get(v_config_2714_, 6);
v_second_2738_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_second_2738_);
v_nano_2739_ = lean_ctor_get(v_a_2736_, 1);
lean_inc(v_nano_2739_);
lean_dec(v_a_2736_);
v___x_2740_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2741_ = lean_int_mul(v_headerTimeout_2737_, v___x_2740_);
v___x_2742_ = l_Std_Time_Duration_ofNanoseconds(v___x_2741_);
lean_dec(v___x_2741_);
v_second_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_second_2743_);
v_nano_2744_ = lean_ctor_get(v___x_2742_, 1);
lean_inc(v_nano_2744_);
lean_dec_ref(v___x_2742_);
v___x_2745_ = lean_box(0);
v___x_2746_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2747_ = lean_int_mul(v_second_2738_, v___x_2746_);
lean_dec(v_second_2738_);
v___x_2748_ = lean_int_add(v___x_2747_, v_nano_2739_);
lean_dec(v_nano_2739_);
lean_dec(v___x_2747_);
v___x_2749_ = lean_int_mul(v_second_2743_, v___x_2746_);
lean_dec(v_second_2743_);
v___x_2750_ = lean_int_add(v___x_2749_, v_nano_2744_);
lean_dec(v_nano_2744_);
lean_dec(v___x_2749_);
v___x_2751_ = lean_int_add(v___x_2748_, v___x_2750_);
lean_dec(v___x_2750_);
lean_dec(v___x_2748_);
v___x_2752_ = l_Std_Time_Duration_ofNanoseconds(v___x_2751_);
lean_dec(v___x_2751_);
v___x_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2754_, 0, v_machine_2715_);
lean_ctor_set(v___x_2754_, 1, v_requestStream_2716_);
lean_ctor_set(v___x_2754_, 2, v___x_2745_);
lean_ctor_set(v___x_2754_, 3, v_currentTimeout_2717_);
lean_ctor_set(v___x_2754_, 4, v___x_2753_);
lean_ctor_set(v___x_2754_, 5, v_response_2718_);
lean_ctor_set(v___x_2754_, 6, v_respStream_2719_);
lean_ctor_set(v___x_2754_, 7, v_expectData_2721_);
lean_ctor_set(v___x_2754_, 8, v_pendingHead_2723_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*9, v_requiresData_2720_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*9 + 1, v_handlerDispatched_2722_);
v___x_2755_ = lean_box(0);
v___x_2756_ = lean_apply_3(v___f_2724_, v___x_2755_, v___x_2754_, lean_box(0));
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2757_, lean_object* v_machine_2758_, lean_object* v_requestStream_2759_, lean_object* v_currentTimeout_2760_, lean_object* v_response_2761_, lean_object* v_respStream_2762_, lean_object* v_requiresData_2763_, lean_object* v_expectData_2764_, lean_object* v_handlerDispatched_2765_, lean_object* v_pendingHead_2766_, lean_object* v___f_2767_, lean_object* v_x_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v_requiresData_boxed_2770_; uint8_t v_handlerDispatched_boxed_2771_; lean_object* v_res_2772_; 
v_requiresData_boxed_2770_ = lean_unbox(v_requiresData_2763_);
v_handlerDispatched_boxed_2771_ = lean_unbox(v_handlerDispatched_2765_);
v_res_2772_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2757_, v_machine_2758_, v_requestStream_2759_, v_currentTimeout_2760_, v_response_2761_, v_respStream_2762_, v_requiresData_boxed_2770_, v_expectData_2764_, v_handlerDispatched_boxed_2771_, v_pendingHead_2766_, v___f_2767_, v_x_2768_);
lean_dec_ref(v_config_2757_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2773_, lean_object* v_requestStream_2774_, lean_object* v_keepAliveTimeout_2775_, lean_object* v_currentTimeout_2776_, lean_object* v_headerTimeout_2777_, lean_object* v_response_2778_, uint8_t v_requiresData_2779_, lean_object* v_expectData_2780_, uint8_t v_handlerDispatched_2781_, lean_object* v_pendingHead_2782_, lean_object* v_____r_2783_){
_start:
{
lean_object* v_writer_2785_; lean_object* v_reader_2786_; lean_object* v_config_2787_; lean_object* v_events_2788_; lean_object* v_error_2789_; lean_object* v_instant_2790_; uint8_t v_keepAlive_2791_; uint8_t v_forcedFlush_2792_; uint8_t v_pullBodyStalled_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2823_; 
v_writer_2785_ = lean_ctor_get(v_machine_2773_, 1);
v_reader_2786_ = lean_ctor_get(v_machine_2773_, 0);
v_config_2787_ = lean_ctor_get(v_machine_2773_, 2);
v_events_2788_ = lean_ctor_get(v_machine_2773_, 3);
v_error_2789_ = lean_ctor_get(v_machine_2773_, 4);
v_instant_2790_ = lean_ctor_get(v_machine_2773_, 5);
v_keepAlive_2791_ = lean_ctor_get_uint8(v_machine_2773_, sizeof(void*)*6);
v_forcedFlush_2792_ = lean_ctor_get_uint8(v_machine_2773_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2793_ = lean_ctor_get_uint8(v_machine_2773_, sizeof(void*)*6 + 2);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_machine_2773_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2795_ = v_machine_2773_;
v_isShared_2796_ = v_isSharedCheck_2823_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_instant_2790_);
lean_inc(v_error_2789_);
lean_inc(v_events_2788_);
lean_inc(v_config_2787_);
lean_inc(v_writer_2785_);
lean_inc(v_reader_2786_);
lean_dec(v_machine_2773_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2823_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v_userData_2797_; lean_object* v_outputData_2798_; lean_object* v_state_2799_; lean_object* v_knownSize_2800_; lean_object* v_messageHead_2801_; uint8_t v_sentMessage_2802_; uint8_t v_omitBody_2803_; lean_object* v_userDataBytes_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2822_; 
v_userData_2797_ = lean_ctor_get(v_writer_2785_, 0);
v_outputData_2798_ = lean_ctor_get(v_writer_2785_, 1);
v_state_2799_ = lean_ctor_get(v_writer_2785_, 2);
v_knownSize_2800_ = lean_ctor_get(v_writer_2785_, 3);
v_messageHead_2801_ = lean_ctor_get(v_writer_2785_, 4);
v_sentMessage_2802_ = lean_ctor_get_uint8(v_writer_2785_, sizeof(void*)*6);
v_omitBody_2803_ = lean_ctor_get_uint8(v_writer_2785_, sizeof(void*)*6 + 2);
v_userDataBytes_2804_ = lean_ctor_get(v_writer_2785_, 5);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_writer_2785_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2806_ = v_writer_2785_;
v_isShared_2807_ = v_isSharedCheck_2822_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_userDataBytes_2804_);
lean_inc(v_messageHead_2801_);
lean_inc(v_knownSize_2800_);
lean_inc(v_state_2799_);
lean_inc(v_outputData_2798_);
lean_inc(v_userData_2797_);
lean_dec(v_writer_2785_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2822_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
uint8_t v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = 1;
if (v_isShared_2807_ == 0)
{
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_userData_2797_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_outputData_2798_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_state_2799_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v_knownSize_2800_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v_messageHead_2801_);
lean_ctor_set(v_reuseFailAlloc_2821_, 5, v_userDataBytes_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*6, v_sentMessage_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*6 + 2, v_omitBody_2803_);
v___x_2810_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2812_; 
lean_ctor_set_uint8(v___x_2810_, sizeof(void*)*6 + 1, v___x_2808_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v___x_2810_);
v___x_2812_ = v___x_2795_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_reader_2786_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v_config_2787_);
lean_ctor_set(v_reuseFailAlloc_2820_, 3, v_events_2788_);
lean_ctor_set(v_reuseFailAlloc_2820_, 4, v_error_2789_);
lean_ctor_set(v_reuseFailAlloc_2820_, 5, v_instant_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2820_, sizeof(void*)*6, v_keepAlive_2791_);
lean_ctor_set_uint8(v_reuseFailAlloc_2820_, sizeof(void*)*6 + 1, v_forcedFlush_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2820_, sizeof(void*)*6 + 2, v_pullBodyStalled_2793_);
v___x_2812_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v_requestStream_2774_);
lean_ctor_set(v___x_2814_, 2, v_keepAliveTimeout_2775_);
lean_ctor_set(v___x_2814_, 3, v_currentTimeout_2776_);
lean_ctor_set(v___x_2814_, 4, v_headerTimeout_2777_);
lean_ctor_set(v___x_2814_, 5, v_response_2778_);
lean_ctor_set(v___x_2814_, 6, v___x_2813_);
lean_ctor_set(v___x_2814_, 7, v_expectData_2780_);
lean_ctor_set(v___x_2814_, 8, v_pendingHead_2782_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*9, v_requiresData_2779_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*9 + 1, v_handlerDispatched_2781_);
v___x_2815_ = 0;
v___x_2816_ = lean_box(v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2814_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2824_, lean_object* v_requestStream_2825_, lean_object* v_keepAliveTimeout_2826_, lean_object* v_currentTimeout_2827_, lean_object* v_headerTimeout_2828_, lean_object* v_response_2829_, lean_object* v_requiresData_2830_, lean_object* v_expectData_2831_, lean_object* v_handlerDispatched_2832_, lean_object* v_pendingHead_2833_, lean_object* v_____r_2834_, lean_object* v___y_2835_){
_start:
{
uint8_t v_requiresData_boxed_2836_; uint8_t v_handlerDispatched_boxed_2837_; lean_object* v_res_2838_; 
v_requiresData_boxed_2836_ = lean_unbox(v_requiresData_2830_);
v_handlerDispatched_boxed_2837_ = lean_unbox(v_handlerDispatched_2832_);
v_res_2838_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2824_, v_requestStream_2825_, v_keepAliveTimeout_2826_, v_currentTimeout_2827_, v_headerTimeout_2828_, v_response_2829_, v_requiresData_boxed_2836_, v_expectData_2831_, v_handlerDispatched_boxed_2837_, v_pendingHead_2833_, v_____r_2834_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2839_, lean_object* v_x_2840_){
_start:
{
if (lean_obj_tag(v_x_2840_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v___f_2839_);
v_a_2842_ = lean_ctor_get(v_x_2840_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2840_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2844_ = v_x_2840_;
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v_x_2840_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v_x_2840_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v_x_2840_, 1);
v___x_2852_ = lean_apply_2(v___f_2839_, v_a_2851_, lean_box(0));
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2853_, v_x_2854_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2857_, lean_object* v_val_2858_, lean_object* v___f_2859_, lean_object* v___f_2860_, lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v___f_2860_);
lean_dec_ref(v___f_2859_);
lean_dec(v_val_2858_);
lean_dec_ref(v_close_2857_);
v_a_2863_ = lean_ctor_get(v_x_2861_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_x_2861_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2865_ = v_x_2861_;
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v_x_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
}
}
else
{
lean_object* v_a_2872_; uint8_t v___x_2873_; 
v_a_2872_ = lean_ctor_get(v_x_2861_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v_x_2861_, 1);
v___x_2873_ = lean_unbox(v_a_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v___f_2860_);
v___x_2874_ = lean_apply_2(v_close_2857_, v_val_2858_, lean_box(0));
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_unbox(v_a_2872_);
lean_dec(v_a_2872_);
v___x_2877_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2875_, v___x_2876_, v___x_2874_, v___f_2859_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_dec(v_a_2872_);
lean_dec_ref(v___f_2859_);
lean_dec(v_val_2858_);
lean_dec_ref(v_close_2857_);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_apply_2(v___f_2860_, v___x_2878_, lean_box(0));
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2880_, lean_object* v_val_2881_, lean_object* v___f_2882_, lean_object* v___f_2883_, lean_object* v_x_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2880_, v_val_2881_, v___f_2882_, v___f_2883_, v_x_2884_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2887_, lean_object* v_handler_2888_, lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
lean_object* v_a_2891_; lean_object* v_onFailure_2892_; lean_object* v___x_2893_; 
v_a_2891_ = lean_ctor_get(v_x_2889_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v_x_2889_, 1);
v_onFailure_2892_ = lean_ctor_get(v_inst_2887_, 2);
lean_inc_ref(v_onFailure_2892_);
lean_dec_ref(v_inst_2887_);
v___x_2893_ = lean_apply_3(v_onFailure_2892_, v_handler_2888_, v_a_2891_, lean_box(0));
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; 
lean_dec(v_handler_2888_);
lean_dec_ref(v_inst_2887_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v_x_2889_);
return v___x_2894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2895_, lean_object* v_handler_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2895_, v_handler_2896_, v_x_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2900_, lean_object* v_____r_2901_){
_start:
{
uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2903_ = 0;
v___x_2904_ = lean_box(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_st_2900_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2908_, lean_object* v_____r_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2908_, v_____r_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2912_, lean_object* v___f_2913_, lean_object* v___f_2914_, lean_object* v_x_2915_){
_start:
{
if (lean_obj_tag(v_x_2915_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2925_; 
lean_dec_ref(v___f_2914_);
lean_dec_ref(v___f_2913_);
lean_dec_ref(v_requestStream_2912_);
v_a_2917_ = lean_ctor_get(v_x_2915_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_x_2915_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2919_ = v_x_2915_;
v_isShared_2920_ = v_isSharedCheck_2925_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v_x_2915_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2925_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
}
else
{
lean_object* v_a_2926_; uint8_t v___x_2927_; 
v_a_2926_ = lean_ctor_get(v_x_2915_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v_x_2915_, 1);
v___x_2927_ = lean_unbox(v_a_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; 
lean_dec_ref(v___f_2914_);
v___x_2928_ = l_Std_Http_Body_Stream_close(v_requestStream_2912_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_unbox(v_a_2926_);
lean_dec(v_a_2926_);
v___x_2931_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2929_, v___x_2930_, v___x_2928_, v___f_2913_);
return v___x_2931_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v_a_2926_);
lean_dec_ref(v___f_2913_);
lean_dec_ref(v_requestStream_2912_);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_apply_2(v___f_2914_, v___x_2932_, lean_box(0));
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2934_, lean_object* v___f_2935_, lean_object* v___f_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2934_, v___f_2935_, v___f_2936_, v_x_2937_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2940_, lean_object* v___f_2941_, lean_object* v___f_2942_, lean_object* v_requestStream_2943_, lean_object* v___f_2944_, lean_object* v_x_2945_){
_start:
{
if (lean_obj_tag(v_x_2945_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v___f_2944_);
lean_dec_ref(v_requestStream_2943_);
lean_dec_ref(v___f_2942_);
lean_dec_ref(v___f_2941_);
v_a_2947_ = lean_ctor_get(v_x_2945_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_x_2945_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2949_ = v_x_2945_;
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v_x_2945_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
}
}
else
{
lean_dec_ref_known(v_x_2945_, 1);
if (v_final_2940_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec_ref(v___f_2944_);
lean_dec_ref(v_requestStream_2943_);
lean_dec_ref(v___f_2942_);
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_apply_2(v___f_2941_, v___x_2956_, lean_box(0));
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; lean_object* v___f_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_6969__overap_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; 
lean_dec_ref(v___f_2941_);
v___x_2958_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2959_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2960_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2961_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2962_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2962_, 0, lean_box(0));
lean_closure_set(v___x_2962_, 1, lean_box(0));
lean_closure_set(v___x_2962_, 2, v___x_2958_);
lean_closure_set(v___x_2962_, 3, lean_box(0));
lean_closure_set(v___x_2962_, 4, lean_box(0));
lean_closure_set(v___x_2962_, 5, v___x_2961_);
lean_closure_set(v___x_2962_, 6, v___f_2942_);
v___x_6969__overap_2963_ = l_Std_Mutex_atomically___redArg(v___x_2958_, v___f_2959_, v___f_2960_, v_requestStream_2943_, v___x_2962_);
v___x_2964_ = lean_apply_1(v___x_6969__overap_2963_, lean_box(0));
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = 0;
v___x_2967_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2965_, v___x_2966_, v___x_2964_, v___f_2944_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_2968_, lean_object* v___f_2969_, lean_object* v___f_2970_, lean_object* v_requestStream_2971_, lean_object* v___f_2972_, lean_object* v_x_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v_final_boxed_2975_; lean_object* v_res_2976_; 
v_final_boxed_2975_ = lean_unbox(v_final_2968_);
v_res_2976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_2975_, v___f_2969_, v___f_2970_, v_requestStream_2971_, v___f_2972_, v_x_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2977_, lean_object* v_x_2978_){
_start:
{
if (lean_obj_tag(v_x_2978_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v_state_2977_);
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
lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3018_; 
v_isSharedCheck_3018_ = !lean_is_exclusive(v_x_2978_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v_x_2978_, 0);
lean_dec(v_unused_3019_);
v___x_2990_ = v_x_2978_;
v_isShared_2991_ = v_isSharedCheck_3018_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v_x_2978_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3018_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_machine_2992_; lean_object* v_requestStream_2993_; lean_object* v_keepAliveTimeout_2994_; lean_object* v_currentTimeout_2995_; lean_object* v_headerTimeout_2996_; lean_object* v_response_2997_; lean_object* v_respStream_2998_; uint8_t v_requiresData_2999_; lean_object* v_expectData_3000_; lean_object* v_pendingHead_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3017_; 
v_machine_2992_ = lean_ctor_get(v_state_2977_, 0);
v_requestStream_2993_ = lean_ctor_get(v_state_2977_, 1);
v_keepAliveTimeout_2994_ = lean_ctor_get(v_state_2977_, 2);
v_currentTimeout_2995_ = lean_ctor_get(v_state_2977_, 3);
v_headerTimeout_2996_ = lean_ctor_get(v_state_2977_, 4);
v_response_2997_ = lean_ctor_get(v_state_2977_, 5);
v_respStream_2998_ = lean_ctor_get(v_state_2977_, 6);
v_requiresData_2999_ = lean_ctor_get_uint8(v_state_2977_, sizeof(void*)*9);
v_expectData_3000_ = lean_ctor_get(v_state_2977_, 7);
v_pendingHead_3001_ = lean_ctor_get(v_state_2977_, 8);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_state_2977_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3003_ = v_state_2977_;
v_isShared_3004_ = v_isSharedCheck_3017_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_pendingHead_3001_);
lean_inc(v_expectData_3000_);
lean_inc(v_respStream_2998_);
lean_inc(v_response_2997_);
lean_inc(v_headerTimeout_2996_);
lean_inc(v_currentTimeout_2995_);
lean_inc(v_keepAliveTimeout_2994_);
lean_inc(v_requestStream_2993_);
lean_inc(v_machine_2992_);
lean_dec(v_state_2977_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3017_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; lean_object* v___x_3009_; 
v___x_3005_ = lean_box(52);
v___x_3006_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2992_, v___x_3005_);
v___x_3007_ = 0;
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3006_);
v___x_3009_ = v___x_3003_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_requestStream_2993_);
lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_keepAliveTimeout_2994_);
lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_currentTimeout_2995_);
lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_headerTimeout_2996_);
lean_ctor_set(v_reuseFailAlloc_3016_, 5, v_response_2997_);
lean_ctor_set(v_reuseFailAlloc_3016_, 6, v_respStream_2998_);
lean_ctor_set(v_reuseFailAlloc_3016_, 7, v_expectData_3000_);
lean_ctor_set(v_reuseFailAlloc_3016_, 8, v_pendingHead_3001_);
lean_ctor_set_uint8(v_reuseFailAlloc_3016_, sizeof(void*)*9, v_requiresData_2999_);
v___x_3009_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*9 + 1, v___x_3007_);
v___x_3010_ = lean_box(v___x_3007_);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_3011_);
v___x_3013_ = v___x_2990_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3020_, lean_object* v_x_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3020_, v_x_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3024_, lean_object* v_requestStream_3025_, lean_object* v_keepAliveTimeout_3026_, lean_object* v_currentTimeout_3027_, lean_object* v_headerTimeout_3028_, lean_object* v_response_3029_, lean_object* v_respStream_3030_, uint8_t v_requiresData_3031_, lean_object* v_expectData_3032_, lean_object* v_pendingHead_3033_, lean_object* v_____r_3034_){
_start:
{
uint8_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3036_ = 0;
v___x_3037_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3037_, 0, v_machine_3024_);
lean_ctor_set(v___x_3037_, 1, v_requestStream_3025_);
lean_ctor_set(v___x_3037_, 2, v_keepAliveTimeout_3026_);
lean_ctor_set(v___x_3037_, 3, v_currentTimeout_3027_);
lean_ctor_set(v___x_3037_, 4, v_headerTimeout_3028_);
lean_ctor_set(v___x_3037_, 5, v_response_3029_);
lean_ctor_set(v___x_3037_, 6, v_respStream_3030_);
lean_ctor_set(v___x_3037_, 7, v_expectData_3032_);
lean_ctor_set(v___x_3037_, 8, v_pendingHead_3033_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*9, v_requiresData_3031_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*9 + 1, v___x_3036_);
v___x_3038_ = lean_box(v___x_3036_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3042_, lean_object* v_requestStream_3043_, lean_object* v_keepAliveTimeout_3044_, lean_object* v_currentTimeout_3045_, lean_object* v_headerTimeout_3046_, lean_object* v_response_3047_, lean_object* v_respStream_3048_, lean_object* v_requiresData_3049_, lean_object* v_expectData_3050_, lean_object* v_pendingHead_3051_, lean_object* v_____r_3052_, lean_object* v___y_3053_){
_start:
{
uint8_t v_requiresData_boxed_3054_; lean_object* v_res_3055_; 
v_requiresData_boxed_3054_ = lean_unbox(v_requiresData_3049_);
v_res_3055_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3042_, v_requestStream_3043_, v_keepAliveTimeout_3044_, v_currentTimeout_3045_, v_headerTimeout_3046_, v_response_3047_, v_respStream_3048_, v_requiresData_boxed_3054_, v_expectData_3050_, v_pendingHead_3051_, v_____r_3052_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3056_, lean_object* v_body_3057_, lean_object* v___f_3058_, lean_object* v___f_3059_, lean_object* v_x_3060_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v___f_3059_);
lean_dec_ref(v___f_3058_);
lean_dec(v_body_3057_);
lean_dec_ref(v_close_3056_);
v_a_3062_ = lean_ctor_get(v_x_3060_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_x_3060_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3064_ = v_x_3060_;
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v_x_3060_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
}
else
{
lean_object* v_a_3071_; uint8_t v___x_3072_; 
v_a_3071_ = lean_ctor_get(v_x_3060_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v_x_3060_, 1);
v___x_3072_ = lean_unbox(v_a_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; 
lean_dec_ref(v___f_3059_);
v___x_3073_ = lean_apply_2(v_close_3056_, v_body_3057_, lean_box(0));
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_unbox(v_a_3071_);
lean_dec(v_a_3071_);
v___x_3076_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3074_, v___x_3075_, v___x_3073_, v___f_3058_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec(v_a_3071_);
lean_dec_ref(v___f_3058_);
lean_dec(v_body_3057_);
lean_dec_ref(v_close_3056_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_apply_2(v___f_3059_, v___x_3077_, lean_box(0));
return v___x_3078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3079_, lean_object* v_body_3080_, lean_object* v___f_3081_, lean_object* v___f_3082_, lean_object* v_x_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3079_, v_body_3080_, v___f_3081_, v___f_3082_, v_x_3083_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3086_, lean_object* v_keepAliveTimeout_3087_, lean_object* v_currentTimeout_3088_, lean_object* v_headerTimeout_3089_, lean_object* v_response_3090_, uint8_t v_requiresData_3091_, lean_object* v_expectData_3092_, uint8_t v___x_3093_, lean_object* v_pendingHead_3094_, lean_object* v_____x_3095_){
_start:
{
lean_object* v_snd_3097_; lean_object* v_fst_3098_; lean_object* v_fst_3099_; lean_object* v_snd_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3110_; 
v_snd_3097_ = lean_ctor_get(v_____x_3095_, 1);
lean_inc(v_snd_3097_);
v_fst_3098_ = lean_ctor_get(v_____x_3095_, 0);
lean_inc(v_fst_3098_);
lean_dec_ref(v_____x_3095_);
v_fst_3099_ = lean_ctor_get(v_snd_3097_, 0);
v_snd_3100_ = lean_ctor_get(v_snd_3097_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_snd_3097_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3102_ = v_snd_3097_;
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_snd_3100_);
lean_inc(v_fst_3099_);
lean_dec(v_snd_3097_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3104_, 0, v_fst_3098_);
lean_ctor_set(v___x_3104_, 1, v_requestStream_3086_);
lean_ctor_set(v___x_3104_, 2, v_keepAliveTimeout_3087_);
lean_ctor_set(v___x_3104_, 3, v_currentTimeout_3088_);
lean_ctor_set(v___x_3104_, 4, v_headerTimeout_3089_);
lean_ctor_set(v___x_3104_, 5, v_response_3090_);
lean_ctor_set(v___x_3104_, 6, v_fst_3099_);
lean_ctor_set(v___x_3104_, 7, v_expectData_3092_);
lean_ctor_set(v___x_3104_, 8, v_pendingHead_3094_);
lean_ctor_set_uint8(v___x_3104_, sizeof(void*)*9, v_requiresData_3091_);
lean_ctor_set_uint8(v___x_3104_, sizeof(void*)*9 + 1, v___x_3093_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3104_);
v___x_3106_ = v___x_3102_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_snd_3100_);
v___x_3106_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3111_, lean_object* v_keepAliveTimeout_3112_, lean_object* v_currentTimeout_3113_, lean_object* v_headerTimeout_3114_, lean_object* v_response_3115_, lean_object* v_requiresData_3116_, lean_object* v_expectData_3117_, lean_object* v___x_3118_, lean_object* v_pendingHead_3119_, lean_object* v_____x_3120_, lean_object* v___y_3121_){
_start:
{
uint8_t v_requiresData_boxed_3122_; uint8_t v___x_7791__boxed_3123_; lean_object* v_res_3124_; 
v_requiresData_boxed_3122_ = lean_unbox(v_requiresData_3116_);
v___x_7791__boxed_3123_ = lean_unbox(v___x_3118_);
v_res_3124_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3111_, v_keepAliveTimeout_3112_, v_currentTimeout_3113_, v_headerTimeout_3114_, v_response_3115_, v_requiresData_boxed_3122_, v_expectData_3117_, v___x_7791__boxed_3123_, v_pendingHead_3119_, v_____x_3120_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3125_, lean_object* v_x_3126_){
_start:
{
if (lean_obj_tag(v_x_3126_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v___f_3125_);
v_a_3128_ = lean_ctor_get(v_x_3126_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_x_3126_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3130_ = v_x_3126_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v_x_3126_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3138_; 
v_a_3137_ = lean_ctor_get(v_x_3126_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v_x_3126_, 1);
v___x_3138_ = lean_apply_2(v___f_3125_, v_a_3137_, lean_box(0));
return v___x_3138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3139_, lean_object* v_x_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3139_, v_x_3140_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3143_, lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3154_; 
v_a_3146_ = lean_ctor_get(v_x_3144_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_x_3144_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3148_ = v_x_3144_;
v_isShared_3149_ = v_isSharedCheck_3154_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v_x_3144_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3154_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3174_; 
v_a_3155_ = lean_ctor_get(v_x_3144_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_x_3144_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3157_ = v_x_3144_;
v_isShared_3158_ = v_isSharedCheck_3174_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v_x_3144_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3174_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_fst_3159_; lean_object* v_snd_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3173_; 
v_fst_3159_ = lean_ctor_get(v_a_3155_, 0);
v_snd_3160_ = lean_ctor_get(v_a_3155_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_a_3155_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3162_ = v_a_3155_;
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3160_);
lean_inc(v_fst_3159_);
lean_dec(v_a_3155_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_box(v___x_3143_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3164_);
lean_ctor_set(v___x_3162_, 0, v_snd_3160_);
v___x_3166_ = v___x_3162_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_snd_3160_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3167_, 0, v_fst_3159_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3167_);
v___x_3169_ = v___x_3157_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
return v___x_3170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3175_, lean_object* v_x_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v___x_7859__boxed_3178_; lean_object* v_res_3179_; 
v___x_7859__boxed_3178_ = lean_unbox(v___x_3175_);
v_res_3179_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7859__boxed_3178_, v_x_3176_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3180_, uint8_t v___x_3181_, lean_object* v_fst_3182_, lean_object* v_x_3183_){
_start:
{
if (lean_obj_tag(v_x_3183_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v_fst_3182_);
lean_dec(v_snd_3180_);
v_a_3185_ = lean_ctor_get(v_x_3183_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_x_3183_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3187_ = v_x_3183_;
v_isShared_3188_ = v_isSharedCheck_3193_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v_x_3183_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3193_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
}
else
{
lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3204_; 
v_isSharedCheck_3204_ = !lean_is_exclusive(v_x_3183_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v_x_3183_, 0);
lean_dec(v_unused_3205_);
v___x_3195_ = v_x_3183_;
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v_x_3183_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3197_ = lean_box(v___x_3181_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_snd_3180_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_fst_3182_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3199_);
v___x_3201_ = v___x_3195_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3199_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3206_, lean_object* v___x_3207_, lean_object* v_fst_3208_, lean_object* v_x_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v___x_7927__boxed_3211_; lean_object* v_res_3212_; 
v___x_7927__boxed_3211_ = lean_unbox(v___x_3207_);
v_res_3212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3206_, v___x_7927__boxed_3211_, v_fst_3208_, v_x_3209_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3213_, lean_object* v_handler_3214_, uint8_t v___x_3215_, lean_object* v___f_3216_, lean_object* v_x_3217_){
_start:
{
if (lean_obj_tag(v_x_3217_) == 0)
{
lean_object* v_a_3219_; lean_object* v_onFailure_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_a_3219_ = lean_ctor_get(v_x_3217_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v_x_3217_, 1);
v_onFailure_3220_ = lean_ctor_get(v_inst_3213_, 2);
lean_inc_ref(v_onFailure_3220_);
lean_dec_ref(v_inst_3213_);
v___x_3221_ = lean_apply_3(v_onFailure_3220_, v_handler_3214_, v_a_3219_, lean_box(0));
v___x_3222_ = lean_unsigned_to_nat(0u);
v___x_3223_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3222_, v___x_3215_, v___x_3221_, v___f_3216_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; 
lean_dec_ref(v___f_3216_);
lean_dec(v_handler_3214_);
lean_dec_ref(v_inst_3213_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_x_3217_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3225_, lean_object* v_handler_3226_, lean_object* v___x_3227_, lean_object* v___f_3228_, lean_object* v_x_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v___x_7985__boxed_3231_; lean_object* v_res_3232_; 
v___x_7985__boxed_3231_ = lean_unbox(v___x_3227_);
v_res_3232_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3225_, v_handler_3226_, v___x_7985__boxed_3231_, v___f_3228_, v_x_3229_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3233_, lean_object* v___f_3234_, lean_object* v_inst_3235_, lean_object* v___f_3236_, uint8_t v___x_3237_, lean_object* v_inst_3238_, lean_object* v_handler_3239_, lean_object* v___f_3240_, lean_object* v_x_3241_){
_start:
{
if (lean_obj_tag(v_x_3241_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v___f_3240_);
lean_dec(v_handler_3239_);
lean_dec_ref(v_inst_3238_);
lean_dec_ref(v___f_3236_);
lean_dec_ref(v_inst_3235_);
lean_dec_ref(v___f_3234_);
v_a_3243_ = lean_ctor_get(v_x_3241_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_x_3241_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3245_ = v_x_3241_;
v_isShared_3246_ = v_isSharedCheck_3251_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v_x_3241_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3251_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3285_; 
v_a_3252_ = lean_ctor_get(v_x_3241_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_x_3241_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3254_ = v_x_3241_;
v_isShared_3255_ = v_isSharedCheck_3285_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v_x_3241_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3285_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v_snd_3256_; 
v_snd_3256_ = lean_ctor_get(v_a_3252_, 1);
lean_inc(v_snd_3256_);
if (lean_obj_tag(v_snd_3256_) == 0)
{
lean_object* v_fst_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v___f_3240_);
lean_dec(v_handler_3239_);
lean_dec_ref(v_inst_3238_);
lean_dec_ref(v___f_3236_);
lean_dec_ref(v_inst_3235_);
v_fst_3257_ = lean_ctor_get(v_a_3252_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_a_3252_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v_a_3252_, 1);
lean_dec(v_unused_3273_);
v___x_3259_ = v_a_3252_;
v_isShared_3260_ = v_isSharedCheck_3272_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_fst_3257_);
lean_dec(v_a_3252_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3272_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3261_ = lean_box(v___x_3233_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 1, v___x_3261_);
lean_ctor_set(v___x_3259_, 0, v_snd_3256_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_snd_3256_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v_fst_3257_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3264_);
v___x_3266_ = v___x_3254_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
v___x_3268_ = lean_unsigned_to_nat(0u);
v___x_3269_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3268_, v___x_3233_, v___x_3267_, v___f_3234_);
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_fst_3274_; lean_object* v_val_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___f_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_del_object(v___x_3254_);
lean_dec_ref(v___f_3234_);
v_fst_3274_ = lean_ctor_get(v_a_3252_, 0);
lean_inc_n(v_fst_3274_, 2);
lean_dec(v_a_3252_);
v_val_3275_ = lean_ctor_get(v_snd_3256_, 0);
lean_inc(v_val_3275_);
v___x_3276_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3235_, v_fst_3274_, v_val_3275_);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3277_, v___x_3233_, v___x_3276_, v___f_3236_);
v___x_3279_ = lean_box(v___x_3237_);
v___f_3280_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3280_, 0, v_snd_3256_);
lean_closure_set(v___f_3280_, 1, v___x_3279_);
lean_closure_set(v___f_3280_, 2, v_fst_3274_);
v___x_3281_ = lean_box(v___x_3233_);
v___f_3282_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3282_, 0, v_inst_3238_);
lean_closure_set(v___f_3282_, 1, v_handler_3239_);
lean_closure_set(v___f_3282_, 2, v___x_3281_);
lean_closure_set(v___f_3282_, 3, v___f_3280_);
v___x_3283_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3277_, v___x_3233_, v___x_3278_, v___f_3282_);
v___x_3284_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3277_, v___x_3233_, v___x_3283_, v___f_3240_);
return v___x_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3286_, lean_object* v___f_3287_, lean_object* v_inst_3288_, lean_object* v___f_3289_, lean_object* v___x_3290_, lean_object* v_inst_3291_, lean_object* v_handler_3292_, lean_object* v___f_3293_, lean_object* v_x_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v___x_8010__boxed_3296_; uint8_t v___x_8014__boxed_3297_; lean_object* v_res_3298_; 
v___x_8010__boxed_3296_ = lean_unbox(v___x_3286_);
v___x_8014__boxed_3297_ = lean_unbox(v___x_3290_);
v_res_3298_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8010__boxed_3296_, v___f_3287_, v_inst_3288_, v___f_3289_, v___x_8014__boxed_3297_, v_inst_3291_, v_handler_3292_, v___f_3293_, v_x_3294_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3299_, lean_object* v_x_3300_){
_start:
{
if (lean_obj_tag(v_x_3300_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_state_3299_);
v_a_3302_ = lean_ctor_get(v_x_3300_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_x_3300_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3304_ = v_x_3300_;
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v_x_3300_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
}
}
else
{
lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3340_; 
v_isSharedCheck_3340_ = !lean_is_exclusive(v_x_3300_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; 
v_unused_3341_ = lean_ctor_get(v_x_3300_, 0);
lean_dec(v_unused_3341_);
v___x_3312_ = v_x_3300_;
v_isShared_3313_ = v_isSharedCheck_3340_;
goto v_resetjp_3311_;
}
else
{
lean_dec(v_x_3300_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3340_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v_machine_3314_; lean_object* v_requestStream_3315_; lean_object* v_keepAliveTimeout_3316_; lean_object* v_currentTimeout_3317_; lean_object* v_headerTimeout_3318_; lean_object* v_response_3319_; lean_object* v_respStream_3320_; uint8_t v_requiresData_3321_; lean_object* v_expectData_3322_; lean_object* v_pendingHead_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3339_; 
v_machine_3314_ = lean_ctor_get(v_state_3299_, 0);
v_requestStream_3315_ = lean_ctor_get(v_state_3299_, 1);
v_keepAliveTimeout_3316_ = lean_ctor_get(v_state_3299_, 2);
v_currentTimeout_3317_ = lean_ctor_get(v_state_3299_, 3);
v_headerTimeout_3318_ = lean_ctor_get(v_state_3299_, 4);
v_response_3319_ = lean_ctor_get(v_state_3299_, 5);
v_respStream_3320_ = lean_ctor_get(v_state_3299_, 6);
v_requiresData_3321_ = lean_ctor_get_uint8(v_state_3299_, sizeof(void*)*9);
v_expectData_3322_ = lean_ctor_get(v_state_3299_, 7);
v_pendingHead_3323_ = lean_ctor_get(v_state_3299_, 8);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_state_3299_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3325_ = v_state_3299_;
v_isShared_3326_ = v_isSharedCheck_3339_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_pendingHead_3323_);
lean_inc(v_expectData_3322_);
lean_inc(v_respStream_3320_);
lean_inc(v_response_3319_);
lean_inc(v_headerTimeout_3318_);
lean_inc(v_currentTimeout_3317_);
lean_inc(v_keepAliveTimeout_3316_);
lean_inc(v_requestStream_3315_);
lean_inc(v_machine_3314_);
lean_dec(v_state_3299_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3339_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; lean_object* v___x_3331_; 
v___x_3327_ = lean_box(31);
v___x_3328_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3314_, v___x_3327_);
v___x_3329_ = 0;
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3328_);
v___x_3331_ = v___x_3325_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_requestStream_3315_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_keepAliveTimeout_3316_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_currentTimeout_3317_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v_headerTimeout_3318_);
lean_ctor_set(v_reuseFailAlloc_3338_, 5, v_response_3319_);
lean_ctor_set(v_reuseFailAlloc_3338_, 6, v_respStream_3320_);
lean_ctor_set(v_reuseFailAlloc_3338_, 7, v_expectData_3322_);
lean_ctor_set(v_reuseFailAlloc_3338_, 8, v_pendingHead_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3338_, sizeof(void*)*9, v_requiresData_3321_);
v___x_3331_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*9 + 1, v___x_3329_);
v___x_3332_ = lean_box(v___x_3329_);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3333_);
v___x_3335_ = v___x_3312_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
return v___x_3336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3342_, lean_object* v_x_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3342_, v_x_3343_);
return v_res_3345_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3351_ = lean_mk_io_user_error(v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_handler_3354_, lean_object* v_config_3355_, lean_object* v_event_3356_, lean_object* v_state_3357_){
_start:
{
switch(lean_obj_tag(v_event_3356_))
{
case 0:
{
lean_object* v_x_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_handler_3354_);
lean_dec_ref(v_inst_3353_);
lean_dec_ref(v_inst_3352_);
v_x_3359_ = lean_ctor_get(v_event_3356_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_event_3356_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3361_ = v_event_3356_;
v_isShared_3362_ = v_isSharedCheck_3466_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_x_3359_);
lean_dec(v_event_3356_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3466_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
if (lean_obj_tag(v_x_3359_) == 0)
{
lean_object* v_machine_3363_; lean_object* v_reader_3364_; lean_object* v_requestStream_3365_; lean_object* v_keepAliveTimeout_3366_; lean_object* v_currentTimeout_3367_; lean_object* v_headerTimeout_3368_; lean_object* v_response_3369_; lean_object* v_respStream_3370_; uint8_t v_requiresData_3371_; lean_object* v_expectData_3372_; uint8_t v_handlerDispatched_3373_; lean_object* v_pendingHead_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v_config_3355_);
v_machine_3363_ = lean_ctor_get(v_state_3357_, 0);
lean_inc_ref(v_machine_3363_);
v_reader_3364_ = lean_ctor_get(v_machine_3363_, 0);
lean_inc_ref(v_reader_3364_);
v_requestStream_3365_ = lean_ctor_get(v_state_3357_, 1);
v_keepAliveTimeout_3366_ = lean_ctor_get(v_state_3357_, 2);
v_currentTimeout_3367_ = lean_ctor_get(v_state_3357_, 3);
v_headerTimeout_3368_ = lean_ctor_get(v_state_3357_, 4);
v_response_3369_ = lean_ctor_get(v_state_3357_, 5);
v_respStream_3370_ = lean_ctor_get(v_state_3357_, 6);
v_requiresData_3371_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3372_ = lean_ctor_get(v_state_3357_, 7);
v_handlerDispatched_3373_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9 + 1);
v_pendingHead_3374_ = lean_ctor_get(v_state_3357_, 8);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_state_3357_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v_state_3357_, 0);
lean_dec(v_unused_3418_);
v___x_3376_ = v_state_3357_;
v_isShared_3377_ = v_isSharedCheck_3417_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_pendingHead_3374_);
lean_inc(v_expectData_3372_);
lean_inc(v_respStream_3370_);
lean_inc(v_response_3369_);
lean_inc(v_headerTimeout_3368_);
lean_inc(v_currentTimeout_3367_);
lean_inc(v_keepAliveTimeout_3366_);
lean_inc(v_requestStream_3365_);
lean_dec(v_state_3357_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3417_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_writer_3378_; lean_object* v_config_3379_; lean_object* v_events_3380_; lean_object* v_error_3381_; lean_object* v_instant_3382_; uint8_t v_keepAlive_3383_; uint8_t v_forcedFlush_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3415_; 
v_writer_3378_ = lean_ctor_get(v_machine_3363_, 1);
v_config_3379_ = lean_ctor_get(v_machine_3363_, 2);
v_events_3380_ = lean_ctor_get(v_machine_3363_, 3);
v_error_3381_ = lean_ctor_get(v_machine_3363_, 4);
v_instant_3382_ = lean_ctor_get(v_machine_3363_, 5);
v_keepAlive_3383_ = lean_ctor_get_uint8(v_machine_3363_, sizeof(void*)*6);
v_forcedFlush_3384_ = lean_ctor_get_uint8(v_machine_3363_, sizeof(void*)*6 + 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_machine_3363_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v_machine_3363_, 0);
lean_dec(v_unused_3416_);
v___x_3386_ = v_machine_3363_;
v_isShared_3387_ = v_isSharedCheck_3415_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_instant_3382_);
lean_inc(v_error_3381_);
lean_inc(v_events_3380_);
lean_inc(v_config_3379_);
lean_inc(v_writer_3378_);
lean_dec(v_machine_3363_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3415_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_state_3388_; lean_object* v_input_3389_; lean_object* v_messageHead_3390_; lean_object* v_messageCount_3391_; lean_object* v_bodyBytesRead_3392_; lean_object* v_headerBytesRead_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3414_; 
v_state_3388_ = lean_ctor_get(v_reader_3364_, 0);
v_input_3389_ = lean_ctor_get(v_reader_3364_, 1);
v_messageHead_3390_ = lean_ctor_get(v_reader_3364_, 2);
v_messageCount_3391_ = lean_ctor_get(v_reader_3364_, 3);
v_bodyBytesRead_3392_ = lean_ctor_get(v_reader_3364_, 4);
v_headerBytesRead_3393_ = lean_ctor_get(v_reader_3364_, 5);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_reader_3364_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3395_ = v_reader_3364_;
v_isShared_3396_ = v_isSharedCheck_3414_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_headerBytesRead_3393_);
lean_inc(v_bodyBytesRead_3392_);
lean_inc(v_messageCount_3391_);
lean_inc(v_messageHead_3390_);
lean_inc(v_input_3389_);
lean_inc(v_state_3388_);
lean_dec(v_reader_3364_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3414_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
uint8_t v___x_3397_; lean_object* v___x_3399_; 
v___x_3397_ = 1;
if (v_isShared_3396_ == 0)
{
v___x_3399_ = v___x_3395_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_state_3388_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_input_3389_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_messageHead_3390_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_messageCount_3391_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v_bodyBytesRead_3392_);
lean_ctor_set(v_reuseFailAlloc_3413_, 5, v_headerBytesRead_3393_);
v___x_3399_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
uint8_t v___x_3400_; lean_object* v___x_3402_; 
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*6, v___x_3397_);
v___x_3400_ = 0;
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3399_);
v___x_3402_ = v___x_3386_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_writer_3378_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_config_3379_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_events_3380_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_error_3381_);
lean_ctor_set(v_reuseFailAlloc_3412_, 5, v_instant_3382_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*6, v_keepAlive_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*6 + 1, v_forcedFlush_3384_);
v___x_3402_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
lean_ctor_set_uint8(v___x_3402_, sizeof(void*)*6 + 2, v___x_3400_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3402_);
v___x_3404_ = v___x_3376_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_requestStream_3365_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_keepAliveTimeout_3366_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_currentTimeout_3367_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v_headerTimeout_3368_);
lean_ctor_set(v_reuseFailAlloc_3411_, 5, v_response_3369_);
lean_ctor_set(v_reuseFailAlloc_3411_, 6, v_respStream_3370_);
lean_ctor_set(v_reuseFailAlloc_3411_, 7, v_expectData_3372_);
lean_ctor_set(v_reuseFailAlloc_3411_, 8, v_pendingHead_3374_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*9, v_requiresData_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*9 + 1, v_handlerDispatched_3373_);
v___x_3404_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3405_ = lean_box(v___x_3400_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set_tag(v___x_3361_, 1);
lean_ctor_set(v___x_3361_, 0, v___x_3406_);
v___x_3408_ = v___x_3361_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3406_);
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
}
}
}
}
}
else
{
lean_object* v_val_3419_; lean_object* v_machine_3420_; lean_object* v_requestStream_3421_; lean_object* v_keepAliveTimeout_3422_; lean_object* v_currentTimeout_3423_; lean_object* v_response_3424_; lean_object* v_respStream_3425_; uint8_t v_requiresData_3426_; lean_object* v_expectData_3427_; uint8_t v_handlerDispatched_3428_; lean_object* v_pendingHead_3429_; lean_object* v___f_3430_; 
lean_del_object(v___x_3361_);
v_val_3419_ = lean_ctor_get(v_x_3359_, 0);
lean_inc_n(v_val_3419_, 2);
lean_dec_ref_known(v_x_3359_, 1);
v_machine_3420_ = lean_ctor_get(v_state_3357_, 0);
v_requestStream_3421_ = lean_ctor_get(v_state_3357_, 1);
v_keepAliveTimeout_3422_ = lean_ctor_get(v_state_3357_, 2);
lean_inc(v_keepAliveTimeout_3422_);
v_currentTimeout_3423_ = lean_ctor_get(v_state_3357_, 3);
v_response_3424_ = lean_ctor_get(v_state_3357_, 5);
v_respStream_3425_ = lean_ctor_get(v_state_3357_, 6);
v_requiresData_3426_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3427_ = lean_ctor_get(v_state_3357_, 7);
v_handlerDispatched_3428_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9 + 1);
v_pendingHead_3429_ = lean_ctor_get(v_state_3357_, 8);
v___f_3430_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3430_, 0, v_val_3419_);
if (lean_obj_tag(v_keepAliveTimeout_3422_) == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_dec_ref(v___f_3430_);
lean_dec_ref(v_config_3355_);
v___x_3431_ = lean_box(0);
v___x_3432_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3419_, v___x_3431_, v_state_3357_);
return v___x_3432_;
}
else
{
lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3464_; 
lean_inc(v_pendingHead_3429_);
lean_inc(v_expectData_3427_);
lean_inc(v_respStream_3425_);
lean_inc_ref(v_response_3424_);
lean_inc(v_currentTimeout_3423_);
lean_inc_ref(v_requestStream_3421_);
lean_inc_ref(v_machine_3420_);
lean_dec(v_val_3419_);
lean_dec_ref(v_state_3357_);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_keepAliveTimeout_3422_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; 
v_unused_3465_ = lean_ctor_get(v_keepAliveTimeout_3422_, 0);
lean_dec(v_unused_3465_);
v___x_3434_ = v_keepAliveTimeout_3422_;
v_isShared_3435_ = v_isSharedCheck_3464_;
goto v_resetjp_3433_;
}
else
{
lean_dec(v_keepAliveTimeout_3422_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3464_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; lean_object* v_val_3440_; lean_object* v___x_3447_; 
v___x_3436_ = lean_box(v_requiresData_3426_);
v___x_3437_ = lean_box(v_handlerDispatched_3428_);
v___f_3438_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3438_, 0, v_config_3355_);
lean_closure_set(v___f_3438_, 1, v_machine_3420_);
lean_closure_set(v___f_3438_, 2, v_requestStream_3421_);
lean_closure_set(v___f_3438_, 3, v_currentTimeout_3423_);
lean_closure_set(v___f_3438_, 4, v_response_3424_);
lean_closure_set(v___f_3438_, 5, v_respStream_3425_);
lean_closure_set(v___f_3438_, 6, v___x_3436_);
lean_closure_set(v___f_3438_, 7, v_expectData_3427_);
lean_closure_set(v___f_3438_, 8, v___x_3437_);
lean_closure_set(v___f_3438_, 9, v_pendingHead_3429_);
lean_closure_set(v___f_3438_, 10, v___f_3430_);
v___x_3447_ = lean_get_current_time();
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 1);
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
v_val_3440_ = v___x_3453_;
goto v___jp_3439_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
v_a_3456_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3447_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3447_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 0);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
v_val_3440_ = v___x_3461_;
goto v___jp_3439_;
}
}
}
v___jp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 0);
lean_ctor_set(v___x_3434_, 0, v_val_3440_);
v___x_3442_ = v___x_3434_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_val_3440_);
v___x_3442_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; uint8_t v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = 0;
v___x_3445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3443_, v___x_3444_, v___x_3442_, v___f_3438_);
return v___x_3445_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v_config_3355_);
lean_dec(v_handler_3354_);
lean_dec_ref(v_inst_3352_);
v_x_3467_ = lean_ctor_get(v_event_3356_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_event_3356_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3469_ = v_event_3356_;
v_isShared_3470_ = v_isSharedCheck_3578_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_x_3467_);
lean_dec(v_event_3356_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3578_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
if (lean_obj_tag(v_x_3467_) == 0)
{
lean_object* v_machine_3471_; lean_object* v_requestStream_3472_; lean_object* v_keepAliveTimeout_3473_; lean_object* v_currentTimeout_3474_; lean_object* v_headerTimeout_3475_; lean_object* v_response_3476_; lean_object* v_respStream_3477_; uint8_t v_requiresData_3478_; lean_object* v_expectData_3479_; uint8_t v_handlerDispatched_3480_; lean_object* v_pendingHead_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___f_3484_; 
lean_del_object(v___x_3469_);
v_machine_3471_ = lean_ctor_get(v_state_3357_, 0);
lean_inc_ref_n(v_machine_3471_, 2);
v_requestStream_3472_ = lean_ctor_get(v_state_3357_, 1);
lean_inc_ref_n(v_requestStream_3472_, 2);
v_keepAliveTimeout_3473_ = lean_ctor_get(v_state_3357_, 2);
lean_inc_n(v_keepAliveTimeout_3473_, 2);
v_currentTimeout_3474_ = lean_ctor_get(v_state_3357_, 3);
lean_inc_n(v_currentTimeout_3474_, 2);
v_headerTimeout_3475_ = lean_ctor_get(v_state_3357_, 4);
lean_inc_n(v_headerTimeout_3475_, 2);
v_response_3476_ = lean_ctor_get(v_state_3357_, 5);
lean_inc_ref_n(v_response_3476_, 2);
v_respStream_3477_ = lean_ctor_get(v_state_3357_, 6);
lean_inc(v_respStream_3477_);
v_requiresData_3478_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3479_ = lean_ctor_get(v_state_3357_, 7);
lean_inc_n(v_expectData_3479_, 2);
v_handlerDispatched_3480_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9 + 1);
v_pendingHead_3481_ = lean_ctor_get(v_state_3357_, 8);
lean_inc_n(v_pendingHead_3481_, 2);
lean_dec_ref(v_state_3357_);
v___x_3482_ = lean_box(v_requiresData_3478_);
v___x_3483_ = lean_box(v_handlerDispatched_3480_);
v___f_3484_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3484_, 0, v_machine_3471_);
lean_closure_set(v___f_3484_, 1, v_requestStream_3472_);
lean_closure_set(v___f_3484_, 2, v_keepAliveTimeout_3473_);
lean_closure_set(v___f_3484_, 3, v_currentTimeout_3474_);
lean_closure_set(v___f_3484_, 4, v_headerTimeout_3475_);
lean_closure_set(v___f_3484_, 5, v_response_3476_);
lean_closure_set(v___f_3484_, 6, v___x_3482_);
lean_closure_set(v___f_3484_, 7, v_expectData_3479_);
lean_closure_set(v___f_3484_, 8, v___x_3483_);
lean_closure_set(v___f_3484_, 9, v_pendingHead_3481_);
if (lean_obj_tag(v_respStream_3477_) == 1)
{
lean_object* v_val_3485_; lean_object* v_close_3486_; lean_object* v_isClosed_3487_; lean_object* v___x_3488_; lean_object* v___f_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; 
lean_dec(v_pendingHead_3481_);
lean_dec(v_expectData_3479_);
lean_dec_ref(v_response_3476_);
lean_dec(v_headerTimeout_3475_);
lean_dec(v_currentTimeout_3474_);
lean_dec(v_keepAliveTimeout_3473_);
lean_dec_ref(v_requestStream_3472_);
lean_dec_ref(v_machine_3471_);
v_val_3485_ = lean_ctor_get(v_respStream_3477_, 0);
lean_inc_n(v_val_3485_, 2);
lean_dec_ref_known(v_respStream_3477_, 1);
v_close_3486_ = lean_ctor_get(v_inst_3353_, 1);
lean_inc_ref(v_close_3486_);
v_isClosed_3487_ = lean_ctor_get(v_inst_3353_, 2);
lean_inc_ref(v_isClosed_3487_);
lean_dec_ref(v_inst_3353_);
v___x_3488_ = lean_apply_2(v_isClosed_3487_, v_val_3485_, lean_box(0));
lean_inc_ref(v___f_3484_);
v___f_3489_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3489_, 0, v___f_3484_);
v___f_3490_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3490_, 0, v_close_3486_);
lean_closure_set(v___f_3490_, 1, v_val_3485_);
lean_closure_set(v___f_3490_, 2, v___f_3489_);
lean_closure_set(v___f_3490_, 3, v___f_3484_);
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = 0;
v___x_3493_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3491_, v___x_3492_, v___x_3488_, v___f_3490_);
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_dec_ref(v___f_3484_);
lean_dec(v_respStream_3477_);
lean_dec_ref(v_inst_3353_);
v___x_3494_ = lean_box(0);
v___x_3495_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3471_, v_requestStream_3472_, v_keepAliveTimeout_3473_, v_currentTimeout_3474_, v_headerTimeout_3475_, v_response_3476_, v_requiresData_3478_, v_expectData_3479_, v_handlerDispatched_3480_, v_pendingHead_3481_, v___x_3494_);
return v___x_3495_;
}
}
else
{
lean_object* v_val_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v_inst_3353_);
v_val_3496_ = lean_ctor_get(v_x_3467_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_x_3467_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3498_ = v_x_3467_;
v_isShared_3499_ = v_isSharedCheck_3577_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_val_3496_);
lean_dec(v_x_3467_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3577_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_machine_3500_; lean_object* v_requestStream_3501_; lean_object* v_keepAliveTimeout_3502_; lean_object* v_currentTimeout_3503_; lean_object* v_headerTimeout_3504_; lean_object* v_response_3505_; lean_object* v_respStream_3506_; uint8_t v_requiresData_3507_; lean_object* v_expectData_3508_; uint8_t v_handlerDispatched_3509_; lean_object* v_pendingHead_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3576_; 
v_machine_3500_ = lean_ctor_get(v_state_3357_, 0);
v_requestStream_3501_ = lean_ctor_get(v_state_3357_, 1);
v_keepAliveTimeout_3502_ = lean_ctor_get(v_state_3357_, 2);
v_currentTimeout_3503_ = lean_ctor_get(v_state_3357_, 3);
v_headerTimeout_3504_ = lean_ctor_get(v_state_3357_, 4);
v_response_3505_ = lean_ctor_get(v_state_3357_, 5);
v_respStream_3506_ = lean_ctor_get(v_state_3357_, 6);
v_requiresData_3507_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3508_ = lean_ctor_get(v_state_3357_, 7);
v_handlerDispatched_3509_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9 + 1);
v_pendingHead_3510_ = lean_ctor_get(v_state_3357_, 8);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_state_3357_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3512_ = v_state_3357_;
v_isShared_3513_ = v_isSharedCheck_3576_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_pendingHead_3510_);
lean_inc(v_expectData_3508_);
lean_inc(v_respStream_3506_);
lean_inc(v_response_3505_);
lean_inc(v_headerTimeout_3504_);
lean_inc(v_currentTimeout_3503_);
lean_inc(v_keepAliveTimeout_3502_);
lean_inc(v_requestStream_3501_);
lean_inc(v_machine_3500_);
lean_dec(v_state_3357_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3576_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___y_3515_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3528_ = lean_unsigned_to_nat(1u);
v___x_3529_ = lean_mk_empty_array_with_capacity(v___x_3528_);
v___x_3530_ = lean_array_push(v___x_3529_, v_val_3496_);
v___x_3531_ = lean_array_get_size(v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = lean_nat_dec_eq(v___x_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v_reader_3534_; lean_object* v_writer_3535_; lean_object* v_config_3536_; lean_object* v_events_3537_; lean_object* v_error_3538_; lean_object* v_instant_3539_; uint8_t v_keepAlive_3540_; uint8_t v_forcedFlush_3541_; uint8_t v_pullBodyStalled_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3575_; 
v_reader_3534_ = lean_ctor_get(v_machine_3500_, 0);
v_writer_3535_ = lean_ctor_get(v_machine_3500_, 1);
v_config_3536_ = lean_ctor_get(v_machine_3500_, 2);
v_events_3537_ = lean_ctor_get(v_machine_3500_, 3);
v_error_3538_ = lean_ctor_get(v_machine_3500_, 4);
v_instant_3539_ = lean_ctor_get(v_machine_3500_, 5);
v_keepAlive_3540_ = lean_ctor_get_uint8(v_machine_3500_, sizeof(void*)*6);
v_forcedFlush_3541_ = lean_ctor_get_uint8(v_machine_3500_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3542_ = lean_ctor_get_uint8(v_machine_3500_, sizeof(void*)*6 + 2);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_machine_3500_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3544_ = v_machine_3500_;
v_isShared_3545_ = v_isSharedCheck_3575_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_instant_3539_);
lean_inc(v_error_3538_);
lean_inc(v_events_3537_);
lean_inc(v_config_3536_);
lean_inc(v_writer_3535_);
lean_inc(v_reader_3534_);
lean_dec(v_machine_3500_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3575_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___y_3547_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3569_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_3570_ = lean_nat_dec_lt(v___x_3532_, v___x_3531_);
if (v___x_3570_ == 0)
{
v___y_3547_ = v___x_3532_;
goto v___jp_3546_;
}
else
{
lean_object* v___f_3571_; size_t v___x_3572_; size_t v___x_3573_; lean_object* v___x_3574_; 
v___f_3571_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3572_ = ((size_t)0ULL);
v___x_3573_ = lean_usize_of_nat(v___x_3531_);
lean_inc_ref(v___x_3530_);
v___x_3574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3569_, v___f_3571_, v___x_3530_, v___x_3572_, v___x_3573_, v___x_3532_);
v___y_3547_ = v___x_3574_;
goto v___jp_3546_;
}
v___jp_3546_:
{
lean_object* v_userData_3548_; lean_object* v_outputData_3549_; lean_object* v_state_3550_; lean_object* v_knownSize_3551_; lean_object* v_messageHead_3552_; uint8_t v_sentMessage_3553_; uint8_t v_userClosedBody_3554_; uint8_t v_omitBody_3555_; lean_object* v_userDataBytes_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3568_; 
v_userData_3548_ = lean_ctor_get(v_writer_3535_, 0);
v_outputData_3549_ = lean_ctor_get(v_writer_3535_, 1);
v_state_3550_ = lean_ctor_get(v_writer_3535_, 2);
v_knownSize_3551_ = lean_ctor_get(v_writer_3535_, 3);
v_messageHead_3552_ = lean_ctor_get(v_writer_3535_, 4);
v_sentMessage_3553_ = lean_ctor_get_uint8(v_writer_3535_, sizeof(void*)*6);
v_userClosedBody_3554_ = lean_ctor_get_uint8(v_writer_3535_, sizeof(void*)*6 + 1);
v_omitBody_3555_ = lean_ctor_get_uint8(v_writer_3535_, sizeof(void*)*6 + 2);
v_userDataBytes_3556_ = lean_ctor_get(v_writer_3535_, 5);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_writer_3535_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3558_ = v_writer_3535_;
v_isShared_3559_ = v_isSharedCheck_3568_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_userDataBytes_3556_);
lean_inc(v_messageHead_3552_);
lean_inc(v_knownSize_3551_);
lean_inc(v_state_3550_);
lean_inc(v_outputData_3549_);
lean_inc(v_userData_3548_);
lean_dec(v_writer_3535_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3568_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3560_ = l_Array_append___redArg(v_userData_3548_, v___x_3530_);
lean_dec_ref(v___x_3530_);
v___x_3561_ = lean_nat_add(v_userDataBytes_3556_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec(v_userDataBytes_3556_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 5, v___x_3561_);
lean_ctor_set(v___x_3558_, 0, v___x_3560_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_outputData_3549_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_state_3550_);
lean_ctor_set(v_reuseFailAlloc_3567_, 3, v_knownSize_3551_);
lean_ctor_set(v_reuseFailAlloc_3567_, 4, v_messageHead_3552_);
lean_ctor_set(v_reuseFailAlloc_3567_, 5, v___x_3561_);
lean_ctor_set_uint8(v_reuseFailAlloc_3567_, sizeof(void*)*6, v_sentMessage_3553_);
lean_ctor_set_uint8(v_reuseFailAlloc_3567_, sizeof(void*)*6 + 1, v_userClosedBody_3554_);
lean_ctor_set_uint8(v_reuseFailAlloc_3567_, sizeof(void*)*6 + 2, v_omitBody_3555_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v___x_3563_);
v___x_3565_ = v___x_3544_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_reader_3534_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_config_3536_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_events_3537_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v_error_3538_);
lean_ctor_set(v_reuseFailAlloc_3566_, 5, v_instant_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3566_, sizeof(void*)*6, v_keepAlive_3540_);
lean_ctor_set_uint8(v_reuseFailAlloc_3566_, sizeof(void*)*6 + 1, v_forcedFlush_3541_);
lean_ctor_set_uint8(v_reuseFailAlloc_3566_, sizeof(void*)*6 + 2, v_pullBodyStalled_3542_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
v___y_3515_ = v___x_3565_;
goto v___jp_3514_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3530_);
v___y_3515_ = v_machine_3500_;
goto v___jp_3514_;
}
v___jp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___y_3515_);
v___x_3517_ = v___x_3512_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___y_3515_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_requestStream_3501_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_keepAliveTimeout_3502_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_currentTimeout_3503_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_headerTimeout_3504_);
lean_ctor_set(v_reuseFailAlloc_3527_, 5, v_response_3505_);
lean_ctor_set(v_reuseFailAlloc_3527_, 6, v_respStream_3506_);
lean_ctor_set(v_reuseFailAlloc_3527_, 7, v_expectData_3508_);
lean_ctor_set(v_reuseFailAlloc_3527_, 8, v_pendingHead_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*9, v_requiresData_3507_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*9 + 1, v_handlerDispatched_3509_);
v___x_3517_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3518_ = 0;
v___x_3519_ = lean_box(v___x_3518_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3517_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3520_);
v___x_3522_ = v___x_3498_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3522_);
v___x_3524_ = v___x_3469_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
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
uint8_t v_x_3579_; 
lean_dec_ref(v_config_3355_);
lean_dec_ref(v_inst_3353_);
v_x_3579_ = lean_ctor_get_uint8(v_event_3356_, 0);
lean_dec_ref_known(v_event_3356_, 0);
if (v_x_3579_ == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec(v_handler_3354_);
lean_dec_ref(v_inst_3352_);
v___x_3580_ = lean_box(v_x_3579_);
v___x_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3581_, 0, v_state_3357_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
return v___x_3583_;
}
else
{
lean_object* v_machine_3584_; lean_object* v_requestStream_3585_; lean_object* v_keepAliveTimeout_3586_; lean_object* v_currentTimeout_3587_; lean_object* v_headerTimeout_3588_; lean_object* v_response_3589_; lean_object* v_respStream_3590_; uint8_t v_requiresData_3591_; lean_object* v_expectData_3592_; uint8_t v_handlerDispatched_3593_; lean_object* v_pendingHead_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3644_; 
v_machine_3584_ = lean_ctor_get(v_state_3357_, 0);
v_requestStream_3585_ = lean_ctor_get(v_state_3357_, 1);
v_keepAliveTimeout_3586_ = lean_ctor_get(v_state_3357_, 2);
v_currentTimeout_3587_ = lean_ctor_get(v_state_3357_, 3);
v_headerTimeout_3588_ = lean_ctor_get(v_state_3357_, 4);
v_response_3589_ = lean_ctor_get(v_state_3357_, 5);
v_respStream_3590_ = lean_ctor_get(v_state_3357_, 6);
v_requiresData_3591_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3592_ = lean_ctor_get(v_state_3357_, 7);
v_handlerDispatched_3593_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9 + 1);
v_pendingHead_3594_ = lean_ctor_get(v_state_3357_, 8);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_state_3357_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3596_ = v_state_3357_;
v_isShared_3597_ = v_isSharedCheck_3644_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_pendingHead_3594_);
lean_inc(v_expectData_3592_);
lean_inc(v_respStream_3590_);
lean_inc(v_response_3589_);
lean_inc(v_headerTimeout_3588_);
lean_inc(v_currentTimeout_3587_);
lean_inc(v_keepAliveTimeout_3586_);
lean_inc(v_requestStream_3585_);
lean_inc(v_machine_3584_);
lean_dec(v_state_3357_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3644_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v_fst_3600_; lean_object* v_snd_3601_; lean_object* v_reader_3602_; lean_object* v_writer_3603_; lean_object* v_config_3604_; lean_object* v_events_3605_; lean_object* v_error_3606_; lean_object* v_instant_3607_; uint8_t v_keepAlive_3608_; uint8_t v_forcedFlush_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3643_; 
v___x_3598_ = 0;
v___x_3599_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3598_, v_machine_3584_);
v_fst_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_fst_3600_);
v_snd_3601_ = lean_ctor_get(v___x_3599_, 1);
lean_inc(v_snd_3601_);
lean_dec_ref(v___x_3599_);
v_reader_3602_ = lean_ctor_get(v_fst_3600_, 0);
v_writer_3603_ = lean_ctor_get(v_fst_3600_, 1);
v_config_3604_ = lean_ctor_get(v_fst_3600_, 2);
v_events_3605_ = lean_ctor_get(v_fst_3600_, 3);
v_error_3606_ = lean_ctor_get(v_fst_3600_, 4);
v_instant_3607_ = lean_ctor_get(v_fst_3600_, 5);
v_keepAlive_3608_ = lean_ctor_get_uint8(v_fst_3600_, sizeof(void*)*6);
v_forcedFlush_3609_ = lean_ctor_get_uint8(v_fst_3600_, sizeof(void*)*6 + 1);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_fst_3600_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3611_ = v_fst_3600_;
v_isShared_3612_ = v_isSharedCheck_3643_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_instant_3607_);
lean_inc(v_error_3606_);
lean_inc(v_events_3605_);
lean_inc(v_config_3604_);
lean_inc(v_writer_3603_);
lean_inc(v_reader_3602_);
lean_dec(v_fst_3600_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3643_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___f_3613_; lean_object* v___f_3614_; uint8_t v___y_3616_; 
v___f_3613_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3613_, 0, v_inst_3352_);
lean_closure_set(v___f_3613_, 1, v_handler_3354_);
v___f_3614_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3601_) == 0)
{
uint8_t v_sentMessage_3639_; 
v_sentMessage_3639_ = lean_ctor_get_uint8(v_writer_3603_, sizeof(void*)*6);
if (v_sentMessage_3639_ == 0)
{
lean_object* v_state_3640_; 
v_state_3640_ = lean_ctor_get(v_reader_3602_, 0);
if (lean_obj_tag(v_state_3640_) == 2)
{
v___y_3616_ = v_x_3579_;
goto v___jp_3615_;
}
else
{
v___y_3616_ = v_sentMessage_3639_;
goto v___jp_3615_;
}
}
else
{
uint8_t v___x_3641_; 
v___x_3641_ = 0;
v___y_3616_ = v___x_3641_;
goto v___jp_3615_;
}
}
else
{
uint8_t v___x_3642_; 
v___x_3642_ = 0;
v___y_3616_ = v___x_3642_;
goto v___jp_3615_;
}
v___jp_3615_:
{
lean_object* v___x_3618_; 
if (v_isShared_3612_ == 0)
{
v___x_3618_ = v___x_3611_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_reader_3602_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_writer_3603_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_config_3604_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v_events_3605_);
lean_ctor_set(v_reuseFailAlloc_3638_, 4, v_error_3606_);
lean_ctor_set(v_reuseFailAlloc_3638_, 5, v_instant_3607_);
lean_ctor_set_uint8(v_reuseFailAlloc_3638_, sizeof(void*)*6, v_keepAlive_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3638_, sizeof(void*)*6 + 1, v_forcedFlush_3609_);
v___x_3618_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v_st_3620_; 
lean_ctor_set_uint8(v___x_3618_, sizeof(void*)*6 + 2, v___y_3616_);
lean_inc_ref(v_requestStream_3585_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 0, v___x_3618_);
v_st_3620_ = v___x_3596_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_requestStream_3585_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_keepAliveTimeout_3586_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_currentTimeout_3587_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_headerTimeout_3588_);
lean_ctor_set(v_reuseFailAlloc_3637_, 5, v_response_3589_);
lean_ctor_set(v_reuseFailAlloc_3637_, 6, v_respStream_3590_);
lean_ctor_set(v_reuseFailAlloc_3637_, 7, v_expectData_3592_);
lean_ctor_set(v_reuseFailAlloc_3637_, 8, v_pendingHead_3594_);
lean_ctor_set_uint8(v_reuseFailAlloc_3637_, sizeof(void*)*9, v_requiresData_3591_);
lean_ctor_set_uint8(v_reuseFailAlloc_3637_, sizeof(void*)*9 + 1, v_handlerDispatched_3593_);
v_st_3620_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___f_3621_; 
lean_inc_ref(v_st_3620_);
v___f_3621_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3621_, 0, v_st_3620_);
if (lean_obj_tag(v_snd_3601_) == 1)
{
lean_object* v_val_3622_; uint8_t v_final_3623_; uint8_t v_incomplete_3624_; lean_object* v_chunk_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___f_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; lean_object* v___f_3633_; lean_object* v___x_3634_; 
lean_dec_ref(v_st_3620_);
v_val_3622_ = lean_ctor_get(v_snd_3601_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v_snd_3601_, 1);
v_final_3623_ = lean_ctor_get_uint8(v_val_3622_, sizeof(void*)*1);
v_incomplete_3624_ = lean_ctor_get_uint8(v_val_3622_, sizeof(void*)*1 + 1);
v_chunk_3625_ = lean_ctor_get(v_val_3622_, 0);
lean_inc_ref(v_chunk_3625_);
lean_dec(v_val_3622_);
lean_inc_ref_n(v_requestStream_3585_, 2);
v___x_3626_ = l_Std_Http_Body_Stream_send(v_requestStream_3585_, v_chunk_3625_, v_incomplete_3624_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = 0;
v___x_3629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3627_, v___x_3628_, v___x_3626_, v___f_3613_);
lean_inc_ref_n(v___f_3621_, 2);
v___f_3630_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3630_, 0, v___f_3621_);
v___f_3631_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3631_, 0, v_requestStream_3585_);
lean_closure_set(v___f_3631_, 1, v___f_3630_);
lean_closure_set(v___f_3631_, 2, v___f_3621_);
v___x_3632_ = lean_box(v_final_3623_);
v___f_3633_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3633_, 0, v___x_3632_);
lean_closure_set(v___f_3633_, 1, v___f_3621_);
lean_closure_set(v___f_3633_, 2, v___f_3614_);
lean_closure_set(v___f_3633_, 3, v_requestStream_3585_);
lean_closure_set(v___f_3633_, 4, v___f_3631_);
v___x_3634_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3627_, v___x_3628_, v___x_3629_, v___f_3633_);
return v___x_3634_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec_ref(v___f_3621_);
lean_dec_ref(v___f_3613_);
lean_dec(v_snd_3601_);
lean_dec_ref(v_requestStream_3585_);
v___x_3635_ = lean_box(0);
v___x_3636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3620_, v___x_3635_);
return v___x_3636_;
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
lean_object* v_x_3645_; 
v_x_3645_ = lean_ctor_get(v_event_3356_, 0);
lean_inc_ref(v_x_3645_);
lean_dec_ref_known(v_event_3356_, 1);
if (lean_obj_tag(v_x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v_onFailure_3647_; lean_object* v___x_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; 
lean_dec_ref(v_config_3355_);
lean_dec_ref(v_inst_3353_);
v_a_3646_ = lean_ctor_get(v_x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v_x_3645_, 1);
v_onFailure_3647_ = lean_ctor_get(v_inst_3352_, 2);
lean_inc_ref(v_onFailure_3647_);
lean_dec_ref(v_inst_3352_);
v___x_3648_ = lean_apply_3(v_onFailure_3647_, v_handler_3354_, v_a_3646_, lean_box(0));
v___f_3649_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3649_, 0, v_state_3357_);
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = 0;
v___x_3652_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3650_, v___x_3651_, v___x_3648_, v___f_3649_);
return v___x_3652_;
}
else
{
lean_object* v_machine_3653_; lean_object* v_reader_3654_; lean_object* v_state_3655_; 
v_machine_3653_ = lean_ctor_get(v_state_3357_, 0);
lean_inc_ref(v_machine_3653_);
v_reader_3654_ = lean_ctor_get(v_machine_3653_, 0);
v_state_3655_ = lean_ctor_get(v_reader_3654_, 0);
if (lean_obj_tag(v_state_3655_) == 7)
{
lean_object* v_a_3656_; lean_object* v_requestStream_3657_; lean_object* v_keepAliveTimeout_3658_; lean_object* v_currentTimeout_3659_; lean_object* v_headerTimeout_3660_; lean_object* v_response_3661_; lean_object* v_respStream_3662_; uint8_t v_requiresData_3663_; lean_object* v_expectData_3664_; lean_object* v_pendingHead_3665_; lean_object* v_close_3666_; lean_object* v_isClosed_3667_; lean_object* v_body_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___f_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; lean_object* v___x_3676_; 
lean_dec_ref(v_config_3355_);
lean_dec(v_handler_3354_);
lean_dec_ref(v_inst_3352_);
v_a_3656_ = lean_ctor_get(v_x_3645_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v_x_3645_, 1);
v_requestStream_3657_ = lean_ctor_get(v_state_3357_, 1);
lean_inc_ref(v_requestStream_3657_);
v_keepAliveTimeout_3658_ = lean_ctor_get(v_state_3357_, 2);
lean_inc(v_keepAliveTimeout_3658_);
v_currentTimeout_3659_ = lean_ctor_get(v_state_3357_, 3);
lean_inc(v_currentTimeout_3659_);
v_headerTimeout_3660_ = lean_ctor_get(v_state_3357_, 4);
lean_inc(v_headerTimeout_3660_);
v_response_3661_ = lean_ctor_get(v_state_3357_, 5);
lean_inc_ref(v_response_3661_);
v_respStream_3662_ = lean_ctor_get(v_state_3357_, 6);
lean_inc(v_respStream_3662_);
v_requiresData_3663_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3664_ = lean_ctor_get(v_state_3357_, 7);
lean_inc(v_expectData_3664_);
v_pendingHead_3665_ = lean_ctor_get(v_state_3357_, 8);
lean_inc(v_pendingHead_3665_);
lean_dec_ref(v_state_3357_);
v_close_3666_ = lean_ctor_get(v_inst_3353_, 1);
lean_inc_ref(v_close_3666_);
v_isClosed_3667_ = lean_ctor_get(v_inst_3353_, 2);
lean_inc_ref(v_isClosed_3667_);
lean_dec_ref(v_inst_3353_);
v_body_3668_ = lean_ctor_get(v_a_3656_, 1);
lean_inc_n(v_body_3668_, 2);
lean_dec(v_a_3656_);
v___x_3669_ = lean_apply_2(v_isClosed_3667_, v_body_3668_, lean_box(0));
v___x_3670_ = lean_box(v_requiresData_3663_);
v___f_3671_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3671_, 0, v_machine_3653_);
lean_closure_set(v___f_3671_, 1, v_requestStream_3657_);
lean_closure_set(v___f_3671_, 2, v_keepAliveTimeout_3658_);
lean_closure_set(v___f_3671_, 3, v_currentTimeout_3659_);
lean_closure_set(v___f_3671_, 4, v_headerTimeout_3660_);
lean_closure_set(v___f_3671_, 5, v_response_3661_);
lean_closure_set(v___f_3671_, 6, v_respStream_3662_);
lean_closure_set(v___f_3671_, 7, v___x_3670_);
lean_closure_set(v___f_3671_, 8, v_expectData_3664_);
lean_closure_set(v___f_3671_, 9, v_pendingHead_3665_);
lean_inc_ref(v___f_3671_);
v___f_3672_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3672_, 0, v___f_3671_);
v___f_3673_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3673_, 0, v_close_3666_);
lean_closure_set(v___f_3673_, 1, v_body_3668_);
lean_closure_set(v___f_3673_, 2, v___f_3672_);
lean_closure_set(v___f_3673_, 3, v___f_3671_);
v___x_3674_ = lean_unsigned_to_nat(0u);
v___x_3675_ = 0;
v___x_3676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3674_, v___x_3675_, v___x_3669_, v___f_3673_);
return v___x_3676_;
}
else
{
lean_object* v_a_3677_; lean_object* v_requestStream_3678_; lean_object* v_keepAliveTimeout_3679_; lean_object* v_currentTimeout_3680_; lean_object* v_headerTimeout_3681_; lean_object* v_response_3682_; uint8_t v_requiresData_3683_; lean_object* v_expectData_3684_; lean_object* v_pendingHead_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___f_3690_; lean_object* v___f_3691_; lean_object* v___f_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___f_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_a_3677_ = lean_ctor_get(v_x_3645_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v_x_3645_, 1);
v_requestStream_3678_ = lean_ctor_get(v_state_3357_, 1);
lean_inc_ref(v_requestStream_3678_);
v_keepAliveTimeout_3679_ = lean_ctor_get(v_state_3357_, 2);
lean_inc(v_keepAliveTimeout_3679_);
v_currentTimeout_3680_ = lean_ctor_get(v_state_3357_, 3);
lean_inc(v_currentTimeout_3680_);
v_headerTimeout_3681_ = lean_ctor_get(v_state_3357_, 4);
lean_inc(v_headerTimeout_3681_);
v_response_3682_ = lean_ctor_get(v_state_3357_, 5);
lean_inc_ref(v_response_3682_);
v_requiresData_3683_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3684_ = lean_ctor_get(v_state_3357_, 7);
lean_inc(v_expectData_3684_);
v_pendingHead_3685_ = lean_ctor_get(v_state_3357_, 8);
lean_inc(v_pendingHead_3685_);
lean_dec_ref(v_state_3357_);
lean_inc_ref(v_inst_3353_);
v___x_3686_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3353_, v_config_3355_, v_machine_3653_, v_a_3677_);
v___x_3687_ = 0;
v___x_3688_ = lean_box(v_requiresData_3683_);
v___x_3689_ = lean_box(v___x_3687_);
v___f_3690_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3690_, 0, v_requestStream_3678_);
lean_closure_set(v___f_3690_, 1, v_keepAliveTimeout_3679_);
lean_closure_set(v___f_3690_, 2, v_currentTimeout_3680_);
lean_closure_set(v___f_3690_, 3, v_headerTimeout_3681_);
lean_closure_set(v___f_3690_, 4, v_response_3682_);
lean_closure_set(v___f_3690_, 5, v___x_3688_);
lean_closure_set(v___f_3690_, 6, v_expectData_3684_);
lean_closure_set(v___f_3690_, 7, v___x_3689_);
lean_closure_set(v___f_3690_, 8, v_pendingHead_3685_);
v___f_3691_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3691_, 0, v___f_3690_);
v___f_3692_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3693_ = 1;
v___x_3694_ = lean_box(v___x_3687_);
v___x_3695_ = lean_box(v___x_3693_);
lean_inc_ref(v___f_3691_);
v___f_3696_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3696_, 0, v___x_3694_);
lean_closure_set(v___f_3696_, 1, v___f_3691_);
lean_closure_set(v___f_3696_, 2, v_inst_3353_);
lean_closure_set(v___f_3696_, 3, v___f_3692_);
lean_closure_set(v___f_3696_, 4, v___x_3695_);
lean_closure_set(v___f_3696_, 5, v_inst_3352_);
lean_closure_set(v___f_3696_, 6, v_handler_3354_);
lean_closure_set(v___f_3696_, 7, v___f_3691_);
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3697_, v___x_3687_, v___x_3686_, v___f_3696_);
return v___x_3698_;
}
}
}
case 4:
{
lean_object* v_onFailure_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; lean_object* v___x_3705_; 
lean_dec_ref(v_config_3355_);
lean_dec_ref(v_inst_3353_);
v_onFailure_3699_ = lean_ctor_get(v_inst_3352_, 2);
lean_inc_ref(v_onFailure_3699_);
lean_dec_ref(v_inst_3352_);
v___x_3700_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3701_ = lean_apply_3(v_onFailure_3699_, v_handler_3354_, v___x_3700_, lean_box(0));
v___f_3702_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3702_, 0, v_state_3357_);
v___x_3703_ = lean_unsigned_to_nat(0u);
v___x_3704_ = 0;
v___x_3705_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3703_, v___x_3704_, v___x_3701_, v___f_3702_);
return v___x_3705_;
}
case 5:
{
lean_object* v_machine_3706_; lean_object* v_requestStream_3707_; lean_object* v_keepAliveTimeout_3708_; lean_object* v_currentTimeout_3709_; lean_object* v_headerTimeout_3710_; lean_object* v_response_3711_; lean_object* v_respStream_3712_; uint8_t v_requiresData_3713_; lean_object* v_expectData_3714_; lean_object* v_pendingHead_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v_config_3355_);
lean_dec(v_handler_3354_);
lean_dec_ref(v_inst_3353_);
lean_dec_ref(v_inst_3352_);
v_machine_3706_ = lean_ctor_get(v_state_3357_, 0);
v_requestStream_3707_ = lean_ctor_get(v_state_3357_, 1);
v_keepAliveTimeout_3708_ = lean_ctor_get(v_state_3357_, 2);
v_currentTimeout_3709_ = lean_ctor_get(v_state_3357_, 3);
v_headerTimeout_3710_ = lean_ctor_get(v_state_3357_, 4);
v_response_3711_ = lean_ctor_get(v_state_3357_, 5);
v_respStream_3712_ = lean_ctor_get(v_state_3357_, 6);
v_requiresData_3713_ = lean_ctor_get_uint8(v_state_3357_, sizeof(void*)*9);
v_expectData_3714_ = lean_ctor_get(v_state_3357_, 7);
v_pendingHead_3715_ = lean_ctor_get(v_state_3357_, 8);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_state_3357_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3717_ = v_state_3357_;
v_isShared_3718_ = v_isSharedCheck_3729_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_pendingHead_3715_);
lean_inc(v_expectData_3714_);
lean_inc(v_respStream_3712_);
lean_inc(v_response_3711_);
lean_inc(v_headerTimeout_3710_);
lean_inc(v_currentTimeout_3709_);
lean_inc(v_keepAliveTimeout_3708_);
lean_inc(v_requestStream_3707_);
lean_inc(v_machine_3706_);
lean_dec(v_state_3357_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3729_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3723_; 
v___x_3719_ = lean_box(55);
v___x_3720_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3706_, v___x_3719_);
v___x_3721_ = 0;
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3720_);
v___x_3723_ = v___x_3717_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_requestStream_3707_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_keepAliveTimeout_3708_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v_currentTimeout_3709_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_headerTimeout_3710_);
lean_ctor_set(v_reuseFailAlloc_3728_, 5, v_response_3711_);
lean_ctor_set(v_reuseFailAlloc_3728_, 6, v_respStream_3712_);
lean_ctor_set(v_reuseFailAlloc_3728_, 7, v_expectData_3714_);
lean_ctor_set(v_reuseFailAlloc_3728_, 8, v_pendingHead_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, sizeof(void*)*9, v_requiresData_3713_);
v___x_3723_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*9 + 1, v___x_3721_);
v___x_3724_ = lean_box(v___x_3721_);
v___x_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
return v___x_3727_;
}
}
}
default: 
{
uint8_t v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec_ref(v_config_3355_);
lean_dec(v_handler_3354_);
lean_dec_ref(v_inst_3353_);
lean_dec_ref(v_inst_3352_);
v___x_3730_ = 1;
v___x_3731_ = lean_box(v___x_3730_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_state_3357_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3735_, lean_object* v_inst_3736_, lean_object* v_handler_3737_, lean_object* v_config_3738_, lean_object* v_event_3739_, lean_object* v_state_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3735_, v_inst_3736_, v_handler_3737_, v_config_3738_, v_event_3739_, v_state_3740_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3743_, lean_object* v_00_u03b2_3744_, lean_object* v_inst_3745_, lean_object* v_inst_3746_, lean_object* v_handler_3747_, lean_object* v_config_3748_, lean_object* v_event_3749_, lean_object* v_state_3750_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3745_, v_inst_3746_, v_handler_3747_, v_config_3748_, v_event_3749_, v_state_3750_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3753_, lean_object* v_00_u03b2_3754_, lean_object* v_inst_3755_, lean_object* v_inst_3756_, lean_object* v_handler_3757_, lean_object* v_config_3758_, lean_object* v_event_3759_, lean_object* v_state_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3753_, v_00_u03b2_3754_, v_inst_3755_, v_inst_3756_, v_handler_3757_, v_config_3758_, v_event_3759_, v_state_3760_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_expectData_3763_, lean_object* v_respStream_3764_, lean_object* v_currentTimeout_3765_, lean_object* v_keepAliveTimeout_3766_, lean_object* v_headerTimeout_3767_, lean_object* v_connectionContext_3768_, uint8_t v_handlerDispatched_3769_, lean_object* v_response_3770_, lean_object* v_socket_3771_, uint8_t v_requiresData_3772_, uint8_t v_sentMessage_3773_, lean_object* v_reader_3774_, uint8_t v_requestBodyInterested_3775_, lean_object* v_requestBody_3776_){
_start:
{
lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3785_; uint8_t v___y_3791_; uint8_t v___y_3794_; uint8_t v___y_3795_; uint8_t v___y_3797_; uint8_t v___y_3798_; uint8_t v___y_3799_; uint8_t v___y_3801_; uint8_t v___y_3802_; uint8_t v___y_3805_; 
if (v_handlerDispatched_3769_ == 0)
{
uint8_t v___x_3808_; 
v___x_3808_ = 1;
v___y_3805_ = v___x_3808_;
goto v___jp_3804_;
}
else
{
uint8_t v___x_3809_; 
v___x_3809_ = 0;
v___y_3805_ = v___x_3809_;
goto v___jp_3804_;
}
v___jp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3781_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3781_, 0, v___y_3779_);
lean_ctor_set(v___x_3781_, 1, v_expectData_3763_);
lean_ctor_set(v___x_3781_, 2, v___y_3780_);
lean_ctor_set(v___x_3781_, 3, v_respStream_3764_);
lean_ctor_set(v___x_3781_, 4, v_requestBody_3776_);
lean_ctor_set(v___x_3781_, 5, v_currentTimeout_3765_);
lean_ctor_set(v___x_3781_, 6, v_keepAliveTimeout_3766_);
lean_ctor_set(v___x_3781_, 7, v_headerTimeout_3767_);
lean_ctor_set(v___x_3781_, 8, v_connectionContext_3768_);
v___x_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
v___jp_3784_:
{
if (v_handlerDispatched_3769_ == 0)
{
lean_object* v___x_3786_; 
lean_dec_ref(v_response_3770_);
v___x_3786_ = lean_box(0);
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___x_3786_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_response_3770_);
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___x_3787_;
goto v___jp_3778_;
}
}
v___jp_3788_:
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_socket_3771_);
v___y_3785_ = v___x_3789_;
goto v___jp_3784_;
}
v___jp_3790_:
{
if (v_requiresData_3772_ == 0)
{
if (v___y_3791_ == 0)
{
lean_object* v___x_3792_; 
lean_dec(v_socket_3771_);
v___x_3792_ = lean_box(0);
v___y_3785_ = v___x_3792_;
goto v___jp_3784_;
}
else
{
goto v___jp_3788_;
}
}
else
{
goto v___jp_3788_;
}
}
v___jp_3793_:
{
if (v___y_3794_ == 0)
{
v___y_3791_ = v___y_3795_;
goto v___jp_3790_;
}
else
{
v___y_3791_ = v___y_3794_;
goto v___jp_3790_;
}
}
v___jp_3796_:
{
if (v___y_3797_ == 0)
{
v___y_3794_ = v___y_3798_;
v___y_3795_ = v___y_3799_;
goto v___jp_3793_;
}
else
{
v___y_3794_ = v___y_3798_;
v___y_3795_ = v___y_3797_;
goto v___jp_3793_;
}
}
v___jp_3800_:
{
if (v_sentMessage_3773_ == 0)
{
lean_object* v_state_3803_; 
v_state_3803_ = lean_ctor_get(v_reader_3774_, 0);
if (lean_obj_tag(v_state_3803_) == 2)
{
v___y_3797_ = v___y_3802_;
v___y_3798_ = v___y_3801_;
v___y_3799_ = v_requestBodyInterested_3775_;
goto v___jp_3796_;
}
else
{
v___y_3797_ = v___y_3802_;
v___y_3798_ = v___y_3801_;
v___y_3799_ = v_sentMessage_3773_;
goto v___jp_3796_;
}
}
else
{
v___y_3797_ = v___y_3802_;
v___y_3798_ = v___y_3801_;
v___y_3799_ = v_sentMessage_3773_;
goto v___jp_3796_;
}
}
v___jp_3804_:
{
if (lean_obj_tag(v_respStream_3764_) == 0)
{
uint8_t v___x_3806_; 
v___x_3806_ = 0;
v___y_3801_ = v___y_3805_;
v___y_3802_ = v___x_3806_;
goto v___jp_3800_;
}
else
{
uint8_t v___x_3807_; 
v___x_3807_ = 1;
v___y_3801_ = v___y_3805_;
v___y_3802_ = v___x_3807_;
goto v___jp_3800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_expectData_3810_, lean_object* v_respStream_3811_, lean_object* v_currentTimeout_3812_, lean_object* v_keepAliveTimeout_3813_, lean_object* v_headerTimeout_3814_, lean_object* v_connectionContext_3815_, lean_object* v_handlerDispatched_3816_, lean_object* v_response_3817_, lean_object* v_socket_3818_, lean_object* v_requiresData_3819_, lean_object* v_sentMessage_3820_, lean_object* v_reader_3821_, lean_object* v_requestBodyInterested_3822_, lean_object* v_requestBody_3823_, lean_object* v___y_3824_){
_start:
{
uint8_t v_handlerDispatched_boxed_3825_; uint8_t v_requiresData_boxed_3826_; uint8_t v_sentMessage_boxed_3827_; uint8_t v_requestBodyInterested_boxed_3828_; lean_object* v_res_3829_; 
v_handlerDispatched_boxed_3825_ = lean_unbox(v_handlerDispatched_3816_);
v_requiresData_boxed_3826_ = lean_unbox(v_requiresData_3819_);
v_sentMessage_boxed_3827_ = lean_unbox(v_sentMessage_3820_);
v_requestBodyInterested_boxed_3828_ = lean_unbox(v_requestBodyInterested_3822_);
v_res_3829_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_expectData_3810_, v_respStream_3811_, v_currentTimeout_3812_, v_keepAliveTimeout_3813_, v_headerTimeout_3814_, v_connectionContext_3815_, v_handlerDispatched_boxed_3825_, v_response_3817_, v_socket_3818_, v_requiresData_boxed_3826_, v_sentMessage_boxed_3827_, v_reader_3821_, v_requestBodyInterested_boxed_3828_, v_requestBody_3823_);
lean_dec_ref(v_reader_3821_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3830_, lean_object* v_x_3831_){
_start:
{
if (lean_obj_tag(v_x_3831_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v___f_3830_);
v_a_3833_ = lean_ctor_get(v_x_3831_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_x_3831_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v_x_3831_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v_x_3831_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
return v___x_3839_;
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3843_; 
v_a_3842_ = lean_ctor_get(v_x_3831_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v_x_3831_, 1);
v___x_3843_ = lean_apply_2(v___f_3830_, v_a_3842_, lean_box(0));
return v___x_3843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3844_, lean_object* v_x_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3844_, v_x_3845_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_expectData_3852_, lean_object* v_respStream_3853_, lean_object* v_currentTimeout_3854_, lean_object* v_keepAliveTimeout_3855_, lean_object* v_headerTimeout_3856_, lean_object* v_connectionContext_3857_, uint8_t v_handlerDispatched_3858_, lean_object* v_response_3859_, lean_object* v_socket_3860_, uint8_t v_requiresData_3861_, uint8_t v_sentMessage_3862_, lean_object* v_reader_3863_, uint8_t v_pullBodyStalled_3864_, uint8_t v_requestBodyOpen_3865_, lean_object* v_requestStream_3866_, uint8_t v_requestBodyInterested_3867_){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; uint8_t v___y_3876_; 
v___x_3869_ = lean_box(v_handlerDispatched_3858_);
v___x_3870_ = lean_box(v_requiresData_3861_);
v___x_3871_ = lean_box(v_sentMessage_3862_);
v___x_3872_ = lean_box(v_requestBodyInterested_3867_);
lean_inc_ref(v_reader_3863_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3873_, 0, v_expectData_3852_);
lean_closure_set(v___f_3873_, 1, v_respStream_3853_);
lean_closure_set(v___f_3873_, 2, v_currentTimeout_3854_);
lean_closure_set(v___f_3873_, 3, v_keepAliveTimeout_3855_);
lean_closure_set(v___f_3873_, 4, v_headerTimeout_3856_);
lean_closure_set(v___f_3873_, 5, v_connectionContext_3857_);
lean_closure_set(v___f_3873_, 6, v___x_3869_);
lean_closure_set(v___f_3873_, 7, v_response_3859_);
lean_closure_set(v___f_3873_, 8, v_socket_3860_);
lean_closure_set(v___f_3873_, 9, v___x_3870_);
lean_closure_set(v___f_3873_, 10, v___x_3871_);
lean_closure_set(v___f_3873_, 11, v_reader_3863_);
lean_closure_set(v___f_3873_, 12, v___x_3872_);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3874_, 0, v___f_3873_);
if (v_sentMessage_3862_ == 0)
{
lean_object* v_state_3880_; 
v_state_3880_ = lean_ctor_get(v_reader_3863_, 0);
lean_inc(v_state_3880_);
lean_dec_ref(v_reader_3863_);
if (lean_obj_tag(v_state_3880_) == 2)
{
lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3891_; 
v_isSharedCheck_3891_ = !lean_is_exclusive(v_state_3880_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; 
v_unused_3892_ = lean_ctor_get(v_state_3880_, 0);
lean_dec(v_unused_3892_);
v___x_3882_ = v_state_3880_;
v_isShared_3883_ = v_isSharedCheck_3891_;
goto v_resetjp_3881_;
}
else
{
lean_dec(v_state_3880_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3891_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
if (v_pullBodyStalled_3864_ == 0)
{
if (v_requestBodyOpen_3865_ == 0)
{
lean_del_object(v___x_3882_);
lean_dec_ref(v_requestStream_3866_);
v___y_3876_ = v_requestBodyOpen_3865_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
lean_ctor_set(v___x_3882_, 0, v_requestStream_3866_);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_requestStream_3866_);
v___x_3885_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
v___x_3888_ = lean_unsigned_to_nat(0u);
v___x_3889_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3888_, v_pullBodyStalled_3864_, v___x_3887_, v___f_3874_);
return v___x_3889_;
}
}
}
else
{
lean_del_object(v___x_3882_);
lean_dec_ref(v_requestStream_3866_);
v___y_3876_ = v_sentMessage_3862_;
goto v___jp_3875_;
}
}
}
else
{
lean_dec(v_state_3880_);
lean_dec_ref(v_requestStream_3866_);
v___y_3876_ = v_sentMessage_3862_;
goto v___jp_3875_;
}
}
else
{
uint8_t v___x_3893_; 
lean_dec_ref(v_requestStream_3866_);
lean_dec_ref(v_reader_3863_);
v___x_3893_ = 0;
v___y_3876_ = v___x_3893_;
goto v___jp_3875_;
}
v___jp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3877_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3878_ = lean_unsigned_to_nat(0u);
v___x_3879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3878_, v___y_3876_, v___x_3877_, v___f_3874_);
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_expectData_3894_ = _args[0];
lean_object* v_respStream_3895_ = _args[1];
lean_object* v_currentTimeout_3896_ = _args[2];
lean_object* v_keepAliveTimeout_3897_ = _args[3];
lean_object* v_headerTimeout_3898_ = _args[4];
lean_object* v_connectionContext_3899_ = _args[5];
lean_object* v_handlerDispatched_3900_ = _args[6];
lean_object* v_response_3901_ = _args[7];
lean_object* v_socket_3902_ = _args[8];
lean_object* v_requiresData_3903_ = _args[9];
lean_object* v_sentMessage_3904_ = _args[10];
lean_object* v_reader_3905_ = _args[11];
lean_object* v_pullBodyStalled_3906_ = _args[12];
lean_object* v_requestBodyOpen_3907_ = _args[13];
lean_object* v_requestStream_3908_ = _args[14];
lean_object* v_requestBodyInterested_3909_ = _args[15];
lean_object* v___y_3910_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3911_; uint8_t v_requiresData_boxed_3912_; uint8_t v_sentMessage_boxed_3913_; uint8_t v_pullBodyStalled_boxed_3914_; uint8_t v_requestBodyOpen_boxed_3915_; uint8_t v_requestBodyInterested_boxed_3916_; lean_object* v_res_3917_; 
v_handlerDispatched_boxed_3911_ = lean_unbox(v_handlerDispatched_3900_);
v_requiresData_boxed_3912_ = lean_unbox(v_requiresData_3903_);
v_sentMessage_boxed_3913_ = lean_unbox(v_sentMessage_3904_);
v_pullBodyStalled_boxed_3914_ = lean_unbox(v_pullBodyStalled_3906_);
v_requestBodyOpen_boxed_3915_ = lean_unbox(v_requestBodyOpen_3907_);
v_requestBodyInterested_boxed_3916_ = lean_unbox(v_requestBodyInterested_3909_);
v_res_3917_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_expectData_3894_, v_respStream_3895_, v_currentTimeout_3896_, v_keepAliveTimeout_3897_, v_headerTimeout_3898_, v_connectionContext_3899_, v_handlerDispatched_boxed_3911_, v_response_3901_, v_socket_3902_, v_requiresData_boxed_3912_, v_sentMessage_boxed_3913_, v_reader_3905_, v_pullBodyStalled_boxed_3914_, v_requestBodyOpen_boxed_3915_, v_requestStream_3908_, v_requestBodyInterested_boxed_3916_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3918_, lean_object* v_x_3919_){
_start:
{
if (lean_obj_tag(v_x_3919_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3929_; 
lean_dec_ref(v___f_3918_);
v_a_3921_ = lean_ctor_get(v_x_3919_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_x_3919_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3923_ = v_x_3919_;
v_isShared_3924_ = v_isSharedCheck_3929_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v_x_3919_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3929_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3931_; 
v_a_3930_ = lean_ctor_get(v_x_3919_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v_x_3919_, 1);
v___x_3931_ = lean_apply_2(v___f_3918_, v_a_3930_, lean_box(0));
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3932_, lean_object* v_x_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3932_, v_x_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_expectData_3936_, lean_object* v_respStream_3937_, lean_object* v_currentTimeout_3938_, lean_object* v_keepAliveTimeout_3939_, lean_object* v_headerTimeout_3940_, lean_object* v_connectionContext_3941_, uint8_t v_handlerDispatched_3942_, lean_object* v_response_3943_, lean_object* v_socket_3944_, uint8_t v_requiresData_3945_, uint8_t v_sentMessage_3946_, lean_object* v_reader_3947_, uint8_t v_pullBodyStalled_3948_, lean_object* v_requestStream_3949_, uint8_t v_requestBodyOpen_3950_){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; lean_object* v___f_3958_; uint8_t v___y_3960_; 
v___x_3952_ = lean_box(v_handlerDispatched_3942_);
v___x_3953_ = lean_box(v_requiresData_3945_);
v___x_3954_ = lean_box(v_sentMessage_3946_);
v___x_3955_ = lean_box(v_pullBodyStalled_3948_);
v___x_3956_ = lean_box(v_requestBodyOpen_3950_);
lean_inc_ref(v_requestStream_3949_);
lean_inc_ref(v_reader_3947_);
v___f_3957_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3957_, 0, v_expectData_3936_);
lean_closure_set(v___f_3957_, 1, v_respStream_3937_);
lean_closure_set(v___f_3957_, 2, v_currentTimeout_3938_);
lean_closure_set(v___f_3957_, 3, v_keepAliveTimeout_3939_);
lean_closure_set(v___f_3957_, 4, v_headerTimeout_3940_);
lean_closure_set(v___f_3957_, 5, v_connectionContext_3941_);
lean_closure_set(v___f_3957_, 6, v___x_3952_);
lean_closure_set(v___f_3957_, 7, v_response_3943_);
lean_closure_set(v___f_3957_, 8, v_socket_3944_);
lean_closure_set(v___f_3957_, 9, v___x_3953_);
lean_closure_set(v___f_3957_, 10, v___x_3954_);
lean_closure_set(v___f_3957_, 11, v_reader_3947_);
lean_closure_set(v___f_3957_, 12, v___x_3955_);
lean_closure_set(v___f_3957_, 13, v___x_3956_);
lean_closure_set(v___f_3957_, 14, v_requestStream_3949_);
v___f_3958_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3958_, 0, v___f_3957_);
if (v_sentMessage_3946_ == 0)
{
lean_object* v_state_3966_; 
v_state_3966_ = lean_ctor_get(v_reader_3947_, 0);
lean_inc(v_state_3966_);
lean_dec_ref(v_reader_3947_);
if (lean_obj_tag(v_state_3966_) == 2)
{
lean_dec_ref_known(v_state_3966_, 1);
if (v_requestBodyOpen_3950_ == 0)
{
lean_dec_ref(v_requestStream_3949_);
v___y_3960_ = v_requestBodyOpen_3950_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3949_);
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3968_, v_sentMessage_3946_, v___x_3967_, v___f_3958_);
return v___x_3969_;
}
}
else
{
lean_dec(v_state_3966_);
lean_dec_ref(v_requestStream_3949_);
v___y_3960_ = v_sentMessage_3946_;
goto v___jp_3959_;
}
}
else
{
uint8_t v___x_3970_; 
lean_dec_ref(v_requestStream_3949_);
lean_dec_ref(v_reader_3947_);
v___x_3970_ = 0;
v___y_3960_ = v___x_3970_;
goto v___jp_3959_;
}
v___jp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3961_ = lean_box(v___y_3960_);
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
v___x_3964_ = lean_unsigned_to_nat(0u);
v___x_3965_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3964_, v___y_3960_, v___x_3963_, v___f_3958_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_expectData_3971_, lean_object* v_respStream_3972_, lean_object* v_currentTimeout_3973_, lean_object* v_keepAliveTimeout_3974_, lean_object* v_headerTimeout_3975_, lean_object* v_connectionContext_3976_, lean_object* v_handlerDispatched_3977_, lean_object* v_response_3978_, lean_object* v_socket_3979_, lean_object* v_requiresData_3980_, lean_object* v_sentMessage_3981_, lean_object* v_reader_3982_, lean_object* v_pullBodyStalled_3983_, lean_object* v_requestStream_3984_, lean_object* v_requestBodyOpen_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v_handlerDispatched_boxed_3987_; uint8_t v_requiresData_boxed_3988_; uint8_t v_sentMessage_boxed_3989_; uint8_t v_pullBodyStalled_boxed_3990_; uint8_t v_requestBodyOpen_boxed_3991_; lean_object* v_res_3992_; 
v_handlerDispatched_boxed_3987_ = lean_unbox(v_handlerDispatched_3977_);
v_requiresData_boxed_3988_ = lean_unbox(v_requiresData_3980_);
v_sentMessage_boxed_3989_ = lean_unbox(v_sentMessage_3981_);
v_pullBodyStalled_boxed_3990_ = lean_unbox(v_pullBodyStalled_3983_);
v_requestBodyOpen_boxed_3991_ = lean_unbox(v_requestBodyOpen_3985_);
v_res_3992_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_expectData_3971_, v_respStream_3972_, v_currentTimeout_3973_, v_keepAliveTimeout_3974_, v_headerTimeout_3975_, v_connectionContext_3976_, v_handlerDispatched_boxed_3987_, v_response_3978_, v_socket_3979_, v_requiresData_boxed_3988_, v_sentMessage_boxed_3989_, v_reader_3982_, v_pullBodyStalled_boxed_3990_, v_requestStream_3984_, v_requestBodyOpen_boxed_3991_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3993_, lean_object* v___f_3994_, uint8_t v___x_3995_, lean_object* v_x_3996_){
_start:
{
uint8_t v___y_3999_; 
if (lean_obj_tag(v_x_3996_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4013_; 
lean_dec_ref(v___f_3994_);
v_a_4005_ = lean_ctor_get(v_x_3996_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_x_3996_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4007_ = v_x_3996_;
v_isShared_4008_ = v_isSharedCheck_4013_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v_x_3996_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4013_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
}
else
{
lean_object* v_a_4014_; uint8_t v___x_4015_; 
v_a_4014_ = lean_ctor_get(v_x_3996_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v_x_3996_, 1);
v___x_4015_ = lean_unbox(v_a_4014_);
lean_dec(v_a_4014_);
if (v___x_4015_ == 0)
{
v___y_3999_ = v___x_3995_;
goto v___jp_3998_;
}
else
{
v___y_3999_ = v_sentMessage_3993_;
goto v___jp_3998_;
}
}
v___jp_3998_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4000_ = lean_box(v___y_3999_);
v___x_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4003_, v_sentMessage_3993_, v___x_4002_, v___f_3994_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4016_, lean_object* v___f_4017_, lean_object* v___x_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_){
_start:
{
uint8_t v_sentMessage_boxed_4021_; uint8_t v___x_2561__boxed_4022_; lean_object* v_res_4023_; 
v_sentMessage_boxed_4021_ = lean_unbox(v_sentMessage_4016_);
v___x_2561__boxed_4022_ = lean_unbox(v___x_4018_);
v_res_4023_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4021_, v___f_4017_, v___x_2561__boxed_4022_, v_x_4019_);
return v_res_4023_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___f_4024_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4025_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4026_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4027_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4027_, 0, lean_box(0));
lean_closure_set(v___x_4027_, 1, lean_box(0));
lean_closure_set(v___x_4027_, 2, v___x_4026_);
lean_closure_set(v___x_4027_, 3, lean_box(0));
lean_closure_set(v___x_4027_, 4, lean_box(0));
lean_closure_set(v___x_4027_, 5, v___x_4025_);
lean_closure_set(v___x_4027_, 6, v___f_4024_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4028_, lean_object* v_connectionContext_4029_, lean_object* v_state_4030_){
_start:
{
lean_object* v_machine_4032_; lean_object* v_writer_4033_; lean_object* v_requestStream_4034_; lean_object* v_keepAliveTimeout_4035_; lean_object* v_currentTimeout_4036_; lean_object* v_headerTimeout_4037_; lean_object* v_response_4038_; lean_object* v_respStream_4039_; uint8_t v_requiresData_4040_; lean_object* v_expectData_4041_; uint8_t v_handlerDispatched_4042_; lean_object* v_reader_4043_; uint8_t v_pullBodyStalled_4044_; uint8_t v_sentMessage_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___f_4050_; lean_object* v___f_4051_; uint8_t v___y_4053_; 
v_machine_4032_ = lean_ctor_get(v_state_4030_, 0);
lean_inc_ref(v_machine_4032_);
v_writer_4033_ = lean_ctor_get(v_machine_4032_, 1);
lean_inc_ref(v_writer_4033_);
v_requestStream_4034_ = lean_ctor_get(v_state_4030_, 1);
lean_inc_ref_n(v_requestStream_4034_, 2);
v_keepAliveTimeout_4035_ = lean_ctor_get(v_state_4030_, 2);
lean_inc(v_keepAliveTimeout_4035_);
v_currentTimeout_4036_ = lean_ctor_get(v_state_4030_, 3);
lean_inc(v_currentTimeout_4036_);
v_headerTimeout_4037_ = lean_ctor_get(v_state_4030_, 4);
lean_inc(v_headerTimeout_4037_);
v_response_4038_ = lean_ctor_get(v_state_4030_, 5);
lean_inc_ref(v_response_4038_);
v_respStream_4039_ = lean_ctor_get(v_state_4030_, 6);
lean_inc(v_respStream_4039_);
v_requiresData_4040_ = lean_ctor_get_uint8(v_state_4030_, sizeof(void*)*9);
v_expectData_4041_ = lean_ctor_get(v_state_4030_, 7);
lean_inc(v_expectData_4041_);
v_handlerDispatched_4042_ = lean_ctor_get_uint8(v_state_4030_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4030_);
v_reader_4043_ = lean_ctor_get(v_machine_4032_, 0);
lean_inc_ref_n(v_reader_4043_, 2);
v_pullBodyStalled_4044_ = lean_ctor_get_uint8(v_machine_4032_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4032_);
v_sentMessage_4045_ = lean_ctor_get_uint8(v_writer_4033_, sizeof(void*)*6);
lean_dec_ref(v_writer_4033_);
v___x_4046_ = lean_box(v_handlerDispatched_4042_);
v___x_4047_ = lean_box(v_requiresData_4040_);
v___x_4048_ = lean_box(v_sentMessage_4045_);
v___x_4049_ = lean_box(v_pullBodyStalled_4044_);
v___f_4050_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4050_, 0, v_expectData_4041_);
lean_closure_set(v___f_4050_, 1, v_respStream_4039_);
lean_closure_set(v___f_4050_, 2, v_currentTimeout_4036_);
lean_closure_set(v___f_4050_, 3, v_keepAliveTimeout_4035_);
lean_closure_set(v___f_4050_, 4, v_headerTimeout_4037_);
lean_closure_set(v___f_4050_, 5, v_connectionContext_4029_);
lean_closure_set(v___f_4050_, 6, v___x_4046_);
lean_closure_set(v___f_4050_, 7, v_response_4038_);
lean_closure_set(v___f_4050_, 8, v_socket_4028_);
lean_closure_set(v___f_4050_, 9, v___x_4047_);
lean_closure_set(v___f_4050_, 10, v___x_4048_);
lean_closure_set(v___f_4050_, 11, v_reader_4043_);
lean_closure_set(v___f_4050_, 12, v___x_4049_);
lean_closure_set(v___f_4050_, 13, v_requestStream_4034_);
v___f_4051_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4051_, 0, v___f_4050_);
if (v_sentMessage_4045_ == 0)
{
lean_object* v_state_4059_; 
v_state_4059_ = lean_ctor_get(v_reader_4043_, 0);
lean_inc(v_state_4059_);
lean_dec_ref(v_reader_4043_);
if (lean_obj_tag(v_state_4059_) == 2)
{
lean_object* v___x_4060_; lean_object* v___f_4061_; lean_object* v___f_4062_; lean_object* v___x_4063_; lean_object* v___x_2027__overap_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___f_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec_ref_known(v_state_4059_, 1);
v___x_4060_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4061_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4062_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4063_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2027__overap_4064_ = l_Std_Mutex_atomically___redArg(v___x_4060_, v___f_4061_, v___f_4062_, v_requestStream_4034_, v___x_4063_);
v___x_4065_ = lean_apply_1(v___x_2027__overap_4064_, lean_box(0));
v___x_4066_ = 1;
v___x_4067_ = lean_box(v_sentMessage_4045_);
v___x_4068_ = lean_box(v___x_4066_);
v___f_4069_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4069_, 0, v___x_4067_);
lean_closure_set(v___f_4069_, 1, v___f_4051_);
lean_closure_set(v___f_4069_, 2, v___x_4068_);
v___x_4070_ = lean_unsigned_to_nat(0u);
v___x_4071_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4070_, v_sentMessage_4045_, v___x_4065_, v___f_4069_);
return v___x_4071_;
}
else
{
lean_dec(v_state_4059_);
lean_dec_ref(v_requestStream_4034_);
v___y_4053_ = v_sentMessage_4045_;
goto v___jp_4052_;
}
}
else
{
uint8_t v___x_4072_; 
lean_dec_ref(v_reader_4043_);
lean_dec_ref(v_requestStream_4034_);
v___x_4072_ = 0;
v___y_4053_ = v___x_4072_;
goto v___jp_4052_;
}
v___jp_4052_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4054_ = lean_box(v___y_4053_);
v___x_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4057_, v___y_4053_, v___x_4056_, v___f_4051_);
return v___x_4058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4073_, lean_object* v_connectionContext_4074_, lean_object* v_state_4075_, lean_object* v_a_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4073_, v_connectionContext_4074_, v_state_4075_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4078_, lean_object* v_00_u03b2_4079_, lean_object* v_inst_4080_, lean_object* v_socket_4081_, lean_object* v_connectionContext_4082_, lean_object* v_state_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4081_, v_connectionContext_4082_, v_state_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_00_u03b2_4087_, lean_object* v_inst_4088_, lean_object* v_socket_4089_, lean_object* v_connectionContext_4090_, lean_object* v_state_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4086_, v_00_u03b2_4087_, v_inst_4088_, v_socket_4089_, v_connectionContext_4090_, v_state_4091_);
lean_dec_ref(v_inst_4088_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4098_){
_start:
{
if (lean_obj_tag(v_x_4098_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4108_; 
v_a_4100_ = lean_ctor_get(v_x_4098_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v_x_4098_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4102_ = v_x_4098_;
v_isShared_4103_ = v_isSharedCheck_4108_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v_x_4098_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4108_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
return v___x_4106_;
}
}
}
else
{
lean_object* v___x_4109_; 
lean_dec_ref_known(v_x_4098_, 1);
v___x_4109_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__1));
return v___x_4109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4110_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_onFailure_4113_, lean_object* v_handler_4114_, lean_object* v___f_4115_, lean_object* v_x_4116_){
_start:
{
if (lean_obj_tag(v_x_4116_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; lean_object* v___x_4122_; 
v_a_4118_ = lean_ctor_get(v_x_4116_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v_x_4116_, 1);
v___x_4119_ = lean_apply_3(v_onFailure_4113_, v_handler_4114_, v_a_4118_, lean_box(0));
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = 0;
v___x_4122_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4120_, v___x_4121_, v___x_4119_, v___f_4115_);
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; 
lean_dec_ref(v___f_4115_);
lean_dec(v_handler_4114_);
lean_dec_ref(v_onFailure_4113_);
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_x_4116_);
return v___x_4123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_onFailure_4124_, lean_object* v_handler_4125_, lean_object* v___f_4126_, lean_object* v_x_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_onFailure_4124_, v_handler_4125_, v___f_4126_, v_x_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4130_){
_start:
{
if (lean_obj_tag(v_x_4130_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4140_; 
v_a_4132_ = lean_ctor_get(v_x_4130_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_x_4130_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4134_ = v_x_4130_;
v_isShared_4135_ = v_isSharedCheck_4140_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v_x_4130_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4140_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
return v___x_4138_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4150_; 
v_a_4141_ = lean_ctor_get(v_x_4130_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_x_4130_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4143_ = v_x_4130_;
v_isShared_4144_ = v_isSharedCheck_4150_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v_x_4130_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4150_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v_a_4141_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4145_);
v___x_4147_ = v___x_4143_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4151_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4154_){
_start:
{
if (lean_obj_tag(v_x_4154_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4164_; 
v_a_4156_ = lean_ctor_get(v_x_4154_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_x_4154_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4158_ = v_x_4154_;
v_isShared_4159_ = v_isSharedCheck_4164_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v_x_4154_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4164_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
return v___x_4162_;
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4183_; 
v_a_4165_ = lean_ctor_get(v_x_4154_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_x_4154_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4167_ = v_x_4154_;
v_isShared_4168_ = v_isSharedCheck_4183_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v_x_4154_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4183_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v_snd_4169_; uint8_t v___x_4170_; 
v_snd_4169_ = lean_ctor_get(v_a_4165_, 1);
v___x_4170_ = lean_unbox(v_snd_4169_);
if (v___x_4170_ == 0)
{
lean_object* v_fst_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v_fst_4171_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_fst_4171_);
lean_dec(v_a_4165_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_fst_4171_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4172_);
v___x_4174_ = v___x_4167_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
else
{
lean_object* v_fst_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v_fst_4177_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_fst_4177_);
lean_dec(v_a_4165_);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v_fst_4177_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4178_);
v___x_4180_ = v___x_4167_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
return v___x_4181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4184_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4187_, lean_object* v_socket_4188_, lean_object* v_____r_4189_){
_start:
{
lean_object* v_val_4192_; lean_object* v_close_4194_; lean_object* v___x_4195_; 
v_close_4194_ = lean_ctor_get(v_inst_4187_, 3);
lean_inc_ref(v_close_4194_);
lean_dec_ref(v_inst_4187_);
v___x_4195_ = lean_apply_2(v_close_4194_, v_socket_4188_, lean_box(0));
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set_tag(v___x_4198_, 1);
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
v_val_4192_ = v___x_4201_;
goto v___jp_4191_;
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
v_a_4204_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4195_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4195_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
lean_ctor_set_tag(v___x_4206_, 0);
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
v_val_4192_ = v___x_4209_;
goto v___jp_4191_;
}
}
}
v___jp_4191_:
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_val_4192_);
return v___x_4193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4212_, lean_object* v_socket_4213_, lean_object* v_____r_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4212_, v_socket_4213_, v_____r_4214_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4217_, lean_object* v_x_4218_){
_start:
{
if (lean_obj_tag(v_x_4218_) == 0)
{
lean_object* v___x_4220_; 
lean_dec_ref(v___f_4217_);
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v_x_4218_);
return v___x_4220_;
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4222_; 
v_a_4221_ = lean_ctor_get(v_x_4218_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v_x_4218_, 1);
v___x_4222_ = lean_apply_2(v___f_4217_, v_a_4221_, lean_box(0));
return v___x_4222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4223_, lean_object* v_x_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4223_, v_x_4224_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4227_, lean_object* v_val_4228_, lean_object* v___f_4229_, lean_object* v___f_4230_, lean_object* v_x_4231_){
_start:
{
if (lean_obj_tag(v_x_4231_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4241_; 
lean_dec_ref(v___f_4230_);
lean_dec_ref(v___f_4229_);
lean_dec(v_val_4228_);
lean_dec_ref(v_close_4227_);
v_a_4233_ = lean_ctor_get(v_x_4231_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_x_4231_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4235_ = v_x_4231_;
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v_x_4231_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
return v___x_4239_;
}
}
}
else
{
lean_object* v_a_4242_; uint8_t v___x_4243_; 
v_a_4242_ = lean_ctor_get(v_x_4231_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v_x_4231_, 1);
v___x_4243_ = lean_unbox(v_a_4242_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; lean_object* v___x_4247_; 
lean_dec_ref(v___f_4230_);
v___x_4244_ = lean_apply_2(v_close_4227_, v_val_4228_, lean_box(0));
v___x_4245_ = lean_unsigned_to_nat(0u);
v___x_4246_ = lean_unbox(v_a_4242_);
lean_dec(v_a_4242_);
v___x_4247_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4245_, v___x_4246_, v___x_4244_, v___f_4229_);
return v___x_4247_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_dec(v_a_4242_);
lean_dec_ref(v___f_4229_);
lean_dec(v_val_4228_);
lean_dec_ref(v_close_4227_);
v___x_4248_ = lean_box(0);
v___x_4249_ = lean_apply_2(v___f_4230_, v___x_4248_, lean_box(0));
return v___x_4249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4250_, lean_object* v_val_4251_, lean_object* v___f_4252_, lean_object* v___f_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4250_, v_val_4251_, v___f_4252_, v___f_4253_, v_x_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4257_, lean_object* v_responseBodyInstance_4258_, lean_object* v___f_4259_, lean_object* v___f_4260_, lean_object* v_____r_4261_){
_start:
{
if (lean_obj_tag(v_respStream_4257_) == 1)
{
lean_object* v_val_4263_; lean_object* v_close_4264_; lean_object* v_isClosed_4265_; lean_object* v___x_4266_; lean_object* v___f_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; lean_object* v___x_4270_; 
v_val_4263_ = lean_ctor_get(v_respStream_4257_, 0);
lean_inc_n(v_val_4263_, 2);
lean_dec_ref_known(v_respStream_4257_, 1);
v_close_4264_ = lean_ctor_get(v_responseBodyInstance_4258_, 1);
lean_inc_ref(v_close_4264_);
v_isClosed_4265_ = lean_ctor_get(v_responseBodyInstance_4258_, 2);
lean_inc_ref(v_isClosed_4265_);
lean_dec_ref(v_responseBodyInstance_4258_);
v___x_4266_ = lean_apply_2(v_isClosed_4265_, v_val_4263_, lean_box(0));
v___f_4267_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4267_, 0, v_close_4264_);
lean_closure_set(v___f_4267_, 1, v_val_4263_);
lean_closure_set(v___f_4267_, 2, v___f_4259_);
lean_closure_set(v___f_4267_, 3, v___f_4260_);
v___x_4268_ = lean_unsigned_to_nat(0u);
v___x_4269_ = 0;
v___x_4270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4268_, v___x_4269_, v___x_4266_, v___f_4267_);
return v___x_4270_;
}
else
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
lean_dec_ref(v___f_4259_);
lean_dec_ref(v_responseBodyInstance_4258_);
lean_dec(v_respStream_4257_);
v___x_4271_ = lean_box(0);
v___x_4272_ = lean_apply_2(v___f_4260_, v___x_4271_, lean_box(0));
return v___x_4272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4273_, lean_object* v_responseBodyInstance_4274_, lean_object* v___f_4275_, lean_object* v___f_4276_, lean_object* v_____r_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4273_, v_responseBodyInstance_4274_, v___f_4275_, v___f_4276_, v_____r_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4280_, lean_object* v___f_4281_, lean_object* v___f_4282_, lean_object* v_x_4283_){
_start:
{
if (lean_obj_tag(v_x_4283_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4293_; 
lean_dec_ref(v___f_4282_);
lean_dec_ref(v___f_4281_);
lean_dec_ref(v_requestStream_4280_);
v_a_4285_ = lean_ctor_get(v_x_4283_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_x_4283_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4287_ = v_x_4283_;
v_isShared_4288_ = v_isSharedCheck_4293_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v_x_4283_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4293_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
lean_object* v___x_4291_; 
v___x_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
return v___x_4291_;
}
}
}
else
{
lean_object* v_a_4294_; uint8_t v___x_4295_; 
v_a_4294_ = lean_ctor_get(v_x_4283_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v_x_4283_, 1);
v___x_4295_ = lean_unbox(v_a_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; lean_object* v___x_4299_; 
lean_dec_ref(v___f_4282_);
v___x_4296_ = l_Std_Http_Body_Stream_close(v_requestStream_4280_);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_unbox(v_a_4294_);
lean_dec(v_a_4294_);
v___x_4299_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4297_, v___x_4298_, v___x_4296_, v___f_4281_);
return v___x_4299_;
}
else
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
lean_dec(v_a_4294_);
lean_dec_ref(v___f_4281_);
lean_dec_ref(v_requestStream_4280_);
v___x_4300_ = lean_box(0);
v___x_4301_ = lean_apply_2(v___f_4282_, v___x_4300_, lean_box(0));
return v___x_4301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4302_, lean_object* v___f_4303_, lean_object* v___f_4304_, lean_object* v_x_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4302_, v___f_4303_, v___f_4304_, v_x_4305_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4308_, lean_object* v_responseBodyInstance_4309_, lean_object* v___f_4310_, lean_object* v___f_4311_, lean_object* v_x_4312_){
_start:
{
if (lean_obj_tag(v_x_4312_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4322_; 
lean_dec_ref(v___f_4311_);
lean_dec_ref(v___f_4310_);
lean_dec_ref(v_responseBodyInstance_4309_);
lean_dec_ref(v___f_4308_);
v_a_4314_ = lean_ctor_get(v_x_4312_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_x_4312_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4316_ = v_x_4312_;
v_isShared_4317_ = v_isSharedCheck_4322_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v_x_4312_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4322_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v_requestStream_4324_; lean_object* v_respStream_4325_; lean_object* v___x_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4409__overap_4331_; lean_object* v___x_4332_; lean_object* v___f_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; 
v_a_4323_ = lean_ctor_get(v_x_4312_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v_x_4312_, 1);
v_requestStream_4324_ = lean_ctor_get(v_a_4323_, 1);
lean_inc_ref_n(v_requestStream_4324_, 2);
v_respStream_4325_ = lean_ctor_get(v_a_4323_, 6);
lean_inc(v_respStream_4325_);
lean_dec(v_a_4323_);
v___x_4326_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4327_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4328_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4329_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4330_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4330_, 0, lean_box(0));
lean_closure_set(v___x_4330_, 1, lean_box(0));
lean_closure_set(v___x_4330_, 2, v___x_4326_);
lean_closure_set(v___x_4330_, 3, lean_box(0));
lean_closure_set(v___x_4330_, 4, lean_box(0));
lean_closure_set(v___x_4330_, 5, v___x_4329_);
lean_closure_set(v___x_4330_, 6, v___f_4308_);
v___x_4409__overap_4331_ = l_Std_Mutex_atomically___redArg(v___x_4326_, v___f_4327_, v___f_4328_, v_requestStream_4324_, v___x_4330_);
v___x_4332_ = lean_apply_1(v___x_4409__overap_4331_, lean_box(0));
v___f_4333_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4333_, 0, v_respStream_4325_);
lean_closure_set(v___f_4333_, 1, v_responseBodyInstance_4309_);
lean_closure_set(v___f_4333_, 2, v___f_4310_);
lean_closure_set(v___f_4333_, 3, v___f_4311_);
lean_inc_ref(v___f_4333_);
v___f_4334_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4334_, 0, v___f_4333_);
v___f_4335_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4335_, 0, v_requestStream_4324_);
lean_closure_set(v___f_4335_, 1, v___f_4334_);
lean_closure_set(v___f_4335_, 2, v___f_4333_);
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = 0;
v___x_4338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4336_, v___x_4337_, v___x_4332_, v___f_4335_);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4339_, lean_object* v_responseBodyInstance_4340_, lean_object* v___f_4341_, lean_object* v___f_4342_, lean_object* v_x_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4339_, v_responseBodyInstance_4340_, v___f_4341_, v___f_4342_, v_x_4343_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4346_, lean_object* v_responseBodyInstance_4347_, lean_object* v_handler_4348_, lean_object* v_config_4349_, lean_object* v___x_4350_, uint8_t v___x_4351_, lean_object* v___f_4352_, lean_object* v_x_4353_){
_start:
{
if (lean_obj_tag(v_x_4353_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4363_; 
lean_dec_ref(v___f_4352_);
lean_dec_ref(v___x_4350_);
lean_dec_ref(v_config_4349_);
lean_dec(v_handler_4348_);
lean_dec_ref(v_responseBodyInstance_4347_);
lean_dec_ref(v_h_4346_);
v_a_4355_ = lean_ctor_get(v_x_4353_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v_x_4353_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4357_ = v_x_4353_;
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v_x_4353_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; 
v___x_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
return v___x_4361_;
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v_a_4364_ = lean_ctor_get(v_x_4353_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v_x_4353_, 1);
v___x_4365_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4346_, v_responseBodyInstance_4347_, v_handler_4348_, v_config_4349_, v_a_4364_, v___x_4350_);
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4366_, v___x_4351_, v___x_4365_, v___f_4352_);
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4368_, lean_object* v_responseBodyInstance_4369_, lean_object* v_handler_4370_, lean_object* v_config_4371_, lean_object* v___x_4372_, lean_object* v___x_4373_, lean_object* v___f_4374_, lean_object* v_x_4375_, lean_object* v___y_4376_){
_start:
{
uint8_t v___x_5090__boxed_4377_; lean_object* v_res_4378_; 
v___x_5090__boxed_4377_ = lean_unbox(v___x_4373_);
v_res_4378_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4368_, v_responseBodyInstance_4369_, v_handler_4370_, v_config_4371_, v___x_4372_, v___x_5090__boxed_4377_, v___f_4374_, v_x_4375_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4379_, lean_object* v_h_4380_, lean_object* v_responseBodyInstance_4381_, lean_object* v_config_4382_, lean_object* v_handler_4383_, uint8_t v___x_4384_, lean_object* v___f_4385_, lean_object* v_x_4386_){
_start:
{
if (lean_obj_tag(v_x_4386_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v___f_4385_);
lean_dec(v_handler_4383_);
lean_dec_ref(v_config_4382_);
lean_dec_ref(v_responseBodyInstance_4381_);
lean_dec_ref(v_h_4380_);
lean_dec_ref(v_inst_4379_);
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
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_a_4397_ = lean_ctor_get(v_x_4386_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v_x_4386_, 1);
v___x_4398_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4379_, v_h_4380_, v_responseBodyInstance_4381_, v_config_4382_, v_handler_4383_, v_a_4397_);
v___x_4399_ = lean_unsigned_to_nat(0u);
v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4399_, v___x_4384_, v___x_4398_, v___f_4385_);
return v___x_4400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4401_, lean_object* v_h_4402_, lean_object* v_responseBodyInstance_4403_, lean_object* v_config_4404_, lean_object* v_handler_4405_, lean_object* v___x_4406_, lean_object* v___f_4407_, lean_object* v_x_4408_, lean_object* v___y_4409_){
_start:
{
uint8_t v___x_5131__boxed_4410_; lean_object* v_res_4411_; 
v___x_5131__boxed_4410_ = lean_unbox(v___x_4406_);
v_res_4411_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4401_, v_h_4402_, v_responseBodyInstance_4403_, v_config_4404_, v_handler_4405_, v___x_5131__boxed_4410_, v___f_4407_, v_x_4408_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4412_, lean_object* v_socket_4413_, lean_object* v_connectionContext_4414_, lean_object* v_h_4415_, lean_object* v_responseBodyInstance_4416_, lean_object* v_handler_4417_, lean_object* v_config_4418_, lean_object* v___f_4419_, lean_object* v_inst_4420_, uint8_t v___x_4421_, lean_object* v_x_4422_){
_start:
{
if (lean_obj_tag(v_x_4422_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4432_; 
lean_dec_ref(v_inst_4420_);
lean_dec_ref(v___f_4419_);
lean_dec_ref(v_config_4418_);
lean_dec(v_handler_4417_);
lean_dec_ref(v_responseBodyInstance_4416_);
lean_dec_ref(v_h_4415_);
lean_dec_ref(v_connectionContext_4414_);
lean_dec(v_socket_4413_);
v_a_4424_ = lean_ctor_get(v_x_4422_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_x_4422_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4426_ = v_x_4422_;
v_isShared_4427_ = v_isSharedCheck_4432_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v_x_4422_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4432_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v___x_4430_; 
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4475_; 
v_a_4433_ = lean_ctor_get(v_x_4422_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_x_4422_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4435_ = v_x_4422_;
v_isShared_4436_ = v_isSharedCheck_4475_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v_x_4422_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4475_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v_machine_4437_; lean_object* v_requestStream_4438_; lean_object* v_keepAliveTimeout_4439_; lean_object* v_currentTimeout_4440_; lean_object* v_headerTimeout_4441_; lean_object* v_response_4442_; lean_object* v_respStream_4443_; uint8_t v_requiresData_4444_; lean_object* v_expectData_4445_; uint8_t v_handlerDispatched_4446_; lean_object* v_pendingHead_4447_; uint8_t v___y_4458_; uint8_t v___y_4465_; uint8_t v___y_4467_; uint8_t v___y_4468_; uint8_t v___y_4470_; 
v_machine_4437_ = lean_ctor_get(v_a_4433_, 0);
v_requestStream_4438_ = lean_ctor_get(v_a_4433_, 1);
v_keepAliveTimeout_4439_ = lean_ctor_get(v_a_4433_, 2);
v_currentTimeout_4440_ = lean_ctor_get(v_a_4433_, 3);
v_headerTimeout_4441_ = lean_ctor_get(v_a_4433_, 4);
v_response_4442_ = lean_ctor_get(v_a_4433_, 5);
v_respStream_4443_ = lean_ctor_get(v_a_4433_, 6);
v_requiresData_4444_ = lean_ctor_get_uint8(v_a_4433_, sizeof(void*)*9);
v_expectData_4445_ = lean_ctor_get(v_a_4433_, 7);
v_handlerDispatched_4446_ = lean_ctor_get_uint8(v_a_4433_, sizeof(void*)*9 + 1);
v_pendingHead_4447_ = lean_ctor_get(v_a_4433_, 8);
if (lean_obj_tag(v_respStream_4443_) == 0)
{
v___y_4470_ = v___x_4412_;
goto v___jp_4469_;
}
else
{
v___y_4470_ = v___x_4421_;
goto v___jp_4469_;
}
v___jp_4448_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___f_4452_; lean_object* v___x_4453_; lean_object* v___f_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4449_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4449_, 0, v_machine_4437_);
lean_ctor_set(v___x_4449_, 1, v_requestStream_4438_);
lean_ctor_set(v___x_4449_, 2, v_keepAliveTimeout_4439_);
lean_ctor_set(v___x_4449_, 3, v_currentTimeout_4440_);
lean_ctor_set(v___x_4449_, 4, v_headerTimeout_4441_);
lean_ctor_set(v___x_4449_, 5, v_response_4442_);
lean_ctor_set(v___x_4449_, 6, v_respStream_4443_);
lean_ctor_set(v___x_4449_, 7, v_expectData_4445_);
lean_ctor_set(v___x_4449_, 8, v_pendingHead_4447_);
lean_ctor_set_uint8(v___x_4449_, sizeof(void*)*9, v___x_4412_);
lean_ctor_set_uint8(v___x_4449_, sizeof(void*)*9 + 1, v_handlerDispatched_4446_);
lean_inc_ref(v___x_4449_);
v___x_4450_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4413_, v_connectionContext_4414_, v___x_4449_);
v___x_4451_ = lean_box(v___x_4412_);
lean_inc_ref(v_config_4418_);
lean_inc(v_handler_4417_);
lean_inc_ref(v_responseBodyInstance_4416_);
lean_inc_ref(v_h_4415_);
v___f_4452_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4452_, 0, v_h_4415_);
lean_closure_set(v___f_4452_, 1, v_responseBodyInstance_4416_);
lean_closure_set(v___f_4452_, 2, v_handler_4417_);
lean_closure_set(v___f_4452_, 3, v_config_4418_);
lean_closure_set(v___f_4452_, 4, v___x_4449_);
lean_closure_set(v___f_4452_, 5, v___x_4451_);
lean_closure_set(v___f_4452_, 6, v___f_4419_);
v___x_4453_ = lean_box(v___x_4412_);
v___f_4454_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4454_, 0, v_inst_4420_);
lean_closure_set(v___f_4454_, 1, v_h_4415_);
lean_closure_set(v___f_4454_, 2, v_responseBodyInstance_4416_);
lean_closure_set(v___f_4454_, 3, v_config_4418_);
lean_closure_set(v___f_4454_, 4, v_handler_4417_);
lean_closure_set(v___f_4454_, 5, v___x_4453_);
lean_closure_set(v___f_4454_, 6, v___f_4452_);
v___x_4455_ = lean_unsigned_to_nat(0u);
v___x_4456_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4455_, v___x_4412_, v___x_4450_, v___f_4454_);
return v___x_4456_;
}
v___jp_4457_:
{
if (v_requiresData_4444_ == 0)
{
if (v___y_4458_ == 0)
{
lean_object* v___x_4459_; lean_object* v___x_4461_; 
lean_dec_ref(v_inst_4420_);
lean_dec_ref(v___f_4419_);
lean_dec_ref(v_config_4418_);
lean_dec(v_handler_4417_);
lean_dec_ref(v_responseBodyInstance_4416_);
lean_dec_ref(v_h_4415_);
lean_dec_ref(v_connectionContext_4414_);
lean_dec(v_socket_4413_);
v___x_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_a_4433_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4459_);
v___x_4461_ = v___x_4435_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4462_; 
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
}
else
{
lean_inc(v_pendingHead_4447_);
lean_inc(v_expectData_4445_);
lean_inc(v_respStream_4443_);
lean_inc_ref(v_response_4442_);
lean_inc(v_headerTimeout_4441_);
lean_inc(v_currentTimeout_4440_);
lean_inc(v_keepAliveTimeout_4439_);
lean_inc_ref(v_requestStream_4438_);
lean_inc_ref(v_machine_4437_);
lean_del_object(v___x_4435_);
lean_dec(v_a_4433_);
goto v___jp_4448_;
}
}
else
{
lean_inc(v_pendingHead_4447_);
lean_inc(v_expectData_4445_);
lean_inc(v_respStream_4443_);
lean_inc_ref(v_response_4442_);
lean_inc(v_headerTimeout_4441_);
lean_inc(v_currentTimeout_4440_);
lean_inc(v_keepAliveTimeout_4439_);
lean_inc_ref(v_requestStream_4438_);
lean_inc_ref(v_machine_4437_);
lean_del_object(v___x_4435_);
lean_dec(v_a_4433_);
goto v___jp_4448_;
}
}
v___jp_4464_:
{
if (v_handlerDispatched_4446_ == 0)
{
v___y_4458_ = v___y_4465_;
goto v___jp_4457_;
}
else
{
v___y_4458_ = v_handlerDispatched_4446_;
goto v___jp_4457_;
}
}
v___jp_4466_:
{
if (v___y_4467_ == 0)
{
v___y_4465_ = v___y_4468_;
goto v___jp_4464_;
}
else
{
v___y_4465_ = v___y_4467_;
goto v___jp_4464_;
}
}
v___jp_4469_:
{
lean_object* v_writer_4471_; uint8_t v_sentMessage_4472_; 
v_writer_4471_ = lean_ctor_get(v_machine_4437_, 1);
v_sentMessage_4472_ = lean_ctor_get_uint8(v_writer_4471_, sizeof(void*)*6);
if (v_sentMessage_4472_ == 0)
{
lean_object* v_reader_4473_; lean_object* v_state_4474_; 
v_reader_4473_ = lean_ctor_get(v_machine_4437_, 0);
v_state_4474_ = lean_ctor_get(v_reader_4473_, 0);
if (lean_obj_tag(v_state_4474_) == 2)
{
v___y_4467_ = v___y_4470_;
v___y_4468_ = v___x_4421_;
goto v___jp_4466_;
}
else
{
v___y_4467_ = v___y_4470_;
v___y_4468_ = v_sentMessage_4472_;
goto v___jp_4466_;
}
}
else
{
v___y_4467_ = v___y_4470_;
v___y_4468_ = v___x_4412_;
goto v___jp_4466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4476_, lean_object* v_socket_4477_, lean_object* v_connectionContext_4478_, lean_object* v_h_4479_, lean_object* v_responseBodyInstance_4480_, lean_object* v_handler_4481_, lean_object* v_config_4482_, lean_object* v___f_4483_, lean_object* v_inst_4484_, lean_object* v___x_4485_, lean_object* v_x_4486_, lean_object* v___y_4487_){
_start:
{
uint8_t v___x_5171__boxed_4488_; uint8_t v___x_5174__boxed_4489_; lean_object* v_res_4490_; 
v___x_5171__boxed_4488_ = lean_unbox(v___x_4476_);
v___x_5174__boxed_4489_ = lean_unbox(v___x_4485_);
v_res_4490_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5171__boxed_4488_, v_socket_4477_, v_connectionContext_4478_, v_h_4479_, v_responseBodyInstance_4480_, v_handler_4481_, v_config_4482_, v___f_4483_, v_inst_4484_, v___x_5174__boxed_4489_, v_x_4486_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4491_, lean_object* v_handler_4492_, lean_object* v_extensions_4493_, lean_object* v_connectionContext_4494_, uint8_t v___x_4495_, lean_object* v___f_4496_, lean_object* v_x_4497_){
_start:
{
if (lean_obj_tag(v_x_4497_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4507_; 
lean_dec_ref(v___f_4496_);
lean_dec_ref(v_connectionContext_4494_);
lean_dec(v_extensions_4493_);
lean_dec(v_handler_4492_);
lean_dec_ref(v_h_4491_);
v_a_4499_ = lean_ctor_get(v_x_4497_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_x_4497_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4501_ = v_x_4497_;
v_isShared_4502_ = v_isSharedCheck_4507_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v_x_4497_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4507_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
return v___x_4505_;
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v_a_4508_ = lean_ctor_get(v_x_4497_, 0);
lean_inc(v_a_4508_);
lean_dec_ref_known(v_x_4497_, 1);
v___x_4509_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4491_, v_handler_4492_, v_extensions_4493_, v_connectionContext_4494_, v_a_4508_);
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4510_, v___x_4495_, v___x_4509_, v___f_4496_);
return v___x_4511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4512_, lean_object* v_handler_4513_, lean_object* v_extensions_4514_, lean_object* v_connectionContext_4515_, lean_object* v___x_4516_, lean_object* v___f_4517_, lean_object* v_x_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v___x_5265__boxed_4520_; lean_object* v_res_4521_; 
v___x_5265__boxed_4520_ = lean_unbox(v___x_4516_);
v_res_4521_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4512_, v_handler_4513_, v_extensions_4514_, v_connectionContext_4515_, v___x_5265__boxed_4520_, v___f_4517_, v_x_4518_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4522_, lean_object* v_responseBodyInstance_4523_, lean_object* v_handler_4524_, lean_object* v_config_4525_, lean_object* v_connectionContext_4526_, lean_object* v_events_4527_, lean_object* v___x_4528_, uint8_t v___x_4529_, lean_object* v___f_4530_, lean_object* v_____r_4531_){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4533_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4522_, v_responseBodyInstance_4523_, v_handler_4524_, v_config_4525_, v_connectionContext_4526_, v_events_4527_, v___x_4528_);
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4534_, v___x_4529_, v___x_4533_, v___f_4530_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4536_, lean_object* v_responseBodyInstance_4537_, lean_object* v_handler_4538_, lean_object* v_config_4539_, lean_object* v_connectionContext_4540_, lean_object* v_events_4541_, lean_object* v___x_4542_, lean_object* v___x_4543_, lean_object* v___f_4544_, lean_object* v_____r_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v___x_5304__boxed_4547_; lean_object* v_res_4548_; 
v___x_5304__boxed_4547_ = lean_unbox(v___x_4543_);
v_res_4548_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4536_, v_responseBodyInstance_4537_, v_handler_4538_, v_config_4539_, v_connectionContext_4540_, v_events_4541_, v___x_4542_, v___x_5304__boxed_4547_, v___f_4544_, v_____r_4545_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4549_, lean_object* v___f_4550_, lean_object* v_x_4551_){
_start:
{
if (lean_obj_tag(v_x_4551_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v___f_4550_);
lean_dec_ref(v___x_4549_);
v_a_4553_ = lean_ctor_get(v_x_4551_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_x_4551_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4555_ = v_x_4551_;
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v_x_4551_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
return v___x_4559_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4573_; 
v_a_4562_ = lean_ctor_get(v_x_4551_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v_x_4551_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4564_ = v_x_4551_;
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v_x_4551_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
if (lean_obj_tag(v_a_4562_) == 0)
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
lean_dec_ref(v___f_4550_);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4549_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4566_);
v___x_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4566_);
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
else
{
lean_object* v_val_4571_; lean_object* v___x_4572_; 
lean_del_object(v___x_4564_);
lean_dec_ref(v___x_4549_);
v_val_4571_ = lean_ctor_get(v_a_4562_, 0);
lean_inc(v_val_4571_);
lean_dec_ref_known(v_a_4562_, 1);
v___x_4572_ = lean_apply_2(v___f_4550_, v_val_4571_, lean_box(0));
return v___x_4572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4574_, lean_object* v___f_4575_, lean_object* v_x_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4574_, v___f_4575_, v_x_4576_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(uint8_t v___x_4579_, lean_object* v_socket_4580_, lean_object* v_connectionContext_4581_, lean_object* v_h_4582_, lean_object* v_responseBodyInstance_4583_, lean_object* v_handler_4584_, lean_object* v_config_4585_, lean_object* v___f_4586_, lean_object* v_inst_4587_, lean_object* v_extensions_4588_, lean_object* v___f_4589_, lean_object* v___f_4590_, lean_object* v_x_4591_, lean_object* v_____s_4592_){
_start:
{
lean_object* v_machine_4594_; lean_object* v_reader_4595_; lean_object* v_requestStream_4596_; lean_object* v_keepAliveTimeout_4597_; lean_object* v_currentTimeout_4598_; lean_object* v_headerTimeout_4599_; lean_object* v_response_4600_; lean_object* v_respStream_4601_; uint8_t v_requiresData_4602_; lean_object* v_expectData_4603_; uint8_t v_handlerDispatched_4604_; lean_object* v_pendingHead_4605_; lean_object* v_writer_4606_; lean_object* v_state_4607_; uint8_t v___x_4608_; 
v_machine_4594_ = lean_ctor_get(v_____s_4592_, 0);
v_reader_4595_ = lean_ctor_get(v_machine_4594_, 0);
v_requestStream_4596_ = lean_ctor_get(v_____s_4592_, 1);
v_keepAliveTimeout_4597_ = lean_ctor_get(v_____s_4592_, 2);
v_currentTimeout_4598_ = lean_ctor_get(v_____s_4592_, 3);
v_headerTimeout_4599_ = lean_ctor_get(v_____s_4592_, 4);
v_response_4600_ = lean_ctor_get(v_____s_4592_, 5);
v_respStream_4601_ = lean_ctor_get(v_____s_4592_, 6);
v_requiresData_4602_ = lean_ctor_get_uint8(v_____s_4592_, sizeof(void*)*9);
v_expectData_4603_ = lean_ctor_get(v_____s_4592_, 7);
v_handlerDispatched_4604_ = lean_ctor_get_uint8(v_____s_4592_, sizeof(void*)*9 + 1);
v_pendingHead_4605_ = lean_ctor_get(v_____s_4592_, 8);
v_writer_4606_ = lean_ctor_get(v_machine_4594_, 1);
v_state_4607_ = lean_ctor_get(v_reader_4595_, 0);
v___x_4608_ = 0;
if (lean_obj_tag(v_state_4607_) == 6)
{
lean_object* v_state_4636_; 
v_state_4636_ = lean_ctor_get(v_writer_4606_, 2);
if (lean_obj_tag(v_state_4636_) == 7)
{
lean_object* v_outputData_4637_; lean_object* v_size_4638_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v_outputData_4637_ = lean_ctor_get(v_writer_4606_, 1);
v_size_4638_ = lean_ctor_get(v_outputData_4637_, 1);
v___x_4639_ = lean_unsigned_to_nat(0u);
v___x_4640_ = lean_nat_dec_eq(v_size_4638_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_inc(v_pendingHead_4605_);
lean_inc(v_expectData_4603_);
lean_inc(v_respStream_4601_);
lean_inc_ref(v_response_4600_);
lean_inc(v_headerTimeout_4599_);
lean_inc(v_currentTimeout_4598_);
lean_inc(v_keepAliveTimeout_4597_);
lean_inc_ref(v_requestStream_4596_);
lean_inc_ref(v_machine_4594_);
lean_dec_ref(v_____s_4592_);
goto v___jp_4609_;
}
else
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
lean_dec_ref(v___f_4590_);
lean_dec_ref(v___f_4589_);
lean_dec(v_extensions_4588_);
lean_dec_ref(v_inst_4587_);
lean_dec_ref(v___f_4586_);
lean_dec_ref(v_config_4585_);
lean_dec(v_handler_4584_);
lean_dec_ref(v_responseBodyInstance_4583_);
lean_dec_ref(v_h_4582_);
lean_dec_ref(v_connectionContext_4581_);
lean_dec(v_socket_4580_);
v___x_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4641_, 0, v_____s_4592_);
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
return v___x_4643_;
}
}
else
{
lean_inc(v_pendingHead_4605_);
lean_inc(v_expectData_4603_);
lean_inc(v_respStream_4601_);
lean_inc_ref(v_response_4600_);
lean_inc(v_headerTimeout_4599_);
lean_inc(v_currentTimeout_4598_);
lean_inc(v_keepAliveTimeout_4597_);
lean_inc_ref(v_requestStream_4596_);
lean_inc_ref(v_machine_4594_);
lean_dec_ref(v_____s_4592_);
goto v___jp_4609_;
}
}
else
{
lean_inc(v_pendingHead_4605_);
lean_inc(v_expectData_4603_);
lean_inc(v_respStream_4601_);
lean_inc_ref(v_response_4600_);
lean_inc(v_headerTimeout_4599_);
lean_inc(v_currentTimeout_4598_);
lean_inc(v_keepAliveTimeout_4597_);
lean_inc_ref(v_requestStream_4596_);
lean_inc_ref(v_machine_4594_);
lean_dec_ref(v_____s_4592_);
goto v___jp_4609_;
}
v___jp_4609_:
{
lean_object* v___x_4610_; lean_object* v_snd_4611_; lean_object* v_output_4612_; lean_object* v_fst_4613_; lean_object* v_events_4614_; lean_object* v_data_4615_; lean_object* v_size_4616_; uint8_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___f_4620_; lean_object* v___x_4621_; lean_object* v___f_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___f_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v___x_4610_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4608_, v_machine_4594_);
v_snd_4611_ = lean_ctor_get(v___x_4610_, 1);
lean_inc(v_snd_4611_);
v_output_4612_ = lean_ctor_get(v_snd_4611_, 1);
lean_inc_ref(v_output_4612_);
v_fst_4613_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_fst_4613_);
lean_dec_ref(v___x_4610_);
v_events_4614_ = lean_ctor_get(v_snd_4611_, 0);
lean_inc_ref_n(v_events_4614_, 2);
lean_dec(v_snd_4611_);
v_data_4615_ = lean_ctor_get(v_output_4612_, 0);
lean_inc_ref(v_data_4615_);
v_size_4616_ = lean_ctor_get(v_output_4612_, 1);
lean_inc(v_size_4616_);
lean_dec_ref(v_output_4612_);
v___x_4617_ = 1;
v___x_4618_ = lean_box(v___x_4579_);
v___x_4619_ = lean_box(v___x_4617_);
lean_inc_ref(v_inst_4587_);
lean_inc_ref_n(v_config_4585_, 2);
lean_inc_n(v_handler_4584_, 3);
lean_inc_ref_n(v_responseBodyInstance_4583_, 2);
lean_inc_ref_n(v_h_4582_, 3);
lean_inc_ref_n(v_connectionContext_4581_, 3);
lean_inc(v_socket_4580_);
v___f_4620_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 12, 10);
lean_closure_set(v___f_4620_, 0, v___x_4618_);
lean_closure_set(v___f_4620_, 1, v_socket_4580_);
lean_closure_set(v___f_4620_, 2, v_connectionContext_4581_);
lean_closure_set(v___f_4620_, 3, v_h_4582_);
lean_closure_set(v___f_4620_, 4, v_responseBodyInstance_4583_);
lean_closure_set(v___f_4620_, 5, v_handler_4584_);
lean_closure_set(v___f_4620_, 6, v_config_4585_);
lean_closure_set(v___f_4620_, 7, v___f_4586_);
lean_closure_set(v___f_4620_, 8, v_inst_4587_);
lean_closure_set(v___f_4620_, 9, v___x_4619_);
v___x_4621_ = lean_box(v___x_4579_);
v___f_4622_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4622_, 0, v_h_4582_);
lean_closure_set(v___f_4622_, 1, v_handler_4584_);
lean_closure_set(v___f_4622_, 2, v_extensions_4588_);
lean_closure_set(v___f_4622_, 3, v_connectionContext_4581_);
lean_closure_set(v___f_4622_, 4, v___x_4621_);
lean_closure_set(v___f_4622_, 5, v___f_4620_);
v___x_4623_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4623_, 0, v_fst_4613_);
lean_ctor_set(v___x_4623_, 1, v_requestStream_4596_);
lean_ctor_set(v___x_4623_, 2, v_keepAliveTimeout_4597_);
lean_ctor_set(v___x_4623_, 3, v_currentTimeout_4598_);
lean_ctor_set(v___x_4623_, 4, v_headerTimeout_4599_);
lean_ctor_set(v___x_4623_, 5, v_response_4600_);
lean_ctor_set(v___x_4623_, 6, v_respStream_4601_);
lean_ctor_set(v___x_4623_, 7, v_expectData_4603_);
lean_ctor_set(v___x_4623_, 8, v_pendingHead_4605_);
lean_ctor_set_uint8(v___x_4623_, sizeof(void*)*9, v_requiresData_4602_);
lean_ctor_set_uint8(v___x_4623_, sizeof(void*)*9 + 1, v_handlerDispatched_4604_);
v___x_4624_ = lean_box(v___x_4579_);
lean_inc_ref(v___f_4622_);
lean_inc_ref(v___x_4623_);
v___f_4625_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4625_, 0, v_h_4582_);
lean_closure_set(v___f_4625_, 1, v_responseBodyInstance_4583_);
lean_closure_set(v___f_4625_, 2, v_handler_4584_);
lean_closure_set(v___f_4625_, 3, v_config_4585_);
lean_closure_set(v___f_4625_, 4, v_connectionContext_4581_);
lean_closure_set(v___f_4625_, 5, v_events_4614_);
lean_closure_set(v___f_4625_, 6, v___x_4623_);
lean_closure_set(v___f_4625_, 7, v___x_4624_);
lean_closure_set(v___f_4625_, 8, v___f_4622_);
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = lean_nat_dec_lt(v___x_4626_, v_size_4616_);
lean_dec(v_size_4616_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_dec_ref(v___f_4625_);
lean_dec_ref(v_data_4615_);
lean_dec_ref(v___f_4590_);
lean_dec_ref(v___f_4589_);
lean_dec_ref(v_inst_4587_);
lean_dec(v_socket_4580_);
v___x_4628_ = lean_box(0);
v___x_4629_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4582_, v_responseBodyInstance_4583_, v_handler_4584_, v_config_4585_, v_connectionContext_4581_, v_events_4614_, v___x_4623_, v___x_4579_, v___f_4622_, v___x_4628_);
return v___x_4629_;
}
else
{
lean_object* v_sendAll_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___f_4634_; lean_object* v___x_4635_; 
lean_dec_ref(v___f_4622_);
lean_dec_ref(v_events_4614_);
lean_dec_ref(v_config_4585_);
lean_dec(v_handler_4584_);
lean_dec_ref(v_responseBodyInstance_4583_);
lean_dec_ref(v_h_4582_);
lean_dec_ref(v_connectionContext_4581_);
v_sendAll_4630_ = lean_ctor_get(v_inst_4587_, 1);
lean_inc_ref(v_sendAll_4630_);
lean_dec_ref(v_inst_4587_);
v___x_4631_ = lean_apply_3(v_sendAll_4630_, v_socket_4580_, v_data_4615_, lean_box(0));
v___x_4632_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4626_, v___x_4579_, v___x_4631_, v___f_4589_);
v___x_4633_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4626_, v___x_4579_, v___x_4632_, v___f_4590_);
v___f_4634_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4634_, 0, v___x_4623_);
lean_closure_set(v___f_4634_, 1, v___f_4625_);
v___x_4635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4626_, v___x_4579_, v___x_4633_, v___f_4634_);
return v___x_4635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v___x_4644_, lean_object* v_socket_4645_, lean_object* v_connectionContext_4646_, lean_object* v_h_4647_, lean_object* v_responseBodyInstance_4648_, lean_object* v_handler_4649_, lean_object* v_config_4650_, lean_object* v___f_4651_, lean_object* v_inst_4652_, lean_object* v_extensions_4653_, lean_object* v___f_4654_, lean_object* v___f_4655_, lean_object* v_x_4656_, lean_object* v_____s_4657_, lean_object* v___y_4658_){
_start:
{
uint8_t v___x_5378__boxed_4659_; lean_object* v_res_4660_; 
v___x_5378__boxed_4659_ = lean_unbox(v___x_4644_);
v_res_4660_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v___x_5378__boxed_4659_, v_socket_4645_, v_connectionContext_4646_, v_h_4647_, v_responseBodyInstance_4648_, v_handler_4649_, v_config_4650_, v___f_4651_, v_inst_4652_, v_extensions_4653_, v___f_4654_, v___f_4655_, v_x_4656_, v_____s_4657_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4661_, lean_object* v_x_4662_){
_start:
{
if (lean_obj_tag(v_x_4662_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4672_; 
v_a_4664_ = lean_ctor_get(v_x_4662_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_x_4662_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4666_ = v_x_4662_;
v_isShared_4667_ = v_isSharedCheck_4672_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v_x_4662_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4672_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4669_);
return v___x_4670_;
}
}
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
lean_dec_ref_known(v_x_4662_, 1);
v___x_4673_ = l_IO_Promise_result_x21___redArg(v_a_4661_);
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
return v___x_4674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4675_, lean_object* v_x_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4675_, v_x_4676_);
lean_dec(v_a_4675_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4679_, lean_object* v___x_4680_, lean_object* v___x_4681_, uint8_t v___x_4682_, lean_object* v_x_4683_){
_start:
{
if (lean_obj_tag(v_x_4683_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4693_; 
lean_dec_ref(v___x_4681_);
lean_dec(v___x_4680_);
lean_dec_ref(v___f_4679_);
v_a_4685_ = lean_ctor_get(v_x_4683_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v_x_4683_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4687_ = v_x_4683_;
v_isShared_4688_ = v_isSharedCheck_4693_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v_x_4683_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4693_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4691_; 
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
return v___x_4691_;
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4705_; 
v_a_4694_ = lean_ctor_get(v_x_4683_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v_x_4683_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4696_ = v_x_4683_;
v_isShared_4697_ = v_isSharedCheck_4705_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v_x_4683_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4705_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v___f_4699_; lean_object* v___x_4701_; 
lean_inc(v_a_4694_);
lean_inc(v___x_4680_);
v___x_4698_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4679_, v___x_4680_, v_a_4694_, v___x_4681_);
v___f_4699_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4699_, 0, v_a_4694_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4698_);
v___x_4701_ = v___x_4696_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4698_);
v___x_4701_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
v___x_4703_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4680_, v___x_4682_, v___x_4702_, v___f_4699_);
return v___x_4703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4706_, lean_object* v___x_4707_, lean_object* v___x_4708_, lean_object* v___x_4709_, lean_object* v_x_4710_, lean_object* v___y_4711_){
_start:
{
uint8_t v___x_5493__boxed_4712_; lean_object* v_res_4713_; 
v___x_5493__boxed_4712_ = lean_unbox(v___x_4709_);
v_res_4713_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4706_, v___x_4707_, v___x_4708_, v___x_5493__boxed_4712_, v_x_4710_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4714_, lean_object* v_machine_4715_, lean_object* v_a_4716_, lean_object* v___x_4717_, lean_object* v_socket_4718_, lean_object* v_connectionContext_4719_, lean_object* v_h_4720_, lean_object* v_responseBodyInstance_4721_, lean_object* v_handler_4722_, lean_object* v___f_4723_, lean_object* v_inst_4724_, lean_object* v_extensions_4725_, lean_object* v___f_4726_, lean_object* v___f_4727_, lean_object* v___f_4728_, lean_object* v_x_4729_){
_start:
{
if (lean_obj_tag(v_x_4729_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4739_; 
lean_dec_ref(v___f_4728_);
lean_dec_ref(v___f_4727_);
lean_dec_ref(v___f_4726_);
lean_dec(v_extensions_4725_);
lean_dec_ref(v_inst_4724_);
lean_dec_ref(v___f_4723_);
lean_dec(v_handler_4722_);
lean_dec_ref(v_responseBodyInstance_4721_);
lean_dec_ref(v_h_4720_);
lean_dec_ref(v_connectionContext_4719_);
lean_dec(v_socket_4718_);
lean_dec(v___x_4717_);
lean_dec_ref(v_a_4716_);
lean_dec_ref(v_machine_4715_);
lean_dec_ref(v_config_4714_);
v_a_4731_ = lean_ctor_get(v_x_4729_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_x_4729_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4733_ = v_x_4729_;
v_isShared_4734_ = v_isSharedCheck_4739_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v_x_4729_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4739_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; 
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
return v___x_4737_;
}
}
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4761_; 
v_a_4740_ = lean_ctor_get(v_x_4729_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_x_4729_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4742_ = v_x_4729_;
v_isShared_4743_ = v_isSharedCheck_4761_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v_x_4729_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4761_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_keepAliveTimeout_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___f_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___f_4754_; lean_object* v___x_4756_; 
v_keepAliveTimeout_4744_ = lean_ctor_get(v_config_4714_, 5);
lean_inc_n(v_keepAliveTimeout_4744_, 2);
v___x_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4745_, 0, v_keepAliveTimeout_4744_);
v___x_4746_ = lean_box(0);
v___x_4747_ = 0;
v___x_4748_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4748_, 0, v_machine_4715_);
lean_ctor_set(v___x_4748_, 1, v_a_4716_);
lean_ctor_set(v___x_4748_, 2, v___x_4745_);
lean_ctor_set(v___x_4748_, 3, v_keepAliveTimeout_4744_);
lean_ctor_set(v___x_4748_, 4, v___x_4746_);
lean_ctor_set(v___x_4748_, 5, v_a_4740_);
lean_ctor_set(v___x_4748_, 6, v___x_4746_);
lean_ctor_set(v___x_4748_, 7, v___x_4717_);
lean_ctor_set(v___x_4748_, 8, v___x_4746_);
lean_ctor_set_uint8(v___x_4748_, sizeof(void*)*9, v___x_4747_);
lean_ctor_set_uint8(v___x_4748_, sizeof(void*)*9 + 1, v___x_4747_);
v___x_4749_ = lean_io_promise_new();
v___x_4750_ = lean_box(v___x_4747_);
v___f_4751_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 15, 12);
lean_closure_set(v___f_4751_, 0, v___x_4750_);
lean_closure_set(v___f_4751_, 1, v_socket_4718_);
lean_closure_set(v___f_4751_, 2, v_connectionContext_4719_);
lean_closure_set(v___f_4751_, 3, v_h_4720_);
lean_closure_set(v___f_4751_, 4, v_responseBodyInstance_4721_);
lean_closure_set(v___f_4751_, 5, v_handler_4722_);
lean_closure_set(v___f_4751_, 6, v_config_4714_);
lean_closure_set(v___f_4751_, 7, v___f_4723_);
lean_closure_set(v___f_4751_, 8, v_inst_4724_);
lean_closure_set(v___f_4751_, 9, v_extensions_4725_);
lean_closure_set(v___f_4751_, 10, v___f_4726_);
lean_closure_set(v___f_4751_, 11, v___f_4727_);
v___x_4752_ = lean_unsigned_to_nat(0u);
v___x_4753_ = lean_box(v___x_4747_);
v___f_4754_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4754_, 0, v___f_4751_);
lean_closure_set(v___f_4754_, 1, v___x_4752_);
lean_closure_set(v___f_4754_, 2, v___x_4748_);
lean_closure_set(v___f_4754_, 3, v___x_4753_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4749_);
v___x_4756_ = v___x_4742_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4749_);
v___x_4756_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
v___x_4758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4752_, v___x_4747_, v___x_4757_, v___f_4754_);
v___x_4759_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4752_, v___x_4747_, v___x_4758_, v___f_4728_);
return v___x_4759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4762_ = _args[0];
lean_object* v_machine_4763_ = _args[1];
lean_object* v_a_4764_ = _args[2];
lean_object* v___x_4765_ = _args[3];
lean_object* v_socket_4766_ = _args[4];
lean_object* v_connectionContext_4767_ = _args[5];
lean_object* v_h_4768_ = _args[6];
lean_object* v_responseBodyInstance_4769_ = _args[7];
lean_object* v_handler_4770_ = _args[8];
lean_object* v___f_4771_ = _args[9];
lean_object* v_inst_4772_ = _args[10];
lean_object* v_extensions_4773_ = _args[11];
lean_object* v___f_4774_ = _args[12];
lean_object* v___f_4775_ = _args[13];
lean_object* v___f_4776_ = _args[14];
lean_object* v_x_4777_ = _args[15];
lean_object* v___y_4778_ = _args[16];
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4762_, v_machine_4763_, v_a_4764_, v___x_4765_, v_socket_4766_, v_connectionContext_4767_, v_h_4768_, v_responseBodyInstance_4769_, v_handler_4770_, v___f_4771_, v_inst_4772_, v_extensions_4773_, v___f_4774_, v___f_4775_, v___f_4776_, v_x_4777_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4780_, lean_object* v_machine_4781_, lean_object* v_socket_4782_, lean_object* v_connectionContext_4783_, lean_object* v_h_4784_, lean_object* v_responseBodyInstance_4785_, lean_object* v_handler_4786_, lean_object* v___f_4787_, lean_object* v_inst_4788_, lean_object* v_extensions_4789_, lean_object* v___f_4790_, lean_object* v___f_4791_, lean_object* v___f_4792_, lean_object* v_x_4793_){
_start:
{
if (lean_obj_tag(v_x_4793_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4803_; 
lean_dec_ref(v___f_4792_);
lean_dec_ref(v___f_4791_);
lean_dec_ref(v___f_4790_);
lean_dec(v_extensions_4789_);
lean_dec_ref(v_inst_4788_);
lean_dec_ref(v___f_4787_);
lean_dec(v_handler_4786_);
lean_dec_ref(v_responseBodyInstance_4785_);
lean_dec_ref(v_h_4784_);
lean_dec_ref(v_connectionContext_4783_);
lean_dec(v_socket_4782_);
lean_dec_ref(v_machine_4781_);
lean_dec_ref(v_config_4780_);
v_a_4795_ = lean_ctor_get(v_x_4793_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_x_4793_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4797_ = v_x_4793_;
v_isShared_4798_ = v_isSharedCheck_4803_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v_x_4793_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4803_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4801_; 
v___x_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
return v___x_4801_;
}
}
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4818_; 
v_a_4804_ = lean_ctor_get(v_x_4793_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_x_4793_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4806_ = v_x_4793_;
v_isShared_4807_ = v_isSharedCheck_4818_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v_x_4793_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4818_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___f_4810_; lean_object* v___x_4812_; 
v___x_4808_ = lean_box(0);
v___x_4809_ = l_Std_CloseableChannel_new___redArg(v___x_4808_);
v___f_4810_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4810_, 0, v_config_4780_);
lean_closure_set(v___f_4810_, 1, v_machine_4781_);
lean_closure_set(v___f_4810_, 2, v_a_4804_);
lean_closure_set(v___f_4810_, 3, v___x_4808_);
lean_closure_set(v___f_4810_, 4, v_socket_4782_);
lean_closure_set(v___f_4810_, 5, v_connectionContext_4783_);
lean_closure_set(v___f_4810_, 6, v_h_4784_);
lean_closure_set(v___f_4810_, 7, v_responseBodyInstance_4785_);
lean_closure_set(v___f_4810_, 8, v_handler_4786_);
lean_closure_set(v___f_4810_, 9, v___f_4787_);
lean_closure_set(v___f_4810_, 10, v_inst_4788_);
lean_closure_set(v___f_4810_, 11, v_extensions_4789_);
lean_closure_set(v___f_4810_, 12, v___f_4790_);
lean_closure_set(v___f_4810_, 13, v___f_4791_);
lean_closure_set(v___f_4810_, 14, v___f_4792_);
if (v_isShared_4807_ == 0)
{
lean_ctor_set(v___x_4806_, 0, v___x_4809_);
v___x_4812_ = v___x_4806_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4809_);
v___x_4812_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; lean_object* v___x_4816_; 
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
v___x_4814_ = lean_unsigned_to_nat(0u);
v___x_4815_ = 0;
v___x_4816_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4814_, v___x_4815_, v___x_4813_, v___f_4810_);
return v___x_4816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4819_, lean_object* v_machine_4820_, lean_object* v_socket_4821_, lean_object* v_connectionContext_4822_, lean_object* v_h_4823_, lean_object* v_responseBodyInstance_4824_, lean_object* v_handler_4825_, lean_object* v___f_4826_, lean_object* v_inst_4827_, lean_object* v_extensions_4828_, lean_object* v___f_4829_, lean_object* v___f_4830_, lean_object* v___f_4831_, lean_object* v_x_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4819_, v_machine_4820_, v_socket_4821_, v_connectionContext_4822_, v_h_4823_, v_responseBodyInstance_4824_, v_handler_4825_, v___f_4826_, v_inst_4827_, v_extensions_4828_, v___f_4829_, v___f_4830_, v___f_4831_, v_x_4832_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4838_, lean_object* v_h_4839_, lean_object* v_connection_4840_, lean_object* v_config_4841_, lean_object* v_connectionContext_4842_, lean_object* v_handler_4843_){
_start:
{
lean_object* v_responseBodyInstance_4845_; lean_object* v_onFailure_4846_; lean_object* v___x_4847_; lean_object* v_socket_4848_; lean_object* v_machine_4849_; lean_object* v_extensions_4850_; lean_object* v___f_4851_; lean_object* v___f_4852_; lean_object* v___f_4853_; lean_object* v___f_4854_; lean_object* v___f_4855_; lean_object* v___f_4856_; lean_object* v___f_4857_; lean_object* v___f_4858_; lean_object* v___f_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; lean_object* v___x_4862_; 
v_responseBodyInstance_4845_ = lean_ctor_get(v_h_4839_, 0);
lean_inc_ref_n(v_responseBodyInstance_4845_, 2);
v_onFailure_4846_ = lean_ctor_get(v_h_4839_, 2);
v___x_4847_ = l_Std_Http_Body_mkStream();
v_socket_4848_ = lean_ctor_get(v_connection_4840_, 0);
lean_inc_n(v_socket_4848_, 2);
v_machine_4849_ = lean_ctor_get(v_connection_4840_, 1);
lean_inc_ref(v_machine_4849_);
v_extensions_4850_ = lean_ctor_get(v_connection_4840_, 2);
lean_inc(v_extensions_4850_);
lean_dec_ref(v_connection_4840_);
v___f_4851_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4852_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
lean_inc(v_handler_4843_);
lean_inc_ref(v_onFailure_4846_);
v___f_4853_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4853_, 0, v_onFailure_4846_);
lean_closure_set(v___f_4853_, 1, v_handler_4843_);
lean_closure_set(v___f_4853_, 2, v___f_4852_);
v___f_4854_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4855_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4838_);
v___f_4856_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4856_, 0, v_inst_4838_);
lean_closure_set(v___f_4856_, 1, v_socket_4848_);
lean_inc_ref(v___f_4856_);
v___f_4857_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4857_, 0, v___f_4856_);
v___f_4858_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4858_, 0, v___f_4851_);
lean_closure_set(v___f_4858_, 1, v_responseBodyInstance_4845_);
lean_closure_set(v___f_4858_, 2, v___f_4857_);
lean_closure_set(v___f_4858_, 3, v___f_4856_);
v___f_4859_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4859_, 0, v_config_4841_);
lean_closure_set(v___f_4859_, 1, v_machine_4849_);
lean_closure_set(v___f_4859_, 2, v_socket_4848_);
lean_closure_set(v___f_4859_, 3, v_connectionContext_4842_);
lean_closure_set(v___f_4859_, 4, v_h_4839_);
lean_closure_set(v___f_4859_, 5, v_responseBodyInstance_4845_);
lean_closure_set(v___f_4859_, 6, v_handler_4843_);
lean_closure_set(v___f_4859_, 7, v___f_4855_);
lean_closure_set(v___f_4859_, 8, v_inst_4838_);
lean_closure_set(v___f_4859_, 9, v_extensions_4850_);
lean_closure_set(v___f_4859_, 10, v___f_4854_);
lean_closure_set(v___f_4859_, 11, v___f_4853_);
lean_closure_set(v___f_4859_, 12, v___f_4858_);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = 0;
v___x_4862_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4860_, v___x_4861_, v___x_4847_, v___f_4859_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4863_, lean_object* v_h_4864_, lean_object* v_connection_4865_, lean_object* v_config_4866_, lean_object* v_connectionContext_4867_, lean_object* v_handler_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4863_, v_h_4864_, v_connection_4865_, v_config_4866_, v_connectionContext_4867_, v_handler_4868_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4871_, lean_object* v_00_u03c3_4872_, lean_object* v_inst_4873_, lean_object* v_h_4874_, lean_object* v_connection_4875_, lean_object* v_config_4876_, lean_object* v_connectionContext_4877_, lean_object* v_handler_4878_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4873_, v_h_4874_, v_connection_4875_, v_config_4876_, v_connectionContext_4877_, v_handler_4878_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4881_, lean_object* v_00_u03c3_4882_, lean_object* v_inst_4883_, lean_object* v_h_4884_, lean_object* v_connection_4885_, lean_object* v_config_4886_, lean_object* v_connectionContext_4887_, lean_object* v_handler_4888_, lean_object* v_a_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4881_, v_00_u03c3_4882_, v_inst_4883_, v_h_4884_, v_connection_4885_, v_config_4886_, v_connectionContext_4887_, v_handler_4888_);
return v_res_4890_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4891_; lean_object* v___x_4892_; 
v___x_4891_ = 0;
v___x_4892_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4891_);
return v___x_4892_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = lean_unsigned_to_nat(4096u);
v___x_4894_ = lean_mk_empty_byte_array(v___x_4893_);
return v___x_4894_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4896_ = l_ByteArray_mkIterator(v___x_4895_);
return v___x_4896_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4897_ = 0;
v___x_4898_ = lean_unsigned_to_nat(0u);
v___x_4899_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4900_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4901_ = lean_box(0);
v___x_4902_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
lean_ctor_set(v___x_4902_, 1, v___x_4900_);
lean_ctor_set(v___x_4902_, 2, v___x_4899_);
lean_ctor_set(v___x_4902_, 3, v___x_4898_);
lean_ctor_set(v___x_4902_, 4, v___x_4898_);
lean_ctor_set(v___x_4902_, 5, v___x_4898_);
lean_ctor_set_uint8(v___x_4902_, sizeof(void*)*6, v___x_4897_);
return v___x_4902_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = 1;
v___x_4911_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4910_);
return v___x_4911_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4912_; uint8_t v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4912_ = lean_unsigned_to_nat(0u);
v___x_4913_ = 0;
v___x_4914_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4915_ = lean_box(0);
v___x_4916_ = lean_box(0);
v___x_4917_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4918_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4919_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v___x_4917_);
lean_ctor_set(v___x_4919_, 2, v___x_4916_);
lean_ctor_set(v___x_4919_, 3, v___x_4915_);
lean_ctor_set(v___x_4919_, 4, v___x_4914_);
lean_ctor_set(v___x_4919_, 5, v___x_4912_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*6, v___x_4913_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*6 + 1, v___x_4913_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*6 + 2, v___x_4913_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4920_, lean_object* v_client_4921_, lean_object* v_extensions_4922_, lean_object* v_inst_4923_, lean_object* v_inst_4924_, lean_object* v_handler_4925_, lean_object* v_x_4926_){
_start:
{
if (lean_obj_tag(v_x_4926_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4936_; 
lean_dec(v_handler_4925_);
lean_dec_ref(v_inst_4924_);
lean_dec_ref(v_inst_4923_);
lean_dec(v_extensions_4922_);
lean_dec(v_client_4921_);
lean_dec_ref(v_config_4920_);
v_a_4928_ = lean_ctor_get(v_x_4926_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v_x_4926_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4930_ = v_x_4926_;
v_isShared_4931_ = v_isSharedCheck_4936_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v_x_4926_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4936_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4934_; 
v___x_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4933_);
return v___x_4934_;
}
}
}
else
{
lean_object* v_a_4937_; uint8_t v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; uint8_t v_enableKeepAlive_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v_a_4937_ = lean_ctor_get(v_x_4926_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v_x_4926_, 1);
v___x_4938_ = 0;
v___x_4939_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4940_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4941_ = lean_box(0);
v___x_4942_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4943_ = l_Std_Http_Config_toH1Config(v_config_4920_);
v_enableKeepAlive_4944_ = lean_ctor_get_uint8(v___x_4943_, sizeof(void*)*18);
v___x_4945_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4945_, 0, v___x_4939_);
lean_ctor_set(v___x_4945_, 1, v___x_4942_);
lean_ctor_set(v___x_4945_, 2, v___x_4943_);
lean_ctor_set(v___x_4945_, 3, v___x_4940_);
lean_ctor_set(v___x_4945_, 4, v___x_4941_);
lean_ctor_set(v___x_4945_, 5, v___x_4941_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*6, v_enableKeepAlive_4944_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*6 + 1, v___x_4938_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*6 + 2, v___x_4938_);
v___x_4946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4946_, 0, v_client_4921_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
lean_ctor_set(v___x_4946_, 2, v_extensions_4922_);
v___x_4947_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4923_, v_inst_4924_, v___x_4946_, v_config_4920_, v_a_4937_, v_handler_4925_);
return v___x_4947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4948_, lean_object* v_client_4949_, lean_object* v_extensions_4950_, lean_object* v_inst_4951_, lean_object* v_inst_4952_, lean_object* v_handler_4953_, lean_object* v_x_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4948_, v_client_4949_, v_extensions_4950_, v_inst_4951_, v_inst_4952_, v_handler_4953_, v_x_4954_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4957_, lean_object* v_inst_4958_, lean_object* v_client_4959_, lean_object* v_handler_4960_, lean_object* v_config_4961_, lean_object* v_extensions_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___f_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; uint8_t v___x_4969_; lean_object* v___x_4970_; 
v___f_4965_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4965_, 0, v_config_4961_);
lean_closure_set(v___f_4965_, 1, v_client_4959_);
lean_closure_set(v___f_4965_, 2, v_extensions_4962_);
lean_closure_set(v___f_4965_, 3, v_inst_4957_);
lean_closure_set(v___f_4965_, 4, v_inst_4958_);
lean_closure_set(v___f_4965_, 5, v_handler_4960_);
lean_inc_ref(v_a_4963_);
v___x_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4966_, 0, v_a_4963_);
v___x_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
v___x_4968_ = lean_unsigned_to_nat(0u);
v___x_4969_ = 0;
v___x_4970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4968_, v___x_4969_, v___x_4967_, v___f_4965_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4971_, lean_object* v_inst_4972_, lean_object* v_client_4973_, lean_object* v_handler_4974_, lean_object* v_config_4975_, lean_object* v_extensions_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4971_, v_inst_4972_, v_client_4973_, v_handler_4974_, v_config_4975_, v_extensions_4976_, v_a_4977_);
lean_dec_ref(v_a_4977_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4980_, lean_object* v_00_u03c3_4981_, lean_object* v_inst_4982_, lean_object* v_inst_4983_, lean_object* v_client_4984_, lean_object* v_handler_4985_, lean_object* v_config_4986_, lean_object* v_extensions_4987_, lean_object* v_a_4988_){
_start:
{
lean_object* v___x_4990_; 
v___x_4990_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4982_, v_inst_4983_, v_client_4984_, v_handler_4985_, v_config_4986_, v_extensions_4987_, v_a_4988_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4991_, lean_object* v_00_u03c3_4992_, lean_object* v_inst_4993_, lean_object* v_inst_4994_, lean_object* v_client_4995_, lean_object* v_handler_4996_, lean_object* v_config_4997_, lean_object* v_extensions_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Std_Http_Server_serveConnection(v_t_4991_, v_00_u03c3_4992_, v_inst_4993_, v_inst_4994_, v_client_4995_, v_handler_4996_, v_config_4997_, v_extensions_4998_, v_a_4999_);
lean_dec_ref(v_a_4999_);
return v_res_5001_;
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
