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
extern lean_object* l_instInhabitedError;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
uint8_t v_x_3357__boxed_223_; lean_object* v_res_224_; 
v_x_3357__boxed_223_ = lean_unbox(v_x_221_);
v_res_224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3357__boxed_223_);
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
uint8_t v___y_1371__boxed_548_; lean_object* v_res_549_; 
v___y_1371__boxed_548_ = lean_unbox(v___y_546_);
v_res_549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1371__boxed_548_);
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
uint8_t v___x_1415__boxed_577_; lean_object* v_res_578_; 
v___x_1415__boxed_577_ = lean_unbox(v___x_574_);
v_res_578_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1415__boxed_577_, v_x_575_);
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
uint8_t v___x_1430__boxed_623_; uint8_t v___x_1435__boxed_624_; lean_object* v_res_625_; 
v___x_1430__boxed_623_ = lean_unbox(v___x_614_);
v___x_1435__boxed_624_ = lean_unbox(v___x_619_);
v_res_625_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_613_, v___x_1430__boxed_623_, v_a_615_, v___f_616_, v___f_617_, v___x_618_, v___x_1435__boxed_624_, v___f_620_, v_x_621_);
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
uint8_t v___x_1504__boxed_650_; lean_object* v_res_651_; 
v___x_1504__boxed_650_ = lean_unbox(v___x_646_);
v_res_651_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_644_, v___x_645_, v___x_1504__boxed_650_, v___f_647_, v_x_648_);
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
uint8_t v___x_1546__boxed_702_; lean_object* v_res_703_; 
v___x_1546__boxed_702_ = lean_unbox(v___x_695_);
v_res_703_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v___f_692_, v___x_693_, v_connectionContext_694_, v___x_1546__boxed_702_, v_a_696_, v___f_697_, v___f_698_, v_config_699_, v_x_700_);
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
uint8_t v___x_1627__boxed_756_; lean_object* v_res_757_; 
v___x_1627__boxed_756_ = lean_unbox(v___x_749_);
v_res_757_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_745_, v_handler_746_, v_head_747_, v_connectionContext_748_, v___x_1627__boxed_756_, v___f_750_, v___f_751_, v_config_752_, v___f_753_, v_x_754_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_959_, lean_object* v___x_960_, lean_object* v_indexes_961_, lean_object* v_status_962_, uint8_t v_version_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_status_962_);
lean_dec_ref(v_indexes_961_);
lean_dec_ref(v___x_960_);
lean_dec_ref(v_entries_959_);
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
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_991_; 
v_a_975_ = lean_ctor_get(v_x_964_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_991_ == 0)
{
v___x_977_ = v_x_964_;
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v_x_964_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_i_981_; lean_object* v___x_982_; lean_object* v_entries_983_; lean_object* v_indexes_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_979_ = l_Std_Time_DateTime_toRFC822String(v_a_975_);
v___x_980_ = l_Std_Http_Header_Value_ofString_x21(v___x_979_);
v_i_981_ = lean_array_get_size(v_entries_959_);
lean_inc_ref(v___x_960_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_960_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
v_entries_983_ = lean_array_push(v_entries_959_, v___x_982_);
v_indexes_984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_981_, v_indexes_961_, v___x_960_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_entries_983_);
lean_ctor_set(v___x_985_, 1, v_indexes_984_);
v___x_986_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_986_, 0, v_status_962_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*2, v_version_963_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_986_);
v___x_988_ = v___x_977_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_992_, lean_object* v___x_993_, lean_object* v_indexes_994_, lean_object* v_status_995_, lean_object* v_version_996_, lean_object* v_x_997_, lean_object* v___y_998_){
_start:
{
uint8_t v_version_boxed_999_; lean_object* v_res_1000_; 
v_version_boxed_999_ = lean_unbox(v_version_996_);
v_res_1000_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_992_, v___x_993_, v_indexes_994_, v_status_995_, v_version_boxed_999_, v_x_997_);
return v_res_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = lean_nat_to_int(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1003_, lean_object* v_a_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v_offset_1006_; lean_object* v_second_1007_; lean_object* v_nano_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_offset_1006_ = lean_ctor_get(v_tz_1003_, 0);
v_second_1007_ = lean_ctor_get(v_a_1004_, 0);
v_nano_1008_ = lean_ctor_get(v_a_1004_, 1);
v___x_1009_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_1010_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_1011_ = lean_int_mul(v_second_1007_, v___x_1010_);
v___x_1012_ = lean_int_add(v___x_1011_, v_nano_1008_);
lean_dec(v___x_1011_);
v___x_1013_ = lean_int_mul(v_offset_1006_, v___x_1010_);
v___x_1014_ = lean_int_add(v___x_1013_, v___x_1009_);
lean_dec(v___x_1013_);
v___x_1015_ = lean_int_add(v___x_1012_, v___x_1014_);
lean_dec(v___x_1014_);
lean_dec(v___x_1012_);
v___x_1016_ = l_Std_Time_Duration_ofNanoseconds(v___x_1015_);
lean_dec(v___x_1015_);
v___x_1017_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1018_, lean_object* v_a_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1018_, v_a_1019_, v_x_1020_);
lean_dec_ref(v_a_1019_);
lean_dec_ref(v_tz_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object* v_m_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_buckets_1024_; lean_object* v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; uint64_t v___x_1028_; uint64_t v_fold_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_buckets_1024_ = lean_ctor_get(v_m_1022_, 1);
v___x_1025_ = lean_array_get_size(v_buckets_1024_);
v___x_1026_ = lean_string_hash(v_a_1023_);
v___x_1027_ = 32ULL;
v___x_1028_ = lean_uint64_shift_right(v___x_1026_, v___x_1027_);
v_fold_1029_ = lean_uint64_xor(v___x_1026_, v___x_1028_);
v___x_1030_ = 16ULL;
v___x_1031_ = lean_uint64_shift_right(v_fold_1029_, v___x_1030_);
v___x_1032_ = lean_uint64_xor(v_fold_1029_, v___x_1031_);
v___x_1033_ = lean_uint64_to_usize(v___x_1032_);
v___x_1034_ = lean_usize_of_nat(v___x_1025_);
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_sub(v___x_1034_, v___x_1035_);
v___x_1037_ = lean_usize_land(v___x_1033_, v___x_1036_);
v___x_1038_ = lean_array_uget_borrowed(v_buckets_1024_, v___x_1037_);
v___x_1039_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1023_, v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object* v_m_1040_, lean_object* v_a_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1040_, v_a_1041_);
lean_dec_ref(v_a_1041_);
lean_dec_ref(v_m_1040_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1045_, lean_object* v_head_1046_){
_start:
{
lean_object* v_headers_1051_; uint8_t v_generateDate_1052_; lean_object* v_status_1053_; uint8_t v_version_1054_; lean_object* v_entries_1055_; lean_object* v_indexes_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v_val_1061_; lean_object* v_a_1067_; uint8_t v___y_1070_; uint8_t v___x_1089_; 
v_headers_1051_ = lean_ctor_get(v_head_1046_, 1);
v_generateDate_1052_ = lean_ctor_get_uint8(v_config_1045_, sizeof(void*)*24 + 1);
v_status_1053_ = lean_ctor_get(v_head_1046_, 0);
v_version_1054_ = lean_ctor_get_uint8(v_head_1046_, sizeof(void*)*2);
v_entries_1055_ = lean_ctor_get(v_headers_1051_, 0);
v_indexes_1056_ = lean_ctor_get(v_headers_1051_, 1);
v___x_1057_ = l_Std_Http_Header_Name_date;
v___x_1058_ = lean_box(v_version_1054_);
lean_inc(v_status_1053_);
lean_inc_ref(v_indexes_1056_);
lean_inc_ref(v_entries_1055_);
v___f_1059_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1059_, 0, v_entries_1055_);
lean_closure_set(v___f_1059_, 1, v___x_1057_);
lean_closure_set(v___f_1059_, 2, v_indexes_1056_);
lean_closure_set(v___f_1059_, 3, v_status_1053_);
lean_closure_set(v___f_1059_, 4, v___x_1058_);
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_1056_, v___x_1057_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
v___x_1090_ = 1;
v___y_1070_ = v___x_1090_;
goto v___jp_1069_;
}
else
{
uint8_t v___x_1091_; 
v___x_1091_ = 0;
v___y_1070_ = v___x_1091_;
goto v___jp_1069_;
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
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_val_1061_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = 0;
v___x_1065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1063_, v___x_1064_, v___x_1062_, v___f_1059_);
return v___x_1065_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1067_);
v_val_1061_ = v___x_1068_;
goto v___jp_1060_;
}
v___jp_1069_:
{
if (v_generateDate_1052_ == 0)
{
lean_dec_ref(v___f_1059_);
goto v___jp_1048_;
}
else
{
if (v___y_1070_ == 0)
{
lean_dec_ref(v___f_1059_);
goto v___jp_1048_;
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_head_1046_);
v___x_1071_ = lean_get_current_time();
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1074_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1086_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_tz_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_inc(v_a_1075_);
v_tz_1079_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1075_, v_a_1072_);
lean_inc(v_a_1072_);
lean_inc_ref(v_tz_1079_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1080_, 0, v_tz_1079_);
lean_closure_set(v___f_1080_, 1, v_a_1072_);
v___x_1081_ = lean_mk_thunk(v___f_1080_);
v___x_1082_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_a_1072_);
lean_ctor_set(v___x_1082_, 2, v_a_1075_);
lean_ctor_set(v___x_1082_, 3, v_tz_1079_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
lean_ctor_set(v___x_1077_, 0, v___x_1082_);
v___x_1084_ = v___x_1077_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v_val_1061_ = v___x_1084_;
goto v___jp_1060_;
}
}
}
else
{
lean_object* v_a_1087_; 
lean_dec(v_a_1072_);
v_a_1087_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1074_, 1);
v_a_1067_ = v_a_1087_;
goto v___jp_1066_;
}
}
else
{
lean_object* v_a_1088_; 
v_a_1088_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1071_, 1);
v_a_1067_ = v_a_1088_;
goto v___jp_1066_;
}
}
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_00_u03b2_1096_, lean_object* v_m_1097_, lean_object* v_a_1098_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1097_, v_a_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_m_1101_, lean_object* v_a_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(v_00_u03b2_1100_, v_m_1101_, v_a_1102_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_m_1101_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__5(lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_nat_to_int(v_a_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_nat_to_int(v_a_1107_);
v___x_1109_ = l_Rat_ofInt(v___x_1108_);
return v___x_1109_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, lean_object* v_x1_1193_, lean_object* v_x2_1194_){
_start:
{
lean_object* v_fst_1195_; uint8_t v___x_1196_; 
v_fst_1195_ = lean_ctor_get(v_x2_1194_, 0);
lean_inc(v_fst_1195_);
v___x_1196_ = lean_string_dec_eq(v___x_1190_, v_fst_1195_);
if (v___x_1196_ == 0)
{
lean_object* v_entries_1197_; lean_object* v_indexes_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1209_; 
v_entries_1197_ = lean_ctor_get(v_x1_1193_, 0);
v_indexes_1198_ = lean_ctor_get(v_x1_1193_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x1_1193_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1200_ = v_x1_1193_;
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_indexes_1198_);
lean_inc(v_entries_1197_);
lean_dec(v_x1_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_i_1202_; lean_object* v_f_1203_; lean_object* v_entries_1204_; lean_object* v_indexes_1205_; lean_object* v___x_1207_; 
v_i_1202_ = lean_array_get_size(v_entries_1197_);
v_f_1203_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1203_, 0, v_i_1202_);
v_entries_1204_ = lean_array_push(v_entries_1197_, v_x2_1194_);
v_indexes_1205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1191_, v___f_1192_, v_indexes_1198_, v_fst_1195_, v_f_1203_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v_indexes_1205_);
lean_ctor_set(v___x_1200_, 0, v_entries_1204_);
v___x_1207_ = v___x_1200_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_entries_1204_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_indexes_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_dec(v_fst_1195_);
lean_dec_ref(v_x2_1194_);
lean_dec_ref(v___f_1192_);
lean_dec_ref(v___f_1191_);
return v_x1_1193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1210_, lean_object* v___f_1211_, lean_object* v___f_1212_, lean_object* v_x1_1213_, lean_object* v_x2_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1210_, v___f_1211_, v___f_1212_, v_x1_1213_, v_x2_1214_);
lean_dec_ref(v___x_1210_);
return v_res_1215_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2(void){
_start:
{
lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v___f_1218_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1219_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1220_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1219_, v___f_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; lean_object* v___f_1243_; 
v___f_1240_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1241_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1242_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1243_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1243_, 0, v___x_1242_);
lean_closure_set(v___f_1243_, 1, v___f_1241_);
lean_closure_set(v___f_1243_, 2, v___f_1240_);
return v___f_1243_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14(void){
_start:
{
lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___f_1247_; 
v___f_1244_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1245_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1246_ = l_Std_Http_Header_Name_contentLength;
v___f_1247_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1247_, 0, v___x_1246_);
lean_closure_set(v___f_1247_, 1, v___f_1245_);
lean_closure_set(v___f_1247_, 2, v___f_1244_);
return v___f_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1248_, lean_object* v_body_1249_, lean_object* v_isClosed_1250_, lean_object* v_close_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v___y_1255_; uint8_t v_omitBody_1256_; lean_object* v___y_1269_; 
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_close_1251_);
lean_dec_ref(v_isClosed_1250_);
lean_dec(v_body_1249_);
lean_dec_ref(v___y_1248_);
v_a_1303_ = lean_ctor_get(v_x_1252_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v_x_1252_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_x_1252_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; uint8_t v___y_1314_; uint8_t v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; uint8_t v___y_1319_; lean_object* v_writer_1327_; lean_object* v_reader_1328_; lean_object* v_config_1329_; lean_object* v_events_1330_; lean_object* v_error_1331_; lean_object* v_instant_1332_; uint8_t v_keepAlive_1333_; uint8_t v_forcedFlush_1334_; uint8_t v_pullBodyStalled_1335_; lean_object* v_userData_1336_; lean_object* v_outputData_1337_; lean_object* v_state_1338_; lean_object* v_knownSize_1339_; lean_object* v_messageHead_1340_; uint8_t v_sentMessage_1341_; uint8_t v_userClosedBody_1342_; uint8_t v_omitBody_1343_; lean_object* v_userDataBytes_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1427_; 
v_a_1312_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v_x_1252_, 1);
v_writer_1327_ = lean_ctor_get(v___y_1248_, 1);
lean_inc_ref(v_writer_1327_);
v_reader_1328_ = lean_ctor_get(v___y_1248_, 0);
v_config_1329_ = lean_ctor_get(v___y_1248_, 2);
v_events_1330_ = lean_ctor_get(v___y_1248_, 3);
v_error_1331_ = lean_ctor_get(v___y_1248_, 4);
v_instant_1332_ = lean_ctor_get(v___y_1248_, 5);
v_keepAlive_1333_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*6);
v_forcedFlush_1334_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1335_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*6 + 2);
v_userData_1336_ = lean_ctor_get(v_writer_1327_, 0);
v_outputData_1337_ = lean_ctor_get(v_writer_1327_, 1);
v_state_1338_ = lean_ctor_get(v_writer_1327_, 2);
v_knownSize_1339_ = lean_ctor_get(v_writer_1327_, 3);
v_messageHead_1340_ = lean_ctor_get(v_writer_1327_, 4);
v_sentMessage_1341_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6);
v_userClosedBody_1342_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6 + 1);
v_omitBody_1343_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6 + 2);
v_userDataBytes_1344_ = lean_ctor_get(v_writer_1327_, 5);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_writer_1327_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1346_ = v_writer_1327_;
v_isShared_1347_ = v_isSharedCheck_1427_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_userDataBytes_1344_);
lean_inc(v_messageHead_1340_);
lean_inc(v_knownSize_1339_);
lean_inc(v_state_1338_);
lean_inc(v_outputData_1337_);
lean_inc(v_userData_1336_);
lean_dec(v_writer_1327_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1427_;
goto v_resetjp_1345_;
}
v___jp_1313_:
{
lean_object* v_headerSize_1320_; lean_object* v_machine_1321_; lean_object* v_machine_1322_; lean_object* v_reader_1323_; lean_object* v_state_1324_; 
v_headerSize_1320_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1318_, v_a_1312_, v___y_1314_);
v_machine_1321_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1316_, v___y_1317_, v_headerSize_1320_, v___y_1319_);
v_machine_1322_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1316_, v_machine_1321_, v_a_1312_);
lean_dec(v_a_1312_);
v_reader_1323_ = lean_ctor_get(v_machine_1322_, 0);
lean_inc_ref(v_reader_1323_);
v_state_1324_ = lean_ctor_get(v_reader_1323_, 0);
lean_inc(v_state_1324_);
lean_dec_ref(v_reader_1323_);
if (lean_obj_tag(v_state_1324_) == 7)
{
lean_dec_ref_known(v_state_1324_, 1);
if (v___y_1315_ == 0)
{
lean_object* v_writer_1325_; uint8_t v_omitBody_1326_; 
v_writer_1325_ = lean_ctor_get(v_machine_1322_, 1);
lean_inc_ref(v_writer_1325_);
v_omitBody_1326_ = lean_ctor_get_uint8(v_writer_1325_, sizeof(void*)*6 + 2);
lean_dec_ref(v_writer_1325_);
v___y_1255_ = v_machine_1322_;
v_omitBody_1256_ = v_omitBody_1326_;
goto v___jp_1254_;
}
else
{
v___y_1269_ = v_machine_1322_;
goto v___jp_1268_;
}
}
else
{
lean_dec(v_state_1324_);
v___y_1269_ = v_machine_1322_;
goto v___jp_1268_;
}
}
v_resetjp_1345_:
{
uint8_t v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1376_; uint8_t v___y_1377_; uint8_t v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1413_; lean_object* v___x_1421_; uint8_t v___x_1422_; uint8_t v___y_1424_; 
v___x_1421_ = lean_box(1);
v___x_1422_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1338_, v___x_1421_);
if (v_sentMessage_1341_ == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = 1;
v___y_1424_ = v___x_1425_;
goto v___jp_1423_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
v___y_1424_ = v___x_1426_;
goto v___jp_1423_;
}
v___jp_1348_:
{
lean_object* v_message_1351_; lean_object* v___x_2263__overap_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v_message_1351_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1349_, v_a_1312_, v___y_1350_);
v___x_2263__overap_1352_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1349_);
v___x_1353_ = lean_apply_2(v___x_2263__overap_1352_, v_outputData_1337_, v_message_1351_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1353_);
v___x_1355_ = v___x_1346_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_userData_1336_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_state_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_knownSize_1339_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_messageHead_1340_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_userDataBytes_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*6, v_sentMessage_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*6 + 1, v_userClosedBody_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*6 + 2, v_omitBody_1343_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1356_, 0, v_reader_1328_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_ctor_set(v___x_1356_, 2, v_config_1329_);
lean_ctor_set(v___x_1356_, 3, v_events_1330_);
lean_ctor_set(v___x_1356_, 4, v_error_1331_);
lean_ctor_set(v___x_1356_, 5, v_instant_1332_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*6, v_keepAlive_1333_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*6 + 1, v_forcedFlush_1334_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*6 + 2, v_pullBodyStalled_1335_);
v___y_1255_ = v___x_1356_;
v_omitBody_1256_ = v_omitBody_1343_;
goto v___jp_1254_;
}
}
v___jp_1358_:
{
lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; uint8_t v___x_1364_; 
v___x_1361_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1362_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1363_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1364_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1362_, v___f_1363_, v___x_1361_, v___y_1360_);
if (v___x_1364_ == 0)
{
v___y_1349_ = v___y_1359_;
v___y_1350_ = v___y_1360_;
goto v___jp_1348_;
}
else
{
lean_object* v_entries_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_entries_1365_ = lean_ctor_get(v___y_1360_, 0);
lean_inc_ref(v_entries_1365_);
lean_dec_ref(v___y_1360_);
v___x_1366_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_array_get_size(v_entries_1365_);
v___x_1369_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1370_ = lean_nat_dec_lt(v___x_1367_, v___x_1368_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v_entries_1365_);
v___y_1349_ = v___y_1359_;
v___y_1350_ = v___x_1366_;
goto v___jp_1348_;
}
else
{
lean_object* v___f_1371_; size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___f_1371_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1368_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1369_, v___f_1371_, v_entries_1365_, v___x_1372_, v___x_1373_, v___x_1366_);
v___y_1349_ = v___y_1359_;
v___y_1350_ = v___x_1374_;
goto v___jp_1348_;
}
}
}
v___jp_1375_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v_indexes_1382_; lean_object* v___x_1383_; lean_object* v_machine_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; uint8_t v___x_1388_; 
v___x_1380_ = 1;
v___x_1381_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1380_, v_a_1312_);
v_indexes_1382_ = lean_ctor_get(v___x_1381_, 1);
lean_inc_ref(v_indexes_1382_);
lean_dec_ref(v___x_1381_);
lean_inc(v_a_1312_);
v___x_1383_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1383_, 0, v_userData_1336_);
lean_ctor_set(v___x_1383_, 1, v_outputData_1337_);
lean_ctor_set(v___x_1383_, 2, v_state_1338_);
lean_ctor_set(v___x_1383_, 3, v_knownSize_1339_);
lean_ctor_set(v___x_1383_, 4, v_a_1312_);
lean_ctor_set(v___x_1383_, 5, v_userDataBytes_1344_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*6, v___y_1377_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*6 + 1, v_userClosedBody_1342_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*6 + 2, v_omitBody_1343_);
v_machine_1384_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1384_, 0, v_reader_1328_);
lean_ctor_set(v_machine_1384_, 1, v___x_1383_);
lean_ctor_set(v_machine_1384_, 2, v_config_1329_);
lean_ctor_set(v_machine_1384_, 3, v_events_1330_);
lean_ctor_set(v_machine_1384_, 4, v_error_1331_);
lean_ctor_set(v_machine_1384_, 5, v_instant_1332_);
lean_ctor_set_uint8(v_machine_1384_, sizeof(void*)*6, v_keepAlive_1333_);
lean_ctor_set_uint8(v_machine_1384_, sizeof(void*)*6 + 1, v_forcedFlush_1334_);
lean_ctor_set_uint8(v_machine_1384_, sizeof(void*)*6 + 2, v_pullBodyStalled_1335_);
v___x_1385_ = l_Std_Http_Header_Name_contentLength;
v___f_1386_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1387_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1388_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1386_, v___f_1387_, v_indexes_1382_, v___x_1385_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1390_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1386_, v___f_1387_, v_indexes_1382_, v___x_1389_);
lean_dec_ref(v_indexes_1382_);
v___y_1314_ = v___y_1376_;
v___y_1315_ = v___y_1379_;
v___y_1316_ = v___y_1378_;
v___y_1317_ = v_machine_1384_;
v___y_1318_ = v___x_1380_;
v___y_1319_ = v___x_1390_;
goto v___jp_1313_;
}
else
{
lean_dec_ref(v_indexes_1382_);
v___y_1314_ = v___y_1376_;
v___y_1315_ = v___y_1379_;
v___y_1316_ = v___y_1378_;
v___y_1317_ = v_machine_1384_;
v___y_1318_ = v___x_1380_;
v___y_1319_ = v___x_1388_;
goto v___jp_1313_;
}
}
v___jp_1391_:
{
if (v___y_1394_ == 0)
{
lean_object* v_state_1395_; 
lean_del_object(v___x_1346_);
lean_dec(v_messageHead_1340_);
v_state_1395_ = lean_ctor_get(v_reader_1328_, 0);
if (lean_obj_tag(v_state_1395_) == 7)
{
v___y_1376_ = v___y_1394_;
v___y_1377_ = v___y_1392_;
v___y_1378_ = v___y_1393_;
v___y_1379_ = v___y_1392_;
goto v___jp_1375_;
}
else
{
v___y_1376_ = v___y_1394_;
v___y_1377_ = v___y_1392_;
v___y_1378_ = v___y_1393_;
v___y_1379_ = v___y_1394_;
goto v___jp_1375_;
}
}
else
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___f_1400_; uint8_t v___x_1401_; 
v___x_1396_ = 1;
v___x_1397_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1396_, v_a_1312_);
v___x_1398_ = l_Std_Http_Header_Name_contentLength;
v___f_1399_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1400_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1401_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1399_, v___f_1400_, v___x_1398_, v___x_1397_);
if (v___x_1401_ == 0)
{
v___y_1359_ = v___x_1396_;
v___y_1360_ = v___x_1397_;
goto v___jp_1358_;
}
else
{
lean_object* v_entries_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_entries_1402_ = lean_ctor_get(v___x_1397_, 0);
lean_inc_ref(v_entries_1402_);
lean_dec_ref(v___x_1397_);
v___x_1403_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_array_get_size(v_entries_1402_);
v___x_1406_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1407_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1407_ == 0)
{
lean_dec_ref(v_entries_1402_);
v___y_1359_ = v___x_1396_;
v___y_1360_ = v___x_1403_;
goto v___jp_1358_;
}
else
{
lean_object* v___f_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___f_1408_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1405_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___f_1408_, v_entries_1402_, v___x_1409_, v___x_1410_, v___x_1403_);
v___y_1359_ = v___x_1396_;
v___y_1360_ = v___x_1411_;
goto v___jp_1358_;
}
}
}
}
v___jp_1412_:
{
if (v___y_1413_ == 0)
{
lean_del_object(v___x_1346_);
lean_dec(v_userDataBytes_1344_);
lean_dec(v_messageHead_1340_);
lean_dec(v_knownSize_1339_);
lean_dec(v_state_1338_);
lean_dec_ref(v_outputData_1337_);
lean_dec_ref(v_userData_1336_);
lean_dec(v_a_1312_);
v___y_1255_ = v___y_1248_;
v_omitBody_1256_ = v_omitBody_1343_;
goto v___jp_1254_;
}
else
{
lean_object* v_status_1414_; uint8_t v___x_1415_; uint16_t v___x_1416_; uint16_t v___x_1417_; uint8_t v___x_1418_; 
lean_inc(v_instant_1332_);
lean_inc(v_error_1331_);
lean_inc_ref(v_events_1330_);
lean_inc_ref(v_config_1329_);
lean_inc_ref(v_reader_1328_);
lean_dec_ref(v___y_1248_);
v_status_1414_ = lean_ctor_get(v_a_1312_, 0);
v___x_1415_ = 0;
v___x_1416_ = 100;
v___x_1417_ = l_Std_Http_Status_toCode(v_status_1414_);
v___x_1418_ = lean_uint16_dec_le(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1392_ = v___y_1413_;
v___y_1393_ = v___x_1415_;
v___y_1394_ = v___x_1418_;
goto v___jp_1391_;
}
else
{
uint16_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = 200;
v___x_1420_ = lean_uint16_dec_lt(v___x_1417_, v___x_1419_);
v___y_1392_ = v___y_1413_;
v___y_1393_ = v___x_1415_;
v___y_1394_ = v___x_1420_;
goto v___jp_1391_;
}
}
}
v___jp_1423_:
{
if (v___x_1422_ == 0)
{
v___y_1413_ = v___x_1422_;
goto v___jp_1412_;
}
else
{
v___y_1413_ = v___y_1424_;
goto v___jp_1412_;
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1428_, lean_object* v_body_1429_, lean_object* v_isClosed_1430_, lean_object* v_close_1431_, lean_object* v_x_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1428_, v_body_1429_, v_isClosed_1430_, v_close_1431_, v_x_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_config_1435_, lean_object* v_line_1436_, lean_object* v_body_1437_, lean_object* v_isClosed_1438_, lean_object* v_close_1439_, lean_object* v_machine_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v___y_1444_; 
if (lean_obj_tag(v_x_1441_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_machine_1440_);
lean_dec_ref(v_close_1439_);
lean_dec_ref(v_isClosed_1438_);
lean_dec(v_body_1437_);
lean_dec_ref(v_line_1436_);
v_a_1450_ = lean_ctor_get(v_x_1441_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1441_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v_x_1441_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v_x_1441_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v_x_1441_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v_x_1441_, 1);
if (lean_obj_tag(v_a_1459_) == 1)
{
lean_object* v_writer_1460_; lean_object* v_reader_1461_; lean_object* v_config_1462_; lean_object* v_events_1463_; lean_object* v_error_1464_; lean_object* v_instant_1465_; uint8_t v_keepAlive_1466_; uint8_t v_forcedFlush_1467_; uint8_t v_pullBodyStalled_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1491_; 
v_writer_1460_ = lean_ctor_get(v_machine_1440_, 1);
v_reader_1461_ = lean_ctor_get(v_machine_1440_, 0);
v_config_1462_ = lean_ctor_get(v_machine_1440_, 2);
v_events_1463_ = lean_ctor_get(v_machine_1440_, 3);
v_error_1464_ = lean_ctor_get(v_machine_1440_, 4);
v_instant_1465_ = lean_ctor_get(v_machine_1440_, 5);
v_keepAlive_1466_ = lean_ctor_get_uint8(v_machine_1440_, sizeof(void*)*6);
v_forcedFlush_1467_ = lean_ctor_get_uint8(v_machine_1440_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1468_ = lean_ctor_get_uint8(v_machine_1440_, sizeof(void*)*6 + 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_machine_1440_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1470_ = v_machine_1440_;
v_isShared_1471_ = v_isSharedCheck_1491_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_instant_1465_);
lean_inc(v_error_1464_);
lean_inc(v_events_1463_);
lean_inc(v_config_1462_);
lean_inc(v_writer_1460_);
lean_inc(v_reader_1461_);
lean_dec(v_machine_1440_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1491_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_userData_1472_; lean_object* v_outputData_1473_; lean_object* v_state_1474_; lean_object* v_messageHead_1475_; uint8_t v_sentMessage_1476_; uint8_t v_userClosedBody_1477_; uint8_t v_omitBody_1478_; lean_object* v_userDataBytes_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1489_; 
v_userData_1472_ = lean_ctor_get(v_writer_1460_, 0);
v_outputData_1473_ = lean_ctor_get(v_writer_1460_, 1);
v_state_1474_ = lean_ctor_get(v_writer_1460_, 2);
v_messageHead_1475_ = lean_ctor_get(v_writer_1460_, 4);
v_sentMessage_1476_ = lean_ctor_get_uint8(v_writer_1460_, sizeof(void*)*6);
v_userClosedBody_1477_ = lean_ctor_get_uint8(v_writer_1460_, sizeof(void*)*6 + 1);
v_omitBody_1478_ = lean_ctor_get_uint8(v_writer_1460_, sizeof(void*)*6 + 2);
v_userDataBytes_1479_ = lean_ctor_get(v_writer_1460_, 5);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_writer_1460_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_writer_1460_, 3);
lean_dec(v_unused_1490_);
v___x_1481_ = v_writer_1460_;
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_userDataBytes_1479_);
lean_inc(v_messageHead_1475_);
lean_inc(v_state_1474_);
lean_inc(v_outputData_1473_);
lean_inc(v_userData_1472_);
lean_dec(v_writer_1460_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 3, v_a_1459_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_userData_1472_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_outputData_1473_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_state_1474_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_a_1459_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v_messageHead_1475_);
lean_ctor_set(v_reuseFailAlloc_1488_, 5, v_userDataBytes_1479_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, sizeof(void*)*6, v_sentMessage_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, sizeof(void*)*6 + 1, v_userClosedBody_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, sizeof(void*)*6 + 2, v_omitBody_1478_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1484_);
v___x_1486_ = v___x_1470_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_reader_1461_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_config_1462_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v_events_1463_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v_error_1464_);
lean_ctor_set(v_reuseFailAlloc_1487_, 5, v_instant_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1487_, sizeof(void*)*6, v_keepAlive_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1487_, sizeof(void*)*6 + 1, v_forcedFlush_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1487_, sizeof(void*)*6 + 2, v_pullBodyStalled_1468_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v___y_1444_ = v___x_1486_;
goto v___jp_1443_;
}
}
}
}
}
else
{
lean_dec(v_a_1459_);
v___y_1444_ = v_machine_1440_;
goto v___jp_1443_;
}
}
v___jp_1443_:
{
lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1445_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1435_, v_line_1436_);
v___f_1446_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1446_, 0, v___y_1444_);
lean_closure_set(v___f_1446_, 1, v_body_1437_);
lean_closure_set(v___f_1446_, 2, v_isClosed_1438_);
lean_closure_set(v___f_1446_, 3, v_close_1439_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = 0;
v___x_1449_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1447_, v___x_1448_, v___x_1445_, v___f_1446_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_config_1492_, lean_object* v_line_1493_, lean_object* v_body_1494_, lean_object* v_isClosed_1495_, lean_object* v_close_1496_, lean_object* v_machine_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_config_1492_, v_line_1493_, v_body_1494_, v_isClosed_1495_, v_close_1496_, v_machine_1497_, v_x_1498_);
lean_dec_ref(v_config_1492_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1501_, lean_object* v_config_1502_, lean_object* v_machine_1503_, lean_object* v_res_1504_){
_start:
{
lean_object* v_close_1506_; lean_object* v_isClosed_1507_; lean_object* v_getKnownSize_1508_; lean_object* v_line_1509_; lean_object* v_body_1510_; lean_object* v___x_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v_close_1506_ = lean_ctor_get(v_inst_1501_, 1);
lean_inc_ref(v_close_1506_);
v_isClosed_1507_ = lean_ctor_get(v_inst_1501_, 2);
lean_inc_ref(v_isClosed_1507_);
v_getKnownSize_1508_ = lean_ctor_get(v_inst_1501_, 5);
lean_inc_ref(v_getKnownSize_1508_);
lean_dec_ref(v_inst_1501_);
v_line_1509_ = lean_ctor_get(v_res_1504_, 0);
lean_inc_ref(v_line_1509_);
v_body_1510_ = lean_ctor_get(v_res_1504_, 1);
lean_inc_n(v_body_1510_, 2);
lean_dec_ref(v_res_1504_);
v___x_1511_ = lean_apply_2(v_getKnownSize_1508_, v_body_1510_, lean_box(0));
v___f_1512_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1512_, 0, v_config_1502_);
lean_closure_set(v___f_1512_, 1, v_line_1509_);
lean_closure_set(v___f_1512_, 2, v_body_1510_);
lean_closure_set(v___f_1512_, 3, v_isClosed_1507_);
lean_closure_set(v___f_1512_, 4, v_close_1506_);
lean_closure_set(v___f_1512_, 5, v_machine_1503_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = 0;
v___x_1515_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1513_, v___x_1514_, v___x_1511_, v___f_1512_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1516_, lean_object* v_config_1517_, lean_object* v_machine_1518_, lean_object* v_res_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1516_, v_config_1517_, v_machine_1518_, v_res_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1522_, lean_object* v_inst_1523_, lean_object* v_config_1524_, lean_object* v_machine_1525_, lean_object* v_res_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1523_, v_config_1524_, v_machine_1525_, v_res_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1529_, lean_object* v_inst_1530_, lean_object* v_config_1531_, lean_object* v_machine_1532_, lean_object* v_res_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1529_, v_inst_1530_, v_config_1531_, v_machine_1532_, v_res_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_closed_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_closed_1539_ = lean_ctor_get_uint8(v_____do__lift_1536_, sizeof(void*)*6);
v___x_1540_ = lean_box(v_closed_1539_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v_____do__lift_1543_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v_pendingProducer_1555_; lean_object* v_pendingConsumer_1556_; lean_object* v_interestWaiter_1557_; uint8_t v_closed_1558_; lean_object* v_pendingIncompleteChunk_1559_; lean_object* v_closeError_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1569_; 
v___x_1554_ = lean_st_ref_take(v___y_1552_);
v_pendingProducer_1555_ = lean_ctor_get(v___x_1554_, 0);
v_pendingConsumer_1556_ = lean_ctor_get(v___x_1554_, 1);
v_interestWaiter_1557_ = lean_ctor_get(v___x_1554_, 2);
v_closed_1558_ = lean_ctor_get_uint8(v___x_1554_, sizeof(void*)*6);
v_pendingIncompleteChunk_1559_ = lean_ctor_get(v___x_1554_, 4);
v_closeError_1560_ = lean_ctor_get(v___x_1554_, 5);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v___x_1554_, 3);
lean_dec(v_unused_1570_);
v___x_1562_ = v___x_1554_;
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_closeError_1560_);
lean_inc(v_pendingIncompleteChunk_1559_);
lean_inc(v_interestWaiter_1557_);
lean_inc(v_pendingConsumer_1556_);
lean_inc(v_pendingProducer_1555_);
lean_dec(v___x_1554_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 3, v___x_1551_);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_pendingProducer_1555_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_pendingConsumer_1556_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_interestWaiter_1557_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_pendingIncompleteChunk_1559_);
lean_ctor_set(v_reuseFailAlloc_1568_, 5, v_closeError_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, sizeof(void*)*6, v_closed_1558_);
v___x_1565_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_st_ref_put(v___y_1552_, v___x_1565_);
v___x_1567_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1571_, v___y_1572_);
lean_dec(v___y_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1576_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v___x_1575_);
v_a_1578_ = lean_ctor_get(v_x_1576_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1580_ = v_x_1576_;
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v_x_1576_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
return v___x_1584_;
}
}
}
else
{
lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1595_; 
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v_x_1576_, 0);
lean_dec(v_unused_1596_);
v___x_1588_ = v_x_1576_;
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
else
{
lean_dec(v_x_1576_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1575_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1597_, lean_object* v_x_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1597_, v_x_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1601_, lean_object* v_requestStream_1602_, lean_object* v_keepAliveTimeout_1603_, lean_object* v_currentTimeout_1604_, lean_object* v_headerTimeout_1605_, lean_object* v_response_1606_, lean_object* v_respStream_1607_, lean_object* v_expectData_1608_, uint8_t v_handlerDispatched_1609_, lean_object* v_____r_1610_){
_start:
{
uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = 0;
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1614_, 0, v_machine_1601_);
lean_ctor_set(v___x_1614_, 1, v_requestStream_1602_);
lean_ctor_set(v___x_1614_, 2, v_keepAliveTimeout_1603_);
lean_ctor_set(v___x_1614_, 3, v_currentTimeout_1604_);
lean_ctor_set(v___x_1614_, 4, v_headerTimeout_1605_);
lean_ctor_set(v___x_1614_, 5, v_response_1606_);
lean_ctor_set(v___x_1614_, 6, v_respStream_1607_);
lean_ctor_set(v___x_1614_, 7, v_expectData_1608_);
lean_ctor_set(v___x_1614_, 8, v___x_1613_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*9, v___x_1612_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*9 + 1, v_handlerDispatched_1609_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1618_, lean_object* v_requestStream_1619_, lean_object* v_keepAliveTimeout_1620_, lean_object* v_currentTimeout_1621_, lean_object* v_headerTimeout_1622_, lean_object* v_response_1623_, lean_object* v_respStream_1624_, lean_object* v_expectData_1625_, lean_object* v_handlerDispatched_1626_, lean_object* v_____r_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v_handlerDispatched_boxed_1629_; lean_object* v_res_1630_; 
v_handlerDispatched_boxed_1629_ = lean_unbox(v_handlerDispatched_1626_);
v_res_1630_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1618_, v_requestStream_1619_, v_keepAliveTimeout_1620_, v_currentTimeout_1621_, v_headerTimeout_1622_, v_response_1623_, v_respStream_1624_, v_expectData_1625_, v_handlerDispatched_boxed_1629_, v_____r_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1631_, lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v___f_1631_);
v_a_1634_ = lean_ctor_get(v_x_1632_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1636_ = v_x_1632_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v_x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v_x_1632_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v_x_1632_, 1);
v___x_1644_ = lean_apply_2(v___f_1631_, v_a_1643_, lean_box(0));
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1645_, v_x_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1649_, lean_object* v___f_1650_, lean_object* v___f_1651_, lean_object* v_x_1652_){
_start:
{
if (lean_obj_tag(v_x_1652_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v___f_1651_);
lean_dec_ref(v___f_1650_);
lean_dec_ref(v_requestStream_1649_);
v_a_1654_ = lean_ctor_get(v_x_1652_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_x_1652_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1656_ = v_x_1652_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v_x_1652_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1663_; uint8_t v___x_1664_; 
v_a_1663_ = lean_ctor_get(v_x_1652_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v_x_1652_, 1);
v___x_1664_ = lean_unbox(v_a_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v___f_1651_);
v___x_1665_ = l_Std_Http_Body_Stream_close(v_requestStream_1649_);
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_unbox(v_a_1663_);
lean_dec(v_a_1663_);
v___x_1668_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1666_, v___x_1667_, v___x_1665_, v___f_1650_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v_a_1663_);
lean_dec_ref(v___f_1650_);
lean_dec_ref(v_requestStream_1649_);
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_apply_2(v___f_1651_, v___x_1669_, lean_box(0));
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1671_, lean_object* v___f_1672_, lean_object* v___f_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1671_, v___f_1672_, v___f_1673_, v_x_1674_);
return v_res_1676_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1677_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1678_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___f_1685_; lean_object* v___f_1686_; 
v___x_1684_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1685_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1686_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1686_, 0, v___f_1685_);
lean_closure_set(v___f_1686_, 1, v___x_1684_);
return v___f_1686_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; 
v___x_1695_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1696_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1697_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1697_, 0, v___f_1696_);
lean_closure_set(v___f_1697_, 1, v___x_1695_);
return v___f_1697_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1698_; lean_object* v___x_1699_; 
v___f_1698_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1699_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1699_, 0, lean_box(0));
lean_closure_set(v___x_1699_, 1, lean_box(0));
lean_closure_set(v___x_1699_, 2, lean_box(0));
lean_closure_set(v___x_1699_, 3, v___f_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1700_, lean_object* v___f_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v___f_1701_);
lean_dec_ref(v___y_1700_);
v_a_1704_ = lean_ctor_get(v_x_1702_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1706_ = v_x_1702_;
v_isShared_1707_ = v_isSharedCheck_1712_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v_x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1712_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
}
else
{
lean_object* v_machine_1713_; lean_object* v_requestStream_1714_; lean_object* v_keepAliveTimeout_1715_; lean_object* v_currentTimeout_1716_; lean_object* v_headerTimeout_1717_; lean_object* v_response_1718_; lean_object* v_respStream_1719_; lean_object* v_expectData_1720_; uint8_t v_handlerDispatched_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_4846__overap_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___f_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref_known(v_x_1702_, 1);
v_machine_1713_ = lean_ctor_get(v___y_1700_, 0);
lean_inc_ref(v_machine_1713_);
v_requestStream_1714_ = lean_ctor_get(v___y_1700_, 1);
lean_inc_ref_n(v_requestStream_1714_, 3);
v_keepAliveTimeout_1715_ = lean_ctor_get(v___y_1700_, 2);
lean_inc(v_keepAliveTimeout_1715_);
v_currentTimeout_1716_ = lean_ctor_get(v___y_1700_, 3);
lean_inc(v_currentTimeout_1716_);
v_headerTimeout_1717_ = lean_ctor_get(v___y_1700_, 4);
lean_inc(v_headerTimeout_1717_);
v_response_1718_ = lean_ctor_get(v___y_1700_, 5);
lean_inc_ref(v_response_1718_);
v_respStream_1719_ = lean_ctor_get(v___y_1700_, 6);
lean_inc(v_respStream_1719_);
v_expectData_1720_ = lean_ctor_get(v___y_1700_, 7);
lean_inc(v_expectData_1720_);
v_handlerDispatched_1721_ = lean_ctor_get_uint8(v___y_1700_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1700_);
v___x_1722_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1723_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1724_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1725_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1726_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1726_, 0, lean_box(0));
lean_closure_set(v___x_1726_, 1, lean_box(0));
lean_closure_set(v___x_1726_, 2, v___x_1722_);
lean_closure_set(v___x_1726_, 3, lean_box(0));
lean_closure_set(v___x_1726_, 4, lean_box(0));
lean_closure_set(v___x_1726_, 5, v___x_1725_);
lean_closure_set(v___x_1726_, 6, v___f_1701_);
v___x_4846__overap_1727_ = l_Std_Mutex_atomically___redArg(v___x_1722_, v___f_1723_, v___f_1724_, v_requestStream_1714_, v___x_1726_);
v___x_1728_ = lean_apply_1(v___x_4846__overap_1727_, lean_box(0));
v___x_1729_ = lean_box(v_handlerDispatched_1721_);
v___f_1730_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1730_, 0, v_machine_1713_);
lean_closure_set(v___f_1730_, 1, v_requestStream_1714_);
lean_closure_set(v___f_1730_, 2, v_keepAliveTimeout_1715_);
lean_closure_set(v___f_1730_, 3, v_currentTimeout_1716_);
lean_closure_set(v___f_1730_, 4, v_headerTimeout_1717_);
lean_closure_set(v___f_1730_, 5, v_response_1718_);
lean_closure_set(v___f_1730_, 6, v_respStream_1719_);
lean_closure_set(v___f_1730_, 7, v_expectData_1720_);
lean_closure_set(v___f_1730_, 8, v___x_1729_);
lean_inc_ref(v___f_1730_);
v___f_1731_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1731_, 0, v___f_1730_);
v___f_1732_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1732_, 0, v_requestStream_1714_);
lean_closure_set(v___f_1732_, 1, v___f_1731_);
lean_closure_set(v___f_1732_, 2, v___f_1730_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = 0;
v___x_1735_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1733_, v___x_1734_, v___x_1728_, v___f_1732_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1736_, lean_object* v___f_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1736_, v___f_1737_, v_x_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1741_, lean_object* v_x_1742_){
_start:
{
if (lean_obj_tag(v_x_1742_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v___y_1741_);
v_a_1744_ = lean_ctor_get(v_x_1742_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_x_1742_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v_x_1742_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v_x_1742_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
}
else
{
lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1761_; 
v_isSharedCheck_1761_ = !lean_is_exclusive(v_x_1742_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_x_1742_, 0);
lean_dec(v_unused_1762_);
v___x_1754_ = v_x_1742_;
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
else
{
lean_dec(v_x_1742_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1741_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1763_, v_x_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1767_, lean_object* v___f_1768_, lean_object* v___y_1769_, lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___f_1768_);
lean_dec_ref(v_requestStream_1767_);
v_a_1772_ = lean_ctor_get(v_x_1770_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_x_1770_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1774_ = v_x_1770_;
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v_x_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1795_; 
v_a_1781_ = lean_ctor_get(v_x_1770_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_x_1770_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1783_ = v_x_1770_;
v_isShared_1784_ = v_isSharedCheck_1795_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v_x_1770_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1795_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_unbox(v_a_1781_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; 
lean_del_object(v___x_1783_);
lean_dec_ref(v___y_1769_);
v___x_1786_ = l_Std_Http_Body_Stream_close(v_requestStream_1767_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_unbox(v_a_1781_);
lean_dec(v_a_1781_);
v___x_1789_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1787_, v___x_1788_, v___x_1786_, v___f_1768_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_dec(v_a_1781_);
lean_dec_ref(v___f_1768_);
lean_dec_ref(v_requestStream_1767_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___y_1769_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1790_);
v___x_1792_ = v___x_1783_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1796_, lean_object* v___f_1797_, lean_object* v___y_1798_, lean_object* v_x_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1796_, v___f_1797_, v___y_1798_, v_x_1799_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1802_, lean_object* v_machine_1803_, lean_object* v_a_1804_, uint8_t v_requiresData_1805_, lean_object* v_expectData_1806_, lean_object* v_pendingHead_1807_, lean_object* v_x_1808_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_pendingHead_1807_);
lean_dec(v_expectData_1806_);
lean_dec_ref(v_a_1804_);
lean_dec_ref(v_machine_1803_);
v_a_1810_ = lean_ctor_get(v_x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1812_ = v_x_1808_;
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v_x_1808_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1833_; 
v_a_1819_ = lean_ctor_get(v_x_1808_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_x_1808_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1821_ = v_x_1808_;
v_isShared_1822_ = v_isSharedCheck_1833_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v_x_1808_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1833_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_keepAliveTimeout_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v_keepAliveTimeout_1823_ = lean_ctor_get(v_config_1802_, 5);
lean_inc_n(v_keepAliveTimeout_1823_, 2);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_keepAliveTimeout_1823_);
v___x_1825_ = lean_box(0);
v___x_1826_ = 0;
v___x_1827_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1827_, 0, v_machine_1803_);
lean_ctor_set(v___x_1827_, 1, v_a_1804_);
lean_ctor_set(v___x_1827_, 2, v___x_1824_);
lean_ctor_set(v___x_1827_, 3, v_keepAliveTimeout_1823_);
lean_ctor_set(v___x_1827_, 4, v___x_1825_);
lean_ctor_set(v___x_1827_, 5, v_a_1819_);
lean_ctor_set(v___x_1827_, 6, v___x_1825_);
lean_ctor_set(v___x_1827_, 7, v_expectData_1806_);
lean_ctor_set(v___x_1827_, 8, v_pendingHead_1807_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*9, v_requiresData_1805_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*9 + 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1828_);
v___x_1830_ = v___x_1821_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1834_, lean_object* v_machine_1835_, lean_object* v_a_1836_, lean_object* v_requiresData_1837_, lean_object* v_expectData_1838_, lean_object* v_pendingHead_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_){
_start:
{
uint8_t v_requiresData_boxed_1842_; lean_object* v_res_1843_; 
v_requiresData_boxed_1842_ = lean_unbox(v_requiresData_1837_);
v_res_1843_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1834_, v_machine_1835_, v_a_1836_, v_requiresData_boxed_1842_, v_expectData_1838_, v_pendingHead_1839_, v_x_1840_);
lean_dec_ref(v_config_1834_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1844_, lean_object* v_machine_1845_, uint8_t v_requiresData_1846_, lean_object* v_expectData_1847_, lean_object* v_pendingHead_1848_, lean_object* v_x_1849_){
_start:
{
if (lean_obj_tag(v_x_1849_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_pendingHead_1848_);
lean_dec(v_expectData_1847_);
lean_dec_ref(v_machine_1845_);
lean_dec_ref(v_config_1844_);
v_a_1851_ = lean_ctor_get(v_x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v_x_1849_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v_x_1849_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1875_; 
v_a_1860_ = lean_ctor_get(v_x_1849_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_x_1849_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1862_ = v_x_1849_;
v_isShared_1863_ = v_isSharedCheck_1875_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v_x_1849_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1875_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___f_1867_; lean_object* v___x_1869_; 
v___x_1864_ = lean_box(0);
v___x_1865_ = l_Std_CloseableChannel_new___redArg(v___x_1864_);
v___x_1866_ = lean_box(v_requiresData_1846_);
v___f_1867_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1867_, 0, v_config_1844_);
lean_closure_set(v___f_1867_, 1, v_machine_1845_);
lean_closure_set(v___f_1867_, 2, v_a_1860_);
lean_closure_set(v___f_1867_, 3, v___x_1866_);
lean_closure_set(v___f_1867_, 4, v_expectData_1847_);
lean_closure_set(v___f_1867_, 5, v_pendingHead_1848_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1865_);
v___x_1869_ = v___x_1862_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1865_);
v___x_1869_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = 0;
v___x_1873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1871_, v___x_1872_, v___x_1870_, v___f_1867_);
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1876_, lean_object* v_machine_1877_, lean_object* v_requiresData_1878_, lean_object* v_expectData_1879_, lean_object* v_pendingHead_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v_requiresData_boxed_1883_; lean_object* v_res_1884_; 
v_requiresData_boxed_1883_ = lean_unbox(v_requiresData_1878_);
v_res_1884_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1876_, v_machine_1877_, v_requiresData_boxed_1883_, v_expectData_1879_, v_pendingHead_1880_, v_x_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1885_, lean_object* v_____r_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = l_Std_Http_Body_mkStream();
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = 0;
v___x_1891_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1889_, v___x_1890_, v___x_1888_, v___f_1885_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1892_, lean_object* v_____r_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1892_, v_____r_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1896_, lean_object* v_val_1897_, lean_object* v___f_1898_, lean_object* v___f_1899_, lean_object* v_x_1900_){
_start:
{
if (lean_obj_tag(v_x_1900_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v___f_1899_);
lean_dec_ref(v___f_1898_);
lean_dec(v_val_1897_);
lean_dec_ref(v_close_1896_);
v_a_1902_ = lean_ctor_get(v_x_1900_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_x_1900_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1904_ = v_x_1900_;
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v_x_1900_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1911_; uint8_t v___x_1912_; 
v_a_1911_ = lean_ctor_get(v_x_1900_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v_x_1900_, 1);
v___x_1912_ = lean_unbox(v_a_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v___f_1899_);
v___x_1913_ = lean_apply_2(v_close_1896_, v_val_1897_, lean_box(0));
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_unbox(v_a_1911_);
lean_dec(v_a_1911_);
v___x_1916_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1914_, v___x_1915_, v___x_1913_, v___f_1898_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v_a_1911_);
lean_dec_ref(v___f_1898_);
lean_dec(v_val_1897_);
lean_dec_ref(v_close_1896_);
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_apply_2(v___f_1899_, v___x_1917_, lean_box(0));
return v___x_1918_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1919_, lean_object* v_val_1920_, lean_object* v___f_1921_, lean_object* v___f_1922_, lean_object* v_x_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1919_, v_val_1920_, v___f_1921_, v___f_1922_, v_x_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1926_, lean_object* v_inst_1927_, lean_object* v___f_1928_, lean_object* v___f_1929_, lean_object* v_____r_1930_){
_start:
{
if (lean_obj_tag(v_respStream_1926_) == 1)
{
lean_object* v_val_1932_; lean_object* v_close_1933_; lean_object* v_isClosed_1934_; lean_object* v___x_1935_; lean_object* v___f_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; 
v_val_1932_ = lean_ctor_get(v_respStream_1926_, 0);
lean_inc_n(v_val_1932_, 2);
lean_dec_ref_known(v_respStream_1926_, 1);
v_close_1933_ = lean_ctor_get(v_inst_1927_, 1);
lean_inc_ref(v_close_1933_);
v_isClosed_1934_ = lean_ctor_get(v_inst_1927_, 2);
lean_inc_ref(v_isClosed_1934_);
lean_dec_ref(v_inst_1927_);
v___x_1935_ = lean_apply_2(v_isClosed_1934_, v_val_1932_, lean_box(0));
v___f_1936_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1936_, 0, v_close_1933_);
lean_closure_set(v___f_1936_, 1, v_val_1932_);
lean_closure_set(v___f_1936_, 2, v___f_1928_);
lean_closure_set(v___f_1936_, 3, v___f_1929_);
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = 0;
v___x_1939_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1937_, v___x_1938_, v___x_1935_, v___f_1936_);
return v___x_1939_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v___f_1928_);
lean_dec_ref(v_inst_1927_);
lean_dec(v_respStream_1926_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_apply_2(v___f_1929_, v___x_1940_, lean_box(0));
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1942_, lean_object* v_inst_1943_, lean_object* v___f_1944_, lean_object* v___f_1945_, lean_object* v_____r_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1942_, v_inst_1943_, v___f_1944_, v___f_1945_, v_____r_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1949_, lean_object* v_keepAliveTimeout_1950_, lean_object* v_currentTimeout_1951_, lean_object* v_headerTimeout_1952_, lean_object* v_response_1953_, lean_object* v_respStream_1954_, uint8_t v_requiresData_1955_, lean_object* v_expectData_1956_, uint8_t v_handlerDispatched_1957_, lean_object* v_pendingHead_1958_, lean_object* v_x_1959_){
_start:
{
if (lean_obj_tag(v_x_1959_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_pendingHead_1958_);
lean_dec(v_expectData_1956_);
lean_dec(v_respStream_1954_);
lean_dec_ref(v_response_1953_);
lean_dec(v_headerTimeout_1952_);
lean_dec(v_currentTimeout_1951_);
lean_dec(v_keepAliveTimeout_1950_);
lean_dec_ref(v_requestStream_1949_);
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
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1991_; 
v_a_1970_ = lean_ctor_get(v_x_1959_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1959_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1972_ = v_x_1959_;
v_isShared_1973_ = v_isSharedCheck_1991_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v_x_1959_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1991_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_snd_1974_; uint8_t v___x_1975_; 
v_snd_1974_ = lean_ctor_get(v_a_1970_, 1);
v___x_1975_ = lean_unbox(v_snd_1974_);
if (v___x_1975_ == 0)
{
lean_object* v_fst_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v_fst_1976_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_fst_1976_);
lean_dec(v_a_1970_);
v___x_1977_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1977_, 0, v_fst_1976_);
lean_ctor_set(v___x_1977_, 1, v_requestStream_1949_);
lean_ctor_set(v___x_1977_, 2, v_keepAliveTimeout_1950_);
lean_ctor_set(v___x_1977_, 3, v_currentTimeout_1951_);
lean_ctor_set(v___x_1977_, 4, v_headerTimeout_1952_);
lean_ctor_set(v___x_1977_, 5, v_response_1953_);
lean_ctor_set(v___x_1977_, 6, v_respStream_1954_);
lean_ctor_set(v___x_1977_, 7, v_expectData_1956_);
lean_ctor_set(v___x_1977_, 8, v_pendingHead_1958_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*9, v_requiresData_1955_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*9 + 1, v_handlerDispatched_1957_);
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1978_);
v___x_1980_ = v___x_1972_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1978_);
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
else
{
lean_object* v_fst_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_dec(v_pendingHead_1958_);
v_fst_1983_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_fst_1983_);
lean_dec(v_a_1970_);
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1985_, 0, v_fst_1983_);
lean_ctor_set(v___x_1985_, 1, v_requestStream_1949_);
lean_ctor_set(v___x_1985_, 2, v_keepAliveTimeout_1950_);
lean_ctor_set(v___x_1985_, 3, v_currentTimeout_1951_);
lean_ctor_set(v___x_1985_, 4, v_headerTimeout_1952_);
lean_ctor_set(v___x_1985_, 5, v_response_1953_);
lean_ctor_set(v___x_1985_, 6, v_respStream_1954_);
lean_ctor_set(v___x_1985_, 7, v_expectData_1956_);
lean_ctor_set(v___x_1985_, 8, v___x_1984_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*9, v_requiresData_1955_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*9 + 1, v_handlerDispatched_1957_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1986_);
v___x_1988_ = v___x_1972_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_1992_, lean_object* v_keepAliveTimeout_1993_, lean_object* v_currentTimeout_1994_, lean_object* v_headerTimeout_1995_, lean_object* v_response_1996_, lean_object* v_respStream_1997_, lean_object* v_requiresData_1998_, lean_object* v_expectData_1999_, lean_object* v_handlerDispatched_2000_, lean_object* v_pendingHead_2001_, lean_object* v_x_2002_, lean_object* v___y_2003_){
_start:
{
uint8_t v_requiresData_boxed_2004_; uint8_t v_handlerDispatched_boxed_2005_; lean_object* v_res_2006_; 
v_requiresData_boxed_2004_ = lean_unbox(v_requiresData_1998_);
v_handlerDispatched_boxed_2005_ = lean_unbox(v_handlerDispatched_2000_);
v_res_2006_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_1992_, v_keepAliveTimeout_1993_, v_currentTimeout_1994_, v_headerTimeout_1995_, v_response_1996_, v_respStream_1997_, v_requiresData_boxed_2004_, v_expectData_1999_, v_handlerDispatched_boxed_2005_, v_pendingHead_2001_, v_x_2002_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2019_, lean_object* v_inst_2020_, lean_object* v___f_2021_, lean_object* v_handler_2022_, lean_object* v___f_2023_, lean_object* v___f_2024_, lean_object* v_inst_2025_, lean_object* v_connectionContext_2026_, lean_object* v_a_2027_, lean_object* v_x_2028_, lean_object* v___y_2029_){
_start:
{
switch(lean_obj_tag(v_a_2027_))
{
case 0:
{
lean_object* v_head_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_connectionContext_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v___f_2024_);
lean_dec_ref(v___f_2023_);
lean_dec(v_handler_2022_);
lean_dec_ref(v___f_2021_);
lean_dec_ref(v_inst_2020_);
v_head_2031_ = lean_ctor_get(v_a_2027_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2033_ = v_a_2027_;
v_isShared_2034_ = v_isSharedCheck_2074_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_head_2031_);
lean_dec(v_a_2027_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2074_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_machine_2035_; lean_object* v_requestStream_2036_; lean_object* v_response_2037_; lean_object* v_respStream_2038_; uint8_t v_requiresData_2039_; lean_object* v_expectData_2040_; uint8_t v_handlerDispatched_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2069_; 
v_machine_2035_ = lean_ctor_get(v___y_2029_, 0);
v_requestStream_2036_ = lean_ctor_get(v___y_2029_, 1);
v_response_2037_ = lean_ctor_get(v___y_2029_, 5);
v_respStream_2038_ = lean_ctor_get(v___y_2029_, 6);
v_requiresData_2039_ = lean_ctor_get_uint8(v___y_2029_, sizeof(void*)*9);
v_expectData_2040_ = lean_ctor_get(v___y_2029_, 7);
v_handlerDispatched_2041_ = lean_ctor_get_uint8(v___y_2029_, sizeof(void*)*9 + 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___y_2029_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; 
v_unused_2070_ = lean_ctor_get(v___y_2029_, 8);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v___y_2029_, 4);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v___y_2029_, 3);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v___y_2029_, 2);
lean_dec(v_unused_2073_);
v___x_2043_ = v___y_2029_;
v_isShared_2044_ = v_isSharedCheck_2069_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_expectData_2040_);
lean_inc(v_respStream_2038_);
lean_inc(v_response_2037_);
lean_inc(v_requestStream_2036_);
lean_inc(v_machine_2035_);
lean_dec(v___y_2029_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2069_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_lingeringTimeout_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v_lingeringTimeout_2045_ = lean_ctor_get(v_config_2019_, 4);
lean_inc(v_lingeringTimeout_2045_);
lean_dec_ref(v_config_2019_);
v___x_2046_ = lean_box(0);
lean_inc(v_head_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
v___x_2048_ = v___x_2033_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_head_2031_);
v___x_2048_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
lean_inc_ref(v_requestStream_2036_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 8, v___x_2048_);
lean_ctor_set(v___x_2043_, 4, v___x_2046_);
lean_ctor_set(v___x_2043_, 3, v_lingeringTimeout_2045_);
lean_ctor_set(v___x_2043_, 2, v___x_2046_);
v___x_2050_ = v___x_2043_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_machine_2035_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_requestStream_2036_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2067_, 3, v_lingeringTimeout_2045_);
lean_ctor_set(v_reuseFailAlloc_2067_, 4, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2067_, 5, v_response_2037_);
lean_ctor_set(v_reuseFailAlloc_2067_, 6, v_respStream_2038_);
lean_ctor_set(v_reuseFailAlloc_2067_, 7, v_expectData_2040_);
lean_ctor_set(v_reuseFailAlloc_2067_, 8, v___x_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*9, v_requiresData_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*9 + 1, v_handlerDispatched_2041_);
v___x_2050_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
uint8_t v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = 0;
v___x_2052_ = 1;
v___x_2053_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2051_, v_head_2031_, v___x_2052_);
lean_dec(v_head_2031_);
if (lean_obj_tag(v___x_2053_) == 1)
{
lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___x_5039__overap_2058_; lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; 
v___f_2054_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2054_, 0, v___x_2053_);
v___x_2055_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2056_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2057_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5039__overap_2058_ = l_Std_Mutex_atomically___redArg(v___x_2055_, v___f_2056_, v___f_2057_, v_requestStream_2036_, v___f_2054_);
v___x_2059_ = lean_apply_1(v___x_5039__overap_2058_, lean_box(0));
v___f_2060_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2060_, 0, v___x_2050_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = 0;
v___x_2063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2061_, v___x_2062_, v___x_2059_, v___f_2060_);
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v___x_2053_);
lean_dec_ref(v_requestStream_2036_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2050_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_connectionContext_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v___f_2024_);
lean_dec_ref(v___f_2023_);
lean_dec(v_handler_2022_);
lean_dec_ref(v___f_2021_);
lean_dec_ref(v_inst_2020_);
lean_dec_ref(v_config_2019_);
v_size_2075_ = lean_ctor_get(v_a_2027_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2077_ = v_a_2027_;
v_isShared_2078_ = v_isSharedCheck_2102_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_size_2075_);
lean_dec(v_a_2027_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2102_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_machine_2079_; lean_object* v_requestStream_2080_; lean_object* v_keepAliveTimeout_2081_; lean_object* v_currentTimeout_2082_; lean_object* v_headerTimeout_2083_; lean_object* v_response_2084_; lean_object* v_respStream_2085_; uint8_t v_handlerDispatched_2086_; lean_object* v_pendingHead_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2100_; 
v_machine_2079_ = lean_ctor_get(v___y_2029_, 0);
v_requestStream_2080_ = lean_ctor_get(v___y_2029_, 1);
v_keepAliveTimeout_2081_ = lean_ctor_get(v___y_2029_, 2);
v_currentTimeout_2082_ = lean_ctor_get(v___y_2029_, 3);
v_headerTimeout_2083_ = lean_ctor_get(v___y_2029_, 4);
v_response_2084_ = lean_ctor_get(v___y_2029_, 5);
v_respStream_2085_ = lean_ctor_get(v___y_2029_, 6);
v_handlerDispatched_2086_ = lean_ctor_get_uint8(v___y_2029_, sizeof(void*)*9 + 1);
v_pendingHead_2087_ = lean_ctor_get(v___y_2029_, 8);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___y_2029_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; 
v_unused_2101_ = lean_ctor_get(v___y_2029_, 7);
lean_dec(v_unused_2101_);
v___x_2089_ = v___y_2029_;
v_isShared_2090_ = v_isSharedCheck_2100_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_pendingHead_2087_);
lean_inc(v_respStream_2085_);
lean_inc(v_response_2084_);
lean_inc(v_headerTimeout_2083_);
lean_inc(v_currentTimeout_2082_);
lean_inc(v_keepAliveTimeout_2081_);
lean_inc(v_requestStream_2080_);
lean_inc(v_machine_2079_);
lean_dec(v___y_2029_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2100_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
uint8_t v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = 1;
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 7, v_size_2075_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_machine_2079_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_requestStream_2080_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_keepAliveTimeout_2081_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_currentTimeout_2082_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v_headerTimeout_2083_);
lean_ctor_set(v_reuseFailAlloc_2099_, 5, v_response_2084_);
lean_ctor_set(v_reuseFailAlloc_2099_, 6, v_respStream_2085_);
lean_ctor_set(v_reuseFailAlloc_2099_, 7, v_size_2075_);
lean_ctor_set(v_reuseFailAlloc_2099_, 8, v_pendingHead_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2099_, sizeof(void*)*9 + 1, v_handlerDispatched_2086_);
v___x_2093_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*9, v___x_2091_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2093_);
v___x_2095_ = v___x_2077_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2103_; lean_object* v_onFailure_2104_; lean_object* v___f_2105_; lean_object* v___y_2107_; 
lean_dec_ref(v_connectionContext_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v___f_2024_);
lean_dec_ref(v___f_2023_);
lean_dec_ref(v_config_2019_);
v_err_2103_ = lean_ctor_get(v_a_2027_, 0);
lean_inc(v_err_2103_);
lean_dec_ref_known(v_a_2027_, 1);
v_onFailure_2104_ = lean_ctor_get(v_inst_2020_, 2);
lean_inc_ref(v_onFailure_2104_);
lean_dec_ref(v_inst_2020_);
v___f_2105_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2105_, 0, v___y_2029_);
lean_closure_set(v___f_2105_, 1, v___f_2021_);
switch(lean_obj_tag(v_err_2103_))
{
case 0:
{
lean_object* v___x_2113_; 
v___x_2113_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2107_ = v___x_2113_;
goto v___jp_2106_;
}
case 1:
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2107_ = v___x_2114_;
goto v___jp_2106_;
}
case 2:
{
lean_object* v___x_2115_; 
v___x_2115_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2107_ = v___x_2115_;
goto v___jp_2106_;
}
case 3:
{
lean_object* v___x_2116_; 
v___x_2116_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2107_ = v___x_2116_;
goto v___jp_2106_;
}
case 4:
{
lean_object* v___x_2117_; 
v___x_2117_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2107_ = v___x_2117_;
goto v___jp_2106_;
}
case 5:
{
lean_object* v___x_2118_; 
v___x_2118_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2107_ = v___x_2118_;
goto v___jp_2106_;
}
case 6:
{
lean_object* v___x_2119_; 
v___x_2119_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2107_ = v___x_2119_;
goto v___jp_2106_;
}
case 7:
{
lean_object* v___x_2120_; 
v___x_2120_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2107_ = v___x_2120_;
goto v___jp_2106_;
}
case 8:
{
lean_object* v___x_2121_; 
v___x_2121_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2107_ = v___x_2121_;
goto v___jp_2106_;
}
case 9:
{
lean_object* v___x_2122_; 
v___x_2122_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2107_ = v___x_2122_;
goto v___jp_2106_;
}
case 10:
{
lean_object* v___x_2123_; 
v___x_2123_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2107_ = v___x_2123_;
goto v___jp_2106_;
}
default: 
{
lean_object* v_message_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_message_2124_ = lean_ctor_get(v_err_2103_, 0);
lean_inc_ref(v_message_2124_);
lean_dec_ref_known(v_err_2103_, 1);
v___x_2125_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2126_ = lean_string_append(v___x_2125_, v_message_2124_);
lean_dec_ref(v_message_2124_);
v___y_2107_ = v___x_2126_;
goto v___jp_2106_;
}
}
v___jp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2108_ = lean_mk_io_user_error(v___y_2107_);
v___x_2109_ = lean_apply_3(v_onFailure_2104_, v_handler_2022_, v___x_2108_, lean_box(0));
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = 0;
v___x_2112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2110_, v___x_2111_, v___x_2109_, v___f_2105_);
return v___x_2112_;
}
}
case 4:
{
lean_object* v_requestStream_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_5095__overap_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref(v_connectionContext_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v___f_2024_);
lean_dec(v_handler_2022_);
lean_dec_ref(v___f_2021_);
lean_dec_ref(v_inst_2020_);
lean_dec_ref(v_config_2019_);
v_requestStream_2127_ = lean_ctor_get(v___y_2029_, 1);
lean_inc_ref_n(v_requestStream_2127_, 2);
v___x_2128_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2129_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2130_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2131_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2132_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2132_, 0, lean_box(0));
lean_closure_set(v___x_2132_, 1, lean_box(0));
lean_closure_set(v___x_2132_, 2, v___x_2128_);
lean_closure_set(v___x_2132_, 3, lean_box(0));
lean_closure_set(v___x_2132_, 4, lean_box(0));
lean_closure_set(v___x_2132_, 5, v___x_2131_);
lean_closure_set(v___x_2132_, 6, v___f_2023_);
v___x_5095__overap_2133_ = l_Std_Mutex_atomically___redArg(v___x_2128_, v___f_2129_, v___f_2130_, v_requestStream_2127_, v___x_2132_);
v___x_2134_ = lean_apply_1(v___x_5095__overap_2133_, lean_box(0));
lean_inc_ref(v___y_2029_);
v___f_2135_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2135_, 0, v___y_2029_);
v___f_2136_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2136_, 0, v_requestStream_2127_);
lean_closure_set(v___f_2136_, 1, v___f_2135_);
lean_closure_set(v___f_2136_, 2, v___y_2029_);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = 0;
v___x_2139_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2137_, v___x_2138_, v___x_2134_, v___f_2136_);
return v___x_2139_;
}
case 6:
{
lean_object* v_machine_2140_; lean_object* v_requestStream_2141_; lean_object* v_respStream_2142_; uint8_t v_requiresData_2143_; lean_object* v_expectData_2144_; lean_object* v_pendingHead_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_5116__overap_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v_connectionContext_2026_);
lean_dec_ref(v___f_2023_);
lean_dec(v_handler_2022_);
lean_dec_ref(v___f_2021_);
lean_dec_ref(v_inst_2020_);
v_machine_2140_ = lean_ctor_get(v___y_2029_, 0);
lean_inc_ref(v_machine_2140_);
v_requestStream_2141_ = lean_ctor_get(v___y_2029_, 1);
lean_inc_ref_n(v_requestStream_2141_, 2);
v_respStream_2142_ = lean_ctor_get(v___y_2029_, 6);
lean_inc(v_respStream_2142_);
v_requiresData_2143_ = lean_ctor_get_uint8(v___y_2029_, sizeof(void*)*9);
v_expectData_2144_ = lean_ctor_get(v___y_2029_, 7);
lean_inc(v_expectData_2144_);
v_pendingHead_2145_ = lean_ctor_get(v___y_2029_, 8);
lean_inc(v_pendingHead_2145_);
lean_dec_ref(v___y_2029_);
v___x_2146_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2147_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2148_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2149_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2150_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2150_, 0, lean_box(0));
lean_closure_set(v___x_2150_, 1, lean_box(0));
lean_closure_set(v___x_2150_, 2, v___x_2146_);
lean_closure_set(v___x_2150_, 3, lean_box(0));
lean_closure_set(v___x_2150_, 4, lean_box(0));
lean_closure_set(v___x_2150_, 5, v___x_2149_);
lean_closure_set(v___x_2150_, 6, v___f_2024_);
v___x_5116__overap_2151_ = l_Std_Mutex_atomically___redArg(v___x_2146_, v___f_2147_, v___f_2148_, v_requestStream_2141_, v___x_2150_);
v___x_2152_ = lean_apply_1(v___x_5116__overap_2151_, lean_box(0));
v___x_2153_ = lean_box(v_requiresData_2143_);
v___f_2154_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2154_, 0, v_config_2019_);
lean_closure_set(v___f_2154_, 1, v_machine_2140_);
lean_closure_set(v___f_2154_, 2, v___x_2153_);
lean_closure_set(v___f_2154_, 3, v_expectData_2144_);
lean_closure_set(v___f_2154_, 4, v_pendingHead_2145_);
v___f_2155_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2155_, 0, v___f_2154_);
lean_inc_ref(v___f_2155_);
v___f_2156_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2156_, 0, v___f_2155_);
v___f_2157_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2157_, 0, v_respStream_2142_);
lean_closure_set(v___f_2157_, 1, v_inst_2025_);
lean_closure_set(v___f_2157_, 2, v___f_2156_);
lean_closure_set(v___f_2157_, 3, v___f_2155_);
lean_inc_ref(v___f_2157_);
v___f_2158_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2158_, 0, v___f_2157_);
v___f_2159_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2159_, 0, v_requestStream_2141_);
lean_closure_set(v___f_2159_, 1, v___f_2158_);
lean_closure_set(v___f_2159_, 2, v___f_2157_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = 0;
v___x_2162_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2160_, v___x_2161_, v___x_2152_, v___f_2159_);
return v___x_2162_;
}
case 7:
{
lean_object* v_pendingHead_2163_; 
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v___f_2024_);
lean_dec_ref(v___f_2023_);
lean_dec_ref(v___f_2021_);
v_pendingHead_2163_ = lean_ctor_get(v___y_2029_, 8);
if (lean_obj_tag(v_pendingHead_2163_) == 1)
{
lean_object* v_machine_2164_; lean_object* v_requestStream_2165_; lean_object* v_keepAliveTimeout_2166_; lean_object* v_currentTimeout_2167_; lean_object* v_headerTimeout_2168_; lean_object* v_response_2169_; lean_object* v_respStream_2170_; uint8_t v_requiresData_2171_; lean_object* v_expectData_2172_; uint8_t v_handlerDispatched_2173_; lean_object* v_val_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
lean_inc_ref(v_pendingHead_2163_);
v_machine_2164_ = lean_ctor_get(v___y_2029_, 0);
lean_inc_ref(v_machine_2164_);
v_requestStream_2165_ = lean_ctor_get(v___y_2029_, 1);
lean_inc_ref(v_requestStream_2165_);
v_keepAliveTimeout_2166_ = lean_ctor_get(v___y_2029_, 2);
lean_inc(v_keepAliveTimeout_2166_);
v_currentTimeout_2167_ = lean_ctor_get(v___y_2029_, 3);
lean_inc(v_currentTimeout_2167_);
v_headerTimeout_2168_ = lean_ctor_get(v___y_2029_, 4);
lean_inc(v_headerTimeout_2168_);
v_response_2169_ = lean_ctor_get(v___y_2029_, 5);
lean_inc_ref(v_response_2169_);
v_respStream_2170_ = lean_ctor_get(v___y_2029_, 6);
lean_inc(v_respStream_2170_);
v_requiresData_2171_ = lean_ctor_get_uint8(v___y_2029_, sizeof(void*)*9);
v_expectData_2172_ = lean_ctor_get(v___y_2029_, 7);
lean_inc(v_expectData_2172_);
v_handlerDispatched_2173_ = lean_ctor_get_uint8(v___y_2029_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2029_);
v_val_2174_ = lean_ctor_get(v_pendingHead_2163_, 0);
lean_inc(v_val_2174_);
v___x_2175_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2020_, v_handler_2022_, v_machine_2164_, v_val_2174_, v_config_2019_, v_connectionContext_2026_);
v___x_2176_ = lean_box(v_requiresData_2171_);
v___x_2177_ = lean_box(v_handlerDispatched_2173_);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2178_, 0, v_requestStream_2165_);
lean_closure_set(v___f_2178_, 1, v_keepAliveTimeout_2166_);
lean_closure_set(v___f_2178_, 2, v_currentTimeout_2167_);
lean_closure_set(v___f_2178_, 3, v_headerTimeout_2168_);
lean_closure_set(v___f_2178_, 4, v_response_2169_);
lean_closure_set(v___f_2178_, 5, v_respStream_2170_);
lean_closure_set(v___f_2178_, 6, v___x_2176_);
lean_closure_set(v___f_2178_, 7, v_expectData_2172_);
lean_closure_set(v___f_2178_, 8, v___x_2177_);
lean_closure_set(v___f_2178_, 9, v_pendingHead_2163_);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = 0;
v___x_2181_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2179_, v___x_2180_, v___x_2175_, v___f_2178_);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec_ref(v_connectionContext_2026_);
lean_dec(v_handler_2022_);
lean_dec_ref(v_inst_2020_);
lean_dec_ref(v_config_2019_);
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___y_2029_);
v___x_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
return v___x_2184_;
}
}
default: 
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec(v_a_2027_);
lean_dec_ref(v_connectionContext_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v___f_2024_);
lean_dec_ref(v___f_2023_);
lean_dec(v_handler_2022_);
lean_dec_ref(v___f_2021_);
lean_dec_ref(v_inst_2020_);
lean_dec_ref(v_config_2019_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___y_2029_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2188_, lean_object* v_inst_2189_, lean_object* v___f_2190_, lean_object* v_handler_2191_, lean_object* v___f_2192_, lean_object* v___f_2193_, lean_object* v_inst_2194_, lean_object* v_connectionContext_2195_, lean_object* v_a_2196_, lean_object* v_x_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2188_, v_inst_2189_, v___f_2190_, v_handler_2191_, v___f_2192_, v___f_2193_, v_inst_2194_, v_connectionContext_2195_, v_a_2196_, v_x_2197_, v___y_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_x_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2204_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_handler_2211_, lean_object* v_config_2212_, lean_object* v_connectionContext_2213_, lean_object* v_events_2214_, lean_object* v_state_2215_){
_start:
{
lean_object* v___f_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_4070__overap_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
v___f_2217_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2218_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2218_, 0, v_config_2212_);
lean_closure_set(v___f_2218_, 1, v_inst_2209_);
lean_closure_set(v___f_2218_, 2, v___f_2217_);
lean_closure_set(v___f_2218_, 3, v_handler_2211_);
lean_closure_set(v___f_2218_, 4, v___f_2217_);
lean_closure_set(v___f_2218_, 5, v___f_2217_);
lean_closure_set(v___f_2218_, 6, v_inst_2210_);
lean_closure_set(v___f_2218_, 7, v_connectionContext_2213_);
v___x_2219_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2220_ = lean_array_size(v_events_2214_);
v___x_2221_ = ((size_t)0ULL);
v___x_4070__overap_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2219_, v_events_2214_, v___f_2218_, v_sz_2220_, v___x_2221_, v_state_2215_);
v___x_2223_ = lean_apply_1(v___x_4070__overap_2222_, lean_box(0));
v___f_2224_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = 0;
v___x_2227_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2225_, v___x_2226_, v___x_2223_, v___f_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_handler_2230_, lean_object* v_config_2231_, lean_object* v_connectionContext_2232_, lean_object* v_events_2233_, lean_object* v_state_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2228_, v_inst_2229_, v_handler_2230_, v_config_2231_, v_connectionContext_2232_, v_events_2233_, v_state_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2237_, lean_object* v_00_u03b2_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_handler_2241_, lean_object* v_config_2242_, lean_object* v_connectionContext_2243_, lean_object* v_events_2244_, lean_object* v_state_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2239_, v_inst_2240_, v_handler_2241_, v_config_2242_, v_connectionContext_2243_, v_events_2244_, v_state_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_handler_2252_, lean_object* v_config_2253_, lean_object* v_connectionContext_2254_, lean_object* v_events_2255_, lean_object* v_state_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2248_, v_00_u03b2_2249_, v_inst_2250_, v_inst_2251_, v_handler_2252_, v_config_2253_, v_connectionContext_2254_, v_events_2255_, v_state_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2259_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
v_a_2260_ = lean_ctor_get(v_x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v_x_2259_, 1);
v___x_2261_ = lean_task_pure(v_a_2260_);
return v___x_2261_;
}
else
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v_x_2259_, 0);
lean_inc_ref(v_a_2262_);
lean_dec_ref_known(v_x_2259_, 1);
return v_a_2262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2263_, lean_object* v_requestStream_2264_, lean_object* v_keepAliveTimeout_2265_, lean_object* v_currentTimeout_2266_, lean_object* v_headerTimeout_2267_, lean_object* v_response_2268_, lean_object* v_respStream_2269_, uint8_t v_requiresData_2270_, lean_object* v_expectData_2271_, lean_object* v_x_2272_){
_start:
{
if (lean_obj_tag(v_x_2272_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_expectData_2271_);
lean_dec(v_respStream_2269_);
lean_dec_ref(v_response_2268_);
lean_dec(v_headerTimeout_2267_);
lean_dec(v_currentTimeout_2266_);
lean_dec(v_keepAliveTimeout_2265_);
lean_dec_ref(v_requestStream_2264_);
lean_dec_ref(v_machine_2263_);
v_a_2274_ = lean_ctor_get(v_x_2272_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_x_2272_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v_x_2272_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v_x_2272_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
}
else
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2293_; 
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2272_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; 
v_unused_2294_ = lean_ctor_get(v_x_2272_, 0);
lean_dec(v_unused_2294_);
v___x_2284_ = v_x_2272_;
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_x_2272_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2286_ = 1;
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2288_, 0, v_machine_2263_);
lean_ctor_set(v___x_2288_, 1, v_requestStream_2264_);
lean_ctor_set(v___x_2288_, 2, v_keepAliveTimeout_2265_);
lean_ctor_set(v___x_2288_, 3, v_currentTimeout_2266_);
lean_ctor_set(v___x_2288_, 4, v_headerTimeout_2267_);
lean_ctor_set(v___x_2288_, 5, v_response_2268_);
lean_ctor_set(v___x_2288_, 6, v_respStream_2269_);
lean_ctor_set(v___x_2288_, 7, v_expectData_2271_);
lean_ctor_set(v___x_2288_, 8, v___x_2287_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*9, v_requiresData_2270_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*9 + 1, v___x_2286_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2288_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2288_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2295_, lean_object* v_requestStream_2296_, lean_object* v_keepAliveTimeout_2297_, lean_object* v_currentTimeout_2298_, lean_object* v_headerTimeout_2299_, lean_object* v_response_2300_, lean_object* v_respStream_2301_, lean_object* v_requiresData_2302_, lean_object* v_expectData_2303_, lean_object* v_x_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v_requiresData_boxed_2306_; lean_object* v_res_2307_; 
v_requiresData_boxed_2306_ = lean_unbox(v_requiresData_2302_);
v_res_2307_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2295_, v_requestStream_2296_, v_keepAliveTimeout_2297_, v_currentTimeout_2298_, v_headerTimeout_2299_, v_response_2300_, v_respStream_2301_, v_requiresData_boxed_2306_, v_expectData_2303_, v_x_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2308_, lean_object* v_response_2309_, lean_object* v___x_2310_, lean_object* v___f_2311_, lean_object* v_x_2312_){
_start:
{
if (lean_obj_tag(v_x_2312_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___f_2311_);
lean_dec(v___x_2310_);
lean_dec_ref(v_response_2309_);
lean_dec_ref(v_toFunctor_2308_);
v_a_2314_ = lean_ctor_get(v_x_2312_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_x_2312_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2316_ = v_x_2312_;
v_isShared_2317_ = v_isSharedCheck_2322_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v_x_2312_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2322_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_a_2323_ = lean_ctor_get(v_x_2312_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2312_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2325_ = v_x_2312_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v_x_2312_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2327_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2327_, 0, lean_box(0));
lean_closure_set(v___x_2327_, 1, lean_box(0));
lean_closure_set(v___x_2327_, 2, v_toFunctor_2308_);
v___x_2328_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2328_, 0, lean_box(0));
lean_closure_set(v___x_2328_, 1, v_response_2309_);
v___x_2329_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2329_, 0, lean_box(0));
lean_closure_set(v___x_2329_, 1, lean_box(0));
lean_closure_set(v___x_2329_, 2, lean_box(0));
lean_closure_set(v___x_2329_, 3, v___x_2327_);
lean_closure_set(v___x_2329_, 4, v___x_2328_);
v___x_2330_ = 0;
lean_inc(v___x_2310_);
v___x_2331_ = l_BaseIO_chainTask___redArg(v_a_2323_, v___x_2329_, v___x_2310_, v___x_2330_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2331_);
v___x_2333_ = v___x_2325_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
v___x_2335_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2310_, v___x_2330_, v___x_2334_, v___f_2311_);
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2338_, lean_object* v_response_2339_, lean_object* v___x_2340_, lean_object* v___f_2341_, lean_object* v_x_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2338_, v_response_2339_, v___x_2340_, v___f_2341_, v_x_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2346_, lean_object* v_handler_2347_, lean_object* v_extensions_2348_, lean_object* v_connectionContext_2349_, lean_object* v_state_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_toApplicative_2353_; lean_object* v_pendingHead_2354_; 
v___x_2352_ = l_instMonadBaseIO;
v_toApplicative_2353_ = lean_ctor_get(v___x_2352_, 0);
v_pendingHead_2354_ = lean_ctor_get(v_state_2350_, 8);
lean_inc(v_pendingHead_2354_);
if (lean_obj_tag(v_pendingHead_2354_) == 1)
{
lean_object* v_toFunctor_2355_; lean_object* v_machine_2356_; lean_object* v_requestStream_2357_; lean_object* v_keepAliveTimeout_2358_; lean_object* v_currentTimeout_2359_; lean_object* v_headerTimeout_2360_; lean_object* v_response_2361_; lean_object* v_respStream_2362_; uint8_t v_requiresData_2363_; lean_object* v_expectData_2364_; lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2387_; 
v_toFunctor_2355_ = lean_ctor_get(v_toApplicative_2353_, 0);
v_machine_2356_ = lean_ctor_get(v_state_2350_, 0);
lean_inc_ref(v_machine_2356_);
v_requestStream_2357_ = lean_ctor_get(v_state_2350_, 1);
lean_inc_ref(v_requestStream_2357_);
v_keepAliveTimeout_2358_ = lean_ctor_get(v_state_2350_, 2);
lean_inc(v_keepAliveTimeout_2358_);
v_currentTimeout_2359_ = lean_ctor_get(v_state_2350_, 3);
lean_inc(v_currentTimeout_2359_);
v_headerTimeout_2360_ = lean_ctor_get(v_state_2350_, 4);
lean_inc(v_headerTimeout_2360_);
v_response_2361_ = lean_ctor_get(v_state_2350_, 5);
lean_inc_ref(v_response_2361_);
v_respStream_2362_ = lean_ctor_get(v_state_2350_, 6);
lean_inc(v_respStream_2362_);
v_requiresData_2363_ = lean_ctor_get_uint8(v_state_2350_, sizeof(void*)*9);
v_expectData_2364_ = lean_ctor_get(v_state_2350_, 7);
lean_inc(v_expectData_2364_);
lean_dec_ref(v_state_2350_);
v_val_2365_ = lean_ctor_get(v_pendingHead_2354_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_pendingHead_2354_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2367_ = v_pendingHead_2354_;
v_isShared_2368_ = v_isSharedCheck_2387_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v_pendingHead_2354_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2387_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_onRequest_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___f_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v_onRequest_2369_ = lean_ctor_get(v_inst_2346_, 1);
lean_inc_ref(v_onRequest_2369_);
lean_dec_ref(v_inst_2346_);
lean_inc_ref(v_requestStream_2357_);
v___x_2370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2370_, 0, v_val_2365_);
lean_ctor_set(v___x_2370_, 1, v_requestStream_2357_);
lean_ctor_set(v___x_2370_, 2, v_extensions_2348_);
v___x_2371_ = lean_apply_3(v_onRequest_2369_, v_handler_2347_, v___x_2370_, v_connectionContext_2349_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2373_, 0, lean_box(0));
lean_closure_set(v___x_2373_, 1, v___x_2371_);
v___x_2374_ = lean_io_as_task(v___x_2373_, v___x_2372_);
v___f_2375_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2376_ = lean_box(v_requiresData_2363_);
lean_inc_ref(v_response_2361_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2377_, 0, v_machine_2356_);
lean_closure_set(v___f_2377_, 1, v_requestStream_2357_);
lean_closure_set(v___f_2377_, 2, v_keepAliveTimeout_2358_);
lean_closure_set(v___f_2377_, 3, v_currentTimeout_2359_);
lean_closure_set(v___f_2377_, 4, v_headerTimeout_2360_);
lean_closure_set(v___f_2377_, 5, v_response_2361_);
lean_closure_set(v___f_2377_, 6, v_respStream_2362_);
lean_closure_set(v___f_2377_, 7, v___x_2376_);
lean_closure_set(v___f_2377_, 8, v_expectData_2364_);
lean_inc_ref(v_toFunctor_2355_);
v___f_2378_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2378_, 0, v_toFunctor_2355_);
lean_closure_set(v___f_2378_, 1, v_response_2361_);
lean_closure_set(v___f_2378_, 2, v___x_2372_);
lean_closure_set(v___f_2378_, 3, v___f_2377_);
v___x_2379_ = 1;
v___x_2380_ = lean_task_bind(v___x_2374_, v___f_2375_, v___x_2372_, v___x_2379_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2380_);
v___x_2382_ = v___x_2367_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
v___x_2384_ = 0;
v___x_2385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2372_, v___x_2384_, v___x_2383_, v___f_2378_);
return v___x_2385_;
}
}
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v_pendingHead_2354_);
lean_dec_ref(v_connectionContext_2349_);
lean_dec(v_extensions_2348_);
lean_dec(v_handler_2347_);
lean_dec_ref(v_inst_2346_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_state_2350_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2390_, lean_object* v_handler_2391_, lean_object* v_extensions_2392_, lean_object* v_connectionContext_2393_, lean_object* v_state_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2390_, v_handler_2391_, v_extensions_2392_, v_connectionContext_2393_, v_state_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2397_, lean_object* v_inst_2398_, lean_object* v_handler_2399_, lean_object* v_extensions_2400_, lean_object* v_connectionContext_2401_, lean_object* v_state_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2398_, v_handler_2399_, v_extensions_2400_, v_connectionContext_2401_, v_state_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2405_, lean_object* v_inst_2406_, lean_object* v_handler_2407_, lean_object* v_extensions_2408_, lean_object* v_connectionContext_2409_, lean_object* v_state_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2405_, v_inst_2406_, v_handler_2407_, v_extensions_2408_, v_connectionContext_2409_, v_state_2410_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2413_, lean_object* v_____r_2414_){
_start:
{
lean_object* v_writer_2416_; lean_object* v_reader_2417_; lean_object* v_config_2418_; lean_object* v_events_2419_; lean_object* v_error_2420_; lean_object* v_instant_2421_; uint8_t v_keepAlive_2422_; uint8_t v_forcedFlush_2423_; uint8_t v_pullBodyStalled_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2451_; 
v_writer_2416_ = lean_ctor_get(v_machine_2413_, 1);
v_reader_2417_ = lean_ctor_get(v_machine_2413_, 0);
v_config_2418_ = lean_ctor_get(v_machine_2413_, 2);
v_events_2419_ = lean_ctor_get(v_machine_2413_, 3);
v_error_2420_ = lean_ctor_get(v_machine_2413_, 4);
v_instant_2421_ = lean_ctor_get(v_machine_2413_, 5);
v_keepAlive_2422_ = lean_ctor_get_uint8(v_machine_2413_, sizeof(void*)*6);
v_forcedFlush_2423_ = lean_ctor_get_uint8(v_machine_2413_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2424_ = lean_ctor_get_uint8(v_machine_2413_, sizeof(void*)*6 + 2);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_machine_2413_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2426_ = v_machine_2413_;
v_isShared_2427_ = v_isSharedCheck_2451_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_instant_2421_);
lean_inc(v_error_2420_);
lean_inc(v_events_2419_);
lean_inc(v_config_2418_);
lean_inc(v_writer_2416_);
lean_inc(v_reader_2417_);
lean_dec(v_machine_2413_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2451_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_userData_2428_; lean_object* v_outputData_2429_; lean_object* v_state_2430_; lean_object* v_knownSize_2431_; lean_object* v_messageHead_2432_; uint8_t v_sentMessage_2433_; uint8_t v_omitBody_2434_; lean_object* v_userDataBytes_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2450_; 
v_userData_2428_ = lean_ctor_get(v_writer_2416_, 0);
v_outputData_2429_ = lean_ctor_get(v_writer_2416_, 1);
v_state_2430_ = lean_ctor_get(v_writer_2416_, 2);
v_knownSize_2431_ = lean_ctor_get(v_writer_2416_, 3);
v_messageHead_2432_ = lean_ctor_get(v_writer_2416_, 4);
v_sentMessage_2433_ = lean_ctor_get_uint8(v_writer_2416_, sizeof(void*)*6);
v_omitBody_2434_ = lean_ctor_get_uint8(v_writer_2416_, sizeof(void*)*6 + 2);
v_userDataBytes_2435_ = lean_ctor_get(v_writer_2416_, 5);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_writer_2416_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2437_ = v_writer_2416_;
v_isShared_2438_ = v_isSharedCheck_2450_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_userDataBytes_2435_);
lean_inc(v_messageHead_2432_);
lean_inc(v_knownSize_2431_);
lean_inc(v_state_2430_);
lean_inc(v_outputData_2429_);
lean_inc(v_userData_2428_);
lean_dec(v_writer_2416_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2450_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
uint8_t v___x_2439_; lean_object* v___x_2441_; 
v___x_2439_ = 1;
if (v_isShared_2438_ == 0)
{
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_userData_2428_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_outputData_2429_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_state_2430_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_knownSize_2431_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_messageHead_2432_);
lean_ctor_set(v_reuseFailAlloc_2449_, 5, v_userDataBytes_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2449_, sizeof(void*)*6, v_sentMessage_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2449_, sizeof(void*)*6 + 2, v_omitBody_2434_);
v___x_2441_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2443_; 
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*6 + 1, v___x_2439_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2441_);
v___x_2443_ = v___x_2426_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_reader_2417_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_config_2418_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_events_2419_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v_error_2420_);
lean_ctor_set(v_reuseFailAlloc_2448_, 5, v_instant_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*6, v_keepAlive_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*6 + 1, v_forcedFlush_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*6 + 2, v_pullBodyStalled_2424_);
v___x_2443_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2452_, lean_object* v_____r_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2452_, v_____r_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2456_, lean_object* v_x2_2457_){
_start:
{
lean_object* v_data_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_data_2458_ = lean_ctor_get(v_x2_2457_, 0);
v___x_2459_ = lean_byte_array_size(v_data_2458_);
v___x_2460_ = lean_nat_add(v_x1_2456_, v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2461_, lean_object* v_x2_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2461_, v_x2_2462_);
lean_dec_ref(v_x2_2462_);
lean_dec(v_x1_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2464_, lean_object* v_machine_2465_, lean_object* v_isClosed_2466_, lean_object* v___f_2467_, lean_object* v___f_2468_, lean_object* v_x_2469_){
_start:
{
lean_object* v___y_2472_; 
if (lean_obj_tag(v_x_2469_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___f_2468_);
lean_dec_ref(v___f_2467_);
lean_dec_ref(v_isClosed_2466_);
lean_dec_ref(v_machine_2465_);
lean_dec(v_body_2464_);
v_a_2477_ = lean_ctor_get(v_x_2469_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_x_2469_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2479_ = v_x_2469_;
v_isShared_2480_ = v_isSharedCheck_2485_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v_x_2469_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2485_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2549_; 
v_a_2486_ = lean_ctor_get(v_x_2469_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_x_2469_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2488_ = v_x_2469_;
v_isShared_2489_ = v_isSharedCheck_2549_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v_x_2469_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2549_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
if (lean_obj_tag(v_a_2486_) == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec_ref(v___f_2468_);
lean_dec_ref(v___f_2467_);
lean_dec_ref(v_isClosed_2466_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_body_2464_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v_machine_2465_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2491_);
v___x_2493_ = v___x_2488_;
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
else
{
lean_object* v_val_2496_; 
lean_del_object(v___x_2488_);
v_val_2496_ = lean_ctor_get(v_a_2486_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v_a_2486_, 1);
if (lean_obj_tag(v_val_2496_) == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref(v___f_2468_);
lean_dec_ref(v_machine_2465_);
v___x_2497_ = lean_apply_2(v_isClosed_2466_, v_body_2464_, lean_box(0));
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = 0;
v___x_2500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2498_, v___x_2499_, v___x_2497_, v___f_2467_);
return v___x_2500_;
}
else
{
lean_object* v_val_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
lean_dec_ref(v___f_2467_);
lean_dec_ref(v_isClosed_2466_);
v_val_2501_ = lean_ctor_get(v_val_2496_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v_val_2496_, 1);
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___x_2502_);
v___x_2504_ = lean_array_push(v___x_2503_, v_val_2501_);
v___x_2505_ = lean_array_get_size(v___x_2504_);
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2507_ = lean_nat_dec_eq(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v_reader_2508_; lean_object* v_writer_2509_; lean_object* v_config_2510_; lean_object* v_events_2511_; lean_object* v_error_2512_; lean_object* v_instant_2513_; uint8_t v_keepAlive_2514_; uint8_t v_forcedFlush_2515_; uint8_t v_pullBodyStalled_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2548_; 
v_reader_2508_ = lean_ctor_get(v_machine_2465_, 0);
v_writer_2509_ = lean_ctor_get(v_machine_2465_, 1);
v_config_2510_ = lean_ctor_get(v_machine_2465_, 2);
v_events_2511_ = lean_ctor_get(v_machine_2465_, 3);
v_error_2512_ = lean_ctor_get(v_machine_2465_, 4);
v_instant_2513_ = lean_ctor_get(v_machine_2465_, 5);
v_keepAlive_2514_ = lean_ctor_get_uint8(v_machine_2465_, sizeof(void*)*6);
v_forcedFlush_2515_ = lean_ctor_get_uint8(v_machine_2465_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2516_ = lean_ctor_get_uint8(v_machine_2465_, sizeof(void*)*6 + 2);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_machine_2465_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2518_ = v_machine_2465_;
v_isShared_2519_ = v_isSharedCheck_2548_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_instant_2513_);
lean_inc(v_error_2512_);
lean_inc(v_events_2511_);
lean_inc(v_config_2510_);
lean_inc(v_writer_2509_);
lean_inc(v_reader_2508_);
lean_dec(v_machine_2465_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2548_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___y_2521_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_2544_ = lean_nat_dec_lt(v___x_2506_, v___x_2505_);
if (v___x_2544_ == 0)
{
lean_dec_ref(v___f_2468_);
v___y_2521_ = v___x_2506_;
goto v___jp_2520_;
}
else
{
size_t v___x_2545_; size_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = lean_usize_of_nat(v___x_2505_);
lean_inc_ref(v___x_2504_);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2543_, v___f_2468_, v___x_2504_, v___x_2545_, v___x_2546_, v___x_2506_);
v___y_2521_ = v___x_2547_;
goto v___jp_2520_;
}
v___jp_2520_:
{
lean_object* v_userData_2522_; lean_object* v_outputData_2523_; lean_object* v_state_2524_; lean_object* v_knownSize_2525_; lean_object* v_messageHead_2526_; uint8_t v_sentMessage_2527_; uint8_t v_userClosedBody_2528_; uint8_t v_omitBody_2529_; lean_object* v_userDataBytes_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2542_; 
v_userData_2522_ = lean_ctor_get(v_writer_2509_, 0);
v_outputData_2523_ = lean_ctor_get(v_writer_2509_, 1);
v_state_2524_ = lean_ctor_get(v_writer_2509_, 2);
v_knownSize_2525_ = lean_ctor_get(v_writer_2509_, 3);
v_messageHead_2526_ = lean_ctor_get(v_writer_2509_, 4);
v_sentMessage_2527_ = lean_ctor_get_uint8(v_writer_2509_, sizeof(void*)*6);
v_userClosedBody_2528_ = lean_ctor_get_uint8(v_writer_2509_, sizeof(void*)*6 + 1);
v_omitBody_2529_ = lean_ctor_get_uint8(v_writer_2509_, sizeof(void*)*6 + 2);
v_userDataBytes_2530_ = lean_ctor_get(v_writer_2509_, 5);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_writer_2509_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2532_ = v_writer_2509_;
v_isShared_2533_ = v_isSharedCheck_2542_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_userDataBytes_2530_);
lean_inc(v_messageHead_2526_);
lean_inc(v_knownSize_2525_);
lean_inc(v_state_2524_);
lean_inc(v_outputData_2523_);
lean_inc(v_userData_2522_);
lean_dec(v_writer_2509_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2542_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2534_ = l_Array_append___redArg(v_userData_2522_, v___x_2504_);
lean_dec_ref(v___x_2504_);
v___x_2535_ = lean_nat_add(v_userDataBytes_2530_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec(v_userDataBytes_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 5, v___x_2535_);
lean_ctor_set(v___x_2532_, 0, v___x_2534_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_outputData_2523_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_state_2524_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_knownSize_2525_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_messageHead_2526_);
lean_ctor_set(v_reuseFailAlloc_2541_, 5, v___x_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, sizeof(void*)*6, v_sentMessage_2527_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, sizeof(void*)*6 + 1, v_userClosedBody_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, sizeof(void*)*6 + 2, v_omitBody_2529_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 1, v___x_2537_);
v___x_2539_ = v___x_2518_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_reader_2508_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_config_2510_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_events_2511_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_error_2512_);
lean_ctor_set(v_reuseFailAlloc_2540_, 5, v_instant_2513_);
lean_ctor_set_uint8(v_reuseFailAlloc_2540_, sizeof(void*)*6, v_keepAlive_2514_);
lean_ctor_set_uint8(v_reuseFailAlloc_2540_, sizeof(void*)*6 + 1, v_forcedFlush_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2540_, sizeof(void*)*6 + 2, v_pullBodyStalled_2516_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
v___y_2472_ = v___x_2539_;
goto v___jp_2471_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2504_);
lean_dec_ref(v___f_2468_);
v___y_2472_ = v_machine_2465_;
goto v___jp_2471_;
}
}
}
}
}
v___jp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_body_2464_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___y_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2550_, lean_object* v_machine_2551_, lean_object* v_isClosed_2552_, lean_object* v___f_2553_, lean_object* v___f_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2550_, v_machine_2551_, v_isClosed_2552_, v___f_2553_, v___f_2554_, v_x_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2559_, lean_object* v_machine_2560_, lean_object* v_body_2561_){
_start:
{
lean_object* v_close_2563_; lean_object* v_isClosed_2564_; lean_object* v_tryRecv_2565_; lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; 
v_close_2563_ = lean_ctor_get(v_inst_2559_, 1);
lean_inc_ref(v_close_2563_);
v_isClosed_2564_ = lean_ctor_get(v_inst_2559_, 2);
lean_inc_ref(v_isClosed_2564_);
v_tryRecv_2565_ = lean_ctor_get(v_inst_2559_, 4);
lean_inc_ref(v_tryRecv_2565_);
lean_dec_ref(v_inst_2559_);
lean_inc_n(v_body_2561_, 2);
v___x_2566_ = lean_apply_2(v_tryRecv_2565_, v_body_2561_, lean_box(0));
lean_inc_ref(v_machine_2560_);
v___f_2567_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2567_, 0, v_machine_2560_);
lean_inc_ref(v___f_2567_);
v___f_2568_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2568_, 0, v___f_2567_);
v___f_2569_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2569_, 0, v_close_2563_);
lean_closure_set(v___f_2569_, 1, v_body_2561_);
lean_closure_set(v___f_2569_, 2, v___f_2568_);
lean_closure_set(v___f_2569_, 3, v___f_2567_);
v___f_2570_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2571_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2571_, 0, v_body_2561_);
lean_closure_set(v___f_2571_, 1, v_machine_2560_);
lean_closure_set(v___f_2571_, 2, v_isClosed_2564_);
lean_closure_set(v___f_2571_, 3, v___f_2569_);
lean_closure_set(v___f_2571_, 4, v___f_2570_);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = 0;
v___x_2574_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2572_, v___x_2573_, v___x_2566_, v___f_2571_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2575_, lean_object* v_machine_2576_, lean_object* v_body_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2575_, v_machine_2576_, v_body_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2580_, lean_object* v_inst_2581_, lean_object* v_machine_2582_, lean_object* v_body_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2581_, v_machine_2582_, v_body_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2586_, lean_object* v_inst_2587_, lean_object* v_machine_2588_, lean_object* v_body_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2586_, v_inst_2587_, v_machine_2588_, v_body_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2598_, lean_object* v_____r_2599_, lean_object* v_st_2600_){
_start:
{
lean_object* v_machine_2602_; lean_object* v_requestStream_2603_; lean_object* v_keepAliveTimeout_2604_; lean_object* v_currentTimeout_2605_; lean_object* v_headerTimeout_2606_; lean_object* v_response_2607_; lean_object* v_respStream_2608_; uint8_t v_requiresData_2609_; lean_object* v_expectData_2610_; uint8_t v_handlerDispatched_2611_; lean_object* v_pendingHead_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2697_; 
v_machine_2602_ = lean_ctor_get(v_st_2600_, 0);
v_requestStream_2603_ = lean_ctor_get(v_st_2600_, 1);
v_keepAliveTimeout_2604_ = lean_ctor_get(v_st_2600_, 2);
v_currentTimeout_2605_ = lean_ctor_get(v_st_2600_, 3);
v_headerTimeout_2606_ = lean_ctor_get(v_st_2600_, 4);
v_response_2607_ = lean_ctor_get(v_st_2600_, 5);
v_respStream_2608_ = lean_ctor_get(v_st_2600_, 6);
v_requiresData_2609_ = lean_ctor_get_uint8(v_st_2600_, sizeof(void*)*9);
v_expectData_2610_ = lean_ctor_get(v_st_2600_, 7);
v_handlerDispatched_2611_ = lean_ctor_get_uint8(v_st_2600_, sizeof(void*)*9 + 1);
v_pendingHead_2612_ = lean_ctor_get(v_st_2600_, 8);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_st_2600_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2614_ = v_st_2600_;
v_isShared_2615_ = v_isSharedCheck_2697_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_pendingHead_2612_);
lean_inc(v_expectData_2610_);
lean_inc(v_respStream_2608_);
lean_inc(v_response_2607_);
lean_inc(v_headerTimeout_2606_);
lean_inc(v_currentTimeout_2605_);
lean_inc(v_keepAliveTimeout_2604_);
lean_inc(v_requestStream_2603_);
lean_inc(v_machine_2602_);
lean_dec(v_st_2600_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2697_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___y_2617_; uint8_t v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; uint8_t v___y_2631_; uint8_t v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v_reader_2662_; lean_object* v_writer_2663_; lean_object* v_config_2664_; lean_object* v_events_2665_; lean_object* v_error_2666_; lean_object* v_instant_2667_; uint8_t v_keepAlive_2668_; uint8_t v_forcedFlush_2669_; lean_object* v_state_2670_; lean_object* v_input_2671_; lean_object* v_messageHead_2672_; lean_object* v_messageCount_2673_; lean_object* v_bodyBytesRead_2674_; lean_object* v_headerBytesRead_2675_; uint8_t v_noMoreInput_2676_; uint8_t v___y_2678_; uint8_t v___y_2679_; uint8_t v___y_2692_; 
v_reader_2662_ = lean_ctor_get(v_machine_2602_, 0);
v_writer_2663_ = lean_ctor_get(v_machine_2602_, 1);
v_config_2664_ = lean_ctor_get(v_machine_2602_, 2);
v_events_2665_ = lean_ctor_get(v_machine_2602_, 3);
v_error_2666_ = lean_ctor_get(v_machine_2602_, 4);
v_instant_2667_ = lean_ctor_get(v_machine_2602_, 5);
v_keepAlive_2668_ = lean_ctor_get_uint8(v_machine_2602_, sizeof(void*)*6);
v_forcedFlush_2669_ = lean_ctor_get_uint8(v_machine_2602_, sizeof(void*)*6 + 1);
v_state_2670_ = lean_ctor_get(v_reader_2662_, 0);
v_input_2671_ = lean_ctor_get(v_reader_2662_, 1);
v_messageHead_2672_ = lean_ctor_get(v_reader_2662_, 2);
v_messageCount_2673_ = lean_ctor_get(v_reader_2662_, 3);
v_bodyBytesRead_2674_ = lean_ctor_get(v_reader_2662_, 4);
v_headerBytesRead_2675_ = lean_ctor_get(v_reader_2662_, 5);
v_noMoreInput_2676_ = lean_ctor_get_uint8(v_reader_2662_, sizeof(void*)*6);
if (lean_obj_tag(v_state_2670_) == 6)
{
uint8_t v___x_2695_; 
v___x_2695_ = 1;
v___y_2692_ = v___x_2695_;
goto v___jp_2691_;
}
else
{
uint8_t v___x_2696_; 
v___x_2696_ = 0;
v___y_2692_ = v___x_2696_;
goto v___jp_2691_;
}
v___jp_2616_:
{
lean_object* v___x_2619_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___y_2617_);
v___x_2619_ = v___x_2614_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___y_2617_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_requestStream_2603_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_keepAliveTimeout_2604_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_currentTimeout_2605_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_headerTimeout_2606_);
lean_ctor_set(v_reuseFailAlloc_2625_, 5, v_response_2607_);
lean_ctor_set(v_reuseFailAlloc_2625_, 6, v_respStream_2608_);
lean_ctor_set(v_reuseFailAlloc_2625_, 7, v_expectData_2610_);
lean_ctor_set(v_reuseFailAlloc_2625_, 8, v_pendingHead_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*9, v_requiresData_2609_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*9 + 1, v_handlerDispatched_2611_);
v___x_2619_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
uint8_t v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2620_ = 0;
v___x_2621_ = lean_box(v___x_2620_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2619_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
v___jp_2626_:
{
lean_object* v_maxHeaderBytes_2642_; lean_object* v_maxStartLineLength_2643_; lean_object* v_maxChunkLineLength_2644_; lean_object* v_maxBodySize_2645_; lean_object* v_array_2646_; lean_object* v_idx_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v_maxHeaderBytes_2642_ = lean_ctor_get(v___y_2633_, 2);
v_maxStartLineLength_2643_ = lean_ctor_get(v___y_2633_, 5);
v_maxChunkLineLength_2644_ = lean_ctor_get(v___y_2633_, 13);
v_maxBodySize_2645_ = lean_ctor_get(v___y_2633_, 15);
v_array_2646_ = lean_ctor_get(v___y_2641_, 0);
v_idx_2647_ = lean_ctor_get(v___y_2641_, 1);
v___x_2648_ = lean_nat_add(v_maxBodySize_2645_, v_maxHeaderBytes_2642_);
v___x_2649_ = lean_nat_add(v___x_2648_, v_maxStartLineLength_2643_);
lean_dec(v___x_2648_);
v___x_2650_ = lean_nat_add(v___x_2649_, v_maxChunkLineLength_2644_);
lean_dec(v___x_2649_);
v___x_2651_ = lean_byte_array_size(v_array_2646_);
v___x_2652_ = lean_nat_sub(v___x_2651_, v_idx_2647_);
v___x_2653_ = lean_nat_dec_lt(v___x_2650_, v___x_2652_);
lean_dec(v___x_2652_);
lean_dec(v___x_2650_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v_machine_2655_; 
v___x_2654_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2654_, 0, v___y_2628_);
lean_ctor_set(v___x_2654_, 1, v___y_2641_);
lean_ctor_set(v___x_2654_, 2, v___y_2630_);
lean_ctor_set(v___x_2654_, 3, v___y_2634_);
lean_ctor_set(v___x_2654_, 4, v___y_2639_);
lean_ctor_set(v___x_2654_, 5, v___y_2638_);
lean_ctor_set_uint8(v___x_2654_, sizeof(void*)*6, v___y_2627_);
v_machine_2655_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_2655_, 0, v___x_2654_);
lean_ctor_set(v_machine_2655_, 1, v___y_2637_);
lean_ctor_set(v_machine_2655_, 2, v___y_2633_);
lean_ctor_set(v_machine_2655_, 3, v___y_2635_);
lean_ctor_set(v_machine_2655_, 4, v___y_2629_);
lean_ctor_set(v_machine_2655_, 5, v___y_2636_);
lean_ctor_set_uint8(v_machine_2655_, sizeof(void*)*6, v___y_2631_);
lean_ctor_set_uint8(v_machine_2655_, sizeof(void*)*6 + 1, v___y_2640_);
lean_ctor_set_uint8(v_machine_2655_, sizeof(void*)*6 + 2, v___y_2632_);
v___y_2617_ = v_machine_2655_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v___y_2629_);
lean_dec(v___y_2628_);
v___x_2656_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2657_ = lean_array_push(v___y_2635_, v___x_2656_);
v___x_2658_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
v___x_2659_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___y_2641_);
lean_ctor_set(v___x_2659_, 2, v___y_2630_);
lean_ctor_set(v___x_2659_, 3, v___y_2634_);
lean_ctor_set(v___x_2659_, 4, v___y_2639_);
lean_ctor_set(v___x_2659_, 5, v___y_2638_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*6, v___y_2627_);
v___x_2660_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
v___x_2661_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___y_2637_);
lean_ctor_set(v___x_2661_, 2, v___y_2633_);
lean_ctor_set(v___x_2661_, 3, v___x_2657_);
lean_ctor_set(v___x_2661_, 4, v___x_2660_);
lean_ctor_set(v___x_2661_, 5, v___y_2636_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*6, v___y_2631_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*6 + 1, v___y_2640_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*6 + 2, v___y_2632_);
v___y_2617_ = v___x_2661_;
goto v___jp_2616_;
}
}
v___jp_2677_:
{
if (v___y_2678_ == 0)
{
if (v___y_2679_ == 0)
{
lean_object* v_array_2680_; lean_object* v_idx_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
lean_inc(v_headerBytesRead_2675_);
lean_inc(v_bodyBytesRead_2674_);
lean_inc(v_messageCount_2673_);
lean_inc(v_messageHead_2672_);
lean_inc_ref(v_input_2671_);
lean_inc(v_state_2670_);
lean_inc(v_instant_2667_);
lean_inc(v_error_2666_);
lean_inc_ref(v_events_2665_);
lean_inc_ref(v_config_2664_);
lean_inc_ref(v_writer_2663_);
lean_dec_ref(v_machine_2602_);
v_array_2680_ = lean_ctor_get(v_input_2671_, 0);
lean_inc_ref(v_array_2680_);
v_idx_2681_ = lean_ctor_get(v_input_2671_, 1);
lean_inc(v_idx_2681_);
lean_dec_ref(v_input_2671_);
v___x_2682_ = lean_byte_array_size(v_array_2680_);
v___x_2683_ = lean_nat_dec_le(v___x_2682_, v_idx_2681_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2684_ = l_ByteArray_extract(v_array_2680_, v_idx_2681_, v___x_2682_);
lean_dec_ref(v_array_2680_);
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = lean_byte_array_size(v___x_2684_);
v___x_2687_ = lean_byte_array_size(v_val_2598_);
v___x_2688_ = lean_byte_array_copy_slice(v_val_2598_, v___x_2685_, v___x_2684_, v___x_2686_, v___x_2687_, v___x_2683_);
lean_dec_ref(v_val_2598_);
v___x_2689_ = l_ByteArray_mkIterator(v___x_2688_);
v___y_2627_ = v_noMoreInput_2676_;
v___y_2628_ = v_state_2670_;
v___y_2629_ = v_error_2666_;
v___y_2630_ = v_messageHead_2672_;
v___y_2631_ = v_keepAlive_2668_;
v___y_2632_ = v___y_2679_;
v___y_2633_ = v_config_2664_;
v___y_2634_ = v_messageCount_2673_;
v___y_2635_ = v_events_2665_;
v___y_2636_ = v_instant_2667_;
v___y_2637_ = v_writer_2663_;
v___y_2638_ = v_headerBytesRead_2675_;
v___y_2639_ = v_bodyBytesRead_2674_;
v___y_2640_ = v_forcedFlush_2669_;
v___y_2641_ = v___x_2689_;
goto v___jp_2626_;
}
else
{
lean_object* v___x_2690_; 
lean_dec(v_idx_2681_);
lean_dec_ref(v_array_2680_);
v___x_2690_ = l_ByteArray_mkIterator(v_val_2598_);
v___y_2627_ = v_noMoreInput_2676_;
v___y_2628_ = v_state_2670_;
v___y_2629_ = v_error_2666_;
v___y_2630_ = v_messageHead_2672_;
v___y_2631_ = v_keepAlive_2668_;
v___y_2632_ = v___y_2679_;
v___y_2633_ = v_config_2664_;
v___y_2634_ = v_messageCount_2673_;
v___y_2635_ = v_events_2665_;
v___y_2636_ = v_instant_2667_;
v___y_2637_ = v_writer_2663_;
v___y_2638_ = v_headerBytesRead_2675_;
v___y_2639_ = v_bodyBytesRead_2674_;
v___y_2640_ = v_forcedFlush_2669_;
v___y_2641_ = v___x_2690_;
goto v___jp_2626_;
}
}
else
{
lean_dec_ref(v_val_2598_);
v___y_2617_ = v_machine_2602_;
goto v___jp_2616_;
}
}
else
{
lean_dec_ref(v_val_2598_);
v___y_2617_ = v_machine_2602_;
goto v___jp_2616_;
}
}
v___jp_2691_:
{
if (lean_obj_tag(v_state_2670_) == 7)
{
uint8_t v___x_2693_; 
v___x_2693_ = 1;
v___y_2678_ = v___y_2692_;
v___y_2679_ = v___x_2693_;
goto v___jp_2677_;
}
else
{
uint8_t v___x_2694_; 
v___x_2694_ = 0;
v___y_2678_ = v___y_2692_;
v___y_2679_ = v___x_2694_;
goto v___jp_2677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2698_, lean_object* v_____r_2699_, lean_object* v_st_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2698_, v_____r_2699_, v_st_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2703_, lean_object* v_machine_2704_, lean_object* v_requestStream_2705_, lean_object* v_currentTimeout_2706_, lean_object* v_response_2707_, lean_object* v_respStream_2708_, uint8_t v_requiresData_2709_, lean_object* v_expectData_2710_, uint8_t v_handlerDispatched_2711_, lean_object* v_pendingHead_2712_, lean_object* v___f_2713_, lean_object* v_x_2714_){
_start:
{
if (lean_obj_tag(v_x_2714_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v___f_2713_);
lean_dec(v_pendingHead_2712_);
lean_dec(v_expectData_2710_);
lean_dec(v_respStream_2708_);
lean_dec_ref(v_response_2707_);
lean_dec(v_currentTimeout_2706_);
lean_dec_ref(v_requestStream_2705_);
lean_dec_ref(v_machine_2704_);
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
lean_object* v_a_2725_; lean_object* v_headerTimeout_2726_; lean_object* v_second_2727_; lean_object* v_nano_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_second_2732_; lean_object* v_nano_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_a_2725_ = lean_ctor_get(v_x_2714_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v_x_2714_, 1);
v_headerTimeout_2726_ = lean_ctor_get(v_config_2703_, 6);
v_second_2727_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_second_2727_);
v_nano_2728_ = lean_ctor_get(v_a_2725_, 1);
lean_inc(v_nano_2728_);
lean_dec(v_a_2725_);
v___x_2729_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2730_ = lean_int_mul(v_headerTimeout_2726_, v___x_2729_);
v___x_2731_ = l_Std_Time_Duration_ofNanoseconds(v___x_2730_);
lean_dec(v___x_2730_);
v_second_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_second_2732_);
v_nano_2733_ = lean_ctor_get(v___x_2731_, 1);
lean_inc(v_nano_2733_);
lean_dec_ref(v___x_2731_);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2736_ = lean_int_mul(v_second_2727_, v___x_2735_);
lean_dec(v_second_2727_);
v___x_2737_ = lean_int_add(v___x_2736_, v_nano_2728_);
lean_dec(v_nano_2728_);
lean_dec(v___x_2736_);
v___x_2738_ = lean_int_mul(v_second_2732_, v___x_2735_);
lean_dec(v_second_2732_);
v___x_2739_ = lean_int_add(v___x_2738_, v_nano_2733_);
lean_dec(v_nano_2733_);
lean_dec(v___x_2738_);
v___x_2740_ = lean_int_add(v___x_2737_, v___x_2739_);
lean_dec(v___x_2739_);
lean_dec(v___x_2737_);
v___x_2741_ = l_Std_Time_Duration_ofNanoseconds(v___x_2740_);
lean_dec(v___x_2740_);
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2743_, 0, v_machine_2704_);
lean_ctor_set(v___x_2743_, 1, v_requestStream_2705_);
lean_ctor_set(v___x_2743_, 2, v___x_2734_);
lean_ctor_set(v___x_2743_, 3, v_currentTimeout_2706_);
lean_ctor_set(v___x_2743_, 4, v___x_2742_);
lean_ctor_set(v___x_2743_, 5, v_response_2707_);
lean_ctor_set(v___x_2743_, 6, v_respStream_2708_);
lean_ctor_set(v___x_2743_, 7, v_expectData_2710_);
lean_ctor_set(v___x_2743_, 8, v_pendingHead_2712_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*9, v_requiresData_2709_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*9 + 1, v_handlerDispatched_2711_);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_apply_3(v___f_2713_, v___x_2744_, v___x_2743_, lean_box(0));
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2746_, lean_object* v_machine_2747_, lean_object* v_requestStream_2748_, lean_object* v_currentTimeout_2749_, lean_object* v_response_2750_, lean_object* v_respStream_2751_, lean_object* v_requiresData_2752_, lean_object* v_expectData_2753_, lean_object* v_handlerDispatched_2754_, lean_object* v_pendingHead_2755_, lean_object* v___f_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_){
_start:
{
uint8_t v_requiresData_boxed_2759_; uint8_t v_handlerDispatched_boxed_2760_; lean_object* v_res_2761_; 
v_requiresData_boxed_2759_ = lean_unbox(v_requiresData_2752_);
v_handlerDispatched_boxed_2760_ = lean_unbox(v_handlerDispatched_2754_);
v_res_2761_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2746_, v_machine_2747_, v_requestStream_2748_, v_currentTimeout_2749_, v_response_2750_, v_respStream_2751_, v_requiresData_boxed_2759_, v_expectData_2753_, v_handlerDispatched_boxed_2760_, v_pendingHead_2755_, v___f_2756_, v_x_2757_);
lean_dec_ref(v_config_2746_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2762_, lean_object* v_requestStream_2763_, lean_object* v_keepAliveTimeout_2764_, lean_object* v_currentTimeout_2765_, lean_object* v_headerTimeout_2766_, lean_object* v_response_2767_, uint8_t v_requiresData_2768_, lean_object* v_expectData_2769_, uint8_t v_handlerDispatched_2770_, lean_object* v_pendingHead_2771_, lean_object* v_____r_2772_){
_start:
{
lean_object* v_writer_2774_; lean_object* v_reader_2775_; lean_object* v_config_2776_; lean_object* v_events_2777_; lean_object* v_error_2778_; lean_object* v_instant_2779_; uint8_t v_keepAlive_2780_; uint8_t v_forcedFlush_2781_; uint8_t v_pullBodyStalled_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2812_; 
v_writer_2774_ = lean_ctor_get(v_machine_2762_, 1);
v_reader_2775_ = lean_ctor_get(v_machine_2762_, 0);
v_config_2776_ = lean_ctor_get(v_machine_2762_, 2);
v_events_2777_ = lean_ctor_get(v_machine_2762_, 3);
v_error_2778_ = lean_ctor_get(v_machine_2762_, 4);
v_instant_2779_ = lean_ctor_get(v_machine_2762_, 5);
v_keepAlive_2780_ = lean_ctor_get_uint8(v_machine_2762_, sizeof(void*)*6);
v_forcedFlush_2781_ = lean_ctor_get_uint8(v_machine_2762_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2782_ = lean_ctor_get_uint8(v_machine_2762_, sizeof(void*)*6 + 2);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_machine_2762_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2784_ = v_machine_2762_;
v_isShared_2785_ = v_isSharedCheck_2812_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_instant_2779_);
lean_inc(v_error_2778_);
lean_inc(v_events_2777_);
lean_inc(v_config_2776_);
lean_inc(v_writer_2774_);
lean_inc(v_reader_2775_);
lean_dec(v_machine_2762_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2812_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v_userData_2786_; lean_object* v_outputData_2787_; lean_object* v_state_2788_; lean_object* v_knownSize_2789_; lean_object* v_messageHead_2790_; uint8_t v_sentMessage_2791_; uint8_t v_omitBody_2792_; lean_object* v_userDataBytes_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2811_; 
v_userData_2786_ = lean_ctor_get(v_writer_2774_, 0);
v_outputData_2787_ = lean_ctor_get(v_writer_2774_, 1);
v_state_2788_ = lean_ctor_get(v_writer_2774_, 2);
v_knownSize_2789_ = lean_ctor_get(v_writer_2774_, 3);
v_messageHead_2790_ = lean_ctor_get(v_writer_2774_, 4);
v_sentMessage_2791_ = lean_ctor_get_uint8(v_writer_2774_, sizeof(void*)*6);
v_omitBody_2792_ = lean_ctor_get_uint8(v_writer_2774_, sizeof(void*)*6 + 2);
v_userDataBytes_2793_ = lean_ctor_get(v_writer_2774_, 5);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_writer_2774_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2795_ = v_writer_2774_;
v_isShared_2796_ = v_isSharedCheck_2811_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_userDataBytes_2793_);
lean_inc(v_messageHead_2790_);
lean_inc(v_knownSize_2789_);
lean_inc(v_state_2788_);
lean_inc(v_outputData_2787_);
lean_inc(v_userData_2786_);
lean_dec(v_writer_2774_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2811_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
uint8_t v___x_2797_; lean_object* v___x_2799_; 
v___x_2797_ = 1;
if (v_isShared_2796_ == 0)
{
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_userData_2786_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_outputData_2787_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_state_2788_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_knownSize_2789_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v_messageHead_2790_);
lean_ctor_set(v_reuseFailAlloc_2810_, 5, v_userDataBytes_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2810_, sizeof(void*)*6, v_sentMessage_2791_);
lean_ctor_set_uint8(v_reuseFailAlloc_2810_, sizeof(void*)*6 + 2, v_omitBody_2792_);
v___x_2799_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2801_; 
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*6 + 1, v___x_2797_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v___x_2799_);
v___x_2801_ = v___x_2784_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_reader_2775_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_config_2776_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_events_2777_);
lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_error_2778_);
lean_ctor_set(v_reuseFailAlloc_2809_, 5, v_instant_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*6, v_keepAlive_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*6 + 1, v_forcedFlush_2781_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*6 + 2, v_pullBodyStalled_2782_);
v___x_2801_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v_requestStream_2763_);
lean_ctor_set(v___x_2803_, 2, v_keepAliveTimeout_2764_);
lean_ctor_set(v___x_2803_, 3, v_currentTimeout_2765_);
lean_ctor_set(v___x_2803_, 4, v_headerTimeout_2766_);
lean_ctor_set(v___x_2803_, 5, v_response_2767_);
lean_ctor_set(v___x_2803_, 6, v___x_2802_);
lean_ctor_set(v___x_2803_, 7, v_expectData_2769_);
lean_ctor_set(v___x_2803_, 8, v_pendingHead_2771_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*9, v_requiresData_2768_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*9 + 1, v_handlerDispatched_2770_);
v___x_2804_ = 0;
v___x_2805_ = lean_box(v___x_2804_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2803_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2813_, lean_object* v_requestStream_2814_, lean_object* v_keepAliveTimeout_2815_, lean_object* v_currentTimeout_2816_, lean_object* v_headerTimeout_2817_, lean_object* v_response_2818_, lean_object* v_requiresData_2819_, lean_object* v_expectData_2820_, lean_object* v_handlerDispatched_2821_, lean_object* v_pendingHead_2822_, lean_object* v_____r_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v_requiresData_boxed_2825_; uint8_t v_handlerDispatched_boxed_2826_; lean_object* v_res_2827_; 
v_requiresData_boxed_2825_ = lean_unbox(v_requiresData_2819_);
v_handlerDispatched_boxed_2826_ = lean_unbox(v_handlerDispatched_2821_);
v_res_2827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2813_, v_requestStream_2814_, v_keepAliveTimeout_2815_, v_currentTimeout_2816_, v_headerTimeout_2817_, v_response_2818_, v_requiresData_boxed_2825_, v_expectData_2820_, v_handlerDispatched_boxed_2826_, v_pendingHead_2822_, v_____r_2823_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2828_, lean_object* v_x_2829_){
_start:
{
if (lean_obj_tag(v_x_2829_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2839_; 
lean_dec_ref(v___f_2828_);
v_a_2831_ = lean_ctor_get(v_x_2829_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_x_2829_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2833_ = v_x_2829_;
v_isShared_2834_ = v_isSharedCheck_2839_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v_x_2829_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2839_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v_x_2829_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v_x_2829_, 1);
v___x_2841_ = lean_apply_2(v___f_2828_, v_a_2840_, lean_box(0));
return v___x_2841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2842_, v_x_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2846_, lean_object* v_val_2847_, lean_object* v___f_2848_, lean_object* v___f_2849_, lean_object* v_x_2850_){
_start:
{
if (lean_obj_tag(v_x_2850_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v___f_2849_);
lean_dec_ref(v___f_2848_);
lean_dec(v_val_2847_);
lean_dec_ref(v_close_2846_);
v_a_2852_ = lean_ctor_get(v_x_2850_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_x_2850_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2854_ = v_x_2850_;
v_isShared_2855_ = v_isSharedCheck_2860_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v_x_2850_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2860_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2861_; uint8_t v___x_2862_; 
v_a_2861_ = lean_ctor_get(v_x_2850_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v_x_2850_, 1);
v___x_2862_ = lean_unbox(v_a_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; 
lean_dec_ref(v___f_2849_);
v___x_2863_ = lean_apply_2(v_close_2846_, v_val_2847_, lean_box(0));
v___x_2864_ = lean_unsigned_to_nat(0u);
v___x_2865_ = lean_unbox(v_a_2861_);
lean_dec(v_a_2861_);
v___x_2866_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2864_, v___x_2865_, v___x_2863_, v___f_2848_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v_a_2861_);
lean_dec_ref(v___f_2848_);
lean_dec(v_val_2847_);
lean_dec_ref(v_close_2846_);
v___x_2867_ = lean_box(0);
v___x_2868_ = lean_apply_2(v___f_2849_, v___x_2867_, lean_box(0));
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2869_, lean_object* v_val_2870_, lean_object* v___f_2871_, lean_object* v___f_2872_, lean_object* v_x_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2869_, v_val_2870_, v___f_2871_, v___f_2872_, v_x_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2876_, lean_object* v_handler_2877_, lean_object* v_x_2878_){
_start:
{
if (lean_obj_tag(v_x_2878_) == 0)
{
lean_object* v_a_2880_; lean_object* v_onFailure_2881_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v_x_2878_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v_x_2878_, 1);
v_onFailure_2881_ = lean_ctor_get(v_inst_2876_, 2);
lean_inc_ref(v_onFailure_2881_);
lean_dec_ref(v_inst_2876_);
v___x_2882_ = lean_apply_3(v_onFailure_2881_, v_handler_2877_, v_a_2880_, lean_box(0));
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; 
lean_dec(v_handler_2877_);
lean_dec_ref(v_inst_2876_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_x_2878_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2884_, lean_object* v_handler_2885_, lean_object* v_x_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2884_, v_handler_2885_, v_x_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2889_, lean_object* v_____r_2890_){
_start:
{
uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2892_ = 0;
v___x_2893_ = lean_box(v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_st_2889_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2897_, lean_object* v_____r_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2897_, v_____r_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2901_, lean_object* v___f_2902_, lean_object* v___f_2903_, lean_object* v_x_2904_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref(v___f_2903_);
lean_dec_ref(v___f_2902_);
lean_dec_ref(v_requestStream_2901_);
v_a_2906_ = lean_ctor_get(v_x_2904_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_x_2904_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2908_ = v_x_2904_;
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v_x_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; uint8_t v___x_2916_; 
v_a_2915_ = lean_ctor_get(v_x_2904_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v_x_2904_, 1);
v___x_2916_ = lean_unbox(v_a_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
lean_dec_ref(v___f_2903_);
v___x_2917_ = l_Std_Http_Body_Stream_close(v_requestStream_2901_);
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = lean_unbox(v_a_2915_);
lean_dec(v_a_2915_);
v___x_2920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2918_, v___x_2919_, v___x_2917_, v___f_2902_);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_a_2915_);
lean_dec_ref(v___f_2902_);
lean_dec_ref(v_requestStream_2901_);
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_apply_2(v___f_2903_, v___x_2921_, lean_box(0));
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2923_, lean_object* v___f_2924_, lean_object* v___f_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2923_, v___f_2924_, v___f_2925_, v_x_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2929_, lean_object* v___f_2930_, lean_object* v___f_2931_, lean_object* v_requestStream_2932_, lean_object* v___f_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v___f_2933_);
lean_dec_ref(v_requestStream_2932_);
lean_dec_ref(v___f_2931_);
lean_dec_ref(v___f_2930_);
v_a_2936_ = lean_ctor_get(v_x_2934_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v_x_2934_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v_x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
}
else
{
lean_dec_ref_known(v_x_2934_, 1);
if (v_final_2929_ == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_dec_ref(v___f_2933_);
lean_dec_ref(v_requestStream_2932_);
lean_dec_ref(v___f_2931_);
v___x_2945_ = lean_box(0);
v___x_2946_ = lean_apply_2(v___f_2930_, v___x_2945_, lean_box(0));
return v___x_2946_;
}
else
{
lean_object* v___x_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_6969__overap_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; 
lean_dec_ref(v___f_2930_);
v___x_2947_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2948_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2949_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2950_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2951_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2951_, 0, lean_box(0));
lean_closure_set(v___x_2951_, 1, lean_box(0));
lean_closure_set(v___x_2951_, 2, v___x_2947_);
lean_closure_set(v___x_2951_, 3, lean_box(0));
lean_closure_set(v___x_2951_, 4, lean_box(0));
lean_closure_set(v___x_2951_, 5, v___x_2950_);
lean_closure_set(v___x_2951_, 6, v___f_2931_);
v___x_6969__overap_2952_ = l_Std_Mutex_atomically___redArg(v___x_2947_, v___f_2948_, v___f_2949_, v_requestStream_2932_, v___x_2951_);
v___x_2953_ = lean_apply_1(v___x_6969__overap_2952_, lean_box(0));
v___x_2954_ = lean_unsigned_to_nat(0u);
v___x_2955_ = 0;
v___x_2956_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2954_, v___x_2955_, v___x_2953_, v___f_2933_);
return v___x_2956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_2957_, lean_object* v___f_2958_, lean_object* v___f_2959_, lean_object* v_requestStream_2960_, lean_object* v___f_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v_final_boxed_2964_; lean_object* v_res_2965_; 
v_final_boxed_2964_ = lean_unbox(v_final_2957_);
v_res_2965_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_2964_, v___f_2958_, v___f_2959_, v_requestStream_2960_, v___f_2961_, v_x_2962_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2966_, lean_object* v_x_2967_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_state_2966_);
v_a_2969_ = lean_ctor_get(v_x_2967_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_x_2967_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2971_ = v_x_2967_;
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v_x_2967_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
}
}
else
{
lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3007_; 
v_isSharedCheck_3007_ = !lean_is_exclusive(v_x_2967_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v_x_2967_, 0);
lean_dec(v_unused_3008_);
v___x_2979_ = v_x_2967_;
v_isShared_2980_ = v_isSharedCheck_3007_;
goto v_resetjp_2978_;
}
else
{
lean_dec(v_x_2967_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3007_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v_machine_2981_; lean_object* v_requestStream_2982_; lean_object* v_keepAliveTimeout_2983_; lean_object* v_currentTimeout_2984_; lean_object* v_headerTimeout_2985_; lean_object* v_response_2986_; lean_object* v_respStream_2987_; uint8_t v_requiresData_2988_; lean_object* v_expectData_2989_; lean_object* v_pendingHead_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3006_; 
v_machine_2981_ = lean_ctor_get(v_state_2966_, 0);
v_requestStream_2982_ = lean_ctor_get(v_state_2966_, 1);
v_keepAliveTimeout_2983_ = lean_ctor_get(v_state_2966_, 2);
v_currentTimeout_2984_ = lean_ctor_get(v_state_2966_, 3);
v_headerTimeout_2985_ = lean_ctor_get(v_state_2966_, 4);
v_response_2986_ = lean_ctor_get(v_state_2966_, 5);
v_respStream_2987_ = lean_ctor_get(v_state_2966_, 6);
v_requiresData_2988_ = lean_ctor_get_uint8(v_state_2966_, sizeof(void*)*9);
v_expectData_2989_ = lean_ctor_get(v_state_2966_, 7);
v_pendingHead_2990_ = lean_ctor_get(v_state_2966_, 8);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_state_2966_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2992_ = v_state_2966_;
v_isShared_2993_ = v_isSharedCheck_3006_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_pendingHead_2990_);
lean_inc(v_expectData_2989_);
lean_inc(v_respStream_2987_);
lean_inc(v_response_2986_);
lean_inc(v_headerTimeout_2985_);
lean_inc(v_currentTimeout_2984_);
lean_inc(v_keepAliveTimeout_2983_);
lean_inc(v_requestStream_2982_);
lean_inc(v_machine_2981_);
lean_dec(v_state_2966_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3006_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2998_; 
v___x_2994_ = lean_box(52);
v___x_2995_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2981_, v___x_2994_);
v___x_2996_ = 0;
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2995_);
v___x_2998_ = v___x_2992_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_requestStream_2982_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_keepAliveTimeout_2983_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_currentTimeout_2984_);
lean_ctor_set(v_reuseFailAlloc_3005_, 4, v_headerTimeout_2985_);
lean_ctor_set(v_reuseFailAlloc_3005_, 5, v_response_2986_);
lean_ctor_set(v_reuseFailAlloc_3005_, 6, v_respStream_2987_);
lean_ctor_set(v_reuseFailAlloc_3005_, 7, v_expectData_2989_);
lean_ctor_set(v_reuseFailAlloc_3005_, 8, v_pendingHead_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_3005_, sizeof(void*)*9, v_requiresData_2988_);
v___x_2998_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*9 + 1, v___x_2996_);
v___x_2999_ = lean_box(v___x_2996_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_3000_);
v___x_3002_ = v___x_2979_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3000_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3009_, lean_object* v_x_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3009_, v_x_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3013_, lean_object* v_requestStream_3014_, lean_object* v_keepAliveTimeout_3015_, lean_object* v_currentTimeout_3016_, lean_object* v_headerTimeout_3017_, lean_object* v_response_3018_, lean_object* v_respStream_3019_, uint8_t v_requiresData_3020_, lean_object* v_expectData_3021_, lean_object* v_pendingHead_3022_, lean_object* v_____r_3023_){
_start:
{
uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3025_ = 0;
v___x_3026_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3026_, 0, v_machine_3013_);
lean_ctor_set(v___x_3026_, 1, v_requestStream_3014_);
lean_ctor_set(v___x_3026_, 2, v_keepAliveTimeout_3015_);
lean_ctor_set(v___x_3026_, 3, v_currentTimeout_3016_);
lean_ctor_set(v___x_3026_, 4, v_headerTimeout_3017_);
lean_ctor_set(v___x_3026_, 5, v_response_3018_);
lean_ctor_set(v___x_3026_, 6, v_respStream_3019_);
lean_ctor_set(v___x_3026_, 7, v_expectData_3021_);
lean_ctor_set(v___x_3026_, 8, v_pendingHead_3022_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*9, v_requiresData_3020_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*9 + 1, v___x_3025_);
v___x_3027_ = lean_box(v___x_3025_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3031_, lean_object* v_requestStream_3032_, lean_object* v_keepAliveTimeout_3033_, lean_object* v_currentTimeout_3034_, lean_object* v_headerTimeout_3035_, lean_object* v_response_3036_, lean_object* v_respStream_3037_, lean_object* v_requiresData_3038_, lean_object* v_expectData_3039_, lean_object* v_pendingHead_3040_, lean_object* v_____r_3041_, lean_object* v___y_3042_){
_start:
{
uint8_t v_requiresData_boxed_3043_; lean_object* v_res_3044_; 
v_requiresData_boxed_3043_ = lean_unbox(v_requiresData_3038_);
v_res_3044_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3031_, v_requestStream_3032_, v_keepAliveTimeout_3033_, v_currentTimeout_3034_, v_headerTimeout_3035_, v_response_3036_, v_respStream_3037_, v_requiresData_boxed_3043_, v_expectData_3039_, v_pendingHead_3040_, v_____r_3041_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3045_, lean_object* v_body_3046_, lean_object* v___f_3047_, lean_object* v___f_3048_, lean_object* v_x_3049_){
_start:
{
if (lean_obj_tag(v_x_3049_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v___f_3048_);
lean_dec_ref(v___f_3047_);
lean_dec(v_body_3046_);
lean_dec_ref(v_close_3045_);
v_a_3051_ = lean_ctor_get(v_x_3049_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_x_3049_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3053_ = v_x_3049_;
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v_x_3049_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3060_; uint8_t v___x_3061_; 
v_a_3060_ = lean_ctor_get(v_x_3049_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v_x_3049_, 1);
v___x_3061_ = lean_unbox(v_a_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref(v___f_3048_);
v___x_3062_ = lean_apply_2(v_close_3045_, v_body_3046_, lean_box(0));
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_unbox(v_a_3060_);
lean_dec(v_a_3060_);
v___x_3065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3063_, v___x_3064_, v___x_3062_, v___f_3047_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec(v_a_3060_);
lean_dec_ref(v___f_3047_);
lean_dec(v_body_3046_);
lean_dec_ref(v_close_3045_);
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_apply_2(v___f_3048_, v___x_3066_, lean_box(0));
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3068_, lean_object* v_body_3069_, lean_object* v___f_3070_, lean_object* v___f_3071_, lean_object* v_x_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3068_, v_body_3069_, v___f_3070_, v___f_3071_, v_x_3072_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3075_, lean_object* v_keepAliveTimeout_3076_, lean_object* v_currentTimeout_3077_, lean_object* v_headerTimeout_3078_, lean_object* v_response_3079_, uint8_t v_requiresData_3080_, lean_object* v_expectData_3081_, uint8_t v___x_3082_, lean_object* v_pendingHead_3083_, lean_object* v_____x_3084_){
_start:
{
lean_object* v_snd_3086_; lean_object* v_fst_3087_; lean_object* v_fst_3088_; lean_object* v_snd_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3099_; 
v_snd_3086_ = lean_ctor_get(v_____x_3084_, 1);
lean_inc(v_snd_3086_);
v_fst_3087_ = lean_ctor_get(v_____x_3084_, 0);
lean_inc(v_fst_3087_);
lean_dec_ref(v_____x_3084_);
v_fst_3088_ = lean_ctor_get(v_snd_3086_, 0);
v_snd_3089_ = lean_ctor_get(v_snd_3086_, 1);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_snd_3086_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3091_ = v_snd_3086_;
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_snd_3089_);
lean_inc(v_fst_3088_);
lean_dec(v_snd_3086_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3093_, 0, v_fst_3087_);
lean_ctor_set(v___x_3093_, 1, v_requestStream_3075_);
lean_ctor_set(v___x_3093_, 2, v_keepAliveTimeout_3076_);
lean_ctor_set(v___x_3093_, 3, v_currentTimeout_3077_);
lean_ctor_set(v___x_3093_, 4, v_headerTimeout_3078_);
lean_ctor_set(v___x_3093_, 5, v_response_3079_);
lean_ctor_set(v___x_3093_, 6, v_fst_3088_);
lean_ctor_set(v___x_3093_, 7, v_expectData_3081_);
lean_ctor_set(v___x_3093_, 8, v_pendingHead_3083_);
lean_ctor_set_uint8(v___x_3093_, sizeof(void*)*9, v_requiresData_3080_);
lean_ctor_set_uint8(v___x_3093_, sizeof(void*)*9 + 1, v___x_3082_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_snd_3089_);
v___x_3095_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3100_, lean_object* v_keepAliveTimeout_3101_, lean_object* v_currentTimeout_3102_, lean_object* v_headerTimeout_3103_, lean_object* v_response_3104_, lean_object* v_requiresData_3105_, lean_object* v_expectData_3106_, lean_object* v___x_3107_, lean_object* v_pendingHead_3108_, lean_object* v_____x_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v_requiresData_boxed_3111_; uint8_t v___x_7791__boxed_3112_; lean_object* v_res_3113_; 
v_requiresData_boxed_3111_ = lean_unbox(v_requiresData_3105_);
v___x_7791__boxed_3112_ = lean_unbox(v___x_3107_);
v_res_3113_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3100_, v_keepAliveTimeout_3101_, v_currentTimeout_3102_, v_headerTimeout_3103_, v_response_3104_, v_requiresData_boxed_3111_, v_expectData_3106_, v___x_7791__boxed_3112_, v_pendingHead_3108_, v_____x_3109_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3114_, lean_object* v_x_3115_){
_start:
{
if (lean_obj_tag(v_x_3115_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v___f_3114_);
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
lean_object* v_a_3126_; lean_object* v___x_3127_; 
v_a_3126_ = lean_ctor_get(v_x_3115_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v_x_3115_, 1);
v___x_3127_ = lean_apply_2(v___f_3114_, v_a_3126_, lean_box(0));
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3128_, lean_object* v_x_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3128_, v_x_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3132_, lean_object* v_x_3133_){
_start:
{
if (lean_obj_tag(v_x_3133_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3143_; 
v_a_3135_ = lean_ctor_get(v_x_3133_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_x_3133_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3137_ = v_x_3133_;
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v_x_3133_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3163_; 
v_a_3144_ = lean_ctor_get(v_x_3133_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_x_3133_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3146_ = v_x_3133_;
v_isShared_3147_ = v_isSharedCheck_3163_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v_x_3133_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3163_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_fst_3148_; lean_object* v_snd_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3162_; 
v_fst_3148_ = lean_ctor_get(v_a_3144_, 0);
v_snd_3149_ = lean_ctor_get(v_a_3144_, 1);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_a_3144_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3151_ = v_a_3144_;
v_isShared_3152_ = v_isSharedCheck_3162_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_snd_3149_);
lean_inc(v_fst_3148_);
lean_dec(v_a_3144_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3162_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_box(v___x_3132_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v___x_3153_);
lean_ctor_set(v___x_3151_, 0, v_snd_3149_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_snd_3149_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_fst_3148_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3156_);
v___x_3158_ = v___x_3146_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3164_, lean_object* v_x_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v___x_7859__boxed_3167_; lean_object* v_res_3168_; 
v___x_7859__boxed_3167_ = lean_unbox(v___x_3164_);
v_res_3168_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7859__boxed_3167_, v_x_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3169_, uint8_t v___x_3170_, lean_object* v_fst_3171_, lean_object* v_x_3172_){
_start:
{
if (lean_obj_tag(v_x_3172_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_fst_3171_);
lean_dec(v_snd_3169_);
v_a_3174_ = lean_ctor_get(v_x_3172_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_x_3172_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3176_ = v_x_3172_;
v_isShared_3177_ = v_isSharedCheck_3182_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v_x_3172_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3182_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
return v___x_3180_;
}
}
}
else
{
lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3193_; 
v_isSharedCheck_3193_ = !lean_is_exclusive(v_x_3172_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v_x_3172_, 0);
lean_dec(v_unused_3194_);
v___x_3184_ = v_x_3172_;
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
else
{
lean_dec(v_x_3172_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3186_ = lean_box(v___x_3170_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v_snd_3169_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_fst_3171_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3188_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3188_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3195_, lean_object* v___x_3196_, lean_object* v_fst_3197_, lean_object* v_x_3198_, lean_object* v___y_3199_){
_start:
{
uint8_t v___x_7927__boxed_3200_; lean_object* v_res_3201_; 
v___x_7927__boxed_3200_ = lean_unbox(v___x_3196_);
v_res_3201_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3195_, v___x_7927__boxed_3200_, v_fst_3197_, v_x_3198_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3202_, lean_object* v_handler_3203_, uint8_t v___x_3204_, lean_object* v___f_3205_, lean_object* v_x_3206_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 0)
{
lean_object* v_a_3208_; lean_object* v_onFailure_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_a_3208_ = lean_ctor_get(v_x_3206_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v_x_3206_, 1);
v_onFailure_3209_ = lean_ctor_get(v_inst_3202_, 2);
lean_inc_ref(v_onFailure_3209_);
lean_dec_ref(v_inst_3202_);
v___x_3210_ = lean_apply_3(v_onFailure_3209_, v_handler_3203_, v_a_3208_, lean_box(0));
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3211_, v___x_3204_, v___x_3210_, v___f_3205_);
return v___x_3212_;
}
else
{
lean_object* v___x_3213_; 
lean_dec_ref(v___f_3205_);
lean_dec(v_handler_3203_);
lean_dec_ref(v_inst_3202_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v_x_3206_);
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3214_, lean_object* v_handler_3215_, lean_object* v___x_3216_, lean_object* v___f_3217_, lean_object* v_x_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___x_7985__boxed_3220_; lean_object* v_res_3221_; 
v___x_7985__boxed_3220_ = lean_unbox(v___x_3216_);
v_res_3221_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3214_, v_handler_3215_, v___x_7985__boxed_3220_, v___f_3217_, v_x_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3222_, lean_object* v___f_3223_, lean_object* v_inst_3224_, lean_object* v___f_3225_, uint8_t v___x_3226_, lean_object* v_inst_3227_, lean_object* v_handler_3228_, lean_object* v___f_3229_, lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_x_3230_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v___f_3229_);
lean_dec(v_handler_3228_);
lean_dec_ref(v_inst_3227_);
lean_dec_ref(v___f_3225_);
lean_dec_ref(v_inst_3224_);
lean_dec_ref(v___f_3223_);
v_a_3232_ = lean_ctor_get(v_x_3230_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_x_3230_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3234_ = v_x_3230_;
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v_x_3230_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3274_; 
v_a_3241_ = lean_ctor_get(v_x_3230_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_x_3230_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3243_ = v_x_3230_;
v_isShared_3244_ = v_isSharedCheck_3274_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v_x_3230_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3274_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v_snd_3245_; 
v_snd_3245_ = lean_ctor_get(v_a_3241_, 1);
lean_inc(v_snd_3245_);
if (lean_obj_tag(v_snd_3245_) == 0)
{
lean_object* v_fst_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v___f_3229_);
lean_dec(v_handler_3228_);
lean_dec_ref(v_inst_3227_);
lean_dec_ref(v___f_3225_);
lean_dec_ref(v_inst_3224_);
v_fst_3246_ = lean_ctor_get(v_a_3241_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_a_3241_);
if (v_isSharedCheck_3261_ == 0)
{
lean_object* v_unused_3262_; 
v_unused_3262_ = lean_ctor_get(v_a_3241_, 1);
lean_dec(v_unused_3262_);
v___x_3248_ = v_a_3241_;
v_isShared_3249_ = v_isSharedCheck_3261_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_fst_3246_);
lean_dec(v_a_3241_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3261_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = lean_box(v___x_3222_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 1, v___x_3250_);
lean_ctor_set(v___x_3248_, 0, v_snd_3245_);
v___x_3252_ = v___x_3248_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_snd_3245_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v_fst_3246_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3253_);
v___x_3255_ = v___x_3243_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3257_, v___x_3222_, v___x_3256_, v___f_3223_);
return v___x_3258_;
}
}
}
}
else
{
lean_object* v_fst_3263_; lean_object* v_val_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; lean_object* v___f_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_del_object(v___x_3243_);
lean_dec_ref(v___f_3223_);
v_fst_3263_ = lean_ctor_get(v_a_3241_, 0);
lean_inc_n(v_fst_3263_, 2);
lean_dec(v_a_3241_);
v_val_3264_ = lean_ctor_get(v_snd_3245_, 0);
lean_inc(v_val_3264_);
v___x_3265_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3224_, v_fst_3263_, v_val_3264_);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3266_, v___x_3222_, v___x_3265_, v___f_3225_);
v___x_3268_ = lean_box(v___x_3226_);
v___f_3269_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3269_, 0, v_snd_3245_);
lean_closure_set(v___f_3269_, 1, v___x_3268_);
lean_closure_set(v___f_3269_, 2, v_fst_3263_);
v___x_3270_ = lean_box(v___x_3222_);
v___f_3271_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3271_, 0, v_inst_3227_);
lean_closure_set(v___f_3271_, 1, v_handler_3228_);
lean_closure_set(v___f_3271_, 2, v___x_3270_);
lean_closure_set(v___f_3271_, 3, v___f_3269_);
v___x_3272_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3266_, v___x_3222_, v___x_3267_, v___f_3271_);
v___x_3273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3266_, v___x_3222_, v___x_3272_, v___f_3229_);
return v___x_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3275_, lean_object* v___f_3276_, lean_object* v_inst_3277_, lean_object* v___f_3278_, lean_object* v___x_3279_, lean_object* v_inst_3280_, lean_object* v_handler_3281_, lean_object* v___f_3282_, lean_object* v_x_3283_, lean_object* v___y_3284_){
_start:
{
uint8_t v___x_8010__boxed_3285_; uint8_t v___x_8014__boxed_3286_; lean_object* v_res_3287_; 
v___x_8010__boxed_3285_ = lean_unbox(v___x_3275_);
v___x_8014__boxed_3286_ = lean_unbox(v___x_3279_);
v_res_3287_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8010__boxed_3285_, v___f_3276_, v_inst_3277_, v___f_3278_, v___x_8014__boxed_3286_, v_inst_3280_, v_handler_3281_, v___f_3282_, v_x_3283_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3288_, lean_object* v_x_3289_){
_start:
{
if (lean_obj_tag(v_x_3289_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3299_; 
lean_dec_ref(v_state_3288_);
v_a_3291_ = lean_ctor_get(v_x_3289_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_x_3289_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3293_ = v_x_3289_;
v_isShared_3294_ = v_isSharedCheck_3299_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v_x_3289_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3299_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
return v___x_3297_;
}
}
}
else
{
lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3329_; 
v_isSharedCheck_3329_ = !lean_is_exclusive(v_x_3289_);
if (v_isSharedCheck_3329_ == 0)
{
lean_object* v_unused_3330_; 
v_unused_3330_ = lean_ctor_get(v_x_3289_, 0);
lean_dec(v_unused_3330_);
v___x_3301_ = v_x_3289_;
v_isShared_3302_ = v_isSharedCheck_3329_;
goto v_resetjp_3300_;
}
else
{
lean_dec(v_x_3289_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3329_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_machine_3303_; lean_object* v_requestStream_3304_; lean_object* v_keepAliveTimeout_3305_; lean_object* v_currentTimeout_3306_; lean_object* v_headerTimeout_3307_; lean_object* v_response_3308_; lean_object* v_respStream_3309_; uint8_t v_requiresData_3310_; lean_object* v_expectData_3311_; lean_object* v_pendingHead_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3328_; 
v_machine_3303_ = lean_ctor_get(v_state_3288_, 0);
v_requestStream_3304_ = lean_ctor_get(v_state_3288_, 1);
v_keepAliveTimeout_3305_ = lean_ctor_get(v_state_3288_, 2);
v_currentTimeout_3306_ = lean_ctor_get(v_state_3288_, 3);
v_headerTimeout_3307_ = lean_ctor_get(v_state_3288_, 4);
v_response_3308_ = lean_ctor_get(v_state_3288_, 5);
v_respStream_3309_ = lean_ctor_get(v_state_3288_, 6);
v_requiresData_3310_ = lean_ctor_get_uint8(v_state_3288_, sizeof(void*)*9);
v_expectData_3311_ = lean_ctor_get(v_state_3288_, 7);
v_pendingHead_3312_ = lean_ctor_get(v_state_3288_, 8);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_state_3288_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3314_ = v_state_3288_;
v_isShared_3315_ = v_isSharedCheck_3328_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_pendingHead_3312_);
lean_inc(v_expectData_3311_);
lean_inc(v_respStream_3309_);
lean_inc(v_response_3308_);
lean_inc(v_headerTimeout_3307_);
lean_inc(v_currentTimeout_3306_);
lean_inc(v_keepAliveTimeout_3305_);
lean_inc(v_requestStream_3304_);
lean_inc(v_machine_3303_);
lean_dec(v_state_3288_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3328_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3320_; 
v___x_3316_ = lean_box(31);
v___x_3317_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3303_, v___x_3316_);
v___x_3318_ = 0;
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3317_);
v___x_3320_ = v___x_3314_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_requestStream_3304_);
lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_keepAliveTimeout_3305_);
lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_currentTimeout_3306_);
lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_headerTimeout_3307_);
lean_ctor_set(v_reuseFailAlloc_3327_, 5, v_response_3308_);
lean_ctor_set(v_reuseFailAlloc_3327_, 6, v_respStream_3309_);
lean_ctor_set(v_reuseFailAlloc_3327_, 7, v_expectData_3311_);
lean_ctor_set(v_reuseFailAlloc_3327_, 8, v_pendingHead_3312_);
lean_ctor_set_uint8(v_reuseFailAlloc_3327_, sizeof(void*)*9, v_requiresData_3310_);
v___x_3320_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*9 + 1, v___x_3318_);
v___x_3321_ = lean_box(v___x_3318_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v___x_3322_);
v___x_3324_ = v___x_3301_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3331_, v_x_3332_);
return v_res_3334_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3340_ = lean_mk_io_user_error(v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_handler_3343_, lean_object* v_config_3344_, lean_object* v_event_3345_, lean_object* v_state_3346_){
_start:
{
switch(lean_obj_tag(v_event_3345_))
{
case 0:
{
lean_object* v_x_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_handler_3343_);
lean_dec_ref(v_inst_3342_);
lean_dec_ref(v_inst_3341_);
v_x_3348_ = lean_ctor_get(v_event_3345_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_event_3345_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3350_ = v_event_3345_;
v_isShared_3351_ = v_isSharedCheck_3455_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_x_3348_);
lean_dec(v_event_3345_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3455_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
if (lean_obj_tag(v_x_3348_) == 0)
{
lean_object* v_machine_3352_; lean_object* v_reader_3353_; lean_object* v_requestStream_3354_; lean_object* v_keepAliveTimeout_3355_; lean_object* v_currentTimeout_3356_; lean_object* v_headerTimeout_3357_; lean_object* v_response_3358_; lean_object* v_respStream_3359_; uint8_t v_requiresData_3360_; lean_object* v_expectData_3361_; uint8_t v_handlerDispatched_3362_; lean_object* v_pendingHead_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_config_3344_);
v_machine_3352_ = lean_ctor_get(v_state_3346_, 0);
lean_inc_ref(v_machine_3352_);
v_reader_3353_ = lean_ctor_get(v_machine_3352_, 0);
lean_inc_ref(v_reader_3353_);
v_requestStream_3354_ = lean_ctor_get(v_state_3346_, 1);
v_keepAliveTimeout_3355_ = lean_ctor_get(v_state_3346_, 2);
v_currentTimeout_3356_ = lean_ctor_get(v_state_3346_, 3);
v_headerTimeout_3357_ = lean_ctor_get(v_state_3346_, 4);
v_response_3358_ = lean_ctor_get(v_state_3346_, 5);
v_respStream_3359_ = lean_ctor_get(v_state_3346_, 6);
v_requiresData_3360_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3361_ = lean_ctor_get(v_state_3346_, 7);
v_handlerDispatched_3362_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9 + 1);
v_pendingHead_3363_ = lean_ctor_get(v_state_3346_, 8);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_state_3346_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_state_3346_, 0);
lean_dec(v_unused_3407_);
v___x_3365_ = v_state_3346_;
v_isShared_3366_ = v_isSharedCheck_3406_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_pendingHead_3363_);
lean_inc(v_expectData_3361_);
lean_inc(v_respStream_3359_);
lean_inc(v_response_3358_);
lean_inc(v_headerTimeout_3357_);
lean_inc(v_currentTimeout_3356_);
lean_inc(v_keepAliveTimeout_3355_);
lean_inc(v_requestStream_3354_);
lean_dec(v_state_3346_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3406_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_writer_3367_; lean_object* v_config_3368_; lean_object* v_events_3369_; lean_object* v_error_3370_; lean_object* v_instant_3371_; uint8_t v_keepAlive_3372_; uint8_t v_forcedFlush_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3404_; 
v_writer_3367_ = lean_ctor_get(v_machine_3352_, 1);
v_config_3368_ = lean_ctor_get(v_machine_3352_, 2);
v_events_3369_ = lean_ctor_get(v_machine_3352_, 3);
v_error_3370_ = lean_ctor_get(v_machine_3352_, 4);
v_instant_3371_ = lean_ctor_get(v_machine_3352_, 5);
v_keepAlive_3372_ = lean_ctor_get_uint8(v_machine_3352_, sizeof(void*)*6);
v_forcedFlush_3373_ = lean_ctor_get_uint8(v_machine_3352_, sizeof(void*)*6 + 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_machine_3352_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v_machine_3352_, 0);
lean_dec(v_unused_3405_);
v___x_3375_ = v_machine_3352_;
v_isShared_3376_ = v_isSharedCheck_3404_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_instant_3371_);
lean_inc(v_error_3370_);
lean_inc(v_events_3369_);
lean_inc(v_config_3368_);
lean_inc(v_writer_3367_);
lean_dec(v_machine_3352_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3404_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_state_3377_; lean_object* v_input_3378_; lean_object* v_messageHead_3379_; lean_object* v_messageCount_3380_; lean_object* v_bodyBytesRead_3381_; lean_object* v_headerBytesRead_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3403_; 
v_state_3377_ = lean_ctor_get(v_reader_3353_, 0);
v_input_3378_ = lean_ctor_get(v_reader_3353_, 1);
v_messageHead_3379_ = lean_ctor_get(v_reader_3353_, 2);
v_messageCount_3380_ = lean_ctor_get(v_reader_3353_, 3);
v_bodyBytesRead_3381_ = lean_ctor_get(v_reader_3353_, 4);
v_headerBytesRead_3382_ = lean_ctor_get(v_reader_3353_, 5);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_reader_3353_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3384_ = v_reader_3353_;
v_isShared_3385_ = v_isSharedCheck_3403_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_headerBytesRead_3382_);
lean_inc(v_bodyBytesRead_3381_);
lean_inc(v_messageCount_3380_);
lean_inc(v_messageHead_3379_);
lean_inc(v_input_3378_);
lean_inc(v_state_3377_);
lean_dec(v_reader_3353_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3403_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
uint8_t v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = 1;
if (v_isShared_3385_ == 0)
{
v___x_3388_ = v___x_3384_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_state_3377_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_input_3378_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_messageHead_3379_);
lean_ctor_set(v_reuseFailAlloc_3402_, 3, v_messageCount_3380_);
lean_ctor_set(v_reuseFailAlloc_3402_, 4, v_bodyBytesRead_3381_);
lean_ctor_set(v_reuseFailAlloc_3402_, 5, v_headerBytesRead_3382_);
v___x_3388_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
uint8_t v___x_3389_; lean_object* v___x_3391_; 
lean_ctor_set_uint8(v___x_3388_, sizeof(void*)*6, v___x_3386_);
v___x_3389_ = 0;
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3388_);
v___x_3391_ = v___x_3375_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_writer_3367_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_config_3368_);
lean_ctor_set(v_reuseFailAlloc_3401_, 3, v_events_3369_);
lean_ctor_set(v_reuseFailAlloc_3401_, 4, v_error_3370_);
lean_ctor_set(v_reuseFailAlloc_3401_, 5, v_instant_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3401_, sizeof(void*)*6, v_keepAlive_3372_);
lean_ctor_set_uint8(v_reuseFailAlloc_3401_, sizeof(void*)*6 + 1, v_forcedFlush_3373_);
v___x_3391_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3393_; 
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*6 + 2, v___x_3389_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3391_);
v___x_3393_ = v___x_3365_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_requestStream_3354_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_keepAliveTimeout_3355_);
lean_ctor_set(v_reuseFailAlloc_3400_, 3, v_currentTimeout_3356_);
lean_ctor_set(v_reuseFailAlloc_3400_, 4, v_headerTimeout_3357_);
lean_ctor_set(v_reuseFailAlloc_3400_, 5, v_response_3358_);
lean_ctor_set(v_reuseFailAlloc_3400_, 6, v_respStream_3359_);
lean_ctor_set(v_reuseFailAlloc_3400_, 7, v_expectData_3361_);
lean_ctor_set(v_reuseFailAlloc_3400_, 8, v_pendingHead_3363_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, sizeof(void*)*9, v_requiresData_3360_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, sizeof(void*)*9 + 1, v_handlerDispatched_3362_);
v___x_3393_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3394_ = lean_box(v___x_3389_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 1);
lean_ctor_set(v___x_3350_, 0, v___x_3395_);
v___x_3397_ = v___x_3350_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
return v___x_3398_;
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
lean_object* v_val_3408_; lean_object* v_machine_3409_; lean_object* v_requestStream_3410_; lean_object* v_keepAliveTimeout_3411_; lean_object* v_currentTimeout_3412_; lean_object* v_response_3413_; lean_object* v_respStream_3414_; uint8_t v_requiresData_3415_; lean_object* v_expectData_3416_; uint8_t v_handlerDispatched_3417_; lean_object* v_pendingHead_3418_; lean_object* v___f_3419_; 
lean_del_object(v___x_3350_);
v_val_3408_ = lean_ctor_get(v_x_3348_, 0);
lean_inc_n(v_val_3408_, 2);
lean_dec_ref_known(v_x_3348_, 1);
v_machine_3409_ = lean_ctor_get(v_state_3346_, 0);
v_requestStream_3410_ = lean_ctor_get(v_state_3346_, 1);
v_keepAliveTimeout_3411_ = lean_ctor_get(v_state_3346_, 2);
lean_inc(v_keepAliveTimeout_3411_);
v_currentTimeout_3412_ = lean_ctor_get(v_state_3346_, 3);
v_response_3413_ = lean_ctor_get(v_state_3346_, 5);
v_respStream_3414_ = lean_ctor_get(v_state_3346_, 6);
v_requiresData_3415_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3416_ = lean_ctor_get(v_state_3346_, 7);
v_handlerDispatched_3417_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9 + 1);
v_pendingHead_3418_ = lean_ctor_get(v_state_3346_, 8);
v___f_3419_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3419_, 0, v_val_3408_);
if (lean_obj_tag(v_keepAliveTimeout_3411_) == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec_ref(v___f_3419_);
lean_dec_ref(v_config_3344_);
v___x_3420_ = lean_box(0);
v___x_3421_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3408_, v___x_3420_, v_state_3346_);
return v___x_3421_;
}
else
{
lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3453_; 
lean_inc(v_pendingHead_3418_);
lean_inc(v_expectData_3416_);
lean_inc(v_respStream_3414_);
lean_inc_ref(v_response_3413_);
lean_inc(v_currentTimeout_3412_);
lean_inc_ref(v_requestStream_3410_);
lean_inc_ref(v_machine_3409_);
lean_dec(v_val_3408_);
lean_dec_ref(v_state_3346_);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_keepAliveTimeout_3411_);
if (v_isSharedCheck_3453_ == 0)
{
lean_object* v_unused_3454_; 
v_unused_3454_ = lean_ctor_get(v_keepAliveTimeout_3411_, 0);
lean_dec(v_unused_3454_);
v___x_3423_ = v_keepAliveTimeout_3411_;
v_isShared_3424_ = v_isSharedCheck_3453_;
goto v_resetjp_3422_;
}
else
{
lean_dec(v_keepAliveTimeout_3411_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3453_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___f_3427_; lean_object* v_val_3429_; lean_object* v___x_3436_; 
v___x_3425_ = lean_box(v_requiresData_3415_);
v___x_3426_ = lean_box(v_handlerDispatched_3417_);
v___f_3427_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3427_, 0, v_config_3344_);
lean_closure_set(v___f_3427_, 1, v_machine_3409_);
lean_closure_set(v___f_3427_, 2, v_requestStream_3410_);
lean_closure_set(v___f_3427_, 3, v_currentTimeout_3412_);
lean_closure_set(v___f_3427_, 4, v_response_3413_);
lean_closure_set(v___f_3427_, 5, v_respStream_3414_);
lean_closure_set(v___f_3427_, 6, v___x_3425_);
lean_closure_set(v___f_3427_, 7, v_expectData_3416_);
lean_closure_set(v___f_3427_, 8, v___x_3426_);
lean_closure_set(v___f_3427_, 9, v_pendingHead_3418_);
lean_closure_set(v___f_3427_, 10, v___f_3419_);
v___x_3436_ = lean_get_current_time();
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3436_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set_tag(v___x_3439_, 1);
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v_val_3429_ = v___x_3442_;
goto v___jp_3428_;
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v_a_3445_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3436_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3436_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set_tag(v___x_3447_, 0);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
v_val_3429_ = v___x_3450_;
goto v___jp_3428_;
}
}
}
v___jp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 0);
lean_ctor_set(v___x_3423_, 0, v_val_3429_);
v___x_3431_ = v___x_3423_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_val_3429_);
v___x_3431_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; uint8_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = 0;
v___x_3434_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3432_, v___x_3433_, v___x_3431_, v___f_3427_);
return v___x_3434_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3567_; 
lean_dec_ref(v_config_3344_);
lean_dec(v_handler_3343_);
lean_dec_ref(v_inst_3341_);
v_x_3456_ = lean_ctor_get(v_event_3345_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_event_3345_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3458_ = v_event_3345_;
v_isShared_3459_ = v_isSharedCheck_3567_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_x_3456_);
lean_dec(v_event_3345_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3567_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
if (lean_obj_tag(v_x_3456_) == 0)
{
lean_object* v_machine_3460_; lean_object* v_requestStream_3461_; lean_object* v_keepAliveTimeout_3462_; lean_object* v_currentTimeout_3463_; lean_object* v_headerTimeout_3464_; lean_object* v_response_3465_; lean_object* v_respStream_3466_; uint8_t v_requiresData_3467_; lean_object* v_expectData_3468_; uint8_t v_handlerDispatched_3469_; lean_object* v_pendingHead_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___f_3473_; 
lean_del_object(v___x_3458_);
v_machine_3460_ = lean_ctor_get(v_state_3346_, 0);
lean_inc_ref_n(v_machine_3460_, 2);
v_requestStream_3461_ = lean_ctor_get(v_state_3346_, 1);
lean_inc_ref_n(v_requestStream_3461_, 2);
v_keepAliveTimeout_3462_ = lean_ctor_get(v_state_3346_, 2);
lean_inc_n(v_keepAliveTimeout_3462_, 2);
v_currentTimeout_3463_ = lean_ctor_get(v_state_3346_, 3);
lean_inc_n(v_currentTimeout_3463_, 2);
v_headerTimeout_3464_ = lean_ctor_get(v_state_3346_, 4);
lean_inc_n(v_headerTimeout_3464_, 2);
v_response_3465_ = lean_ctor_get(v_state_3346_, 5);
lean_inc_ref_n(v_response_3465_, 2);
v_respStream_3466_ = lean_ctor_get(v_state_3346_, 6);
lean_inc(v_respStream_3466_);
v_requiresData_3467_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3468_ = lean_ctor_get(v_state_3346_, 7);
lean_inc_n(v_expectData_3468_, 2);
v_handlerDispatched_3469_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9 + 1);
v_pendingHead_3470_ = lean_ctor_get(v_state_3346_, 8);
lean_inc_n(v_pendingHead_3470_, 2);
lean_dec_ref(v_state_3346_);
v___x_3471_ = lean_box(v_requiresData_3467_);
v___x_3472_ = lean_box(v_handlerDispatched_3469_);
v___f_3473_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3473_, 0, v_machine_3460_);
lean_closure_set(v___f_3473_, 1, v_requestStream_3461_);
lean_closure_set(v___f_3473_, 2, v_keepAliveTimeout_3462_);
lean_closure_set(v___f_3473_, 3, v_currentTimeout_3463_);
lean_closure_set(v___f_3473_, 4, v_headerTimeout_3464_);
lean_closure_set(v___f_3473_, 5, v_response_3465_);
lean_closure_set(v___f_3473_, 6, v___x_3471_);
lean_closure_set(v___f_3473_, 7, v_expectData_3468_);
lean_closure_set(v___f_3473_, 8, v___x_3472_);
lean_closure_set(v___f_3473_, 9, v_pendingHead_3470_);
if (lean_obj_tag(v_respStream_3466_) == 1)
{
lean_object* v_val_3474_; lean_object* v_close_3475_; lean_object* v_isClosed_3476_; lean_object* v___x_3477_; lean_object* v___f_3478_; lean_object* v___f_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; 
lean_dec(v_pendingHead_3470_);
lean_dec(v_expectData_3468_);
lean_dec_ref(v_response_3465_);
lean_dec(v_headerTimeout_3464_);
lean_dec(v_currentTimeout_3463_);
lean_dec(v_keepAliveTimeout_3462_);
lean_dec_ref(v_requestStream_3461_);
lean_dec_ref(v_machine_3460_);
v_val_3474_ = lean_ctor_get(v_respStream_3466_, 0);
lean_inc_n(v_val_3474_, 2);
lean_dec_ref_known(v_respStream_3466_, 1);
v_close_3475_ = lean_ctor_get(v_inst_3342_, 1);
lean_inc_ref(v_close_3475_);
v_isClosed_3476_ = lean_ctor_get(v_inst_3342_, 2);
lean_inc_ref(v_isClosed_3476_);
lean_dec_ref(v_inst_3342_);
v___x_3477_ = lean_apply_2(v_isClosed_3476_, v_val_3474_, lean_box(0));
lean_inc_ref(v___f_3473_);
v___f_3478_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3478_, 0, v___f_3473_);
v___f_3479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3479_, 0, v_close_3475_);
lean_closure_set(v___f_3479_, 1, v_val_3474_);
lean_closure_set(v___f_3479_, 2, v___f_3478_);
lean_closure_set(v___f_3479_, 3, v___f_3473_);
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = 0;
v___x_3482_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3480_, v___x_3481_, v___x_3477_, v___f_3479_);
return v___x_3482_;
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec_ref(v___f_3473_);
lean_dec(v_respStream_3466_);
lean_dec_ref(v_inst_3342_);
v___x_3483_ = lean_box(0);
v___x_3484_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3460_, v_requestStream_3461_, v_keepAliveTimeout_3462_, v_currentTimeout_3463_, v_headerTimeout_3464_, v_response_3465_, v_requiresData_3467_, v_expectData_3468_, v_handlerDispatched_3469_, v_pendingHead_3470_, v___x_3483_);
return v___x_3484_;
}
}
else
{
lean_object* v_val_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v_inst_3342_);
v_val_3485_ = lean_ctor_get(v_x_3456_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_x_3456_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3487_ = v_x_3456_;
v_isShared_3488_ = v_isSharedCheck_3566_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_val_3485_);
lean_dec(v_x_3456_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3566_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_machine_3489_; lean_object* v_requestStream_3490_; lean_object* v_keepAliveTimeout_3491_; lean_object* v_currentTimeout_3492_; lean_object* v_headerTimeout_3493_; lean_object* v_response_3494_; lean_object* v_respStream_3495_; uint8_t v_requiresData_3496_; lean_object* v_expectData_3497_; uint8_t v_handlerDispatched_3498_; lean_object* v_pendingHead_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3565_; 
v_machine_3489_ = lean_ctor_get(v_state_3346_, 0);
v_requestStream_3490_ = lean_ctor_get(v_state_3346_, 1);
v_keepAliveTimeout_3491_ = lean_ctor_get(v_state_3346_, 2);
v_currentTimeout_3492_ = lean_ctor_get(v_state_3346_, 3);
v_headerTimeout_3493_ = lean_ctor_get(v_state_3346_, 4);
v_response_3494_ = lean_ctor_get(v_state_3346_, 5);
v_respStream_3495_ = lean_ctor_get(v_state_3346_, 6);
v_requiresData_3496_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3497_ = lean_ctor_get(v_state_3346_, 7);
v_handlerDispatched_3498_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9 + 1);
v_pendingHead_3499_ = lean_ctor_get(v_state_3346_, 8);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_state_3346_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3501_ = v_state_3346_;
v_isShared_3502_ = v_isSharedCheck_3565_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_pendingHead_3499_);
lean_inc(v_expectData_3497_);
lean_inc(v_respStream_3495_);
lean_inc(v_response_3494_);
lean_inc(v_headerTimeout_3493_);
lean_inc(v_currentTimeout_3492_);
lean_inc(v_keepAliveTimeout_3491_);
lean_inc(v_requestStream_3490_);
lean_inc(v_machine_3489_);
lean_dec(v_state_3346_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3565_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___y_3504_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_mk_empty_array_with_capacity(v___x_3517_);
v___x_3519_ = lean_array_push(v___x_3518_, v_val_3485_);
v___x_3520_ = lean_array_get_size(v___x_3519_);
v___x_3521_ = lean_unsigned_to_nat(0u);
v___x_3522_ = lean_nat_dec_eq(v___x_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v_reader_3523_; lean_object* v_writer_3524_; lean_object* v_config_3525_; lean_object* v_events_3526_; lean_object* v_error_3527_; lean_object* v_instant_3528_; uint8_t v_keepAlive_3529_; uint8_t v_forcedFlush_3530_; uint8_t v_pullBodyStalled_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3564_; 
v_reader_3523_ = lean_ctor_get(v_machine_3489_, 0);
v_writer_3524_ = lean_ctor_get(v_machine_3489_, 1);
v_config_3525_ = lean_ctor_get(v_machine_3489_, 2);
v_events_3526_ = lean_ctor_get(v_machine_3489_, 3);
v_error_3527_ = lean_ctor_get(v_machine_3489_, 4);
v_instant_3528_ = lean_ctor_get(v_machine_3489_, 5);
v_keepAlive_3529_ = lean_ctor_get_uint8(v_machine_3489_, sizeof(void*)*6);
v_forcedFlush_3530_ = lean_ctor_get_uint8(v_machine_3489_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3531_ = lean_ctor_get_uint8(v_machine_3489_, sizeof(void*)*6 + 2);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_machine_3489_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3533_ = v_machine_3489_;
v_isShared_3534_ = v_isSharedCheck_3564_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_instant_3528_);
lean_inc(v_error_3527_);
lean_inc(v_events_3526_);
lean_inc(v_config_3525_);
lean_inc(v_writer_3524_);
lean_inc(v_reader_3523_);
lean_dec(v_machine_3489_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3564_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___y_3536_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_3559_ = lean_nat_dec_lt(v___x_3521_, v___x_3520_);
if (v___x_3559_ == 0)
{
v___y_3536_ = v___x_3521_;
goto v___jp_3535_;
}
else
{
lean_object* v___f_3560_; size_t v___x_3561_; size_t v___x_3562_; lean_object* v___x_3563_; 
v___f_3560_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = lean_usize_of_nat(v___x_3520_);
lean_inc_ref(v___x_3519_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3558_, v___f_3560_, v___x_3519_, v___x_3561_, v___x_3562_, v___x_3521_);
v___y_3536_ = v___x_3563_;
goto v___jp_3535_;
}
v___jp_3535_:
{
lean_object* v_userData_3537_; lean_object* v_outputData_3538_; lean_object* v_state_3539_; lean_object* v_knownSize_3540_; lean_object* v_messageHead_3541_; uint8_t v_sentMessage_3542_; uint8_t v_userClosedBody_3543_; uint8_t v_omitBody_3544_; lean_object* v_userDataBytes_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3557_; 
v_userData_3537_ = lean_ctor_get(v_writer_3524_, 0);
v_outputData_3538_ = lean_ctor_get(v_writer_3524_, 1);
v_state_3539_ = lean_ctor_get(v_writer_3524_, 2);
v_knownSize_3540_ = lean_ctor_get(v_writer_3524_, 3);
v_messageHead_3541_ = lean_ctor_get(v_writer_3524_, 4);
v_sentMessage_3542_ = lean_ctor_get_uint8(v_writer_3524_, sizeof(void*)*6);
v_userClosedBody_3543_ = lean_ctor_get_uint8(v_writer_3524_, sizeof(void*)*6 + 1);
v_omitBody_3544_ = lean_ctor_get_uint8(v_writer_3524_, sizeof(void*)*6 + 2);
v_userDataBytes_3545_ = lean_ctor_get(v_writer_3524_, 5);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_writer_3524_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3547_ = v_writer_3524_;
v_isShared_3548_ = v_isSharedCheck_3557_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_userDataBytes_3545_);
lean_inc(v_messageHead_3541_);
lean_inc(v_knownSize_3540_);
lean_inc(v_state_3539_);
lean_inc(v_outputData_3538_);
lean_inc(v_userData_3537_);
lean_dec(v_writer_3524_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3557_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3549_ = l_Array_append___redArg(v_userData_3537_, v___x_3519_);
lean_dec_ref(v___x_3519_);
v___x_3550_ = lean_nat_add(v_userDataBytes_3545_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec(v_userDataBytes_3545_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 5, v___x_3550_);
lean_ctor_set(v___x_3547_, 0, v___x_3549_);
v___x_3552_ = v___x_3547_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_outputData_3538_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_state_3539_);
lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_knownSize_3540_);
lean_ctor_set(v_reuseFailAlloc_3556_, 4, v_messageHead_3541_);
lean_ctor_set(v_reuseFailAlloc_3556_, 5, v___x_3550_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*6, v_sentMessage_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*6 + 1, v_userClosedBody_3543_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*6 + 2, v_omitBody_3544_);
v___x_3552_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3554_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 1, v___x_3552_);
v___x_3554_ = v___x_3533_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_reader_3523_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_config_3525_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_events_3526_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_error_3527_);
lean_ctor_set(v_reuseFailAlloc_3555_, 5, v_instant_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3555_, sizeof(void*)*6, v_keepAlive_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3555_, sizeof(void*)*6 + 1, v_forcedFlush_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3555_, sizeof(void*)*6 + 2, v_pullBodyStalled_3531_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
v___y_3504_ = v___x_3554_;
goto v___jp_3503_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3519_);
v___y_3504_ = v_machine_3489_;
goto v___jp_3503_;
}
v___jp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___y_3504_);
v___x_3506_ = v___x_3501_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___y_3504_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_requestStream_3490_);
lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_keepAliveTimeout_3491_);
lean_ctor_set(v_reuseFailAlloc_3516_, 3, v_currentTimeout_3492_);
lean_ctor_set(v_reuseFailAlloc_3516_, 4, v_headerTimeout_3493_);
lean_ctor_set(v_reuseFailAlloc_3516_, 5, v_response_3494_);
lean_ctor_set(v_reuseFailAlloc_3516_, 6, v_respStream_3495_);
lean_ctor_set(v_reuseFailAlloc_3516_, 7, v_expectData_3497_);
lean_ctor_set(v_reuseFailAlloc_3516_, 8, v_pendingHead_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, sizeof(void*)*9, v_requiresData_3496_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, sizeof(void*)*9 + 1, v_handlerDispatched_3498_);
v___x_3506_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
uint8_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3507_ = 0;
v___x_3508_ = lean_box(v___x_3507_);
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3506_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3509_);
v___x_3511_ = v___x_3487_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3511_);
v___x_3513_ = v___x_3458_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
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
uint8_t v_x_3568_; 
lean_dec_ref(v_config_3344_);
lean_dec_ref(v_inst_3342_);
v_x_3568_ = lean_ctor_get_uint8(v_event_3345_, 0);
lean_dec_ref_known(v_event_3345_, 0);
if (v_x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec(v_handler_3343_);
lean_dec_ref(v_inst_3341_);
v___x_3569_ = lean_box(v_x_3568_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_state_3346_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
else
{
lean_object* v_machine_3573_; lean_object* v_requestStream_3574_; lean_object* v_keepAliveTimeout_3575_; lean_object* v_currentTimeout_3576_; lean_object* v_headerTimeout_3577_; lean_object* v_response_3578_; lean_object* v_respStream_3579_; uint8_t v_requiresData_3580_; lean_object* v_expectData_3581_; uint8_t v_handlerDispatched_3582_; lean_object* v_pendingHead_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3633_; 
v_machine_3573_ = lean_ctor_get(v_state_3346_, 0);
v_requestStream_3574_ = lean_ctor_get(v_state_3346_, 1);
v_keepAliveTimeout_3575_ = lean_ctor_get(v_state_3346_, 2);
v_currentTimeout_3576_ = lean_ctor_get(v_state_3346_, 3);
v_headerTimeout_3577_ = lean_ctor_get(v_state_3346_, 4);
v_response_3578_ = lean_ctor_get(v_state_3346_, 5);
v_respStream_3579_ = lean_ctor_get(v_state_3346_, 6);
v_requiresData_3580_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3581_ = lean_ctor_get(v_state_3346_, 7);
v_handlerDispatched_3582_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9 + 1);
v_pendingHead_3583_ = lean_ctor_get(v_state_3346_, 8);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_state_3346_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3585_ = v_state_3346_;
v_isShared_3586_ = v_isSharedCheck_3633_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_pendingHead_3583_);
lean_inc(v_expectData_3581_);
lean_inc(v_respStream_3579_);
lean_inc(v_response_3578_);
lean_inc(v_headerTimeout_3577_);
lean_inc(v_currentTimeout_3576_);
lean_inc(v_keepAliveTimeout_3575_);
lean_inc(v_requestStream_3574_);
lean_inc(v_machine_3573_);
lean_dec(v_state_3346_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3633_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v_fst_3589_; lean_object* v_snd_3590_; lean_object* v_reader_3591_; lean_object* v_writer_3592_; lean_object* v_config_3593_; lean_object* v_events_3594_; lean_object* v_error_3595_; lean_object* v_instant_3596_; uint8_t v_keepAlive_3597_; uint8_t v_forcedFlush_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3632_; 
v___x_3587_ = 0;
v___x_3588_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3587_, v_machine_3573_);
v_fst_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_fst_3589_);
v_snd_3590_ = lean_ctor_get(v___x_3588_, 1);
lean_inc(v_snd_3590_);
lean_dec_ref(v___x_3588_);
v_reader_3591_ = lean_ctor_get(v_fst_3589_, 0);
v_writer_3592_ = lean_ctor_get(v_fst_3589_, 1);
v_config_3593_ = lean_ctor_get(v_fst_3589_, 2);
v_events_3594_ = lean_ctor_get(v_fst_3589_, 3);
v_error_3595_ = lean_ctor_get(v_fst_3589_, 4);
v_instant_3596_ = lean_ctor_get(v_fst_3589_, 5);
v_keepAlive_3597_ = lean_ctor_get_uint8(v_fst_3589_, sizeof(void*)*6);
v_forcedFlush_3598_ = lean_ctor_get_uint8(v_fst_3589_, sizeof(void*)*6 + 1);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_fst_3589_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3600_ = v_fst_3589_;
v_isShared_3601_ = v_isSharedCheck_3632_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_instant_3596_);
lean_inc(v_error_3595_);
lean_inc(v_events_3594_);
lean_inc(v_config_3593_);
lean_inc(v_writer_3592_);
lean_inc(v_reader_3591_);
lean_dec(v_fst_3589_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3632_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___f_3602_; lean_object* v___f_3603_; uint8_t v___y_3605_; 
v___f_3602_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3602_, 0, v_inst_3341_);
lean_closure_set(v___f_3602_, 1, v_handler_3343_);
v___f_3603_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3590_) == 0)
{
uint8_t v_sentMessage_3628_; 
v_sentMessage_3628_ = lean_ctor_get_uint8(v_writer_3592_, sizeof(void*)*6);
if (v_sentMessage_3628_ == 0)
{
lean_object* v_state_3629_; 
v_state_3629_ = lean_ctor_get(v_reader_3591_, 0);
if (lean_obj_tag(v_state_3629_) == 2)
{
v___y_3605_ = v_x_3568_;
goto v___jp_3604_;
}
else
{
v___y_3605_ = v_sentMessage_3628_;
goto v___jp_3604_;
}
}
else
{
uint8_t v___x_3630_; 
v___x_3630_ = 0;
v___y_3605_ = v___x_3630_;
goto v___jp_3604_;
}
}
else
{
uint8_t v___x_3631_; 
v___x_3631_ = 0;
v___y_3605_ = v___x_3631_;
goto v___jp_3604_;
}
v___jp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3601_ == 0)
{
v___x_3607_ = v___x_3600_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_reader_3591_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_writer_3592_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_config_3593_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_events_3594_);
lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_error_3595_);
lean_ctor_set(v_reuseFailAlloc_3627_, 5, v_instant_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3627_, sizeof(void*)*6, v_keepAlive_3597_);
lean_ctor_set_uint8(v_reuseFailAlloc_3627_, sizeof(void*)*6 + 1, v_forcedFlush_3598_);
v___x_3607_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v_st_3609_; 
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*6 + 2, v___y_3605_);
lean_inc_ref(v_requestStream_3574_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3607_);
v_st_3609_ = v___x_3585_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_requestStream_3574_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_keepAliveTimeout_3575_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_currentTimeout_3576_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_headerTimeout_3577_);
lean_ctor_set(v_reuseFailAlloc_3626_, 5, v_response_3578_);
lean_ctor_set(v_reuseFailAlloc_3626_, 6, v_respStream_3579_);
lean_ctor_set(v_reuseFailAlloc_3626_, 7, v_expectData_3581_);
lean_ctor_set(v_reuseFailAlloc_3626_, 8, v_pendingHead_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3626_, sizeof(void*)*9, v_requiresData_3580_);
lean_ctor_set_uint8(v_reuseFailAlloc_3626_, sizeof(void*)*9 + 1, v_handlerDispatched_3582_);
v_st_3609_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___f_3610_; 
lean_inc_ref(v_st_3609_);
v___f_3610_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3610_, 0, v_st_3609_);
if (lean_obj_tag(v_snd_3590_) == 1)
{
lean_object* v_val_3611_; uint8_t v_final_3612_; uint8_t v_incomplete_3613_; lean_object* v_chunk_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; 
lean_dec_ref(v_st_3609_);
v_val_3611_ = lean_ctor_get(v_snd_3590_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v_snd_3590_, 1);
v_final_3612_ = lean_ctor_get_uint8(v_val_3611_, sizeof(void*)*1);
v_incomplete_3613_ = lean_ctor_get_uint8(v_val_3611_, sizeof(void*)*1 + 1);
v_chunk_3614_ = lean_ctor_get(v_val_3611_, 0);
lean_inc_ref(v_chunk_3614_);
lean_dec(v_val_3611_);
lean_inc_ref_n(v_requestStream_3574_, 2);
v___x_3615_ = l_Std_Http_Body_Stream_send(v_requestStream_3574_, v_chunk_3614_, v_incomplete_3613_);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = 0;
v___x_3618_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3616_, v___x_3617_, v___x_3615_, v___f_3602_);
lean_inc_ref_n(v___f_3610_, 2);
v___f_3619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3619_, 0, v___f_3610_);
v___f_3620_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3620_, 0, v_requestStream_3574_);
lean_closure_set(v___f_3620_, 1, v___f_3619_);
lean_closure_set(v___f_3620_, 2, v___f_3610_);
v___x_3621_ = lean_box(v_final_3612_);
v___f_3622_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3622_, 0, v___x_3621_);
lean_closure_set(v___f_3622_, 1, v___f_3610_);
lean_closure_set(v___f_3622_, 2, v___f_3603_);
lean_closure_set(v___f_3622_, 3, v_requestStream_3574_);
lean_closure_set(v___f_3622_, 4, v___f_3620_);
v___x_3623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3616_, v___x_3617_, v___x_3618_, v___f_3622_);
return v___x_3623_;
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_dec_ref(v___f_3610_);
lean_dec_ref(v___f_3602_);
lean_dec(v_snd_3590_);
lean_dec_ref(v_requestStream_3574_);
v___x_3624_ = lean_box(0);
v___x_3625_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3609_, v___x_3624_);
return v___x_3625_;
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
lean_object* v_x_3634_; 
v_x_3634_ = lean_ctor_get(v_event_3345_, 0);
lean_inc_ref(v_x_3634_);
lean_dec_ref_known(v_event_3345_, 1);
if (lean_obj_tag(v_x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v_onFailure_3636_; lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
lean_dec_ref(v_config_3344_);
lean_dec_ref(v_inst_3342_);
v_a_3635_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v_x_3634_, 1);
v_onFailure_3636_ = lean_ctor_get(v_inst_3341_, 2);
lean_inc_ref(v_onFailure_3636_);
lean_dec_ref(v_inst_3341_);
v___x_3637_ = lean_apply_3(v_onFailure_3636_, v_handler_3343_, v_a_3635_, lean_box(0));
v___f_3638_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3638_, 0, v_state_3346_);
v___x_3639_ = lean_unsigned_to_nat(0u);
v___x_3640_ = 0;
v___x_3641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3639_, v___x_3640_, v___x_3637_, v___f_3638_);
return v___x_3641_;
}
else
{
lean_object* v_machine_3642_; lean_object* v_reader_3643_; lean_object* v_state_3644_; 
v_machine_3642_ = lean_ctor_get(v_state_3346_, 0);
lean_inc_ref(v_machine_3642_);
v_reader_3643_ = lean_ctor_get(v_machine_3642_, 0);
v_state_3644_ = lean_ctor_get(v_reader_3643_, 0);
if (lean_obj_tag(v_state_3644_) == 7)
{
lean_object* v_a_3645_; lean_object* v_requestStream_3646_; lean_object* v_keepAliveTimeout_3647_; lean_object* v_currentTimeout_3648_; lean_object* v_headerTimeout_3649_; lean_object* v_response_3650_; lean_object* v_respStream_3651_; uint8_t v_requiresData_3652_; lean_object* v_expectData_3653_; lean_object* v_pendingHead_3654_; lean_object* v_close_3655_; lean_object* v_isClosed_3656_; lean_object* v_body_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___f_3660_; lean_object* v___f_3661_; lean_object* v___f_3662_; lean_object* v___x_3663_; uint8_t v___x_3664_; lean_object* v___x_3665_; 
lean_dec_ref(v_config_3344_);
lean_dec(v_handler_3343_);
lean_dec_ref(v_inst_3341_);
v_a_3645_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v_x_3634_, 1);
v_requestStream_3646_ = lean_ctor_get(v_state_3346_, 1);
lean_inc_ref(v_requestStream_3646_);
v_keepAliveTimeout_3647_ = lean_ctor_get(v_state_3346_, 2);
lean_inc(v_keepAliveTimeout_3647_);
v_currentTimeout_3648_ = lean_ctor_get(v_state_3346_, 3);
lean_inc(v_currentTimeout_3648_);
v_headerTimeout_3649_ = lean_ctor_get(v_state_3346_, 4);
lean_inc(v_headerTimeout_3649_);
v_response_3650_ = lean_ctor_get(v_state_3346_, 5);
lean_inc_ref(v_response_3650_);
v_respStream_3651_ = lean_ctor_get(v_state_3346_, 6);
lean_inc(v_respStream_3651_);
v_requiresData_3652_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3653_ = lean_ctor_get(v_state_3346_, 7);
lean_inc(v_expectData_3653_);
v_pendingHead_3654_ = lean_ctor_get(v_state_3346_, 8);
lean_inc(v_pendingHead_3654_);
lean_dec_ref(v_state_3346_);
v_close_3655_ = lean_ctor_get(v_inst_3342_, 1);
lean_inc_ref(v_close_3655_);
v_isClosed_3656_ = lean_ctor_get(v_inst_3342_, 2);
lean_inc_ref(v_isClosed_3656_);
lean_dec_ref(v_inst_3342_);
v_body_3657_ = lean_ctor_get(v_a_3645_, 1);
lean_inc_n(v_body_3657_, 2);
lean_dec(v_a_3645_);
v___x_3658_ = lean_apply_2(v_isClosed_3656_, v_body_3657_, lean_box(0));
v___x_3659_ = lean_box(v_requiresData_3652_);
v___f_3660_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3660_, 0, v_machine_3642_);
lean_closure_set(v___f_3660_, 1, v_requestStream_3646_);
lean_closure_set(v___f_3660_, 2, v_keepAliveTimeout_3647_);
lean_closure_set(v___f_3660_, 3, v_currentTimeout_3648_);
lean_closure_set(v___f_3660_, 4, v_headerTimeout_3649_);
lean_closure_set(v___f_3660_, 5, v_response_3650_);
lean_closure_set(v___f_3660_, 6, v_respStream_3651_);
lean_closure_set(v___f_3660_, 7, v___x_3659_);
lean_closure_set(v___f_3660_, 8, v_expectData_3653_);
lean_closure_set(v___f_3660_, 9, v_pendingHead_3654_);
lean_inc_ref(v___f_3660_);
v___f_3661_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3661_, 0, v___f_3660_);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3662_, 0, v_close_3655_);
lean_closure_set(v___f_3662_, 1, v_body_3657_);
lean_closure_set(v___f_3662_, 2, v___f_3661_);
lean_closure_set(v___f_3662_, 3, v___f_3660_);
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = 0;
v___x_3665_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3663_, v___x_3664_, v___x_3658_, v___f_3662_);
return v___x_3665_;
}
else
{
lean_object* v_a_3666_; lean_object* v_requestStream_3667_; lean_object* v_keepAliveTimeout_3668_; lean_object* v_currentTimeout_3669_; lean_object* v_headerTimeout_3670_; lean_object* v_response_3671_; uint8_t v_requiresData_3672_; lean_object* v_expectData_3673_; lean_object* v_pendingHead_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___f_3681_; uint8_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___f_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_a_3666_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v_x_3634_, 1);
v_requestStream_3667_ = lean_ctor_get(v_state_3346_, 1);
lean_inc_ref(v_requestStream_3667_);
v_keepAliveTimeout_3668_ = lean_ctor_get(v_state_3346_, 2);
lean_inc(v_keepAliveTimeout_3668_);
v_currentTimeout_3669_ = lean_ctor_get(v_state_3346_, 3);
lean_inc(v_currentTimeout_3669_);
v_headerTimeout_3670_ = lean_ctor_get(v_state_3346_, 4);
lean_inc(v_headerTimeout_3670_);
v_response_3671_ = lean_ctor_get(v_state_3346_, 5);
lean_inc_ref(v_response_3671_);
v_requiresData_3672_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3673_ = lean_ctor_get(v_state_3346_, 7);
lean_inc(v_expectData_3673_);
v_pendingHead_3674_ = lean_ctor_get(v_state_3346_, 8);
lean_inc(v_pendingHead_3674_);
lean_dec_ref(v_state_3346_);
lean_inc_ref(v_inst_3342_);
v___x_3675_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3342_, v_config_3344_, v_machine_3642_, v_a_3666_);
v___x_3676_ = 0;
v___x_3677_ = lean_box(v_requiresData_3672_);
v___x_3678_ = lean_box(v___x_3676_);
v___f_3679_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3679_, 0, v_requestStream_3667_);
lean_closure_set(v___f_3679_, 1, v_keepAliveTimeout_3668_);
lean_closure_set(v___f_3679_, 2, v_currentTimeout_3669_);
lean_closure_set(v___f_3679_, 3, v_headerTimeout_3670_);
lean_closure_set(v___f_3679_, 4, v_response_3671_);
lean_closure_set(v___f_3679_, 5, v___x_3677_);
lean_closure_set(v___f_3679_, 6, v_expectData_3673_);
lean_closure_set(v___f_3679_, 7, v___x_3678_);
lean_closure_set(v___f_3679_, 8, v_pendingHead_3674_);
v___f_3680_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3680_, 0, v___f_3679_);
v___f_3681_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3682_ = 1;
v___x_3683_ = lean_box(v___x_3676_);
v___x_3684_ = lean_box(v___x_3682_);
lean_inc_ref(v___f_3680_);
v___f_3685_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3685_, 0, v___x_3683_);
lean_closure_set(v___f_3685_, 1, v___f_3680_);
lean_closure_set(v___f_3685_, 2, v_inst_3342_);
lean_closure_set(v___f_3685_, 3, v___f_3681_);
lean_closure_set(v___f_3685_, 4, v___x_3684_);
lean_closure_set(v___f_3685_, 5, v_inst_3341_);
lean_closure_set(v___f_3685_, 6, v_handler_3343_);
lean_closure_set(v___f_3685_, 7, v___f_3680_);
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3686_, v___x_3676_, v___x_3675_, v___f_3685_);
return v___x_3687_;
}
}
}
case 4:
{
lean_object* v_onFailure_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___f_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; 
lean_dec_ref(v_config_3344_);
lean_dec_ref(v_inst_3342_);
v_onFailure_3688_ = lean_ctor_get(v_inst_3341_, 2);
lean_inc_ref(v_onFailure_3688_);
lean_dec_ref(v_inst_3341_);
v___x_3689_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3690_ = lean_apply_3(v_onFailure_3688_, v_handler_3343_, v___x_3689_, lean_box(0));
v___f_3691_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3691_, 0, v_state_3346_);
v___x_3692_ = lean_unsigned_to_nat(0u);
v___x_3693_ = 0;
v___x_3694_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3692_, v___x_3693_, v___x_3690_, v___f_3691_);
return v___x_3694_;
}
case 5:
{
lean_object* v_machine_3695_; lean_object* v_requestStream_3696_; lean_object* v_keepAliveTimeout_3697_; lean_object* v_currentTimeout_3698_; lean_object* v_headerTimeout_3699_; lean_object* v_response_3700_; lean_object* v_respStream_3701_; uint8_t v_requiresData_3702_; lean_object* v_expectData_3703_; lean_object* v_pendingHead_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v_config_3344_);
lean_dec(v_handler_3343_);
lean_dec_ref(v_inst_3342_);
lean_dec_ref(v_inst_3341_);
v_machine_3695_ = lean_ctor_get(v_state_3346_, 0);
v_requestStream_3696_ = lean_ctor_get(v_state_3346_, 1);
v_keepAliveTimeout_3697_ = lean_ctor_get(v_state_3346_, 2);
v_currentTimeout_3698_ = lean_ctor_get(v_state_3346_, 3);
v_headerTimeout_3699_ = lean_ctor_get(v_state_3346_, 4);
v_response_3700_ = lean_ctor_get(v_state_3346_, 5);
v_respStream_3701_ = lean_ctor_get(v_state_3346_, 6);
v_requiresData_3702_ = lean_ctor_get_uint8(v_state_3346_, sizeof(void*)*9);
v_expectData_3703_ = lean_ctor_get(v_state_3346_, 7);
v_pendingHead_3704_ = lean_ctor_get(v_state_3346_, 8);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_state_3346_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3706_ = v_state_3346_;
v_isShared_3707_ = v_isSharedCheck_3718_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_pendingHead_3704_);
lean_inc(v_expectData_3703_);
lean_inc(v_respStream_3701_);
lean_inc(v_response_3700_);
lean_inc(v_headerTimeout_3699_);
lean_inc(v_currentTimeout_3698_);
lean_inc(v_keepAliveTimeout_3697_);
lean_inc(v_requestStream_3696_);
lean_inc(v_machine_3695_);
lean_dec(v_state_3346_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3718_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___x_3712_; 
v___x_3708_ = lean_box(55);
v___x_3709_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3695_, v___x_3708_);
v___x_3710_ = 0;
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3709_);
v___x_3712_ = v___x_3706_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_requestStream_3696_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_keepAliveTimeout_3697_);
lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_currentTimeout_3698_);
lean_ctor_set(v_reuseFailAlloc_3717_, 4, v_headerTimeout_3699_);
lean_ctor_set(v_reuseFailAlloc_3717_, 5, v_response_3700_);
lean_ctor_set(v_reuseFailAlloc_3717_, 6, v_respStream_3701_);
lean_ctor_set(v_reuseFailAlloc_3717_, 7, v_expectData_3703_);
lean_ctor_set(v_reuseFailAlloc_3717_, 8, v_pendingHead_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3717_, sizeof(void*)*9, v_requiresData_3702_);
v___x_3712_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_ctor_set_uint8(v___x_3712_, sizeof(void*)*9 + 1, v___x_3710_);
v___x_3713_ = lean_box(v___x_3710_);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
return v___x_3716_;
}
}
}
default: 
{
uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec_ref(v_config_3344_);
lean_dec(v_handler_3343_);
lean_dec_ref(v_inst_3342_);
lean_dec_ref(v_inst_3341_);
v___x_3719_ = 1;
v___x_3720_ = lean_box(v___x_3719_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_state_3346_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3724_, lean_object* v_inst_3725_, lean_object* v_handler_3726_, lean_object* v_config_3727_, lean_object* v_event_3728_, lean_object* v_state_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3724_, v_inst_3725_, v_handler_3726_, v_config_3727_, v_event_3728_, v_state_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3732_, lean_object* v_00_u03b2_3733_, lean_object* v_inst_3734_, lean_object* v_inst_3735_, lean_object* v_handler_3736_, lean_object* v_config_3737_, lean_object* v_event_3738_, lean_object* v_state_3739_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3734_, v_inst_3735_, v_handler_3736_, v_config_3737_, v_event_3738_, v_state_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3742_, lean_object* v_00_u03b2_3743_, lean_object* v_inst_3744_, lean_object* v_inst_3745_, lean_object* v_handler_3746_, lean_object* v_config_3747_, lean_object* v_event_3748_, lean_object* v_state_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3742_, v_00_u03b2_3743_, v_inst_3744_, v_inst_3745_, v_handler_3746_, v_config_3747_, v_event_3748_, v_state_3749_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_expectData_3752_, lean_object* v_respStream_3753_, lean_object* v_currentTimeout_3754_, lean_object* v_keepAliveTimeout_3755_, lean_object* v_headerTimeout_3756_, lean_object* v_connectionContext_3757_, uint8_t v_handlerDispatched_3758_, lean_object* v_response_3759_, lean_object* v_socket_3760_, uint8_t v_requiresData_3761_, uint8_t v_sentMessage_3762_, lean_object* v_reader_3763_, uint8_t v_requestBodyInterested_3764_, lean_object* v_requestBody_3765_){
_start:
{
lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3774_; uint8_t v___y_3780_; uint8_t v___y_3783_; uint8_t v___y_3784_; uint8_t v___y_3786_; uint8_t v___y_3787_; uint8_t v___y_3788_; uint8_t v___y_3790_; uint8_t v___y_3791_; uint8_t v___y_3794_; 
if (v_handlerDispatched_3758_ == 0)
{
uint8_t v___x_3797_; 
v___x_3797_ = 1;
v___y_3794_ = v___x_3797_;
goto v___jp_3793_;
}
else
{
uint8_t v___x_3798_; 
v___x_3798_ = 0;
v___y_3794_ = v___x_3798_;
goto v___jp_3793_;
}
v___jp_3767_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3770_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3770_, 0, v___y_3768_);
lean_ctor_set(v___x_3770_, 1, v_expectData_3752_);
lean_ctor_set(v___x_3770_, 2, v___y_3769_);
lean_ctor_set(v___x_3770_, 3, v_respStream_3753_);
lean_ctor_set(v___x_3770_, 4, v_requestBody_3765_);
lean_ctor_set(v___x_3770_, 5, v_currentTimeout_3754_);
lean_ctor_set(v___x_3770_, 6, v_keepAliveTimeout_3755_);
lean_ctor_set(v___x_3770_, 7, v_headerTimeout_3756_);
lean_ctor_set(v___x_3770_, 8, v_connectionContext_3757_);
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
v___jp_3773_:
{
if (v_handlerDispatched_3758_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v_response_3759_);
v___x_3775_ = lean_box(0);
v___y_3768_ = v___y_3774_;
v___y_3769_ = v___x_3775_;
goto v___jp_3767_;
}
else
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v_response_3759_);
v___y_3768_ = v___y_3774_;
v___y_3769_ = v___x_3776_;
goto v___jp_3767_;
}
}
v___jp_3777_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3778_, 0, v_socket_3760_);
v___y_3774_ = v___x_3778_;
goto v___jp_3773_;
}
v___jp_3779_:
{
if (v_requiresData_3761_ == 0)
{
if (v___y_3780_ == 0)
{
lean_object* v___x_3781_; 
lean_dec(v_socket_3760_);
v___x_3781_ = lean_box(0);
v___y_3774_ = v___x_3781_;
goto v___jp_3773_;
}
else
{
goto v___jp_3777_;
}
}
else
{
goto v___jp_3777_;
}
}
v___jp_3782_:
{
if (v___y_3783_ == 0)
{
v___y_3780_ = v___y_3784_;
goto v___jp_3779_;
}
else
{
v___y_3780_ = v___y_3783_;
goto v___jp_3779_;
}
}
v___jp_3785_:
{
if (v___y_3786_ == 0)
{
v___y_3783_ = v___y_3787_;
v___y_3784_ = v___y_3788_;
goto v___jp_3782_;
}
else
{
v___y_3783_ = v___y_3787_;
v___y_3784_ = v___y_3786_;
goto v___jp_3782_;
}
}
v___jp_3789_:
{
if (v_sentMessage_3762_ == 0)
{
lean_object* v_state_3792_; 
v_state_3792_ = lean_ctor_get(v_reader_3763_, 0);
if (lean_obj_tag(v_state_3792_) == 2)
{
v___y_3786_ = v___y_3791_;
v___y_3787_ = v___y_3790_;
v___y_3788_ = v_requestBodyInterested_3764_;
goto v___jp_3785_;
}
else
{
v___y_3786_ = v___y_3791_;
v___y_3787_ = v___y_3790_;
v___y_3788_ = v_sentMessage_3762_;
goto v___jp_3785_;
}
}
else
{
v___y_3786_ = v___y_3791_;
v___y_3787_ = v___y_3790_;
v___y_3788_ = v_sentMessage_3762_;
goto v___jp_3785_;
}
}
v___jp_3793_:
{
if (lean_obj_tag(v_respStream_3753_) == 0)
{
uint8_t v___x_3795_; 
v___x_3795_ = 0;
v___y_3790_ = v___y_3794_;
v___y_3791_ = v___x_3795_;
goto v___jp_3789_;
}
else
{
uint8_t v___x_3796_; 
v___x_3796_ = 1;
v___y_3790_ = v___y_3794_;
v___y_3791_ = v___x_3796_;
goto v___jp_3789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_expectData_3799_, lean_object* v_respStream_3800_, lean_object* v_currentTimeout_3801_, lean_object* v_keepAliveTimeout_3802_, lean_object* v_headerTimeout_3803_, lean_object* v_connectionContext_3804_, lean_object* v_handlerDispatched_3805_, lean_object* v_response_3806_, lean_object* v_socket_3807_, lean_object* v_requiresData_3808_, lean_object* v_sentMessage_3809_, lean_object* v_reader_3810_, lean_object* v_requestBodyInterested_3811_, lean_object* v_requestBody_3812_, lean_object* v___y_3813_){
_start:
{
uint8_t v_handlerDispatched_boxed_3814_; uint8_t v_requiresData_boxed_3815_; uint8_t v_sentMessage_boxed_3816_; uint8_t v_requestBodyInterested_boxed_3817_; lean_object* v_res_3818_; 
v_handlerDispatched_boxed_3814_ = lean_unbox(v_handlerDispatched_3805_);
v_requiresData_boxed_3815_ = lean_unbox(v_requiresData_3808_);
v_sentMessage_boxed_3816_ = lean_unbox(v_sentMessage_3809_);
v_requestBodyInterested_boxed_3817_ = lean_unbox(v_requestBodyInterested_3811_);
v_res_3818_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_expectData_3799_, v_respStream_3800_, v_currentTimeout_3801_, v_keepAliveTimeout_3802_, v_headerTimeout_3803_, v_connectionContext_3804_, v_handlerDispatched_boxed_3814_, v_response_3806_, v_socket_3807_, v_requiresData_boxed_3815_, v_sentMessage_boxed_3816_, v_reader_3810_, v_requestBodyInterested_boxed_3817_, v_requestBody_3812_);
lean_dec_ref(v_reader_3810_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3819_, lean_object* v_x_3820_){
_start:
{
if (lean_obj_tag(v_x_3820_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v___f_3819_);
v_a_3822_ = lean_ctor_get(v_x_3820_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_x_3820_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3824_ = v_x_3820_;
v_isShared_3825_ = v_isSharedCheck_3830_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v_x_3820_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3830_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
return v___x_3828_;
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3832_; 
v_a_3831_ = lean_ctor_get(v_x_3820_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v_x_3820_, 1);
v___x_3832_ = lean_apply_2(v___f_3819_, v_a_3831_, lean_box(0));
return v___x_3832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3833_, v_x_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_expectData_3841_, lean_object* v_respStream_3842_, lean_object* v_currentTimeout_3843_, lean_object* v_keepAliveTimeout_3844_, lean_object* v_headerTimeout_3845_, lean_object* v_connectionContext_3846_, uint8_t v_handlerDispatched_3847_, lean_object* v_response_3848_, lean_object* v_socket_3849_, uint8_t v_requiresData_3850_, uint8_t v_sentMessage_3851_, lean_object* v_reader_3852_, uint8_t v_pullBodyStalled_3853_, uint8_t v_requestBodyOpen_3854_, lean_object* v_requestStream_3855_, uint8_t v_requestBodyInterested_3856_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___f_3862_; lean_object* v___f_3863_; uint8_t v___y_3865_; 
v___x_3858_ = lean_box(v_handlerDispatched_3847_);
v___x_3859_ = lean_box(v_requiresData_3850_);
v___x_3860_ = lean_box(v_sentMessage_3851_);
v___x_3861_ = lean_box(v_requestBodyInterested_3856_);
lean_inc_ref(v_reader_3852_);
v___f_3862_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3862_, 0, v_expectData_3841_);
lean_closure_set(v___f_3862_, 1, v_respStream_3842_);
lean_closure_set(v___f_3862_, 2, v_currentTimeout_3843_);
lean_closure_set(v___f_3862_, 3, v_keepAliveTimeout_3844_);
lean_closure_set(v___f_3862_, 4, v_headerTimeout_3845_);
lean_closure_set(v___f_3862_, 5, v_connectionContext_3846_);
lean_closure_set(v___f_3862_, 6, v___x_3858_);
lean_closure_set(v___f_3862_, 7, v_response_3848_);
lean_closure_set(v___f_3862_, 8, v_socket_3849_);
lean_closure_set(v___f_3862_, 9, v___x_3859_);
lean_closure_set(v___f_3862_, 10, v___x_3860_);
lean_closure_set(v___f_3862_, 11, v_reader_3852_);
lean_closure_set(v___f_3862_, 12, v___x_3861_);
v___f_3863_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3863_, 0, v___f_3862_);
if (v_sentMessage_3851_ == 0)
{
lean_object* v_state_3869_; 
v_state_3869_ = lean_ctor_get(v_reader_3852_, 0);
lean_inc(v_state_3869_);
lean_dec_ref(v_reader_3852_);
if (lean_obj_tag(v_state_3869_) == 2)
{
lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3880_; 
v_isSharedCheck_3880_ = !lean_is_exclusive(v_state_3869_);
if (v_isSharedCheck_3880_ == 0)
{
lean_object* v_unused_3881_; 
v_unused_3881_ = lean_ctor_get(v_state_3869_, 0);
lean_dec(v_unused_3881_);
v___x_3871_ = v_state_3869_;
v_isShared_3872_ = v_isSharedCheck_3880_;
goto v_resetjp_3870_;
}
else
{
lean_dec(v_state_3869_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3880_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
if (v_pullBodyStalled_3853_ == 0)
{
if (v_requestBodyOpen_3854_ == 0)
{
lean_del_object(v___x_3871_);
lean_dec_ref(v_requestStream_3855_);
v___y_3865_ = v_requestBodyOpen_3854_;
goto v___jp_3864_;
}
else
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
lean_ctor_set_tag(v___x_3871_, 1);
lean_ctor_set(v___x_3871_, 0, v_requestStream_3855_);
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_requestStream_3855_);
v___x_3874_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3877_, v_pullBodyStalled_3853_, v___x_3876_, v___f_3863_);
return v___x_3878_;
}
}
}
else
{
lean_del_object(v___x_3871_);
lean_dec_ref(v_requestStream_3855_);
v___y_3865_ = v_sentMessage_3851_;
goto v___jp_3864_;
}
}
}
else
{
lean_dec(v_state_3869_);
lean_dec_ref(v_requestStream_3855_);
v___y_3865_ = v_sentMessage_3851_;
goto v___jp_3864_;
}
}
else
{
uint8_t v___x_3882_; 
lean_dec_ref(v_requestStream_3855_);
lean_dec_ref(v_reader_3852_);
v___x_3882_ = 0;
v___y_3865_ = v___x_3882_;
goto v___jp_3864_;
}
v___jp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3867_, v___y_3865_, v___x_3866_, v___f_3863_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_expectData_3883_ = _args[0];
lean_object* v_respStream_3884_ = _args[1];
lean_object* v_currentTimeout_3885_ = _args[2];
lean_object* v_keepAliveTimeout_3886_ = _args[3];
lean_object* v_headerTimeout_3887_ = _args[4];
lean_object* v_connectionContext_3888_ = _args[5];
lean_object* v_handlerDispatched_3889_ = _args[6];
lean_object* v_response_3890_ = _args[7];
lean_object* v_socket_3891_ = _args[8];
lean_object* v_requiresData_3892_ = _args[9];
lean_object* v_sentMessage_3893_ = _args[10];
lean_object* v_reader_3894_ = _args[11];
lean_object* v_pullBodyStalled_3895_ = _args[12];
lean_object* v_requestBodyOpen_3896_ = _args[13];
lean_object* v_requestStream_3897_ = _args[14];
lean_object* v_requestBodyInterested_3898_ = _args[15];
lean_object* v___y_3899_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3900_; uint8_t v_requiresData_boxed_3901_; uint8_t v_sentMessage_boxed_3902_; uint8_t v_pullBodyStalled_boxed_3903_; uint8_t v_requestBodyOpen_boxed_3904_; uint8_t v_requestBodyInterested_boxed_3905_; lean_object* v_res_3906_; 
v_handlerDispatched_boxed_3900_ = lean_unbox(v_handlerDispatched_3889_);
v_requiresData_boxed_3901_ = lean_unbox(v_requiresData_3892_);
v_sentMessage_boxed_3902_ = lean_unbox(v_sentMessage_3893_);
v_pullBodyStalled_boxed_3903_ = lean_unbox(v_pullBodyStalled_3895_);
v_requestBodyOpen_boxed_3904_ = lean_unbox(v_requestBodyOpen_3896_);
v_requestBodyInterested_boxed_3905_ = lean_unbox(v_requestBodyInterested_3898_);
v_res_3906_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_expectData_3883_, v_respStream_3884_, v_currentTimeout_3885_, v_keepAliveTimeout_3886_, v_headerTimeout_3887_, v_connectionContext_3888_, v_handlerDispatched_boxed_3900_, v_response_3890_, v_socket_3891_, v_requiresData_boxed_3901_, v_sentMessage_boxed_3902_, v_reader_3894_, v_pullBodyStalled_boxed_3903_, v_requestBodyOpen_boxed_3904_, v_requestStream_3897_, v_requestBodyInterested_boxed_3905_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3907_, lean_object* v_x_3908_){
_start:
{
if (lean_obj_tag(v_x_3908_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3918_; 
lean_dec_ref(v___f_3907_);
v_a_3910_ = lean_ctor_get(v_x_3908_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_x_3908_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3912_ = v_x_3908_;
v_isShared_3913_ = v_isSharedCheck_3918_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v_x_3908_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3918_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3920_; 
v_a_3919_ = lean_ctor_get(v_x_3908_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v_x_3908_, 1);
v___x_3920_ = lean_apply_2(v___f_3907_, v_a_3919_, lean_box(0));
return v___x_3920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3921_, lean_object* v_x_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3921_, v_x_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_expectData_3925_, lean_object* v_respStream_3926_, lean_object* v_currentTimeout_3927_, lean_object* v_keepAliveTimeout_3928_, lean_object* v_headerTimeout_3929_, lean_object* v_connectionContext_3930_, uint8_t v_handlerDispatched_3931_, lean_object* v_response_3932_, lean_object* v_socket_3933_, uint8_t v_requiresData_3934_, uint8_t v_sentMessage_3935_, lean_object* v_reader_3936_, uint8_t v_pullBodyStalled_3937_, lean_object* v_requestStream_3938_, uint8_t v_requestBodyOpen_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___f_3946_; lean_object* v___f_3947_; uint8_t v___y_3949_; 
v___x_3941_ = lean_box(v_handlerDispatched_3931_);
v___x_3942_ = lean_box(v_requiresData_3934_);
v___x_3943_ = lean_box(v_sentMessage_3935_);
v___x_3944_ = lean_box(v_pullBodyStalled_3937_);
v___x_3945_ = lean_box(v_requestBodyOpen_3939_);
lean_inc_ref(v_requestStream_3938_);
lean_inc_ref(v_reader_3936_);
v___f_3946_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3946_, 0, v_expectData_3925_);
lean_closure_set(v___f_3946_, 1, v_respStream_3926_);
lean_closure_set(v___f_3946_, 2, v_currentTimeout_3927_);
lean_closure_set(v___f_3946_, 3, v_keepAliveTimeout_3928_);
lean_closure_set(v___f_3946_, 4, v_headerTimeout_3929_);
lean_closure_set(v___f_3946_, 5, v_connectionContext_3930_);
lean_closure_set(v___f_3946_, 6, v___x_3941_);
lean_closure_set(v___f_3946_, 7, v_response_3932_);
lean_closure_set(v___f_3946_, 8, v_socket_3933_);
lean_closure_set(v___f_3946_, 9, v___x_3942_);
lean_closure_set(v___f_3946_, 10, v___x_3943_);
lean_closure_set(v___f_3946_, 11, v_reader_3936_);
lean_closure_set(v___f_3946_, 12, v___x_3944_);
lean_closure_set(v___f_3946_, 13, v___x_3945_);
lean_closure_set(v___f_3946_, 14, v_requestStream_3938_);
v___f_3947_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3947_, 0, v___f_3946_);
if (v_sentMessage_3935_ == 0)
{
lean_object* v_state_3955_; 
v_state_3955_ = lean_ctor_get(v_reader_3936_, 0);
lean_inc(v_state_3955_);
lean_dec_ref(v_reader_3936_);
if (lean_obj_tag(v_state_3955_) == 2)
{
lean_dec_ref_known(v_state_3955_, 1);
if (v_requestBodyOpen_3939_ == 0)
{
lean_dec_ref(v_requestStream_3938_);
v___y_3949_ = v_requestBodyOpen_3939_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3938_);
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_3958_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3957_, v_sentMessage_3935_, v___x_3956_, v___f_3947_);
return v___x_3958_;
}
}
else
{
lean_dec(v_state_3955_);
lean_dec_ref(v_requestStream_3938_);
v___y_3949_ = v_sentMessage_3935_;
goto v___jp_3948_;
}
}
else
{
uint8_t v___x_3959_; 
lean_dec_ref(v_requestStream_3938_);
lean_dec_ref(v_reader_3936_);
v___x_3959_ = 0;
v___y_3949_ = v___x_3959_;
goto v___jp_3948_;
}
v___jp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3950_ = lean_box(v___y_3949_);
v___x_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
v___x_3953_ = lean_unsigned_to_nat(0u);
v___x_3954_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3953_, v___y_3949_, v___x_3952_, v___f_3947_);
return v___x_3954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_expectData_3960_, lean_object* v_respStream_3961_, lean_object* v_currentTimeout_3962_, lean_object* v_keepAliveTimeout_3963_, lean_object* v_headerTimeout_3964_, lean_object* v_connectionContext_3965_, lean_object* v_handlerDispatched_3966_, lean_object* v_response_3967_, lean_object* v_socket_3968_, lean_object* v_requiresData_3969_, lean_object* v_sentMessage_3970_, lean_object* v_reader_3971_, lean_object* v_pullBodyStalled_3972_, lean_object* v_requestStream_3973_, lean_object* v_requestBodyOpen_3974_, lean_object* v___y_3975_){
_start:
{
uint8_t v_handlerDispatched_boxed_3976_; uint8_t v_requiresData_boxed_3977_; uint8_t v_sentMessage_boxed_3978_; uint8_t v_pullBodyStalled_boxed_3979_; uint8_t v_requestBodyOpen_boxed_3980_; lean_object* v_res_3981_; 
v_handlerDispatched_boxed_3976_ = lean_unbox(v_handlerDispatched_3966_);
v_requiresData_boxed_3977_ = lean_unbox(v_requiresData_3969_);
v_sentMessage_boxed_3978_ = lean_unbox(v_sentMessage_3970_);
v_pullBodyStalled_boxed_3979_ = lean_unbox(v_pullBodyStalled_3972_);
v_requestBodyOpen_boxed_3980_ = lean_unbox(v_requestBodyOpen_3974_);
v_res_3981_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_expectData_3960_, v_respStream_3961_, v_currentTimeout_3962_, v_keepAliveTimeout_3963_, v_headerTimeout_3964_, v_connectionContext_3965_, v_handlerDispatched_boxed_3976_, v_response_3967_, v_socket_3968_, v_requiresData_boxed_3977_, v_sentMessage_boxed_3978_, v_reader_3971_, v_pullBodyStalled_boxed_3979_, v_requestStream_3973_, v_requestBodyOpen_boxed_3980_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3982_, lean_object* v___f_3983_, uint8_t v___x_3984_, lean_object* v_x_3985_){
_start:
{
uint8_t v___y_3988_; 
if (lean_obj_tag(v_x_3985_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4002_; 
lean_dec_ref(v___f_3983_);
v_a_3994_ = lean_ctor_get(v_x_3985_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_x_3985_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3996_ = v_x_3985_;
v_isShared_3997_ = v_isSharedCheck_4002_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v_x_3985_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4002_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
}
else
{
lean_object* v_a_4003_; uint8_t v___x_4004_; 
v_a_4003_ = lean_ctor_get(v_x_3985_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v_x_3985_, 1);
v___x_4004_ = lean_unbox(v_a_4003_);
lean_dec(v_a_4003_);
if (v___x_4004_ == 0)
{
v___y_3988_ = v___x_3984_;
goto v___jp_3987_;
}
else
{
v___y_3988_ = v_sentMessage_3982_;
goto v___jp_3987_;
}
}
v___jp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3989_ = lean_box(v___y_3988_);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
v___x_3992_ = lean_unsigned_to_nat(0u);
v___x_3993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3992_, v_sentMessage_3982_, v___x_3991_, v___f_3983_);
return v___x_3993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4005_, lean_object* v___f_4006_, lean_object* v___x_4007_, lean_object* v_x_4008_, lean_object* v___y_4009_){
_start:
{
uint8_t v_sentMessage_boxed_4010_; uint8_t v___x_2561__boxed_4011_; lean_object* v_res_4012_; 
v_sentMessage_boxed_4010_ = lean_unbox(v_sentMessage_4005_);
v___x_2561__boxed_4011_ = lean_unbox(v___x_4007_);
v_res_4012_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4010_, v___f_4006_, v___x_2561__boxed_4011_, v_x_4008_);
return v_res_4012_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___f_4013_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4014_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4015_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4016_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4016_, 0, lean_box(0));
lean_closure_set(v___x_4016_, 1, lean_box(0));
lean_closure_set(v___x_4016_, 2, v___x_4015_);
lean_closure_set(v___x_4016_, 3, lean_box(0));
lean_closure_set(v___x_4016_, 4, lean_box(0));
lean_closure_set(v___x_4016_, 5, v___x_4014_);
lean_closure_set(v___x_4016_, 6, v___f_4013_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4017_, lean_object* v_connectionContext_4018_, lean_object* v_state_4019_){
_start:
{
lean_object* v_machine_4021_; lean_object* v_writer_4022_; lean_object* v_requestStream_4023_; lean_object* v_keepAliveTimeout_4024_; lean_object* v_currentTimeout_4025_; lean_object* v_headerTimeout_4026_; lean_object* v_response_4027_; lean_object* v_respStream_4028_; uint8_t v_requiresData_4029_; lean_object* v_expectData_4030_; uint8_t v_handlerDispatched_4031_; lean_object* v_reader_4032_; uint8_t v_pullBodyStalled_4033_; uint8_t v_sentMessage_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___f_4039_; lean_object* v___f_4040_; uint8_t v___y_4042_; 
v_machine_4021_ = lean_ctor_get(v_state_4019_, 0);
lean_inc_ref(v_machine_4021_);
v_writer_4022_ = lean_ctor_get(v_machine_4021_, 1);
lean_inc_ref(v_writer_4022_);
v_requestStream_4023_ = lean_ctor_get(v_state_4019_, 1);
lean_inc_ref_n(v_requestStream_4023_, 2);
v_keepAliveTimeout_4024_ = lean_ctor_get(v_state_4019_, 2);
lean_inc(v_keepAliveTimeout_4024_);
v_currentTimeout_4025_ = lean_ctor_get(v_state_4019_, 3);
lean_inc(v_currentTimeout_4025_);
v_headerTimeout_4026_ = lean_ctor_get(v_state_4019_, 4);
lean_inc(v_headerTimeout_4026_);
v_response_4027_ = lean_ctor_get(v_state_4019_, 5);
lean_inc_ref(v_response_4027_);
v_respStream_4028_ = lean_ctor_get(v_state_4019_, 6);
lean_inc(v_respStream_4028_);
v_requiresData_4029_ = lean_ctor_get_uint8(v_state_4019_, sizeof(void*)*9);
v_expectData_4030_ = lean_ctor_get(v_state_4019_, 7);
lean_inc(v_expectData_4030_);
v_handlerDispatched_4031_ = lean_ctor_get_uint8(v_state_4019_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4019_);
v_reader_4032_ = lean_ctor_get(v_machine_4021_, 0);
lean_inc_ref_n(v_reader_4032_, 2);
v_pullBodyStalled_4033_ = lean_ctor_get_uint8(v_machine_4021_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4021_);
v_sentMessage_4034_ = lean_ctor_get_uint8(v_writer_4022_, sizeof(void*)*6);
lean_dec_ref(v_writer_4022_);
v___x_4035_ = lean_box(v_handlerDispatched_4031_);
v___x_4036_ = lean_box(v_requiresData_4029_);
v___x_4037_ = lean_box(v_sentMessage_4034_);
v___x_4038_ = lean_box(v_pullBodyStalled_4033_);
v___f_4039_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4039_, 0, v_expectData_4030_);
lean_closure_set(v___f_4039_, 1, v_respStream_4028_);
lean_closure_set(v___f_4039_, 2, v_currentTimeout_4025_);
lean_closure_set(v___f_4039_, 3, v_keepAliveTimeout_4024_);
lean_closure_set(v___f_4039_, 4, v_headerTimeout_4026_);
lean_closure_set(v___f_4039_, 5, v_connectionContext_4018_);
lean_closure_set(v___f_4039_, 6, v___x_4035_);
lean_closure_set(v___f_4039_, 7, v_response_4027_);
lean_closure_set(v___f_4039_, 8, v_socket_4017_);
lean_closure_set(v___f_4039_, 9, v___x_4036_);
lean_closure_set(v___f_4039_, 10, v___x_4037_);
lean_closure_set(v___f_4039_, 11, v_reader_4032_);
lean_closure_set(v___f_4039_, 12, v___x_4038_);
lean_closure_set(v___f_4039_, 13, v_requestStream_4023_);
v___f_4040_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4040_, 0, v___f_4039_);
if (v_sentMessage_4034_ == 0)
{
lean_object* v_state_4048_; 
v_state_4048_ = lean_ctor_get(v_reader_4032_, 0);
lean_inc(v_state_4048_);
lean_dec_ref(v_reader_4032_);
if (lean_obj_tag(v_state_4048_) == 2)
{
lean_object* v___x_4049_; lean_object* v___f_4050_; lean_object* v___f_4051_; lean_object* v___x_4052_; lean_object* v___x_2027__overap_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___f_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_dec_ref_known(v_state_4048_, 1);
v___x_4049_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4050_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4051_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4052_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2027__overap_4053_ = l_Std_Mutex_atomically___redArg(v___x_4049_, v___f_4050_, v___f_4051_, v_requestStream_4023_, v___x_4052_);
v___x_4054_ = lean_apply_1(v___x_2027__overap_4053_, lean_box(0));
v___x_4055_ = 1;
v___x_4056_ = lean_box(v_sentMessage_4034_);
v___x_4057_ = lean_box(v___x_4055_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4058_, 0, v___x_4056_);
lean_closure_set(v___f_4058_, 1, v___f_4040_);
lean_closure_set(v___f_4058_, 2, v___x_4057_);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4059_, v_sentMessage_4034_, v___x_4054_, v___f_4058_);
return v___x_4060_;
}
else
{
lean_dec(v_state_4048_);
lean_dec_ref(v_requestStream_4023_);
v___y_4042_ = v_sentMessage_4034_;
goto v___jp_4041_;
}
}
else
{
uint8_t v___x_4061_; 
lean_dec_ref(v_reader_4032_);
lean_dec_ref(v_requestStream_4023_);
v___x_4061_ = 0;
v___y_4042_ = v___x_4061_;
goto v___jp_4041_;
}
v___jp_4041_:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4043_ = lean_box(v___y_4042_);
v___x_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
v___x_4046_ = lean_unsigned_to_nat(0u);
v___x_4047_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4046_, v___y_4042_, v___x_4045_, v___f_4040_);
return v___x_4047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4062_, lean_object* v_connectionContext_4063_, lean_object* v_state_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4062_, v_connectionContext_4063_, v_state_4064_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4067_, lean_object* v_00_u03b2_4068_, lean_object* v_inst_4069_, lean_object* v_socket_4070_, lean_object* v_connectionContext_4071_, lean_object* v_state_4072_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4070_, v_connectionContext_4071_, v_state_4072_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4075_, lean_object* v_00_u03b2_4076_, lean_object* v_inst_4077_, lean_object* v_socket_4078_, lean_object* v_connectionContext_4079_, lean_object* v_state_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4075_, v_00_u03b2_4076_, v_inst_4077_, v_socket_4078_, v_connectionContext_4079_, v_state_4080_);
lean_dec_ref(v_inst_4077_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4087_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4097_; 
v_a_4089_ = lean_ctor_get(v_x_4087_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4091_ = v_x_4087_;
v_isShared_4092_ = v_isSharedCheck_4097_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v_x_4087_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4097_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
}
}
else
{
lean_object* v___x_4098_; 
lean_dec_ref_known(v_x_4087_, 1);
v___x_4098_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__1));
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4099_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_onFailure_4102_, lean_object* v_handler_4103_, lean_object* v___f_4104_, lean_object* v_x_4105_){
_start:
{
if (lean_obj_tag(v_x_4105_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; lean_object* v___x_4111_; 
v_a_4107_ = lean_ctor_get(v_x_4105_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v_x_4105_, 1);
v___x_4108_ = lean_apply_3(v_onFailure_4102_, v_handler_4103_, v_a_4107_, lean_box(0));
v___x_4109_ = lean_unsigned_to_nat(0u);
v___x_4110_ = 0;
v___x_4111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4109_, v___x_4110_, v___x_4108_, v___f_4104_);
return v___x_4111_;
}
else
{
lean_object* v___x_4112_; 
lean_dec_ref(v___f_4104_);
lean_dec(v_handler_4103_);
lean_dec_ref(v_onFailure_4102_);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_x_4105_);
return v___x_4112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_onFailure_4113_, lean_object* v_handler_4114_, lean_object* v___f_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_onFailure_4113_, v_handler_4114_, v___f_4115_, v_x_4116_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4119_){
_start:
{
if (lean_obj_tag(v_x_4119_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4129_; 
v_a_4121_ = lean_ctor_get(v_x_4119_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_x_4119_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4123_ = v_x_4119_;
v_isShared_4124_ = v_isSharedCheck_4129_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v_x_4119_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4129_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; 
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
return v___x_4127_;
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4139_; 
v_a_4130_ = lean_ctor_get(v_x_4119_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_x_4119_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4132_ = v_x_4119_;
v_isShared_4133_ = v_isSharedCheck_4139_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v_x_4119_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4139_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_a_4130_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 0, v___x_4134_);
v___x_4136_ = v___x_4132_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; 
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
return v___x_4137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4143_){
_start:
{
if (lean_obj_tag(v_x_4143_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4153_; 
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
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4172_; 
v_a_4154_ = lean_ctor_get(v_x_4143_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v_x_4143_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4156_ = v_x_4143_;
v_isShared_4157_ = v_isSharedCheck_4172_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v_x_4143_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4172_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v_snd_4158_; uint8_t v___x_4159_; 
v_snd_4158_ = lean_ctor_get(v_a_4154_, 1);
v___x_4159_ = lean_unbox(v_snd_4158_);
if (v___x_4159_ == 0)
{
lean_object* v_fst_4160_; lean_object* v___x_4161_; lean_object* v___x_4163_; 
v_fst_4160_ = lean_ctor_get(v_a_4154_, 0);
lean_inc(v_fst_4160_);
lean_dec(v_a_4154_);
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_fst_4160_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4161_);
v___x_4163_ = v___x_4156_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
else
{
lean_object* v_fst_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v_fst_4166_ = lean_ctor_get(v_a_4154_, 0);
lean_inc(v_fst_4166_);
lean_dec(v_a_4154_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v_fst_4166_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4167_);
v___x_4169_ = v___x_4156_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; 
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4173_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4176_, lean_object* v_socket_4177_, lean_object* v_____r_4178_){
_start:
{
lean_object* v_val_4181_; lean_object* v_close_4183_; lean_object* v___x_4184_; 
v_close_4183_ = lean_ctor_get(v_inst_4176_, 3);
lean_inc_ref(v_close_4183_);
lean_dec_ref(v_inst_4176_);
v___x_4184_ = lean_apply_2(v_close_4183_, v_socket_4177_, lean_box(0));
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4184_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4184_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set_tag(v___x_4187_, 1);
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
v_val_4181_ = v___x_4190_;
goto v___jp_4180_;
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4193_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4184_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4184_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 0);
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
v_val_4181_ = v___x_4198_;
goto v___jp_4180_;
}
}
}
v___jp_4180_:
{
lean_object* v___x_4182_; 
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v_val_4181_);
return v___x_4182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4201_, lean_object* v_socket_4202_, lean_object* v_____r_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4201_, v_socket_4202_, v_____r_4203_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4206_, lean_object* v_x_4207_){
_start:
{
if (lean_obj_tag(v_x_4207_) == 0)
{
lean_object* v___x_4209_; 
lean_dec_ref(v___f_4206_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_x_4207_);
return v___x_4209_;
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4211_; 
v_a_4210_ = lean_ctor_get(v_x_4207_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v_x_4207_, 1);
v___x_4211_ = lean_apply_2(v___f_4206_, v_a_4210_, lean_box(0));
return v___x_4211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4212_, lean_object* v_x_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4212_, v_x_4213_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4216_, lean_object* v_val_4217_, lean_object* v___f_4218_, lean_object* v___f_4219_, lean_object* v_x_4220_){
_start:
{
if (lean_obj_tag(v_x_4220_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4230_; 
lean_dec_ref(v___f_4219_);
lean_dec_ref(v___f_4218_);
lean_dec(v_val_4217_);
lean_dec_ref(v_close_4216_);
v_a_4222_ = lean_ctor_get(v_x_4220_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_x_4220_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4224_ = v_x_4220_;
v_isShared_4225_ = v_isSharedCheck_4230_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v_x_4220_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4230_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
}
}
else
{
lean_object* v_a_4231_; uint8_t v___x_4232_; 
v_a_4231_ = lean_ctor_get(v_x_4220_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v_x_4220_, 1);
v___x_4232_ = lean_unbox(v_a_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; 
lean_dec_ref(v___f_4219_);
v___x_4233_ = lean_apply_2(v_close_4216_, v_val_4217_, lean_box(0));
v___x_4234_ = lean_unsigned_to_nat(0u);
v___x_4235_ = lean_unbox(v_a_4231_);
lean_dec(v_a_4231_);
v___x_4236_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4234_, v___x_4235_, v___x_4233_, v___f_4218_);
return v___x_4236_;
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_dec(v_a_4231_);
lean_dec_ref(v___f_4218_);
lean_dec(v_val_4217_);
lean_dec_ref(v_close_4216_);
v___x_4237_ = lean_box(0);
v___x_4238_ = lean_apply_2(v___f_4219_, v___x_4237_, lean_box(0));
return v___x_4238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4239_, lean_object* v_val_4240_, lean_object* v___f_4241_, lean_object* v___f_4242_, lean_object* v_x_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4239_, v_val_4240_, v___f_4241_, v___f_4242_, v_x_4243_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4246_, lean_object* v_responseBodyInstance_4247_, lean_object* v___f_4248_, lean_object* v___f_4249_, lean_object* v_____r_4250_){
_start:
{
if (lean_obj_tag(v_respStream_4246_) == 1)
{
lean_object* v_val_4252_; lean_object* v_close_4253_; lean_object* v_isClosed_4254_; lean_object* v___x_4255_; lean_object* v___f_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; lean_object* v___x_4259_; 
v_val_4252_ = lean_ctor_get(v_respStream_4246_, 0);
lean_inc_n(v_val_4252_, 2);
lean_dec_ref_known(v_respStream_4246_, 1);
v_close_4253_ = lean_ctor_get(v_responseBodyInstance_4247_, 1);
lean_inc_ref(v_close_4253_);
v_isClosed_4254_ = lean_ctor_get(v_responseBodyInstance_4247_, 2);
lean_inc_ref(v_isClosed_4254_);
lean_dec_ref(v_responseBodyInstance_4247_);
v___x_4255_ = lean_apply_2(v_isClosed_4254_, v_val_4252_, lean_box(0));
v___f_4256_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4256_, 0, v_close_4253_);
lean_closure_set(v___f_4256_, 1, v_val_4252_);
lean_closure_set(v___f_4256_, 2, v___f_4248_);
lean_closure_set(v___f_4256_, 3, v___f_4249_);
v___x_4257_ = lean_unsigned_to_nat(0u);
v___x_4258_ = 0;
v___x_4259_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4257_, v___x_4258_, v___x_4255_, v___f_4256_);
return v___x_4259_;
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_dec_ref(v___f_4248_);
lean_dec_ref(v_responseBodyInstance_4247_);
lean_dec(v_respStream_4246_);
v___x_4260_ = lean_box(0);
v___x_4261_ = lean_apply_2(v___f_4249_, v___x_4260_, lean_box(0));
return v___x_4261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4262_, lean_object* v_responseBodyInstance_4263_, lean_object* v___f_4264_, lean_object* v___f_4265_, lean_object* v_____r_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4262_, v_responseBodyInstance_4263_, v___f_4264_, v___f_4265_, v_____r_4266_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4269_, lean_object* v___f_4270_, lean_object* v___f_4271_, lean_object* v_x_4272_){
_start:
{
if (lean_obj_tag(v_x_4272_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4282_; 
lean_dec_ref(v___f_4271_);
lean_dec_ref(v___f_4270_);
lean_dec_ref(v_requestStream_4269_);
v_a_4274_ = lean_ctor_get(v_x_4272_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_x_4272_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4276_ = v_x_4272_;
v_isShared_4277_ = v_isSharedCheck_4282_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v_x_4272_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4282_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4274_);
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
}
else
{
lean_object* v_a_4283_; uint8_t v___x_4284_; 
v_a_4283_ = lean_ctor_get(v_x_4272_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v_x_4272_, 1);
v___x_4284_ = lean_unbox(v_a_4283_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; 
lean_dec_ref(v___f_4271_);
v___x_4285_ = l_Std_Http_Body_Stream_close(v_requestStream_4269_);
v___x_4286_ = lean_unsigned_to_nat(0u);
v___x_4287_ = lean_unbox(v_a_4283_);
lean_dec(v_a_4283_);
v___x_4288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4286_, v___x_4287_, v___x_4285_, v___f_4270_);
return v___x_4288_;
}
else
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
lean_dec(v_a_4283_);
lean_dec_ref(v___f_4270_);
lean_dec_ref(v_requestStream_4269_);
v___x_4289_ = lean_box(0);
v___x_4290_ = lean_apply_2(v___f_4271_, v___x_4289_, lean_box(0));
return v___x_4290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4291_, lean_object* v___f_4292_, lean_object* v___f_4293_, lean_object* v_x_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4291_, v___f_4292_, v___f_4293_, v_x_4294_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4297_, lean_object* v_responseBodyInstance_4298_, lean_object* v___f_4299_, lean_object* v___f_4300_, lean_object* v_x_4301_){
_start:
{
if (lean_obj_tag(v_x_4301_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v___f_4300_);
lean_dec_ref(v___f_4299_);
lean_dec_ref(v_responseBodyInstance_4298_);
lean_dec_ref(v___f_4297_);
v_a_4303_ = lean_ctor_get(v_x_4301_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v_x_4301_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4305_ = v_x_4301_;
v_isShared_4306_ = v_isSharedCheck_4311_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v_x_4301_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4311_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
return v___x_4309_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v_requestStream_4313_; lean_object* v_respStream_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___f_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4409__overap_4320_; lean_object* v___x_4321_; lean_object* v___f_4322_; lean_object* v___f_4323_; lean_object* v___f_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; lean_object* v___x_4327_; 
v_a_4312_ = lean_ctor_get(v_x_4301_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v_x_4301_, 1);
v_requestStream_4313_ = lean_ctor_get(v_a_4312_, 1);
lean_inc_ref_n(v_requestStream_4313_, 2);
v_respStream_4314_ = lean_ctor_get(v_a_4312_, 6);
lean_inc(v_respStream_4314_);
lean_dec(v_a_4312_);
v___x_4315_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4316_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4317_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4318_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4319_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4319_, 0, lean_box(0));
lean_closure_set(v___x_4319_, 1, lean_box(0));
lean_closure_set(v___x_4319_, 2, v___x_4315_);
lean_closure_set(v___x_4319_, 3, lean_box(0));
lean_closure_set(v___x_4319_, 4, lean_box(0));
lean_closure_set(v___x_4319_, 5, v___x_4318_);
lean_closure_set(v___x_4319_, 6, v___f_4297_);
v___x_4409__overap_4320_ = l_Std_Mutex_atomically___redArg(v___x_4315_, v___f_4316_, v___f_4317_, v_requestStream_4313_, v___x_4319_);
v___x_4321_ = lean_apply_1(v___x_4409__overap_4320_, lean_box(0));
v___f_4322_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4322_, 0, v_respStream_4314_);
lean_closure_set(v___f_4322_, 1, v_responseBodyInstance_4298_);
lean_closure_set(v___f_4322_, 2, v___f_4299_);
lean_closure_set(v___f_4322_, 3, v___f_4300_);
lean_inc_ref(v___f_4322_);
v___f_4323_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4323_, 0, v___f_4322_);
v___f_4324_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4324_, 0, v_requestStream_4313_);
lean_closure_set(v___f_4324_, 1, v___f_4323_);
lean_closure_set(v___f_4324_, 2, v___f_4322_);
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = 0;
v___x_4327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4325_, v___x_4326_, v___x_4321_, v___f_4324_);
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4328_, lean_object* v_responseBodyInstance_4329_, lean_object* v___f_4330_, lean_object* v___f_4331_, lean_object* v_x_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4328_, v_responseBodyInstance_4329_, v___f_4330_, v___f_4331_, v_x_4332_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4335_, lean_object* v_responseBodyInstance_4336_, lean_object* v_handler_4337_, lean_object* v_config_4338_, lean_object* v___x_4339_, uint8_t v___x_4340_, lean_object* v___f_4341_, lean_object* v_x_4342_){
_start:
{
if (lean_obj_tag(v_x_4342_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4352_; 
lean_dec_ref(v___f_4341_);
lean_dec_ref(v___x_4339_);
lean_dec_ref(v_config_4338_);
lean_dec(v_handler_4337_);
lean_dec_ref(v_responseBodyInstance_4336_);
lean_dec_ref(v_h_4335_);
v_a_4344_ = lean_ctor_get(v_x_4342_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_x_4342_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4346_ = v_x_4342_;
v_isShared_4347_ = v_isSharedCheck_4352_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v_x_4342_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4352_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
return v___x_4350_;
}
}
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_a_4353_ = lean_ctor_get(v_x_4342_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v_x_4342_, 1);
v___x_4354_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4335_, v_responseBodyInstance_4336_, v_handler_4337_, v_config_4338_, v_a_4353_, v___x_4339_);
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4355_, v___x_4340_, v___x_4354_, v___f_4341_);
return v___x_4356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4357_, lean_object* v_responseBodyInstance_4358_, lean_object* v_handler_4359_, lean_object* v_config_4360_, lean_object* v___x_4361_, lean_object* v___x_4362_, lean_object* v___f_4363_, lean_object* v_x_4364_, lean_object* v___y_4365_){
_start:
{
uint8_t v___x_5090__boxed_4366_; lean_object* v_res_4367_; 
v___x_5090__boxed_4366_ = lean_unbox(v___x_4362_);
v_res_4367_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4357_, v_responseBodyInstance_4358_, v_handler_4359_, v_config_4360_, v___x_4361_, v___x_5090__boxed_4366_, v___f_4363_, v_x_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4368_, lean_object* v_h_4369_, lean_object* v_responseBodyInstance_4370_, lean_object* v_config_4371_, lean_object* v_handler_4372_, uint8_t v___x_4373_, lean_object* v___f_4374_, lean_object* v_x_4375_){
_start:
{
if (lean_obj_tag(v_x_4375_) == 0)
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4385_; 
lean_dec_ref(v___f_4374_);
lean_dec(v_handler_4372_);
lean_dec_ref(v_config_4371_);
lean_dec_ref(v_responseBodyInstance_4370_);
lean_dec_ref(v_h_4369_);
lean_dec_ref(v_inst_4368_);
v_a_4377_ = lean_ctor_get(v_x_4375_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v_x_4375_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4379_ = v_x_4375_;
v_isShared_4380_ = v_isSharedCheck_4385_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v_x_4375_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4385_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; 
v___x_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
return v___x_4383_;
}
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v_a_4386_ = lean_ctor_get(v_x_4375_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v_x_4375_, 1);
v___x_4387_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4368_, v_h_4369_, v_responseBodyInstance_4370_, v_config_4371_, v_handler_4372_, v_a_4386_);
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4388_, v___x_4373_, v___x_4387_, v___f_4374_);
return v___x_4389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4390_, lean_object* v_h_4391_, lean_object* v_responseBodyInstance_4392_, lean_object* v_config_4393_, lean_object* v_handler_4394_, lean_object* v___x_4395_, lean_object* v___f_4396_, lean_object* v_x_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v___x_5131__boxed_4399_; lean_object* v_res_4400_; 
v___x_5131__boxed_4399_ = lean_unbox(v___x_4395_);
v_res_4400_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4390_, v_h_4391_, v_responseBodyInstance_4392_, v_config_4393_, v_handler_4394_, v___x_5131__boxed_4399_, v___f_4396_, v_x_4397_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4401_, lean_object* v_socket_4402_, lean_object* v_connectionContext_4403_, lean_object* v_h_4404_, lean_object* v_responseBodyInstance_4405_, lean_object* v_handler_4406_, lean_object* v_config_4407_, lean_object* v___f_4408_, lean_object* v_inst_4409_, uint8_t v___x_4410_, lean_object* v_x_4411_){
_start:
{
if (lean_obj_tag(v_x_4411_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4421_; 
lean_dec_ref(v_inst_4409_);
lean_dec_ref(v___f_4408_);
lean_dec_ref(v_config_4407_);
lean_dec(v_handler_4406_);
lean_dec_ref(v_responseBodyInstance_4405_);
lean_dec_ref(v_h_4404_);
lean_dec_ref(v_connectionContext_4403_);
lean_dec(v_socket_4402_);
v_a_4413_ = lean_ctor_get(v_x_4411_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_x_4411_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4415_ = v_x_4411_;
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v_x_4411_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
return v___x_4419_;
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4464_; 
v_a_4422_ = lean_ctor_get(v_x_4411_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_x_4411_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4424_ = v_x_4411_;
v_isShared_4425_ = v_isSharedCheck_4464_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v_x_4411_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4464_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v_machine_4426_; lean_object* v_requestStream_4427_; lean_object* v_keepAliveTimeout_4428_; lean_object* v_currentTimeout_4429_; lean_object* v_headerTimeout_4430_; lean_object* v_response_4431_; lean_object* v_respStream_4432_; uint8_t v_requiresData_4433_; lean_object* v_expectData_4434_; uint8_t v_handlerDispatched_4435_; lean_object* v_pendingHead_4436_; uint8_t v___y_4447_; uint8_t v___y_4454_; uint8_t v___y_4456_; uint8_t v___y_4457_; uint8_t v___y_4459_; 
v_machine_4426_ = lean_ctor_get(v_a_4422_, 0);
v_requestStream_4427_ = lean_ctor_get(v_a_4422_, 1);
v_keepAliveTimeout_4428_ = lean_ctor_get(v_a_4422_, 2);
v_currentTimeout_4429_ = lean_ctor_get(v_a_4422_, 3);
v_headerTimeout_4430_ = lean_ctor_get(v_a_4422_, 4);
v_response_4431_ = lean_ctor_get(v_a_4422_, 5);
v_respStream_4432_ = lean_ctor_get(v_a_4422_, 6);
v_requiresData_4433_ = lean_ctor_get_uint8(v_a_4422_, sizeof(void*)*9);
v_expectData_4434_ = lean_ctor_get(v_a_4422_, 7);
v_handlerDispatched_4435_ = lean_ctor_get_uint8(v_a_4422_, sizeof(void*)*9 + 1);
v_pendingHead_4436_ = lean_ctor_get(v_a_4422_, 8);
if (lean_obj_tag(v_respStream_4432_) == 0)
{
v___y_4459_ = v___x_4401_;
goto v___jp_4458_;
}
else
{
v___y_4459_ = v___x_4410_;
goto v___jp_4458_;
}
v___jp_4437_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___f_4441_; lean_object* v___x_4442_; lean_object* v___f_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4438_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4438_, 0, v_machine_4426_);
lean_ctor_set(v___x_4438_, 1, v_requestStream_4427_);
lean_ctor_set(v___x_4438_, 2, v_keepAliveTimeout_4428_);
lean_ctor_set(v___x_4438_, 3, v_currentTimeout_4429_);
lean_ctor_set(v___x_4438_, 4, v_headerTimeout_4430_);
lean_ctor_set(v___x_4438_, 5, v_response_4431_);
lean_ctor_set(v___x_4438_, 6, v_respStream_4432_);
lean_ctor_set(v___x_4438_, 7, v_expectData_4434_);
lean_ctor_set(v___x_4438_, 8, v_pendingHead_4436_);
lean_ctor_set_uint8(v___x_4438_, sizeof(void*)*9, v___x_4401_);
lean_ctor_set_uint8(v___x_4438_, sizeof(void*)*9 + 1, v_handlerDispatched_4435_);
lean_inc_ref(v___x_4438_);
v___x_4439_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4402_, v_connectionContext_4403_, v___x_4438_);
v___x_4440_ = lean_box(v___x_4401_);
lean_inc_ref(v_config_4407_);
lean_inc(v_handler_4406_);
lean_inc_ref(v_responseBodyInstance_4405_);
lean_inc_ref(v_h_4404_);
v___f_4441_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4441_, 0, v_h_4404_);
lean_closure_set(v___f_4441_, 1, v_responseBodyInstance_4405_);
lean_closure_set(v___f_4441_, 2, v_handler_4406_);
lean_closure_set(v___f_4441_, 3, v_config_4407_);
lean_closure_set(v___f_4441_, 4, v___x_4438_);
lean_closure_set(v___f_4441_, 5, v___x_4440_);
lean_closure_set(v___f_4441_, 6, v___f_4408_);
v___x_4442_ = lean_box(v___x_4401_);
v___f_4443_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4443_, 0, v_inst_4409_);
lean_closure_set(v___f_4443_, 1, v_h_4404_);
lean_closure_set(v___f_4443_, 2, v_responseBodyInstance_4405_);
lean_closure_set(v___f_4443_, 3, v_config_4407_);
lean_closure_set(v___f_4443_, 4, v_handler_4406_);
lean_closure_set(v___f_4443_, 5, v___x_4442_);
lean_closure_set(v___f_4443_, 6, v___f_4441_);
v___x_4444_ = lean_unsigned_to_nat(0u);
v___x_4445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4444_, v___x_4401_, v___x_4439_, v___f_4443_);
return v___x_4445_;
}
v___jp_4446_:
{
if (v_requiresData_4433_ == 0)
{
if (v___y_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4450_; 
lean_dec_ref(v_inst_4409_);
lean_dec_ref(v___f_4408_);
lean_dec_ref(v_config_4407_);
lean_dec(v_handler_4406_);
lean_dec_ref(v_responseBodyInstance_4405_);
lean_dec_ref(v_h_4404_);
lean_dec_ref(v_connectionContext_4403_);
lean_dec(v_socket_4402_);
v___x_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4448_, 0, v_a_4422_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4448_);
v___x_4450_ = v___x_4424_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
lean_object* v___x_4451_; 
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
}
else
{
lean_inc(v_pendingHead_4436_);
lean_inc(v_expectData_4434_);
lean_inc(v_respStream_4432_);
lean_inc_ref(v_response_4431_);
lean_inc(v_headerTimeout_4430_);
lean_inc(v_currentTimeout_4429_);
lean_inc(v_keepAliveTimeout_4428_);
lean_inc_ref(v_requestStream_4427_);
lean_inc_ref(v_machine_4426_);
lean_del_object(v___x_4424_);
lean_dec(v_a_4422_);
goto v___jp_4437_;
}
}
else
{
lean_inc(v_pendingHead_4436_);
lean_inc(v_expectData_4434_);
lean_inc(v_respStream_4432_);
lean_inc_ref(v_response_4431_);
lean_inc(v_headerTimeout_4430_);
lean_inc(v_currentTimeout_4429_);
lean_inc(v_keepAliveTimeout_4428_);
lean_inc_ref(v_requestStream_4427_);
lean_inc_ref(v_machine_4426_);
lean_del_object(v___x_4424_);
lean_dec(v_a_4422_);
goto v___jp_4437_;
}
}
v___jp_4453_:
{
if (v_handlerDispatched_4435_ == 0)
{
v___y_4447_ = v___y_4454_;
goto v___jp_4446_;
}
else
{
v___y_4447_ = v_handlerDispatched_4435_;
goto v___jp_4446_;
}
}
v___jp_4455_:
{
if (v___y_4456_ == 0)
{
v___y_4454_ = v___y_4457_;
goto v___jp_4453_;
}
else
{
v___y_4454_ = v___y_4456_;
goto v___jp_4453_;
}
}
v___jp_4458_:
{
lean_object* v_writer_4460_; uint8_t v_sentMessage_4461_; 
v_writer_4460_ = lean_ctor_get(v_machine_4426_, 1);
v_sentMessage_4461_ = lean_ctor_get_uint8(v_writer_4460_, sizeof(void*)*6);
if (v_sentMessage_4461_ == 0)
{
lean_object* v_reader_4462_; lean_object* v_state_4463_; 
v_reader_4462_ = lean_ctor_get(v_machine_4426_, 0);
v_state_4463_ = lean_ctor_get(v_reader_4462_, 0);
if (lean_obj_tag(v_state_4463_) == 2)
{
v___y_4456_ = v___y_4459_;
v___y_4457_ = v___x_4410_;
goto v___jp_4455_;
}
else
{
v___y_4456_ = v___y_4459_;
v___y_4457_ = v_sentMessage_4461_;
goto v___jp_4455_;
}
}
else
{
v___y_4456_ = v___y_4459_;
v___y_4457_ = v___x_4401_;
goto v___jp_4455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4465_, lean_object* v_socket_4466_, lean_object* v_connectionContext_4467_, lean_object* v_h_4468_, lean_object* v_responseBodyInstance_4469_, lean_object* v_handler_4470_, lean_object* v_config_4471_, lean_object* v___f_4472_, lean_object* v_inst_4473_, lean_object* v___x_4474_, lean_object* v_x_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v___x_5171__boxed_4477_; uint8_t v___x_5174__boxed_4478_; lean_object* v_res_4479_; 
v___x_5171__boxed_4477_ = lean_unbox(v___x_4465_);
v___x_5174__boxed_4478_ = lean_unbox(v___x_4474_);
v_res_4479_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5171__boxed_4477_, v_socket_4466_, v_connectionContext_4467_, v_h_4468_, v_responseBodyInstance_4469_, v_handler_4470_, v_config_4471_, v___f_4472_, v_inst_4473_, v___x_5174__boxed_4478_, v_x_4475_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4480_, lean_object* v_handler_4481_, lean_object* v_extensions_4482_, lean_object* v_connectionContext_4483_, uint8_t v___x_4484_, lean_object* v___f_4485_, lean_object* v_x_4486_){
_start:
{
if (lean_obj_tag(v_x_4486_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4496_; 
lean_dec_ref(v___f_4485_);
lean_dec_ref(v_connectionContext_4483_);
lean_dec(v_extensions_4482_);
lean_dec(v_handler_4481_);
lean_dec_ref(v_h_4480_);
v_a_4488_ = lean_ctor_get(v_x_4486_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_x_4486_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4490_ = v_x_4486_;
v_isShared_4491_ = v_isSharedCheck_4496_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v_x_4486_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4496_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; 
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
return v___x_4494_;
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v_a_4497_ = lean_ctor_get(v_x_4486_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v_x_4486_, 1);
v___x_4498_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4480_, v_handler_4481_, v_extensions_4482_, v_connectionContext_4483_, v_a_4497_);
v___x_4499_ = lean_unsigned_to_nat(0u);
v___x_4500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4499_, v___x_4484_, v___x_4498_, v___f_4485_);
return v___x_4500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4501_, lean_object* v_handler_4502_, lean_object* v_extensions_4503_, lean_object* v_connectionContext_4504_, lean_object* v___x_4505_, lean_object* v___f_4506_, lean_object* v_x_4507_, lean_object* v___y_4508_){
_start:
{
uint8_t v___x_5265__boxed_4509_; lean_object* v_res_4510_; 
v___x_5265__boxed_4509_ = lean_unbox(v___x_4505_);
v_res_4510_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4501_, v_handler_4502_, v_extensions_4503_, v_connectionContext_4504_, v___x_5265__boxed_4509_, v___f_4506_, v_x_4507_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4511_, lean_object* v_responseBodyInstance_4512_, lean_object* v_handler_4513_, lean_object* v_config_4514_, lean_object* v_connectionContext_4515_, lean_object* v_events_4516_, lean_object* v___x_4517_, uint8_t v___x_4518_, lean_object* v___f_4519_, lean_object* v_____r_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4511_, v_responseBodyInstance_4512_, v_handler_4513_, v_config_4514_, v_connectionContext_4515_, v_events_4516_, v___x_4517_);
v___x_4523_ = lean_unsigned_to_nat(0u);
v___x_4524_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4523_, v___x_4518_, v___x_4522_, v___f_4519_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4525_, lean_object* v_responseBodyInstance_4526_, lean_object* v_handler_4527_, lean_object* v_config_4528_, lean_object* v_connectionContext_4529_, lean_object* v_events_4530_, lean_object* v___x_4531_, lean_object* v___x_4532_, lean_object* v___f_4533_, lean_object* v_____r_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___x_5304__boxed_4536_; lean_object* v_res_4537_; 
v___x_5304__boxed_4536_ = lean_unbox(v___x_4532_);
v_res_4537_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4525_, v_responseBodyInstance_4526_, v_handler_4527_, v_config_4528_, v_connectionContext_4529_, v_events_4530_, v___x_4531_, v___x_5304__boxed_4536_, v___f_4533_, v_____r_4534_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4538_, lean_object* v___f_4539_, lean_object* v_x_4540_){
_start:
{
if (lean_obj_tag(v_x_4540_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v___f_4539_);
lean_dec_ref(v___x_4538_);
v_a_4542_ = lean_ctor_get(v_x_4540_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_x_4540_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4544_ = v_x_4540_;
v_isShared_4545_ = v_isSharedCheck_4550_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v_x_4540_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4550_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4562_; 
v_a_4551_ = lean_ctor_get(v_x_4540_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x_4540_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4553_ = v_x_4540_;
v_isShared_4554_ = v_isSharedCheck_4562_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v_x_4540_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4562_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
if (lean_obj_tag(v_a_4551_) == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4557_; 
lean_dec_ref(v___f_4539_);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4538_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4555_);
v___x_4557_ = v___x_4553_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4555_);
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
else
{
lean_object* v_val_4560_; lean_object* v___x_4561_; 
lean_del_object(v___x_4553_);
lean_dec_ref(v___x_4538_);
v_val_4560_ = lean_ctor_get(v_a_4551_, 0);
lean_inc(v_val_4560_);
lean_dec_ref_known(v_a_4551_, 1);
v___x_4561_ = lean_apply_2(v___f_4539_, v_val_4560_, lean_box(0));
return v___x_4561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4563_, lean_object* v___f_4564_, lean_object* v_x_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4563_, v___f_4564_, v_x_4565_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(uint8_t v___x_4568_, lean_object* v_socket_4569_, lean_object* v_connectionContext_4570_, lean_object* v_h_4571_, lean_object* v_responseBodyInstance_4572_, lean_object* v_handler_4573_, lean_object* v_config_4574_, lean_object* v___f_4575_, lean_object* v_inst_4576_, lean_object* v_extensions_4577_, lean_object* v___f_4578_, lean_object* v___f_4579_, lean_object* v_x_4580_, lean_object* v_____s_4581_){
_start:
{
lean_object* v_machine_4583_; lean_object* v_reader_4584_; lean_object* v_requestStream_4585_; lean_object* v_keepAliveTimeout_4586_; lean_object* v_currentTimeout_4587_; lean_object* v_headerTimeout_4588_; lean_object* v_response_4589_; lean_object* v_respStream_4590_; uint8_t v_requiresData_4591_; lean_object* v_expectData_4592_; uint8_t v_handlerDispatched_4593_; lean_object* v_pendingHead_4594_; lean_object* v_writer_4595_; lean_object* v_state_4596_; uint8_t v___x_4597_; 
v_machine_4583_ = lean_ctor_get(v_____s_4581_, 0);
v_reader_4584_ = lean_ctor_get(v_machine_4583_, 0);
v_requestStream_4585_ = lean_ctor_get(v_____s_4581_, 1);
v_keepAliveTimeout_4586_ = lean_ctor_get(v_____s_4581_, 2);
v_currentTimeout_4587_ = lean_ctor_get(v_____s_4581_, 3);
v_headerTimeout_4588_ = lean_ctor_get(v_____s_4581_, 4);
v_response_4589_ = lean_ctor_get(v_____s_4581_, 5);
v_respStream_4590_ = lean_ctor_get(v_____s_4581_, 6);
v_requiresData_4591_ = lean_ctor_get_uint8(v_____s_4581_, sizeof(void*)*9);
v_expectData_4592_ = lean_ctor_get(v_____s_4581_, 7);
v_handlerDispatched_4593_ = lean_ctor_get_uint8(v_____s_4581_, sizeof(void*)*9 + 1);
v_pendingHead_4594_ = lean_ctor_get(v_____s_4581_, 8);
v_writer_4595_ = lean_ctor_get(v_machine_4583_, 1);
v_state_4596_ = lean_ctor_get(v_reader_4584_, 0);
v___x_4597_ = 0;
if (lean_obj_tag(v_state_4596_) == 6)
{
lean_object* v_state_4625_; 
v_state_4625_ = lean_ctor_get(v_writer_4595_, 2);
if (lean_obj_tag(v_state_4625_) == 7)
{
lean_object* v_outputData_4626_; lean_object* v_size_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
v_outputData_4626_ = lean_ctor_get(v_writer_4595_, 1);
v_size_4627_ = lean_ctor_get(v_outputData_4626_, 1);
v___x_4628_ = lean_unsigned_to_nat(0u);
v___x_4629_ = lean_nat_dec_eq(v_size_4627_, v___x_4628_);
if (v___x_4629_ == 0)
{
lean_inc(v_pendingHead_4594_);
lean_inc(v_expectData_4592_);
lean_inc(v_respStream_4590_);
lean_inc_ref(v_response_4589_);
lean_inc(v_headerTimeout_4588_);
lean_inc(v_currentTimeout_4587_);
lean_inc(v_keepAliveTimeout_4586_);
lean_inc_ref(v_requestStream_4585_);
lean_inc_ref(v_machine_4583_);
lean_dec_ref(v_____s_4581_);
goto v___jp_4598_;
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
lean_dec_ref(v___f_4579_);
lean_dec_ref(v___f_4578_);
lean_dec(v_extensions_4577_);
lean_dec_ref(v_inst_4576_);
lean_dec_ref(v___f_4575_);
lean_dec_ref(v_config_4574_);
lean_dec(v_handler_4573_);
lean_dec_ref(v_responseBodyInstance_4572_);
lean_dec_ref(v_h_4571_);
lean_dec_ref(v_connectionContext_4570_);
lean_dec(v_socket_4569_);
v___x_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4630_, 0, v_____s_4581_);
v___x_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
return v___x_4632_;
}
}
else
{
lean_inc(v_pendingHead_4594_);
lean_inc(v_expectData_4592_);
lean_inc(v_respStream_4590_);
lean_inc_ref(v_response_4589_);
lean_inc(v_headerTimeout_4588_);
lean_inc(v_currentTimeout_4587_);
lean_inc(v_keepAliveTimeout_4586_);
lean_inc_ref(v_requestStream_4585_);
lean_inc_ref(v_machine_4583_);
lean_dec_ref(v_____s_4581_);
goto v___jp_4598_;
}
}
else
{
lean_inc(v_pendingHead_4594_);
lean_inc(v_expectData_4592_);
lean_inc(v_respStream_4590_);
lean_inc_ref(v_response_4589_);
lean_inc(v_headerTimeout_4588_);
lean_inc(v_currentTimeout_4587_);
lean_inc(v_keepAliveTimeout_4586_);
lean_inc_ref(v_requestStream_4585_);
lean_inc_ref(v_machine_4583_);
lean_dec_ref(v_____s_4581_);
goto v___jp_4598_;
}
v___jp_4598_:
{
lean_object* v___x_4599_; lean_object* v_snd_4600_; lean_object* v_output_4601_; lean_object* v_fst_4602_; lean_object* v_events_4603_; lean_object* v_data_4604_; lean_object* v_size_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___f_4609_; lean_object* v___x_4610_; lean_object* v___f_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___f_4614_; lean_object* v___x_4615_; uint8_t v___x_4616_; 
v___x_4599_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4597_, v_machine_4583_);
v_snd_4600_ = lean_ctor_get(v___x_4599_, 1);
lean_inc(v_snd_4600_);
v_output_4601_ = lean_ctor_get(v_snd_4600_, 1);
lean_inc_ref(v_output_4601_);
v_fst_4602_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_fst_4602_);
lean_dec_ref(v___x_4599_);
v_events_4603_ = lean_ctor_get(v_snd_4600_, 0);
lean_inc_ref_n(v_events_4603_, 2);
lean_dec(v_snd_4600_);
v_data_4604_ = lean_ctor_get(v_output_4601_, 0);
lean_inc_ref(v_data_4604_);
v_size_4605_ = lean_ctor_get(v_output_4601_, 1);
lean_inc(v_size_4605_);
lean_dec_ref(v_output_4601_);
v___x_4606_ = 1;
v___x_4607_ = lean_box(v___x_4568_);
v___x_4608_ = lean_box(v___x_4606_);
lean_inc_ref(v_inst_4576_);
lean_inc_ref_n(v_config_4574_, 2);
lean_inc_n(v_handler_4573_, 3);
lean_inc_ref_n(v_responseBodyInstance_4572_, 2);
lean_inc_ref_n(v_h_4571_, 3);
lean_inc_ref_n(v_connectionContext_4570_, 3);
lean_inc(v_socket_4569_);
v___f_4609_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 12, 10);
lean_closure_set(v___f_4609_, 0, v___x_4607_);
lean_closure_set(v___f_4609_, 1, v_socket_4569_);
lean_closure_set(v___f_4609_, 2, v_connectionContext_4570_);
lean_closure_set(v___f_4609_, 3, v_h_4571_);
lean_closure_set(v___f_4609_, 4, v_responseBodyInstance_4572_);
lean_closure_set(v___f_4609_, 5, v_handler_4573_);
lean_closure_set(v___f_4609_, 6, v_config_4574_);
lean_closure_set(v___f_4609_, 7, v___f_4575_);
lean_closure_set(v___f_4609_, 8, v_inst_4576_);
lean_closure_set(v___f_4609_, 9, v___x_4608_);
v___x_4610_ = lean_box(v___x_4568_);
v___f_4611_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4611_, 0, v_h_4571_);
lean_closure_set(v___f_4611_, 1, v_handler_4573_);
lean_closure_set(v___f_4611_, 2, v_extensions_4577_);
lean_closure_set(v___f_4611_, 3, v_connectionContext_4570_);
lean_closure_set(v___f_4611_, 4, v___x_4610_);
lean_closure_set(v___f_4611_, 5, v___f_4609_);
v___x_4612_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4612_, 0, v_fst_4602_);
lean_ctor_set(v___x_4612_, 1, v_requestStream_4585_);
lean_ctor_set(v___x_4612_, 2, v_keepAliveTimeout_4586_);
lean_ctor_set(v___x_4612_, 3, v_currentTimeout_4587_);
lean_ctor_set(v___x_4612_, 4, v_headerTimeout_4588_);
lean_ctor_set(v___x_4612_, 5, v_response_4589_);
lean_ctor_set(v___x_4612_, 6, v_respStream_4590_);
lean_ctor_set(v___x_4612_, 7, v_expectData_4592_);
lean_ctor_set(v___x_4612_, 8, v_pendingHead_4594_);
lean_ctor_set_uint8(v___x_4612_, sizeof(void*)*9, v_requiresData_4591_);
lean_ctor_set_uint8(v___x_4612_, sizeof(void*)*9 + 1, v_handlerDispatched_4593_);
v___x_4613_ = lean_box(v___x_4568_);
lean_inc_ref(v___f_4611_);
lean_inc_ref(v___x_4612_);
v___f_4614_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4614_, 0, v_h_4571_);
lean_closure_set(v___f_4614_, 1, v_responseBodyInstance_4572_);
lean_closure_set(v___f_4614_, 2, v_handler_4573_);
lean_closure_set(v___f_4614_, 3, v_config_4574_);
lean_closure_set(v___f_4614_, 4, v_connectionContext_4570_);
lean_closure_set(v___f_4614_, 5, v_events_4603_);
lean_closure_set(v___f_4614_, 6, v___x_4612_);
lean_closure_set(v___f_4614_, 7, v___x_4613_);
lean_closure_set(v___f_4614_, 8, v___f_4611_);
v___x_4615_ = lean_unsigned_to_nat(0u);
v___x_4616_ = lean_nat_dec_lt(v___x_4615_, v_size_4605_);
lean_dec(v_size_4605_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
lean_dec_ref(v___f_4614_);
lean_dec_ref(v_data_4604_);
lean_dec_ref(v___f_4579_);
lean_dec_ref(v___f_4578_);
lean_dec_ref(v_inst_4576_);
lean_dec(v_socket_4569_);
v___x_4617_ = lean_box(0);
v___x_4618_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4571_, v_responseBodyInstance_4572_, v_handler_4573_, v_config_4574_, v_connectionContext_4570_, v_events_4603_, v___x_4612_, v___x_4568_, v___f_4611_, v___x_4617_);
return v___x_4618_;
}
else
{
lean_object* v_sendAll_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___f_4623_; lean_object* v___x_4624_; 
lean_dec_ref(v___f_4611_);
lean_dec_ref(v_events_4603_);
lean_dec_ref(v_config_4574_);
lean_dec(v_handler_4573_);
lean_dec_ref(v_responseBodyInstance_4572_);
lean_dec_ref(v_h_4571_);
lean_dec_ref(v_connectionContext_4570_);
v_sendAll_4619_ = lean_ctor_get(v_inst_4576_, 1);
lean_inc_ref(v_sendAll_4619_);
lean_dec_ref(v_inst_4576_);
v___x_4620_ = lean_apply_3(v_sendAll_4619_, v_socket_4569_, v_data_4604_, lean_box(0));
v___x_4621_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4615_, v___x_4568_, v___x_4620_, v___f_4578_);
v___x_4622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4615_, v___x_4568_, v___x_4621_, v___f_4579_);
v___f_4623_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4623_, 0, v___x_4612_);
lean_closure_set(v___f_4623_, 1, v___f_4614_);
v___x_4624_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4615_, v___x_4568_, v___x_4622_, v___f_4623_);
return v___x_4624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v___x_4633_, lean_object* v_socket_4634_, lean_object* v_connectionContext_4635_, lean_object* v_h_4636_, lean_object* v_responseBodyInstance_4637_, lean_object* v_handler_4638_, lean_object* v_config_4639_, lean_object* v___f_4640_, lean_object* v_inst_4641_, lean_object* v_extensions_4642_, lean_object* v___f_4643_, lean_object* v___f_4644_, lean_object* v_x_4645_, lean_object* v_____s_4646_, lean_object* v___y_4647_){
_start:
{
uint8_t v___x_5378__boxed_4648_; lean_object* v_res_4649_; 
v___x_5378__boxed_4648_ = lean_unbox(v___x_4633_);
v_res_4649_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v___x_5378__boxed_4648_, v_socket_4634_, v_connectionContext_4635_, v_h_4636_, v_responseBodyInstance_4637_, v_handler_4638_, v_config_4639_, v___f_4640_, v_inst_4641_, v_extensions_4642_, v___f_4643_, v___f_4644_, v_x_4645_, v_____s_4646_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4650_, lean_object* v_x_4651_){
_start:
{
if (lean_obj_tag(v_x_4651_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4661_; 
v_a_4653_ = lean_ctor_get(v_x_4651_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_x_4651_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4655_ = v_x_4651_;
v_isShared_4656_ = v_isSharedCheck_4661_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v_x_4651_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4661_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
lean_object* v___x_4659_; 
v___x_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
return v___x_4659_;
}
}
}
else
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
lean_dec_ref_known(v_x_4651_, 1);
v___x_4662_ = l_IO_Promise_result_x21___redArg(v_a_4650_);
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4664_, lean_object* v_x_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4664_, v_x_4665_);
lean_dec(v_a_4664_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4668_, lean_object* v___x_4669_, lean_object* v___x_4670_, uint8_t v___x_4671_, lean_object* v_x_4672_){
_start:
{
if (lean_obj_tag(v_x_4672_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4682_; 
lean_dec_ref(v___x_4670_);
lean_dec(v___x_4669_);
lean_dec_ref(v___f_4668_);
v_a_4674_ = lean_ctor_get(v_x_4672_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_x_4672_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4676_ = v_x_4672_;
v_isShared_4677_ = v_isSharedCheck_4682_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v_x_4672_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4682_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4680_; 
v___x_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4679_);
return v___x_4680_;
}
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4694_; 
v_a_4683_ = lean_ctor_get(v_x_4672_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_x_4672_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4685_ = v_x_4672_;
v_isShared_4686_ = v_isSharedCheck_4694_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v_x_4672_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4694_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v___f_4688_; lean_object* v___x_4690_; 
lean_inc(v_a_4683_);
lean_inc(v___x_4669_);
v___x_4687_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4668_, v___x_4669_, v_a_4683_, v___x_4670_);
v___f_4688_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4688_, 0, v_a_4683_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4687_);
v___x_4690_ = v___x_4685_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4687_);
v___x_4690_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
v___x_4692_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4669_, v___x_4671_, v___x_4691_, v___f_4688_);
return v___x_4692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4695_, lean_object* v___x_4696_, lean_object* v___x_4697_, lean_object* v___x_4698_, lean_object* v_x_4699_, lean_object* v___y_4700_){
_start:
{
uint8_t v___x_5493__boxed_4701_; lean_object* v_res_4702_; 
v___x_5493__boxed_4701_ = lean_unbox(v___x_4698_);
v_res_4702_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4695_, v___x_4696_, v___x_4697_, v___x_5493__boxed_4701_, v_x_4699_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4703_, lean_object* v_machine_4704_, lean_object* v_a_4705_, lean_object* v___x_4706_, lean_object* v_socket_4707_, lean_object* v_connectionContext_4708_, lean_object* v_h_4709_, lean_object* v_responseBodyInstance_4710_, lean_object* v_handler_4711_, lean_object* v___f_4712_, lean_object* v_inst_4713_, lean_object* v_extensions_4714_, lean_object* v___f_4715_, lean_object* v___f_4716_, lean_object* v___f_4717_, lean_object* v_x_4718_){
_start:
{
if (lean_obj_tag(v_x_4718_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4728_; 
lean_dec_ref(v___f_4717_);
lean_dec_ref(v___f_4716_);
lean_dec_ref(v___f_4715_);
lean_dec(v_extensions_4714_);
lean_dec_ref(v_inst_4713_);
lean_dec_ref(v___f_4712_);
lean_dec(v_handler_4711_);
lean_dec_ref(v_responseBodyInstance_4710_);
lean_dec_ref(v_h_4709_);
lean_dec_ref(v_connectionContext_4708_);
lean_dec(v_socket_4707_);
lean_dec(v___x_4706_);
lean_dec_ref(v_a_4705_);
lean_dec_ref(v_machine_4704_);
lean_dec_ref(v_config_4703_);
v_a_4720_ = lean_ctor_get(v_x_4718_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v_x_4718_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4722_ = v_x_4718_;
v_isShared_4723_ = v_isSharedCheck_4728_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v_x_4718_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4728_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; 
v___x_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
return v___x_4726_;
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4750_; 
v_a_4729_ = lean_ctor_get(v_x_4718_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_x_4718_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4731_ = v_x_4718_;
v_isShared_4732_ = v_isSharedCheck_4750_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v_x_4718_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4750_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v_keepAliveTimeout_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___f_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___f_4743_; lean_object* v___x_4745_; 
v_keepAliveTimeout_4733_ = lean_ctor_get(v_config_4703_, 5);
lean_inc_n(v_keepAliveTimeout_4733_, 2);
v___x_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4734_, 0, v_keepAliveTimeout_4733_);
v___x_4735_ = lean_box(0);
v___x_4736_ = 0;
v___x_4737_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4737_, 0, v_machine_4704_);
lean_ctor_set(v___x_4737_, 1, v_a_4705_);
lean_ctor_set(v___x_4737_, 2, v___x_4734_);
lean_ctor_set(v___x_4737_, 3, v_keepAliveTimeout_4733_);
lean_ctor_set(v___x_4737_, 4, v___x_4735_);
lean_ctor_set(v___x_4737_, 5, v_a_4729_);
lean_ctor_set(v___x_4737_, 6, v___x_4735_);
lean_ctor_set(v___x_4737_, 7, v___x_4706_);
lean_ctor_set(v___x_4737_, 8, v___x_4735_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*9, v___x_4736_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*9 + 1, v___x_4736_);
v___x_4738_ = lean_io_promise_new();
v___x_4739_ = lean_box(v___x_4736_);
v___f_4740_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 15, 12);
lean_closure_set(v___f_4740_, 0, v___x_4739_);
lean_closure_set(v___f_4740_, 1, v_socket_4707_);
lean_closure_set(v___f_4740_, 2, v_connectionContext_4708_);
lean_closure_set(v___f_4740_, 3, v_h_4709_);
lean_closure_set(v___f_4740_, 4, v_responseBodyInstance_4710_);
lean_closure_set(v___f_4740_, 5, v_handler_4711_);
lean_closure_set(v___f_4740_, 6, v_config_4703_);
lean_closure_set(v___f_4740_, 7, v___f_4712_);
lean_closure_set(v___f_4740_, 8, v_inst_4713_);
lean_closure_set(v___f_4740_, 9, v_extensions_4714_);
lean_closure_set(v___f_4740_, 10, v___f_4715_);
lean_closure_set(v___f_4740_, 11, v___f_4716_);
v___x_4741_ = lean_unsigned_to_nat(0u);
v___x_4742_ = lean_box(v___x_4736_);
v___f_4743_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4743_, 0, v___f_4740_);
lean_closure_set(v___f_4743_, 1, v___x_4741_);
lean_closure_set(v___f_4743_, 2, v___x_4737_);
lean_closure_set(v___f_4743_, 3, v___x_4742_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v___x_4738_);
v___x_4745_ = v___x_4731_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4738_);
v___x_4745_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
v___x_4747_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4741_, v___x_4736_, v___x_4746_, v___f_4743_);
v___x_4748_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4741_, v___x_4736_, v___x_4747_, v___f_4717_);
return v___x_4748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4751_ = _args[0];
lean_object* v_machine_4752_ = _args[1];
lean_object* v_a_4753_ = _args[2];
lean_object* v___x_4754_ = _args[3];
lean_object* v_socket_4755_ = _args[4];
lean_object* v_connectionContext_4756_ = _args[5];
lean_object* v_h_4757_ = _args[6];
lean_object* v_responseBodyInstance_4758_ = _args[7];
lean_object* v_handler_4759_ = _args[8];
lean_object* v___f_4760_ = _args[9];
lean_object* v_inst_4761_ = _args[10];
lean_object* v_extensions_4762_ = _args[11];
lean_object* v___f_4763_ = _args[12];
lean_object* v___f_4764_ = _args[13];
lean_object* v___f_4765_ = _args[14];
lean_object* v_x_4766_ = _args[15];
lean_object* v___y_4767_ = _args[16];
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4751_, v_machine_4752_, v_a_4753_, v___x_4754_, v_socket_4755_, v_connectionContext_4756_, v_h_4757_, v_responseBodyInstance_4758_, v_handler_4759_, v___f_4760_, v_inst_4761_, v_extensions_4762_, v___f_4763_, v___f_4764_, v___f_4765_, v_x_4766_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4769_, lean_object* v_machine_4770_, lean_object* v_socket_4771_, lean_object* v_connectionContext_4772_, lean_object* v_h_4773_, lean_object* v_responseBodyInstance_4774_, lean_object* v_handler_4775_, lean_object* v___f_4776_, lean_object* v_inst_4777_, lean_object* v_extensions_4778_, lean_object* v___f_4779_, lean_object* v___f_4780_, lean_object* v___f_4781_, lean_object* v_x_4782_){
_start:
{
if (lean_obj_tag(v_x_4782_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4792_; 
lean_dec_ref(v___f_4781_);
lean_dec_ref(v___f_4780_);
lean_dec_ref(v___f_4779_);
lean_dec(v_extensions_4778_);
lean_dec_ref(v_inst_4777_);
lean_dec_ref(v___f_4776_);
lean_dec(v_handler_4775_);
lean_dec_ref(v_responseBodyInstance_4774_);
lean_dec_ref(v_h_4773_);
lean_dec_ref(v_connectionContext_4772_);
lean_dec(v_socket_4771_);
lean_dec_ref(v_machine_4770_);
lean_dec_ref(v_config_4769_);
v_a_4784_ = lean_ctor_get(v_x_4782_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_x_4782_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4786_ = v_x_4782_;
v_isShared_4787_ = v_isSharedCheck_4792_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v_x_4782_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4792_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4790_; 
v___x_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
return v___x_4790_;
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4807_; 
v_a_4793_ = lean_ctor_get(v_x_4782_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_x_4782_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4795_ = v_x_4782_;
v_isShared_4796_ = v_isSharedCheck_4807_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v_x_4782_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4807_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___f_4799_; lean_object* v___x_4801_; 
v___x_4797_ = lean_box(0);
v___x_4798_ = l_Std_CloseableChannel_new___redArg(v___x_4797_);
v___f_4799_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4799_, 0, v_config_4769_);
lean_closure_set(v___f_4799_, 1, v_machine_4770_);
lean_closure_set(v___f_4799_, 2, v_a_4793_);
lean_closure_set(v___f_4799_, 3, v___x_4797_);
lean_closure_set(v___f_4799_, 4, v_socket_4771_);
lean_closure_set(v___f_4799_, 5, v_connectionContext_4772_);
lean_closure_set(v___f_4799_, 6, v_h_4773_);
lean_closure_set(v___f_4799_, 7, v_responseBodyInstance_4774_);
lean_closure_set(v___f_4799_, 8, v_handler_4775_);
lean_closure_set(v___f_4799_, 9, v___f_4776_);
lean_closure_set(v___f_4799_, 10, v_inst_4777_);
lean_closure_set(v___f_4799_, 11, v_extensions_4778_);
lean_closure_set(v___f_4799_, 12, v___f_4779_);
lean_closure_set(v___f_4799_, 13, v___f_4780_);
lean_closure_set(v___f_4799_, 14, v___f_4781_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v___x_4798_);
v___x_4801_ = v___x_4795_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4798_);
v___x_4801_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; 
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = 0;
v___x_4805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4803_, v___x_4804_, v___x_4802_, v___f_4799_);
return v___x_4805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4808_, lean_object* v_machine_4809_, lean_object* v_socket_4810_, lean_object* v_connectionContext_4811_, lean_object* v_h_4812_, lean_object* v_responseBodyInstance_4813_, lean_object* v_handler_4814_, lean_object* v___f_4815_, lean_object* v_inst_4816_, lean_object* v_extensions_4817_, lean_object* v___f_4818_, lean_object* v___f_4819_, lean_object* v___f_4820_, lean_object* v_x_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4808_, v_machine_4809_, v_socket_4810_, v_connectionContext_4811_, v_h_4812_, v_responseBodyInstance_4813_, v_handler_4814_, v___f_4815_, v_inst_4816_, v_extensions_4817_, v___f_4818_, v___f_4819_, v___f_4820_, v_x_4821_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4827_, lean_object* v_h_4828_, lean_object* v_connection_4829_, lean_object* v_config_4830_, lean_object* v_connectionContext_4831_, lean_object* v_handler_4832_){
_start:
{
lean_object* v_responseBodyInstance_4834_; lean_object* v_onFailure_4835_; lean_object* v___x_4836_; lean_object* v_socket_4837_; lean_object* v_machine_4838_; lean_object* v_extensions_4839_; lean_object* v___f_4840_; lean_object* v___f_4841_; lean_object* v___f_4842_; lean_object* v___f_4843_; lean_object* v___f_4844_; lean_object* v___f_4845_; lean_object* v___f_4846_; lean_object* v___f_4847_; lean_object* v___f_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; lean_object* v___x_4851_; 
v_responseBodyInstance_4834_ = lean_ctor_get(v_h_4828_, 0);
lean_inc_ref_n(v_responseBodyInstance_4834_, 2);
v_onFailure_4835_ = lean_ctor_get(v_h_4828_, 2);
v___x_4836_ = l_Std_Http_Body_mkStream();
v_socket_4837_ = lean_ctor_get(v_connection_4829_, 0);
lean_inc_n(v_socket_4837_, 2);
v_machine_4838_ = lean_ctor_get(v_connection_4829_, 1);
lean_inc_ref(v_machine_4838_);
v_extensions_4839_ = lean_ctor_get(v_connection_4829_, 2);
lean_inc(v_extensions_4839_);
lean_dec_ref(v_connection_4829_);
v___f_4840_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4841_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
lean_inc(v_handler_4832_);
lean_inc_ref(v_onFailure_4835_);
v___f_4842_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4842_, 0, v_onFailure_4835_);
lean_closure_set(v___f_4842_, 1, v_handler_4832_);
lean_closure_set(v___f_4842_, 2, v___f_4841_);
v___f_4843_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4844_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4827_);
v___f_4845_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4845_, 0, v_inst_4827_);
lean_closure_set(v___f_4845_, 1, v_socket_4837_);
lean_inc_ref(v___f_4845_);
v___f_4846_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4846_, 0, v___f_4845_);
v___f_4847_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4847_, 0, v___f_4840_);
lean_closure_set(v___f_4847_, 1, v_responseBodyInstance_4834_);
lean_closure_set(v___f_4847_, 2, v___f_4846_);
lean_closure_set(v___f_4847_, 3, v___f_4845_);
v___f_4848_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4848_, 0, v_config_4830_);
lean_closure_set(v___f_4848_, 1, v_machine_4838_);
lean_closure_set(v___f_4848_, 2, v_socket_4837_);
lean_closure_set(v___f_4848_, 3, v_connectionContext_4831_);
lean_closure_set(v___f_4848_, 4, v_h_4828_);
lean_closure_set(v___f_4848_, 5, v_responseBodyInstance_4834_);
lean_closure_set(v___f_4848_, 6, v_handler_4832_);
lean_closure_set(v___f_4848_, 7, v___f_4844_);
lean_closure_set(v___f_4848_, 8, v_inst_4827_);
lean_closure_set(v___f_4848_, 9, v_extensions_4839_);
lean_closure_set(v___f_4848_, 10, v___f_4843_);
lean_closure_set(v___f_4848_, 11, v___f_4842_);
lean_closure_set(v___f_4848_, 12, v___f_4847_);
v___x_4849_ = lean_unsigned_to_nat(0u);
v___x_4850_ = 0;
v___x_4851_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4849_, v___x_4850_, v___x_4836_, v___f_4848_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4852_, lean_object* v_h_4853_, lean_object* v_connection_4854_, lean_object* v_config_4855_, lean_object* v_connectionContext_4856_, lean_object* v_handler_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4852_, v_h_4853_, v_connection_4854_, v_config_4855_, v_connectionContext_4856_, v_handler_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4860_, lean_object* v_00_u03c3_4861_, lean_object* v_inst_4862_, lean_object* v_h_4863_, lean_object* v_connection_4864_, lean_object* v_config_4865_, lean_object* v_connectionContext_4866_, lean_object* v_handler_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4862_, v_h_4863_, v_connection_4864_, v_config_4865_, v_connectionContext_4866_, v_handler_4867_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4870_, lean_object* v_00_u03c3_4871_, lean_object* v_inst_4872_, lean_object* v_h_4873_, lean_object* v_connection_4874_, lean_object* v_config_4875_, lean_object* v_connectionContext_4876_, lean_object* v_handler_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4870_, v_00_u03c3_4871_, v_inst_4872_, v_h_4873_, v_connection_4874_, v_config_4875_, v_connectionContext_4876_, v_handler_4877_);
return v_res_4879_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = 0;
v___x_4881_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4880_);
return v___x_4881_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = lean_unsigned_to_nat(4096u);
v___x_4883_ = lean_mk_empty_byte_array(v___x_4882_);
return v___x_4883_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4885_ = l_ByteArray_mkIterator(v___x_4884_);
return v___x_4885_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4886_ = 0;
v___x_4887_ = lean_unsigned_to_nat(0u);
v___x_4888_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4889_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4890_ = lean_box(0);
v___x_4891_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
lean_ctor_set(v___x_4891_, 1, v___x_4889_);
lean_ctor_set(v___x_4891_, 2, v___x_4888_);
lean_ctor_set(v___x_4891_, 3, v___x_4887_);
lean_ctor_set(v___x_4891_, 4, v___x_4887_);
lean_ctor_set(v___x_4891_, 5, v___x_4887_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*6, v___x_4886_);
return v___x_4891_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = 1;
v___x_4900_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4899_);
return v___x_4900_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4901_; uint8_t v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4901_ = lean_unsigned_to_nat(0u);
v___x_4902_ = 0;
v___x_4903_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4904_ = lean_box(0);
v___x_4905_ = lean_box(0);
v___x_4906_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4907_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4908_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
lean_ctor_set(v___x_4908_, 1, v___x_4906_);
lean_ctor_set(v___x_4908_, 2, v___x_4905_);
lean_ctor_set(v___x_4908_, 3, v___x_4904_);
lean_ctor_set(v___x_4908_, 4, v___x_4903_);
lean_ctor_set(v___x_4908_, 5, v___x_4901_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*6, v___x_4902_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*6 + 1, v___x_4902_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*6 + 2, v___x_4902_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4909_, lean_object* v_client_4910_, lean_object* v_extensions_4911_, lean_object* v_inst_4912_, lean_object* v_inst_4913_, lean_object* v_handler_4914_, lean_object* v_x_4915_){
_start:
{
if (lean_obj_tag(v_x_4915_) == 0)
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4925_; 
lean_dec(v_handler_4914_);
lean_dec_ref(v_inst_4913_);
lean_dec_ref(v_inst_4912_);
lean_dec(v_extensions_4911_);
lean_dec(v_client_4910_);
lean_dec_ref(v_config_4909_);
v_a_4917_ = lean_ctor_get(v_x_4915_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_x_4915_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4919_ = v_x_4915_;
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v_x_4915_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
lean_object* v___x_4923_; 
v___x_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4922_);
return v___x_4923_;
}
}
}
else
{
lean_object* v_a_4926_; uint8_t v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; uint8_t v_enableKeepAlive_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v_a_4926_ = lean_ctor_get(v_x_4915_, 0);
lean_inc(v_a_4926_);
lean_dec_ref_known(v_x_4915_, 1);
v___x_4927_ = 0;
v___x_4928_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4929_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4930_ = lean_box(0);
v___x_4931_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4932_ = l_Std_Http_Config_toH1Config(v_config_4909_);
v_enableKeepAlive_4933_ = lean_ctor_get_uint8(v___x_4932_, sizeof(void*)*18);
v___x_4934_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4934_, 0, v___x_4928_);
lean_ctor_set(v___x_4934_, 1, v___x_4931_);
lean_ctor_set(v___x_4934_, 2, v___x_4932_);
lean_ctor_set(v___x_4934_, 3, v___x_4929_);
lean_ctor_set(v___x_4934_, 4, v___x_4930_);
lean_ctor_set(v___x_4934_, 5, v___x_4930_);
lean_ctor_set_uint8(v___x_4934_, sizeof(void*)*6, v_enableKeepAlive_4933_);
lean_ctor_set_uint8(v___x_4934_, sizeof(void*)*6 + 1, v___x_4927_);
lean_ctor_set_uint8(v___x_4934_, sizeof(void*)*6 + 2, v___x_4927_);
v___x_4935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4935_, 0, v_client_4910_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
lean_ctor_set(v___x_4935_, 2, v_extensions_4911_);
v___x_4936_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4912_, v_inst_4913_, v___x_4935_, v_config_4909_, v_a_4926_, v_handler_4914_);
return v___x_4936_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4937_, lean_object* v_client_4938_, lean_object* v_extensions_4939_, lean_object* v_inst_4940_, lean_object* v_inst_4941_, lean_object* v_handler_4942_, lean_object* v_x_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4937_, v_client_4938_, v_extensions_4939_, v_inst_4940_, v_inst_4941_, v_handler_4942_, v_x_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4946_, lean_object* v_inst_4947_, lean_object* v_client_4948_, lean_object* v_handler_4949_, lean_object* v_config_4950_, lean_object* v_extensions_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v___f_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; uint8_t v___x_4958_; lean_object* v___x_4959_; 
v___f_4954_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4954_, 0, v_config_4950_);
lean_closure_set(v___f_4954_, 1, v_client_4948_);
lean_closure_set(v___f_4954_, 2, v_extensions_4951_);
lean_closure_set(v___f_4954_, 3, v_inst_4946_);
lean_closure_set(v___f_4954_, 4, v_inst_4947_);
lean_closure_set(v___f_4954_, 5, v_handler_4949_);
lean_inc_ref(v_a_4952_);
v___x_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_a_4952_);
v___x_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
v___x_4957_ = lean_unsigned_to_nat(0u);
v___x_4958_ = 0;
v___x_4959_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4957_, v___x_4958_, v___x_4956_, v___f_4954_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4960_, lean_object* v_inst_4961_, lean_object* v_client_4962_, lean_object* v_handler_4963_, lean_object* v_config_4964_, lean_object* v_extensions_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4960_, v_inst_4961_, v_client_4962_, v_handler_4963_, v_config_4964_, v_extensions_4965_, v_a_4966_);
lean_dec_ref(v_a_4966_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4969_, lean_object* v_00_u03c3_4970_, lean_object* v_inst_4971_, lean_object* v_inst_4972_, lean_object* v_client_4973_, lean_object* v_handler_4974_, lean_object* v_config_4975_, lean_object* v_extensions_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4971_, v_inst_4972_, v_client_4973_, v_handler_4974_, v_config_4975_, v_extensions_4976_, v_a_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4980_, lean_object* v_00_u03c3_4981_, lean_object* v_inst_4982_, lean_object* v_inst_4983_, lean_object* v_client_4984_, lean_object* v_handler_4985_, lean_object* v_config_4986_, lean_object* v_extensions_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Std_Http_Server_serveConnection(v_t_4980_, v_00_u03c3_4981_, v_inst_4982_, v_inst_4983_, v_client_4984_, v_handler_4985_, v_config_4986_, v_extensions_4987_, v_a_4988_);
lean_dec_ref(v_a_4988_);
return v_res_4990_;
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
