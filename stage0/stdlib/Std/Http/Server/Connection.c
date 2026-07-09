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
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1002_, lean_object* v_a_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_offset_1005_; lean_object* v_second_1006_; lean_object* v_nano_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_offset_1005_ = lean_ctor_get(v_tz_1002_, 0);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1017_, lean_object* v_a_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1017_, v_a_1018_, v_x_1019_);
lean_dec_ref(v_a_1018_);
lean_dec_ref(v_tz_1017_);
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
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1083_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_tz_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_inc(v_a_1072_);
v_tz_1076_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1072_, v_a_1069_);
lean_inc(v_a_1069_);
lean_inc_ref(v_tz_1076_);
v___f_1077_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1077_, 0, v_tz_1076_);
lean_closure_set(v___f_1077_, 1, v_a_1069_);
v___x_1078_ = lean_mk_thunk(v___f_1077_);
v___x_1079_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v_a_1069_);
lean_ctor_set(v___x_1079_, 2, v_a_1072_);
lean_ctor_set(v___x_1079_, 3, v_tz_1076_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1079_);
v___x_1081_ = v___x_1074_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v_val_1061_ = v___x_1081_;
goto v___jp_1060_;
}
}
}
else
{
lean_object* v_a_1084_; 
lean_dec(v_a_1069_);
v_a_1084_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1071_, 1);
v_a_1066_ = v_a_1084_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1068_, 1);
v_a_1066_ = v_a_1085_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1086_, lean_object* v_head_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1086_, v_head_1087_);
lean_dec_ref(v_config_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_nat_to_int(v_a_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_nat_to_int(v_a_1092_);
v___x_1094_ = l_Rat_ofInt(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_00_u03b2_1095_, lean_object* v_m_1096_, lean_object* v_a_1097_){
_start:
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_m_1096_, v_a_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___boxed(lean_object* v_00_u03b2_1099_, lean_object* v_m_1100_, lean_object* v_a_1101_){
_start:
{
uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_res_1102_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(v_00_u03b2_1099_, v_m_1100_, v_a_1101_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_m_1100_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1104_, lean_object* v_a_1105_, lean_object* v_x_1106_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1105_, v_x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_a_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1108_, v_a_1109_, v_x_1110_);
lean_dec(v_x_1110_);
lean_dec_ref(v_a_1109_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1113_, lean_object* v_data_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1116_, lean_object* v_i_1117_, lean_object* v_source_1118_, lean_object* v_target_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v_i_1117_, v_source_1118_, v_target_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1125_, lean_object* v_____r_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___y_1125_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1132_, lean_object* v_____r_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1132_, v_____r_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1136_, lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v___f_1136_);
v_a_1139_ = lean_ctor_get(v_x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1141_ = v_x_1137_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v_x_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1149_; 
v_a_1148_ = lean_ctor_get(v_x_1137_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v_x_1137_, 1);
v___x_1149_ = lean_apply_2(v___f_1136_, v_a_1148_, lean_box(0));
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1150_, lean_object* v_x_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1150_, v_x_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1154_, lean_object* v_body_1155_, lean_object* v___f_1156_, lean_object* v___f_1157_, lean_object* v_x_1158_){
_start:
{
if (lean_obj_tag(v_x_1158_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___f_1157_);
lean_dec_ref(v___f_1156_);
lean_dec(v_body_1155_);
lean_dec_ref(v_close_1154_);
v_a_1160_ = lean_ctor_get(v_x_1158_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v_x_1158_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v_x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; uint8_t v___x_1170_; 
v_a_1169_ = lean_ctor_get(v_x_1158_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v_x_1158_, 1);
v___x_1170_ = lean_unbox(v_a_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v___f_1157_);
v___x_1171_ = lean_apply_2(v_close_1154_, v_body_1155_, lean_box(0));
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
v___x_1174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1172_, v___x_1173_, v___x_1171_, v___f_1156_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_a_1169_);
lean_dec_ref(v___f_1156_);
lean_dec(v_body_1155_);
lean_dec_ref(v_close_1154_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_apply_2(v___f_1157_, v___x_1175_, lean_box(0));
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1177_, lean_object* v_body_1178_, lean_object* v___f_1179_, lean_object* v___f_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1177_, v_body_1178_, v___f_1179_, v___f_1180_, v_x_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v___x_1184_, lean_object* v_x1_1185_, lean_object* v_x2_1186_){
_start:
{
lean_object* v_fst_1187_; uint8_t v___x_1188_; 
v_fst_1187_ = lean_ctor_get(v_x2_1186_, 0);
v___x_1188_ = lean_string_dec_eq(v_fst_1187_, v___x_1184_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_array_push(v_x1_1185_, v_x2_1186_);
return v___x_1189_;
}
else
{
lean_dec_ref(v_x2_1186_);
return v_x1_1185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v___x_1190_, lean_object* v_x1_1191_, lean_object* v_x2_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v___x_1190_, v_x1_1191_, v_x2_1192_);
lean_dec_ref(v___x_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___f_1194_, lean_object* v___f_1195_, lean_object* v_x1_1196_, lean_object* v_x2_1197_){
_start:
{
lean_object* v_fst_1198_; lean_object* v_entries_1199_; lean_object* v_indexes_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1211_; 
v_fst_1198_ = lean_ctor_get(v_x2_1197_, 0);
lean_inc(v_fst_1198_);
v_entries_1199_ = lean_ctor_get(v_x1_1196_, 0);
v_indexes_1200_ = lean_ctor_get(v_x1_1196_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x1_1196_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1202_ = v_x1_1196_;
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_indexes_1200_);
lean_inc(v_entries_1199_);
lean_dec(v_x1_1196_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_i_1204_; lean_object* v_f_1205_; lean_object* v_entries_1206_; lean_object* v_indexes_1207_; lean_object* v___x_1209_; 
v_i_1204_ = lean_array_get_size(v_entries_1199_);
v_f_1205_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1205_, 0, v_i_1204_);
v_entries_1206_ = lean_array_push(v_entries_1199_, v_x2_1197_);
v_indexes_1207_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1194_, v___f_1195_, v_indexes_1200_, v_fst_1198_, v_f_1205_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v_indexes_1207_);
lean_ctor_set(v___x_1202_, 0, v_entries_1206_);
v___x_1209_ = v___x_1202_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_entries_1206_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_indexes_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___f_1234_; 
v___x_1233_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1234_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1234_, 0, v___x_1233_);
return v___f_1234_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___f_1241_; 
v___x_1240_ = l_Std_Http_Header_Name_contentLength;
v___f_1241_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1241_, 0, v___x_1240_);
return v___f_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v___y_1242_, lean_object* v_body_1243_, lean_object* v_isClosed_1244_, lean_object* v_close_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v___y_1249_; uint8_t v_omitBody_1250_; lean_object* v___y_1263_; lean_object* v___y_1298_; uint8_t v___y_1299_; uint8_t v___y_1300_; 
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_close_1245_);
lean_dec_ref(v_isClosed_1244_);
lean_dec(v_body_1243_);
lean_dec_ref(v___y_1242_);
v_a_1303_ = lean_ctor_get(v_x_1246_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v_x_1246_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_x_1246_);
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
lean_object* v_writer_1312_; lean_object* v_a_1313_; lean_object* v_reader_1314_; lean_object* v_config_1315_; lean_object* v_events_1316_; lean_object* v_error_1317_; lean_object* v_instant_1318_; uint8_t v_keepAlive_1319_; uint8_t v_forcedFlush_1320_; uint8_t v_pullBodyStalled_1321_; lean_object* v_userData_1322_; lean_object* v_outputData_1323_; lean_object* v_state_1324_; lean_object* v_knownSize_1325_; lean_object* v_messageHead_1326_; uint8_t v_sentMessage_1327_; uint8_t v_userClosedBody_1328_; uint8_t v_omitBody_1329_; lean_object* v_userDataBytes_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1481_; 
v_writer_1312_ = lean_ctor_get(v___y_1242_, 1);
lean_inc_ref(v_writer_1312_);
v_a_1313_ = lean_ctor_get(v_x_1246_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v_x_1246_, 1);
v_reader_1314_ = lean_ctor_get(v___y_1242_, 0);
v_config_1315_ = lean_ctor_get(v___y_1242_, 2);
v_events_1316_ = lean_ctor_get(v___y_1242_, 3);
v_error_1317_ = lean_ctor_get(v___y_1242_, 4);
v_instant_1318_ = lean_ctor_get(v___y_1242_, 5);
v_keepAlive_1319_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*6);
v_forcedFlush_1320_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1321_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*6 + 2);
v_userData_1322_ = lean_ctor_get(v_writer_1312_, 0);
v_outputData_1323_ = lean_ctor_get(v_writer_1312_, 1);
v_state_1324_ = lean_ctor_get(v_writer_1312_, 2);
v_knownSize_1325_ = lean_ctor_get(v_writer_1312_, 3);
v_messageHead_1326_ = lean_ctor_get(v_writer_1312_, 4);
v_sentMessage_1327_ = lean_ctor_get_uint8(v_writer_1312_, sizeof(void*)*6);
v_userClosedBody_1328_ = lean_ctor_get_uint8(v_writer_1312_, sizeof(void*)*6 + 1);
v_omitBody_1329_ = lean_ctor_get_uint8(v_writer_1312_, sizeof(void*)*6 + 2);
v_userDataBytes_1330_ = lean_ctor_get(v_writer_1312_, 5);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_writer_1312_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1332_ = v_writer_1312_;
v_isShared_1333_ = v_isSharedCheck_1481_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_userDataBytes_1330_);
lean_inc(v_messageHead_1326_);
lean_inc(v_knownSize_1325_);
lean_inc(v_state_1324_);
lean_inc(v_outputData_1323_);
lean_inc(v_userData_1322_);
lean_dec(v_writer_1312_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1481_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint8_t v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; uint8_t v___y_1382_; uint8_t v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; uint8_t v___y_1413_; lean_object* v___y_1414_; uint8_t v___y_1415_; uint8_t v___x_1430_; lean_object* v___y_1432_; uint8_t v___y_1433_; uint8_t v___y_1434_; uint8_t v___y_1435_; uint8_t v___y_1436_; uint8_t v___y_1437_; uint8_t v___y_1444_; uint8_t v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1459_; uint8_t v___y_1460_; uint8_t v___y_1463_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1430_ = 0;
v___x_1479_ = lean_box(1);
v___x_1480_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1324_, v___x_1479_);
if (v___x_1480_ == 0)
{
v___y_1463_ = v___x_1480_;
goto v___jp_1462_;
}
else
{
if (v_sentMessage_1327_ == 0)
{
v___y_1463_ = v___x_1480_;
goto v___jp_1462_;
}
else
{
lean_del_object(v___x_1332_);
lean_dec(v_userDataBytes_1330_);
lean_dec(v_messageHead_1326_);
lean_dec(v_knownSize_1325_);
lean_dec(v_state_1324_);
lean_dec_ref(v_outputData_1323_);
lean_dec_ref(v_userData_1322_);
lean_dec(v_a_1313_);
v___y_1249_ = v___y_1242_;
v_omitBody_1250_ = v_omitBody_1329_;
goto v___jp_1248_;
}
}
v___jp_1334_:
{
lean_object* v_message_1337_; lean_object* v___x_2280__overap_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v_message_1337_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1335_, v_a_1313_, v___y_1336_);
v___x_2280__overap_1338_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1335_);
v___x_1339_ = lean_apply_2(v___x_2280__overap_1338_, v_outputData_1323_, v_message_1337_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___x_1339_);
v___x_1341_ = v___x_1332_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_userData_1322_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_state_1324_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_knownSize_1325_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_messageHead_1326_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v_userDataBytes_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6, v_sentMessage_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6 + 1, v_userClosedBody_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6 + 2, v_omitBody_1329_);
v___x_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1342_, 0, v_reader_1314_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
lean_ctor_set(v___x_1342_, 2, v_config_1315_);
lean_ctor_set(v___x_1342_, 3, v_events_1316_);
lean_ctor_set(v___x_1342_, 4, v_error_1317_);
lean_ctor_set(v___x_1342_, 5, v_instant_1318_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*6, v_keepAlive_1319_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*6 + 1, v_forcedFlush_1320_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*6 + 2, v_pullBodyStalled_1321_);
v___y_1249_ = v___x_1342_;
v_omitBody_1250_ = v_omitBody_1329_;
goto v___jp_1248_;
}
}
v___jp_1344_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_array_get_size(v___y_1349_);
v___x_1351_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1352_ = lean_nat_dec_lt(v___y_1346_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___y_1349_);
v___y_1335_ = v___y_1348_;
v___y_1336_ = v___y_1347_;
goto v___jp_1334_;
}
else
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1353_ == 0)
{
if (v___x_1352_ == 0)
{
lean_dec_ref(v___y_1349_);
v___y_1335_ = v___y_1348_;
v___y_1336_ = v___y_1347_;
goto v___jp_1334_;
}
else
{
size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1350_);
lean_inc_ref(v___y_1345_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1351_, v___y_1345_, v___y_1349_, v___x_1354_, v___x_1355_, v___y_1347_);
v___y_1335_ = v___y_1348_;
v___y_1336_ = v___x_1356_;
goto v___jp_1334_;
}
}
else
{
size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = lean_usize_of_nat(v___x_1350_);
lean_inc_ref(v___y_1345_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1351_, v___y_1345_, v___y_1349_, v___x_1357_, v___x_1358_, v___y_1347_);
v___y_1335_ = v___y_1348_;
v___y_1336_ = v___x_1359_;
goto v___jp_1334_;
}
}
}
v___jp_1360_:
{
lean_object* v_entries_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_entries_1367_ = lean_ctor_get(v___y_1364_, 0);
lean_inc_ref(v_entries_1367_);
lean_dec_ref(v___y_1364_);
v___x_1368_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1365_, v___y_1363_);
lean_dec_ref(v___y_1363_);
lean_dec_ref(v___y_1365_);
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v_entries_1367_);
v___x_1371_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1372_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1373_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1373_ == 0)
{
lean_dec_ref(v_entries_1367_);
v___y_1345_ = v___y_1361_;
v___y_1346_ = v___x_1369_;
v___y_1347_ = v___x_1368_;
v___y_1348_ = v___y_1366_;
v___y_1349_ = v___x_1371_;
goto v___jp_1344_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_le(v___x_1370_, v___x_1370_);
if (v___x_1374_ == 0)
{
if (v___x_1373_ == 0)
{
lean_dec_ref(v_entries_1367_);
v___y_1345_ = v___y_1361_;
v___y_1346_ = v___x_1369_;
v___y_1347_ = v___x_1368_;
v___y_1348_ = v___y_1366_;
v___y_1349_ = v___x_1371_;
goto v___jp_1344_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1370_);
lean_inc_ref(v___y_1362_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1372_, v___y_1362_, v_entries_1367_, v___x_1375_, v___x_1376_, v___x_1371_);
v___y_1345_ = v___y_1361_;
v___y_1346_ = v___x_1369_;
v___y_1347_ = v___x_1368_;
v___y_1348_ = v___y_1366_;
v___y_1349_ = v___x_1377_;
goto v___jp_1344_;
}
}
else
{
size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = lean_usize_of_nat(v___x_1370_);
lean_inc_ref(v___y_1362_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1372_, v___y_1362_, v_entries_1367_, v___x_1378_, v___x_1379_, v___x_1371_);
v___y_1345_ = v___y_1361_;
v___y_1346_ = v___x_1369_;
v___y_1347_ = v___x_1368_;
v___y_1348_ = v___y_1366_;
v___y_1349_ = v___x_1380_;
goto v___jp_1344_;
}
}
}
v___jp_1381_:
{
lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___f_1389_; uint8_t v___x_1390_; 
v___x_1385_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1386_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___f_1387_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1388_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1389_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1390_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1387_, v___f_1388_, v___x_1385_, v___y_1384_);
if (v___x_1390_ == 0)
{
if (v___y_1382_ == 0)
{
v___y_1361_ = v___f_1389_;
v___y_1362_ = v___f_1386_;
v___y_1363_ = v___f_1388_;
v___y_1364_ = v___y_1384_;
v___y_1365_ = v___f_1387_;
v___y_1366_ = v___y_1383_;
goto v___jp_1360_;
}
else
{
v___y_1335_ = v___y_1383_;
v___y_1336_ = v___y_1384_;
goto v___jp_1334_;
}
}
else
{
v___y_1361_ = v___f_1389_;
v___y_1362_ = v___f_1386_;
v___y_1363_ = v___f_1388_;
v___y_1364_ = v___y_1384_;
v___y_1365_ = v___f_1387_;
v___y_1366_ = v___y_1383_;
goto v___jp_1360_;
}
}
v___jp_1391_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = lean_array_get_size(v___y_1397_);
v___x_1399_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1400_ = lean_nat_dec_lt(v___y_1395_, v___x_1398_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v___y_1397_);
v___y_1382_ = v___y_1394_;
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___y_1393_;
goto v___jp_1381_;
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_nat_dec_le(v___x_1398_, v___x_1398_);
if (v___x_1401_ == 0)
{
if (v___x_1400_ == 0)
{
lean_dec_ref(v___y_1397_);
v___y_1382_ = v___y_1394_;
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___y_1393_;
goto v___jp_1381_;
}
else
{
size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = lean_usize_of_nat(v___x_1398_);
lean_inc_ref(v___y_1392_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1399_, v___y_1392_, v___y_1397_, v___x_1402_, v___x_1403_, v___y_1393_);
v___y_1382_ = v___y_1394_;
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___x_1404_;
goto v___jp_1381_;
}
}
else
{
size_t v___x_1405_; size_t v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = lean_usize_of_nat(v___x_1398_);
lean_inc_ref(v___y_1392_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1399_, v___y_1392_, v___y_1397_, v___x_1405_, v___x_1406_, v___y_1393_);
v___y_1382_ = v___y_1394_;
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___x_1407_;
goto v___jp_1381_;
}
}
}
v___jp_1408_:
{
lean_object* v_entries_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_entries_1416_ = lean_ctor_get(v___y_1411_, 0);
lean_inc_ref(v_entries_1416_);
lean_dec_ref(v___y_1411_);
v___x_1417_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1412_, v___y_1410_);
lean_dec_ref(v___y_1410_);
lean_dec_ref(v___y_1412_);
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = lean_array_get_size(v_entries_1416_);
v___x_1420_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1421_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1422_ = lean_nat_dec_lt(v___x_1418_, v___x_1419_);
if (v___x_1422_ == 0)
{
lean_dec_ref(v_entries_1416_);
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___x_1417_;
v___y_1394_ = v___y_1413_;
v___y_1395_ = v___x_1418_;
v___y_1396_ = v___y_1415_;
v___y_1397_ = v___x_1420_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_nat_dec_le(v___x_1419_, v___x_1419_);
if (v___x_1423_ == 0)
{
if (v___x_1422_ == 0)
{
lean_dec_ref(v_entries_1416_);
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___x_1417_;
v___y_1394_ = v___y_1413_;
v___y_1395_ = v___x_1418_;
v___y_1396_ = v___y_1415_;
v___y_1397_ = v___x_1420_;
goto v___jp_1391_;
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1419_);
lean_inc_ref(v___y_1414_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1421_, v___y_1414_, v_entries_1416_, v___x_1424_, v___x_1425_, v___x_1420_);
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___x_1417_;
v___y_1394_ = v___y_1413_;
v___y_1395_ = v___x_1418_;
v___y_1396_ = v___y_1415_;
v___y_1397_ = v___x_1426_;
goto v___jp_1391_;
}
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1419_);
lean_inc_ref(v___y_1414_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1421_, v___y_1414_, v_entries_1416_, v___x_1427_, v___x_1428_, v___x_1420_);
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___x_1417_;
v___y_1394_ = v___y_1413_;
v___y_1395_ = v___x_1418_;
v___y_1396_ = v___y_1415_;
v___y_1397_ = v___x_1429_;
goto v___jp_1391_;
}
}
}
v___jp_1431_:
{
lean_object* v_headerSize_1438_; lean_object* v_machine_1439_; lean_object* v_machine_1440_; lean_object* v_reader_1441_; lean_object* v_state_1442_; 
v_headerSize_1438_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1436_, v_a_1313_, v___y_1434_);
v_machine_1439_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1430_, v___y_1432_, v_headerSize_1438_, v___y_1437_);
v_machine_1440_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1430_, v_machine_1439_, v_a_1313_);
lean_dec(v_a_1313_);
v_reader_1441_ = lean_ctor_get(v_machine_1440_, 0);
lean_inc_ref(v_reader_1441_);
v_state_1442_ = lean_ctor_get(v_reader_1441_, 0);
lean_inc(v_state_1442_);
lean_dec_ref(v_reader_1441_);
if (lean_obj_tag(v_state_1442_) == 7)
{
lean_dec_ref_known(v_state_1442_, 1);
v___y_1298_ = v_machine_1440_;
v___y_1299_ = v___y_1435_;
v___y_1300_ = v___y_1433_;
goto v___jp_1297_;
}
else
{
lean_dec(v_state_1442_);
v___y_1298_ = v_machine_1440_;
v___y_1299_ = v___y_1435_;
v___y_1300_ = v___y_1434_;
goto v___jp_1297_;
}
}
v___jp_1443_:
{
uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v_indexes_1449_; lean_object* v___x_1450_; lean_object* v_machine_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; uint8_t v___x_1455_; 
v___x_1447_ = 1;
v___x_1448_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1447_, v_a_1313_);
v_indexes_1449_ = lean_ctor_get(v___x_1448_, 1);
lean_inc_ref(v_indexes_1449_);
lean_dec_ref(v___x_1448_);
lean_inc(v_a_1313_);
v___x_1450_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1450_, 0, v_userData_1322_);
lean_ctor_set(v___x_1450_, 1, v_outputData_1323_);
lean_ctor_set(v___x_1450_, 2, v_state_1324_);
lean_ctor_set(v___x_1450_, 3, v_knownSize_1325_);
lean_ctor_set(v___x_1450_, 4, v_a_1313_);
lean_ctor_set(v___x_1450_, 5, v_userDataBytes_1330_);
lean_ctor_set_uint8(v___x_1450_, sizeof(void*)*6, v___y_1444_);
lean_ctor_set_uint8(v___x_1450_, sizeof(void*)*6 + 1, v_userClosedBody_1328_);
lean_ctor_set_uint8(v___x_1450_, sizeof(void*)*6 + 2, v_omitBody_1329_);
v_machine_1451_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1451_, 0, v_reader_1314_);
lean_ctor_set(v_machine_1451_, 1, v___x_1450_);
lean_ctor_set(v_machine_1451_, 2, v_config_1315_);
lean_ctor_set(v_machine_1451_, 3, v_events_1316_);
lean_ctor_set(v_machine_1451_, 4, v_error_1317_);
lean_ctor_set(v_machine_1451_, 5, v_instant_1318_);
lean_ctor_set_uint8(v_machine_1451_, sizeof(void*)*6, v_keepAlive_1319_);
lean_ctor_set_uint8(v_machine_1451_, sizeof(void*)*6 + 1, v_forcedFlush_1320_);
lean_ctor_set_uint8(v_machine_1451_, sizeof(void*)*6 + 2, v_pullBodyStalled_1321_);
v___x_1452_ = l_Std_Http_Header_Name_contentLength;
v___f_1453_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1454_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1453_, v___f_1454_, v_indexes_1449_, v___x_1452_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1453_, v___f_1454_, v_indexes_1449_, v___x_1456_);
lean_dec_ref(v_indexes_1449_);
v___y_1432_ = v_machine_1451_;
v___y_1433_ = v___y_1444_;
v___y_1434_ = v___y_1445_;
v___y_1435_ = v___y_1446_;
v___y_1436_ = v___x_1447_;
v___y_1437_ = v___x_1457_;
goto v___jp_1431_;
}
else
{
lean_dec_ref(v_indexes_1449_);
v___y_1432_ = v_machine_1451_;
v___y_1433_ = v___y_1444_;
v___y_1434_ = v___y_1445_;
v___y_1435_ = v___y_1446_;
v___y_1436_ = v___x_1447_;
v___y_1437_ = v___x_1455_;
goto v___jp_1431_;
}
}
v___jp_1458_:
{
lean_object* v_state_1461_; 
v_state_1461_ = lean_ctor_get(v_reader_1314_, 0);
if (lean_obj_tag(v_state_1461_) == 7)
{
v___y_1444_ = v___y_1459_;
v___y_1445_ = v___y_1460_;
v___y_1446_ = v___y_1459_;
goto v___jp_1443_;
}
else
{
v___y_1444_ = v___y_1459_;
v___y_1445_ = v___y_1460_;
v___y_1446_ = v___y_1460_;
goto v___jp_1443_;
}
}
v___jp_1462_:
{
if (v___y_1463_ == 0)
{
lean_del_object(v___x_1332_);
lean_dec(v_userDataBytes_1330_);
lean_dec(v_messageHead_1326_);
lean_dec(v_knownSize_1325_);
lean_dec(v_state_1324_);
lean_dec_ref(v_outputData_1323_);
lean_dec_ref(v_userData_1322_);
lean_dec(v_a_1313_);
v___y_1249_ = v___y_1242_;
v_omitBody_1250_ = v_omitBody_1329_;
goto v___jp_1248_;
}
else
{
lean_object* v_status_1464_; uint8_t v___x_1465_; uint16_t v___x_1466_; uint16_t v___x_1467_; uint8_t v___x_1468_; 
lean_inc(v_instant_1318_);
lean_inc(v_error_1317_);
lean_inc_ref(v_events_1316_);
lean_inc_ref(v_config_1315_);
lean_inc_ref(v_reader_1314_);
lean_dec_ref(v___y_1242_);
v_status_1464_ = lean_ctor_get(v_a_1313_, 0);
v___x_1465_ = 0;
v___x_1466_ = 100;
v___x_1467_ = l_Std_Http_Status_toCode(v_status_1464_);
v___x_1468_ = lean_uint16_dec_le(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_del_object(v___x_1332_);
lean_dec(v_messageHead_1326_);
v___y_1459_ = v___y_1463_;
v___y_1460_ = v___x_1465_;
goto v___jp_1458_;
}
else
{
uint16_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = 200;
v___x_1470_ = lean_uint16_dec_lt(v___x_1467_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_del_object(v___x_1332_);
lean_dec(v_messageHead_1326_);
v___y_1459_ = v___y_1463_;
v___y_1460_ = v___x_1465_;
goto v___jp_1458_;
}
else
{
uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___f_1476_; lean_object* v___f_1477_; uint8_t v___x_1478_; 
v___x_1471_ = 1;
v___x_1472_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1471_, v_a_1313_);
v___x_1473_ = l_Std_Http_Header_Name_contentLength;
v___f_1474_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15);
v___f_1475_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___f_1476_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13));
v___f_1477_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1478_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1475_, v___f_1476_, v___x_1473_, v___x_1472_);
if (v___x_1478_ == 0)
{
if (v___x_1470_ == 0)
{
v___y_1409_ = v___f_1477_;
v___y_1410_ = v___f_1476_;
v___y_1411_ = v___x_1472_;
v___y_1412_ = v___f_1475_;
v___y_1413_ = v___x_1470_;
v___y_1414_ = v___f_1474_;
v___y_1415_ = v___x_1471_;
goto v___jp_1408_;
}
else
{
v___y_1382_ = v___x_1470_;
v___y_1383_ = v___x_1471_;
v___y_1384_ = v___x_1472_;
goto v___jp_1381_;
}
}
else
{
v___y_1409_ = v___f_1477_;
v___y_1410_ = v___f_1476_;
v___y_1411_ = v___x_1472_;
v___y_1412_ = v___f_1475_;
v___y_1413_ = v___x_1470_;
v___y_1414_ = v___f_1474_;
v___y_1415_ = v___x_1471_;
goto v___jp_1408_;
}
}
}
}
}
}
}
v___jp_1248_:
{
if (v_omitBody_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_close_1245_);
lean_dec_ref(v_isClosed_1244_);
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_body_1243_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___y_1249_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; 
lean_inc(v_body_1243_);
v___x_1255_ = lean_apply_2(v_isClosed_1244_, v_body_1243_, lean_box(0));
v___f_1256_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1256_, 0, v___y_1249_);
lean_inc_ref(v___f_1256_);
v___f_1257_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1257_, 0, v___f_1256_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1258_, 0, v_close_1245_);
lean_closure_set(v___f_1258_, 1, v_body_1243_);
lean_closure_set(v___f_1258_, 2, v___f_1257_);
lean_closure_set(v___f_1258_, 3, v___f_1256_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = 0;
v___x_1261_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1259_, v___x_1260_, v___x_1255_, v___f_1258_);
return v___x_1261_;
}
}
v___jp_1262_:
{
lean_object* v_writer_1264_; lean_object* v_reader_1265_; lean_object* v_config_1266_; lean_object* v_events_1267_; lean_object* v_error_1268_; lean_object* v_instant_1269_; uint8_t v_keepAlive_1270_; uint8_t v_forcedFlush_1271_; uint8_t v_pullBodyStalled_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1296_; 
v_writer_1264_ = lean_ctor_get(v___y_1263_, 1);
v_reader_1265_ = lean_ctor_get(v___y_1263_, 0);
v_config_1266_ = lean_ctor_get(v___y_1263_, 2);
v_events_1267_ = lean_ctor_get(v___y_1263_, 3);
v_error_1268_ = lean_ctor_get(v___y_1263_, 4);
v_instant_1269_ = lean_ctor_get(v___y_1263_, 5);
v_keepAlive_1270_ = lean_ctor_get_uint8(v___y_1263_, sizeof(void*)*6);
v_forcedFlush_1271_ = lean_ctor_get_uint8(v___y_1263_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1272_ = lean_ctor_get_uint8(v___y_1263_, sizeof(void*)*6 + 2);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___y_1263_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1274_ = v___y_1263_;
v_isShared_1275_ = v_isSharedCheck_1296_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_instant_1269_);
lean_inc(v_error_1268_);
lean_inc(v_events_1267_);
lean_inc(v_config_1266_);
lean_inc(v_writer_1264_);
lean_inc(v_reader_1265_);
lean_dec(v___y_1263_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1296_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_userData_1276_; lean_object* v_outputData_1277_; lean_object* v_knownSize_1278_; lean_object* v_messageHead_1279_; uint8_t v_sentMessage_1280_; uint8_t v_userClosedBody_1281_; uint8_t v_omitBody_1282_; lean_object* v_userDataBytes_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1294_; 
v_userData_1276_ = lean_ctor_get(v_writer_1264_, 0);
v_outputData_1277_ = lean_ctor_get(v_writer_1264_, 1);
v_knownSize_1278_ = lean_ctor_get(v_writer_1264_, 3);
v_messageHead_1279_ = lean_ctor_get(v_writer_1264_, 4);
v_sentMessage_1280_ = lean_ctor_get_uint8(v_writer_1264_, sizeof(void*)*6);
v_userClosedBody_1281_ = lean_ctor_get_uint8(v_writer_1264_, sizeof(void*)*6 + 1);
v_omitBody_1282_ = lean_ctor_get_uint8(v_writer_1264_, sizeof(void*)*6 + 2);
v_userDataBytes_1283_ = lean_ctor_get(v_writer_1264_, 5);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_writer_1264_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_writer_1264_, 2);
lean_dec(v_unused_1295_);
v___x_1285_ = v_writer_1264_;
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_userDataBytes_1283_);
lean_inc(v_messageHead_1279_);
lean_inc(v_knownSize_1278_);
lean_inc(v_outputData_1277_);
lean_inc(v_userData_1276_);
lean_dec(v_writer_1264_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_box(2);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 2, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_userData_1276_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_outputData_1277_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_knownSize_1278_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_messageHead_1279_);
lean_ctor_set(v_reuseFailAlloc_1293_, 5, v_userDataBytes_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*6, v_sentMessage_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*6 + 1, v_userClosedBody_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*6 + 2, v_omitBody_1282_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v___x_1289_);
v___x_1291_ = v___x_1274_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_reader_1265_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_config_1266_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_events_1267_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_error_1268_);
lean_ctor_set(v_reuseFailAlloc_1292_, 5, v_instant_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*6, v_keepAlive_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*6 + 1, v_forcedFlush_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*6 + 2, v_pullBodyStalled_1272_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
v___y_1249_ = v___x_1291_;
v_omitBody_1250_ = v_omitBody_1282_;
goto v___jp_1248_;
}
}
}
}
}
v___jp_1297_:
{
if (v___y_1300_ == 0)
{
v___y_1263_ = v___y_1298_;
goto v___jp_1262_;
}
else
{
if (v___y_1299_ == 0)
{
lean_object* v_writer_1301_; uint8_t v_omitBody_1302_; 
v_writer_1301_ = lean_ctor_get(v___y_1298_, 1);
v_omitBody_1302_ = lean_ctor_get_uint8(v_writer_1301_, sizeof(void*)*6 + 2);
v___y_1249_ = v___y_1298_;
v_omitBody_1250_ = v_omitBody_1302_;
goto v___jp_1248_;
}
else
{
v___y_1263_ = v___y_1298_;
goto v___jp_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1482_, lean_object* v_body_1483_, lean_object* v_isClosed_1484_, lean_object* v_close_1485_, lean_object* v_x_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1482_, v_body_1483_, v_isClosed_1484_, v_close_1485_, v_x_1486_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v_config_1489_, lean_object* v_line_1490_, lean_object* v_body_1491_, lean_object* v_isClosed_1492_, lean_object* v_close_1493_, lean_object* v_machine_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v___y_1498_; 
if (lean_obj_tag(v_x_1495_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v_machine_1494_);
lean_dec_ref(v_close_1493_);
lean_dec_ref(v_isClosed_1492_);
lean_dec(v_body_1491_);
lean_dec_ref(v_line_1490_);
v_a_1504_ = lean_ctor_get(v_x_1495_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_x_1495_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1506_ = v_x_1495_;
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v_x_1495_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
}
else
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v_x_1495_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v_x_1495_, 1);
if (lean_obj_tag(v_a_1513_) == 1)
{
lean_object* v_writer_1514_; lean_object* v_reader_1515_; lean_object* v_config_1516_; lean_object* v_events_1517_; lean_object* v_error_1518_; lean_object* v_instant_1519_; uint8_t v_keepAlive_1520_; uint8_t v_forcedFlush_1521_; uint8_t v_pullBodyStalled_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1545_; 
v_writer_1514_ = lean_ctor_get(v_machine_1494_, 1);
v_reader_1515_ = lean_ctor_get(v_machine_1494_, 0);
v_config_1516_ = lean_ctor_get(v_machine_1494_, 2);
v_events_1517_ = lean_ctor_get(v_machine_1494_, 3);
v_error_1518_ = lean_ctor_get(v_machine_1494_, 4);
v_instant_1519_ = lean_ctor_get(v_machine_1494_, 5);
v_keepAlive_1520_ = lean_ctor_get_uint8(v_machine_1494_, sizeof(void*)*6);
v_forcedFlush_1521_ = lean_ctor_get_uint8(v_machine_1494_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1522_ = lean_ctor_get_uint8(v_machine_1494_, sizeof(void*)*6 + 2);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_machine_1494_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1524_ = v_machine_1494_;
v_isShared_1525_ = v_isSharedCheck_1545_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_instant_1519_);
lean_inc(v_error_1518_);
lean_inc(v_events_1517_);
lean_inc(v_config_1516_);
lean_inc(v_writer_1514_);
lean_inc(v_reader_1515_);
lean_dec(v_machine_1494_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1545_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_userData_1526_; lean_object* v_outputData_1527_; lean_object* v_state_1528_; lean_object* v_messageHead_1529_; uint8_t v_sentMessage_1530_; uint8_t v_userClosedBody_1531_; uint8_t v_omitBody_1532_; lean_object* v_userDataBytes_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1543_; 
v_userData_1526_ = lean_ctor_get(v_writer_1514_, 0);
v_outputData_1527_ = lean_ctor_get(v_writer_1514_, 1);
v_state_1528_ = lean_ctor_get(v_writer_1514_, 2);
v_messageHead_1529_ = lean_ctor_get(v_writer_1514_, 4);
v_sentMessage_1530_ = lean_ctor_get_uint8(v_writer_1514_, sizeof(void*)*6);
v_userClosedBody_1531_ = lean_ctor_get_uint8(v_writer_1514_, sizeof(void*)*6 + 1);
v_omitBody_1532_ = lean_ctor_get_uint8(v_writer_1514_, sizeof(void*)*6 + 2);
v_userDataBytes_1533_ = lean_ctor_get(v_writer_1514_, 5);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_writer_1514_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_writer_1514_, 3);
lean_dec(v_unused_1544_);
v___x_1535_ = v_writer_1514_;
v_isShared_1536_ = v_isSharedCheck_1543_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_userDataBytes_1533_);
lean_inc(v_messageHead_1529_);
lean_inc(v_state_1528_);
lean_inc(v_outputData_1527_);
lean_inc(v_userData_1526_);
lean_dec(v_writer_1514_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1543_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 3, v_a_1513_);
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_userData_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_outputData_1527_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_state_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_a_1513_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_messageHead_1529_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v_userDataBytes_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*6, v_sentMessage_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*6 + 1, v_userClosedBody_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*6 + 2, v_omitBody_1532_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v___x_1538_);
v___x_1540_ = v___x_1524_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_reader_1515_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_config_1516_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_events_1517_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_error_1518_);
lean_ctor_set(v_reuseFailAlloc_1541_, 5, v_instant_1519_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*6, v_keepAlive_1520_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*6 + 1, v_forcedFlush_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*6 + 2, v_pullBodyStalled_1522_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
v___y_1498_ = v___x_1540_;
goto v___jp_1497_;
}
}
}
}
}
else
{
lean_dec(v_a_1513_);
v___y_1498_ = v_machine_1494_;
goto v___jp_1497_;
}
}
v___jp_1497_:
{
lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1489_, v_line_1490_);
v___f_1500_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1500_, 0, v___y_1498_);
lean_closure_set(v___f_1500_, 1, v_body_1491_);
lean_closure_set(v___f_1500_, 2, v_isClosed_1492_);
lean_closure_set(v___f_1500_, 3, v_close_1493_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = 0;
v___x_1503_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1501_, v___x_1502_, v___x_1499_, v___f_1500_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v_config_1546_, lean_object* v_line_1547_, lean_object* v_body_1548_, lean_object* v_isClosed_1549_, lean_object* v_close_1550_, lean_object* v_machine_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v_config_1546_, v_line_1547_, v_body_1548_, v_isClosed_1549_, v_close_1550_, v_machine_1551_, v_x_1552_);
lean_dec_ref(v_config_1546_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1555_, lean_object* v_config_1556_, lean_object* v_machine_1557_, lean_object* v_res_1558_){
_start:
{
lean_object* v_close_1560_; lean_object* v_isClosed_1561_; lean_object* v_getKnownSize_1562_; lean_object* v_line_1563_; lean_object* v_body_1564_; lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v_close_1560_ = lean_ctor_get(v_inst_1555_, 1);
lean_inc_ref(v_close_1560_);
v_isClosed_1561_ = lean_ctor_get(v_inst_1555_, 2);
lean_inc_ref(v_isClosed_1561_);
v_getKnownSize_1562_ = lean_ctor_get(v_inst_1555_, 5);
lean_inc_ref(v_getKnownSize_1562_);
lean_dec_ref(v_inst_1555_);
v_line_1563_ = lean_ctor_get(v_res_1558_, 0);
lean_inc_ref(v_line_1563_);
v_body_1564_ = lean_ctor_get(v_res_1558_, 1);
lean_inc_n(v_body_1564_, 2);
lean_dec_ref(v_res_1558_);
v___x_1565_ = lean_apply_2(v_getKnownSize_1562_, v_body_1564_, lean_box(0));
v___f_1566_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_1566_, 0, v_config_1556_);
lean_closure_set(v___f_1566_, 1, v_line_1563_);
lean_closure_set(v___f_1566_, 2, v_body_1564_);
lean_closure_set(v___f_1566_, 3, v_isClosed_1561_);
lean_closure_set(v___f_1566_, 4, v_close_1560_);
lean_closure_set(v___f_1566_, 5, v_machine_1557_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = 0;
v___x_1569_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1567_, v___x_1568_, v___x_1565_, v___f_1566_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1570_, lean_object* v_config_1571_, lean_object* v_machine_1572_, lean_object* v_res_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1570_, v_config_1571_, v_machine_1572_, v_res_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1576_, lean_object* v_inst_1577_, lean_object* v_config_1578_, lean_object* v_machine_1579_, lean_object* v_res_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1577_, v_config_1578_, v_machine_1579_, v_res_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_inst_1584_, lean_object* v_config_1585_, lean_object* v_machine_1586_, lean_object* v_res_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1583_, v_inst_1584_, v_config_1585_, v_machine_1586_, v_res_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1590_, lean_object* v___y_1591_){
_start:
{
uint8_t v_closed_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_closed_1593_ = lean_ctor_get_uint8(v_____do__lift_1590_, sizeof(void*)*5);
v___x_1594_ = lean_box(v_closed_1593_);
v___x_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v_____do__lift_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v_pendingProducer_1609_; lean_object* v_pendingConsumer_1610_; lean_object* v_interestWaiter_1611_; uint8_t v_closed_1612_; lean_object* v_pendingIncompleteChunk_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1622_; 
v___x_1608_ = lean_st_ref_take(v___y_1606_);
v_pendingProducer_1609_ = lean_ctor_get(v___x_1608_, 0);
v_pendingConsumer_1610_ = lean_ctor_get(v___x_1608_, 1);
v_interestWaiter_1611_ = lean_ctor_get(v___x_1608_, 2);
v_closed_1612_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*5);
v_pendingIncompleteChunk_1613_ = lean_ctor_get(v___x_1608_, 4);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v___x_1608_, 3);
lean_dec(v_unused_1623_);
v___x_1615_ = v___x_1608_;
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1613_);
lean_inc(v_interestWaiter_1611_);
lean_inc(v_pendingConsumer_1610_);
lean_inc(v_pendingProducer_1609_);
lean_dec(v___x_1608_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 3, v___x_1605_);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_pendingProducer_1609_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_pendingConsumer_1610_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_interestWaiter_1611_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_pendingIncompleteChunk_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*5, v_closed_1612_);
v___x_1618_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_st_ref_set(v___y_1606_, v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1624_, v___y_1625_);
lean_dec(v___y_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1628_, lean_object* v_x_1629_){
_start:
{
if (lean_obj_tag(v_x_1629_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v___x_1628_);
v_a_1631_ = lean_ctor_get(v_x_1629_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1629_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1633_ = v_x_1629_;
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v_x_1629_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
}
}
else
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
v_isSharedCheck_1648_ = !lean_is_exclusive(v_x_1629_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v_x_1629_, 0);
lean_dec(v_unused_1649_);
v___x_1641_ = v_x_1629_;
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_x_1629_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1628_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1650_, v_x_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1654_, lean_object* v_requestStream_1655_, lean_object* v_keepAliveTimeout_1656_, lean_object* v_currentTimeout_1657_, lean_object* v_headerTimeout_1658_, lean_object* v_response_1659_, lean_object* v_respStream_1660_, lean_object* v_expectData_1661_, uint8_t v_handlerDispatched_1662_, lean_object* v_____r_1663_){
_start:
{
uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1665_ = 0;
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1667_, 0, v_machine_1654_);
lean_ctor_set(v___x_1667_, 1, v_requestStream_1655_);
lean_ctor_set(v___x_1667_, 2, v_keepAliveTimeout_1656_);
lean_ctor_set(v___x_1667_, 3, v_currentTimeout_1657_);
lean_ctor_set(v___x_1667_, 4, v_headerTimeout_1658_);
lean_ctor_set(v___x_1667_, 5, v_response_1659_);
lean_ctor_set(v___x_1667_, 6, v_respStream_1660_);
lean_ctor_set(v___x_1667_, 7, v_expectData_1661_);
lean_ctor_set(v___x_1667_, 8, v___x_1666_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*9, v___x_1665_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*9 + 1, v_handlerDispatched_1662_);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1671_, lean_object* v_requestStream_1672_, lean_object* v_keepAliveTimeout_1673_, lean_object* v_currentTimeout_1674_, lean_object* v_headerTimeout_1675_, lean_object* v_response_1676_, lean_object* v_respStream_1677_, lean_object* v_expectData_1678_, lean_object* v_handlerDispatched_1679_, lean_object* v_____r_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_handlerDispatched_boxed_1682_; lean_object* v_res_1683_; 
v_handlerDispatched_boxed_1682_ = lean_unbox(v_handlerDispatched_1679_);
v_res_1683_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1671_, v_requestStream_1672_, v_keepAliveTimeout_1673_, v_currentTimeout_1674_, v_headerTimeout_1675_, v_response_1676_, v_respStream_1677_, v_expectData_1678_, v_handlerDispatched_boxed_1682_, v_____r_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1684_, lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v___f_1684_);
v_a_1687_ = lean_ctor_get(v_x_1685_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_x_1685_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1689_ = v_x_1685_;
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v_x_1685_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1697_; 
v_a_1696_ = lean_ctor_get(v_x_1685_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v_x_1685_, 1);
v___x_1697_ = lean_apply_2(v___f_1684_, v_a_1696_, lean_box(0));
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1698_, lean_object* v_x_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1698_, v_x_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1702_, lean_object* v___f_1703_, lean_object* v___f_1704_, lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v___f_1704_);
lean_dec_ref(v___f_1703_);
lean_dec_ref(v_requestStream_1702_);
v_a_1707_ = lean_ctor_get(v_x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v_x_1705_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v_x_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1716_; uint8_t v___x_1717_; 
v_a_1716_ = lean_ctor_get(v_x_1705_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v_x_1705_, 1);
v___x_1717_ = lean_unbox(v_a_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v___f_1704_);
v___x_1718_ = l_Std_Http_Body_Stream_close(v_requestStream_1702_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_unbox(v_a_1716_);
lean_dec(v_a_1716_);
v___x_1721_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1719_, v___x_1720_, v___x_1718_, v___f_1703_);
return v___x_1721_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_a_1716_);
lean_dec_ref(v___f_1703_);
lean_dec_ref(v_requestStream_1702_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_apply_2(v___f_1704_, v___x_1722_, lean_box(0));
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1724_, lean_object* v___f_1725_, lean_object* v___f_1726_, lean_object* v_x_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1724_, v___f_1725_, v___f_1726_, v_x_1727_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1730_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1731_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; 
v___x_1737_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1738_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1739_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1739_, 0, v___f_1738_);
lean_closure_set(v___f_1739_, 1, v___x_1737_);
return v___f_1739_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___f_1750_; 
v___x_1748_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1749_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1750_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1750_, 0, v___f_1749_);
lean_closure_set(v___f_1750_, 1, v___x_1748_);
return v___f_1750_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1751_; lean_object* v___x_1752_; 
v___f_1751_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1752_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1752_, 0, lean_box(0));
lean_closure_set(v___x_1752_, 1, lean_box(0));
lean_closure_set(v___x_1752_, 2, lean_box(0));
lean_closure_set(v___x_1752_, 3, v___f_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1753_, lean_object* v___f_1754_, lean_object* v_x_1755_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v___f_1754_);
lean_dec_ref(v___y_1753_);
v_a_1757_ = lean_ctor_get(v_x_1755_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_x_1755_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1759_ = v_x_1755_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v_x_1755_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
else
{
lean_object* v_machine_1766_; lean_object* v_requestStream_1767_; lean_object* v_keepAliveTimeout_1768_; lean_object* v_currentTimeout_1769_; lean_object* v_headerTimeout_1770_; lean_object* v_response_1771_; lean_object* v_respStream_1772_; lean_object* v_expectData_1773_; uint8_t v_handlerDispatched_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___f_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_4928__overap_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___f_1783_; lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; 
lean_dec_ref_known(v_x_1755_, 1);
v_machine_1766_ = lean_ctor_get(v___y_1753_, 0);
lean_inc_ref(v_machine_1766_);
v_requestStream_1767_ = lean_ctor_get(v___y_1753_, 1);
lean_inc_ref_n(v_requestStream_1767_, 3);
v_keepAliveTimeout_1768_ = lean_ctor_get(v___y_1753_, 2);
lean_inc(v_keepAliveTimeout_1768_);
v_currentTimeout_1769_ = lean_ctor_get(v___y_1753_, 3);
lean_inc(v_currentTimeout_1769_);
v_headerTimeout_1770_ = lean_ctor_get(v___y_1753_, 4);
lean_inc(v_headerTimeout_1770_);
v_response_1771_ = lean_ctor_get(v___y_1753_, 5);
lean_inc_ref(v_response_1771_);
v_respStream_1772_ = lean_ctor_get(v___y_1753_, 6);
lean_inc(v_respStream_1772_);
v_expectData_1773_ = lean_ctor_get(v___y_1753_, 7);
lean_inc(v_expectData_1773_);
v_handlerDispatched_1774_ = lean_ctor_get_uint8(v___y_1753_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1753_);
v___x_1775_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1776_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1777_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1778_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1779_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1779_, 0, lean_box(0));
lean_closure_set(v___x_1779_, 1, lean_box(0));
lean_closure_set(v___x_1779_, 2, v___x_1775_);
lean_closure_set(v___x_1779_, 3, lean_box(0));
lean_closure_set(v___x_1779_, 4, lean_box(0));
lean_closure_set(v___x_1779_, 5, v___x_1778_);
lean_closure_set(v___x_1779_, 6, v___f_1754_);
v___x_4928__overap_1780_ = l_Std_Mutex_atomically___redArg(v___x_1775_, v___f_1776_, v___f_1777_, v_requestStream_1767_, v___x_1779_);
v___x_1781_ = lean_apply_1(v___x_4928__overap_1780_, lean_box(0));
v___x_1782_ = lean_box(v_handlerDispatched_1774_);
v___f_1783_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1783_, 0, v_machine_1766_);
lean_closure_set(v___f_1783_, 1, v_requestStream_1767_);
lean_closure_set(v___f_1783_, 2, v_keepAliveTimeout_1768_);
lean_closure_set(v___f_1783_, 3, v_currentTimeout_1769_);
lean_closure_set(v___f_1783_, 4, v_headerTimeout_1770_);
lean_closure_set(v___f_1783_, 5, v_response_1771_);
lean_closure_set(v___f_1783_, 6, v_respStream_1772_);
lean_closure_set(v___f_1783_, 7, v_expectData_1773_);
lean_closure_set(v___f_1783_, 8, v___x_1782_);
lean_inc_ref(v___f_1783_);
v___f_1784_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1784_, 0, v___f_1783_);
v___f_1785_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1785_, 0, v_requestStream_1767_);
lean_closure_set(v___f_1785_, 1, v___f_1784_);
lean_closure_set(v___f_1785_, 2, v___f_1783_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = 0;
v___x_1788_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1786_, v___x_1787_, v___x_1781_, v___f_1785_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1789_, lean_object* v___f_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1789_, v___f_1790_, v_x_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1794_, lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v___y_1794_);
v_a_1797_ = lean_ctor_get(v_x_1795_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1799_ = v_x_1795_;
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v_x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
else
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1814_; 
v_isSharedCheck_1814_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_x_1795_, 0);
lean_dec(v_unused_1815_);
v___x_1807_ = v_x_1795_;
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v_x_1795_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___y_1794_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1816_, v_x_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1820_, lean_object* v___f_1821_, lean_object* v___y_1822_, lean_object* v_x_1823_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___f_1821_);
lean_dec_ref(v_requestStream_1820_);
v_a_1825_ = lean_ctor_get(v_x_1823_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_x_1823_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1827_ = v_x_1823_;
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v_x_1823_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1833_;
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
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1825_);
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
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1848_; 
v_a_1834_ = lean_ctor_get(v_x_1823_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_x_1823_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1836_ = v_x_1823_;
v_isShared_1837_ = v_isSharedCheck_1848_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v_x_1823_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1848_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_unbox(v_a_1834_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1836_);
lean_dec_ref(v___y_1822_);
v___x_1839_ = l_Std_Http_Body_Stream_close(v_requestStream_1820_);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_unbox(v_a_1834_);
lean_dec(v_a_1834_);
v___x_1842_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1840_, v___x_1841_, v___x_1839_, v___f_1821_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
lean_dec(v_a_1834_);
lean_dec_ref(v___f_1821_);
lean_dec_ref(v_requestStream_1820_);
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___y_1822_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1843_);
v___x_1845_ = v___x_1836_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1849_, lean_object* v___f_1850_, lean_object* v___y_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1849_, v___f_1850_, v___y_1851_, v_x_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1855_, lean_object* v_machine_1856_, lean_object* v_a_1857_, uint8_t v_requiresData_1858_, lean_object* v_expectData_1859_, lean_object* v_pendingHead_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_pendingHead_1860_);
lean_dec(v_expectData_1859_);
lean_dec_ref(v_a_1857_);
lean_dec_ref(v_machine_1856_);
v_a_1863_ = lean_ctor_get(v_x_1861_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_x_1861_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v_x_1861_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v_x_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1886_; 
v_a_1872_ = lean_ctor_get(v_x_1861_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_x_1861_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1874_ = v_x_1861_;
v_isShared_1875_ = v_isSharedCheck_1886_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_x_1861_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1886_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_keepAliveTimeout_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v_keepAliveTimeout_1876_ = lean_ctor_get(v_config_1855_, 5);
lean_inc_n(v_keepAliveTimeout_1876_, 2);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_keepAliveTimeout_1876_);
v___x_1878_ = lean_box(0);
v___x_1879_ = 0;
v___x_1880_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1880_, 0, v_machine_1856_);
lean_ctor_set(v___x_1880_, 1, v_a_1857_);
lean_ctor_set(v___x_1880_, 2, v___x_1877_);
lean_ctor_set(v___x_1880_, 3, v_keepAliveTimeout_1876_);
lean_ctor_set(v___x_1880_, 4, v___x_1878_);
lean_ctor_set(v___x_1880_, 5, v_a_1872_);
lean_ctor_set(v___x_1880_, 6, v___x_1878_);
lean_ctor_set(v___x_1880_, 7, v_expectData_1859_);
lean_ctor_set(v___x_1880_, 8, v_pendingHead_1860_);
lean_ctor_set_uint8(v___x_1880_, sizeof(void*)*9, v_requiresData_1858_);
lean_ctor_set_uint8(v___x_1880_, sizeof(void*)*9 + 1, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1887_, lean_object* v_machine_1888_, lean_object* v_a_1889_, lean_object* v_requiresData_1890_, lean_object* v_expectData_1891_, lean_object* v_pendingHead_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v_requiresData_boxed_1895_; lean_object* v_res_1896_; 
v_requiresData_boxed_1895_ = lean_unbox(v_requiresData_1890_);
v_res_1896_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1887_, v_machine_1888_, v_a_1889_, v_requiresData_boxed_1895_, v_expectData_1891_, v_pendingHead_1892_, v_x_1893_);
lean_dec_ref(v_config_1887_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1897_, lean_object* v_machine_1898_, uint8_t v_requiresData_1899_, lean_object* v_expectData_1900_, lean_object* v_pendingHead_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_pendingHead_1901_);
lean_dec(v_expectData_1900_);
lean_dec_ref(v_machine_1898_);
lean_dec_ref(v_config_1897_);
v_a_1904_ = lean_ctor_get(v_x_1902_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1906_ = v_x_1902_;
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v_x_1902_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1928_; 
v_a_1913_ = lean_ctor_get(v_x_1902_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1915_ = v_x_1902_;
v_isShared_1916_ = v_isSharedCheck_1928_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v_x_1902_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1928_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___f_1920_; lean_object* v___x_1922_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = l_Std_CloseableChannel_new___redArg(v___x_1917_);
v___x_1919_ = lean_box(v_requiresData_1899_);
v___f_1920_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1920_, 0, v_config_1897_);
lean_closure_set(v___f_1920_, 1, v_machine_1898_);
lean_closure_set(v___f_1920_, 2, v_a_1913_);
lean_closure_set(v___f_1920_, 3, v___x_1919_);
lean_closure_set(v___f_1920_, 4, v_expectData_1900_);
lean_closure_set(v___f_1920_, 5, v_pendingHead_1901_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1918_);
v___x_1922_ = v___x_1915_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1918_);
v___x_1922_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = 0;
v___x_1926_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1924_, v___x_1925_, v___x_1923_, v___f_1920_);
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1929_, lean_object* v_machine_1930_, lean_object* v_requiresData_1931_, lean_object* v_expectData_1932_, lean_object* v_pendingHead_1933_, lean_object* v_x_1934_, lean_object* v___y_1935_){
_start:
{
uint8_t v_requiresData_boxed_1936_; lean_object* v_res_1937_; 
v_requiresData_boxed_1936_ = lean_unbox(v_requiresData_1931_);
v_res_1937_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1929_, v_machine_1930_, v_requiresData_boxed_1936_, v_expectData_1932_, v_pendingHead_1933_, v_x_1934_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1938_, lean_object* v_____r_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1941_ = l_Std_Http_Body_mkStream();
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = 0;
v___x_1944_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1942_, v___x_1943_, v___x_1941_, v___f_1938_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1945_, lean_object* v_____r_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1945_, v_____r_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1949_, lean_object* v_val_1950_, lean_object* v___f_1951_, lean_object* v___f_1952_, lean_object* v_x_1953_){
_start:
{
if (lean_obj_tag(v_x_1953_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___f_1952_);
lean_dec_ref(v___f_1951_);
lean_dec(v_val_1950_);
lean_dec_ref(v_close_1949_);
v_a_1955_ = lean_ctor_get(v_x_1953_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_x_1953_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1957_ = v_x_1953_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v_x_1953_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1955_);
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
else
{
lean_object* v_a_1964_; uint8_t v___x_1965_; 
v_a_1964_ = lean_ctor_get(v_x_1953_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v_x_1953_, 1);
v___x_1965_ = lean_unbox(v_a_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v___f_1952_);
v___x_1966_ = lean_apply_2(v_close_1949_, v_val_1950_, lean_box(0));
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_unbox(v_a_1964_);
lean_dec(v_a_1964_);
v___x_1969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1967_, v___x_1968_, v___x_1966_, v___f_1951_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_a_1964_);
lean_dec_ref(v___f_1951_);
lean_dec(v_val_1950_);
lean_dec_ref(v_close_1949_);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_apply_2(v___f_1952_, v___x_1970_, lean_box(0));
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1972_, lean_object* v_val_1973_, lean_object* v___f_1974_, lean_object* v___f_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1972_, v_val_1973_, v___f_1974_, v___f_1975_, v_x_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1979_, lean_object* v_inst_1980_, lean_object* v___f_1981_, lean_object* v___f_1982_, lean_object* v_____r_1983_){
_start:
{
if (lean_obj_tag(v_respStream_1979_) == 1)
{
lean_object* v_val_1985_; lean_object* v_close_1986_; lean_object* v_isClosed_1987_; lean_object* v___x_1988_; lean_object* v___f_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; 
v_val_1985_ = lean_ctor_get(v_respStream_1979_, 0);
lean_inc_n(v_val_1985_, 2);
lean_dec_ref_known(v_respStream_1979_, 1);
v_close_1986_ = lean_ctor_get(v_inst_1980_, 1);
lean_inc_ref(v_close_1986_);
v_isClosed_1987_ = lean_ctor_get(v_inst_1980_, 2);
lean_inc_ref(v_isClosed_1987_);
lean_dec_ref(v_inst_1980_);
v___x_1988_ = lean_apply_2(v_isClosed_1987_, v_val_1985_, lean_box(0));
v___f_1989_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1989_, 0, v_close_1986_);
lean_closure_set(v___f_1989_, 1, v_val_1985_);
lean_closure_set(v___f_1989_, 2, v___f_1981_);
lean_closure_set(v___f_1989_, 3, v___f_1982_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = 0;
v___x_1992_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1990_, v___x_1991_, v___x_1988_, v___f_1989_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec_ref(v___f_1981_);
lean_dec_ref(v_inst_1980_);
lean_dec(v_respStream_1979_);
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_apply_2(v___f_1982_, v___x_1993_, lean_box(0));
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1995_, lean_object* v_inst_1996_, lean_object* v___f_1997_, lean_object* v___f_1998_, lean_object* v_____r_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1995_, v_inst_1996_, v___f_1997_, v___f_1998_, v_____r_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2002_, lean_object* v_keepAliveTimeout_2003_, lean_object* v_currentTimeout_2004_, lean_object* v_headerTimeout_2005_, lean_object* v_response_2006_, lean_object* v_respStream_2007_, uint8_t v_requiresData_2008_, lean_object* v_expectData_2009_, uint8_t v_handlerDispatched_2010_, lean_object* v_pendingHead_2011_, lean_object* v_x_2012_){
_start:
{
if (lean_obj_tag(v_x_2012_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_pendingHead_2011_);
lean_dec(v_expectData_2009_);
lean_dec(v_respStream_2007_);
lean_dec_ref(v_response_2006_);
lean_dec(v_headerTimeout_2005_);
lean_dec(v_currentTimeout_2004_);
lean_dec(v_keepAliveTimeout_2003_);
lean_dec_ref(v_requestStream_2002_);
v_a_2014_ = lean_ctor_get(v_x_2012_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_2012_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2016_ = v_x_2012_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v_x_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2044_; 
v_a_2023_ = lean_ctor_get(v_x_2012_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_x_2012_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2025_ = v_x_2012_;
v_isShared_2026_ = v_isSharedCheck_2044_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v_x_2012_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2044_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v_snd_2027_; uint8_t v___x_2028_; 
v_snd_2027_ = lean_ctor_get(v_a_2023_, 1);
v___x_2028_ = lean_unbox(v_snd_2027_);
if (v___x_2028_ == 0)
{
lean_object* v_fst_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v_fst_2029_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_fst_2029_);
lean_dec(v_a_2023_);
v___x_2030_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2030_, 0, v_fst_2029_);
lean_ctor_set(v___x_2030_, 1, v_requestStream_2002_);
lean_ctor_set(v___x_2030_, 2, v_keepAliveTimeout_2003_);
lean_ctor_set(v___x_2030_, 3, v_currentTimeout_2004_);
lean_ctor_set(v___x_2030_, 4, v_headerTimeout_2005_);
lean_ctor_set(v___x_2030_, 5, v_response_2006_);
lean_ctor_set(v___x_2030_, 6, v_respStream_2007_);
lean_ctor_set(v___x_2030_, 7, v_expectData_2009_);
lean_ctor_set(v___x_2030_, 8, v_pendingHead_2011_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*9, v_requiresData_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*9 + 1, v_handlerDispatched_2010_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2031_);
v___x_2033_ = v___x_2025_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
else
{
lean_object* v_fst_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_dec(v_pendingHead_2011_);
v_fst_2036_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_fst_2036_);
lean_dec(v_a_2023_);
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2038_, 0, v_fst_2036_);
lean_ctor_set(v___x_2038_, 1, v_requestStream_2002_);
lean_ctor_set(v___x_2038_, 2, v_keepAliveTimeout_2003_);
lean_ctor_set(v___x_2038_, 3, v_currentTimeout_2004_);
lean_ctor_set(v___x_2038_, 4, v_headerTimeout_2005_);
lean_ctor_set(v___x_2038_, 5, v_response_2006_);
lean_ctor_set(v___x_2038_, 6, v_respStream_2007_);
lean_ctor_set(v___x_2038_, 7, v_expectData_2009_);
lean_ctor_set(v___x_2038_, 8, v___x_2037_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*9, v_requiresData_2008_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*9 + 1, v_handlerDispatched_2010_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2039_);
v___x_2041_ = v___x_2025_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2045_, lean_object* v_keepAliveTimeout_2046_, lean_object* v_currentTimeout_2047_, lean_object* v_headerTimeout_2048_, lean_object* v_response_2049_, lean_object* v_respStream_2050_, lean_object* v_requiresData_2051_, lean_object* v_expectData_2052_, lean_object* v_handlerDispatched_2053_, lean_object* v_pendingHead_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_){
_start:
{
uint8_t v_requiresData_boxed_2057_; uint8_t v_handlerDispatched_boxed_2058_; lean_object* v_res_2059_; 
v_requiresData_boxed_2057_ = lean_unbox(v_requiresData_2051_);
v_handlerDispatched_boxed_2058_ = lean_unbox(v_handlerDispatched_2053_);
v_res_2059_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2045_, v_keepAliveTimeout_2046_, v_currentTimeout_2047_, v_headerTimeout_2048_, v_response_2049_, v_respStream_2050_, v_requiresData_boxed_2057_, v_expectData_2052_, v_handlerDispatched_boxed_2058_, v_pendingHead_2054_, v_x_2055_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2072_, lean_object* v_inst_2073_, lean_object* v___f_2074_, lean_object* v_handler_2075_, lean_object* v___f_2076_, lean_object* v___f_2077_, lean_object* v_inst_2078_, lean_object* v_connectionContext_2079_, lean_object* v_a_2080_, lean_object* v_x_2081_, lean_object* v___y_2082_){
_start:
{
switch(lean_obj_tag(v_a_2080_))
{
case 0:
{
lean_object* v_head_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_connectionContext_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v___f_2077_);
lean_dec_ref(v___f_2076_);
lean_dec(v_handler_2075_);
lean_dec_ref(v___f_2074_);
lean_dec_ref(v_inst_2073_);
v_head_2084_ = lean_ctor_get(v_a_2080_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2086_ = v_a_2080_;
v_isShared_2087_ = v_isSharedCheck_2127_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_head_2084_);
lean_dec(v_a_2080_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2127_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_machine_2088_; lean_object* v_requestStream_2089_; lean_object* v_response_2090_; lean_object* v_respStream_2091_; uint8_t v_requiresData_2092_; lean_object* v_expectData_2093_; uint8_t v_handlerDispatched_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2122_; 
v_machine_2088_ = lean_ctor_get(v___y_2082_, 0);
v_requestStream_2089_ = lean_ctor_get(v___y_2082_, 1);
v_response_2090_ = lean_ctor_get(v___y_2082_, 5);
v_respStream_2091_ = lean_ctor_get(v___y_2082_, 6);
v_requiresData_2092_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*9);
v_expectData_2093_ = lean_ctor_get(v___y_2082_, 7);
v_handlerDispatched_2094_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*9 + 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___y_2082_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; lean_object* v_unused_2124_; lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2123_ = lean_ctor_get(v___y_2082_, 8);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v___y_2082_, 4);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v___y_2082_, 3);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v___y_2082_, 2);
lean_dec(v_unused_2126_);
v___x_2096_ = v___y_2082_;
v_isShared_2097_ = v_isSharedCheck_2122_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_expectData_2093_);
lean_inc(v_respStream_2091_);
lean_inc(v_response_2090_);
lean_inc(v_requestStream_2089_);
lean_inc(v_machine_2088_);
lean_dec(v___y_2082_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2122_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_lingeringTimeout_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v_lingeringTimeout_2098_ = lean_ctor_get(v_config_2072_, 4);
lean_inc(v_lingeringTimeout_2098_);
lean_dec_ref(v_config_2072_);
v___x_2099_ = lean_box(0);
lean_inc(v_head_2084_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set_tag(v___x_2086_, 1);
v___x_2101_ = v___x_2086_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_head_2084_);
v___x_2101_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
lean_inc_ref(v_requestStream_2089_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 8, v___x_2101_);
lean_ctor_set(v___x_2096_, 4, v___x_2099_);
lean_ctor_set(v___x_2096_, 3, v_lingeringTimeout_2098_);
lean_ctor_set(v___x_2096_, 2, v___x_2099_);
v___x_2103_ = v___x_2096_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_machine_2088_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_requestStream_2089_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_lingeringTimeout_2098_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2120_, 5, v_response_2090_);
lean_ctor_set(v_reuseFailAlloc_2120_, 6, v_respStream_2091_);
lean_ctor_set(v_reuseFailAlloc_2120_, 7, v_expectData_2093_);
lean_ctor_set(v_reuseFailAlloc_2120_, 8, v___x_2101_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*9, v_requiresData_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*9 + 1, v_handlerDispatched_2094_);
v___x_2103_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
uint8_t v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = 0;
v___x_2105_ = 1;
v___x_2106_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2104_, v_head_2084_, v___x_2105_);
lean_dec(v_head_2084_);
if (lean_obj_tag(v___x_2106_) == 1)
{
lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___f_2109_; lean_object* v___f_2110_; lean_object* v___x_5121__overap_2111_; lean_object* v___x_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v___f_2107_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2107_, 0, v___x_2106_);
v___x_2108_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2109_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2110_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5121__overap_2111_ = l_Std_Mutex_atomically___redArg(v___x_2108_, v___f_2109_, v___f_2110_, v_requestStream_2089_, v___f_2107_);
v___x_2112_ = lean_apply_1(v___x_5121__overap_2111_, lean_box(0));
v___f_2113_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2113_, 0, v___x_2103_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = 0;
v___x_2116_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2114_, v___x_2115_, v___x_2112_, v___f_2113_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec(v___x_2106_);
lean_dec_ref(v_requestStream_2089_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2103_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_connectionContext_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v___f_2077_);
lean_dec_ref(v___f_2076_);
lean_dec(v_handler_2075_);
lean_dec_ref(v___f_2074_);
lean_dec_ref(v_inst_2073_);
lean_dec_ref(v_config_2072_);
v_size_2128_ = lean_ctor_get(v_a_2080_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2130_ = v_a_2080_;
v_isShared_2131_ = v_isSharedCheck_2155_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_size_2128_);
lean_dec(v_a_2080_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2155_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_machine_2132_; lean_object* v_requestStream_2133_; lean_object* v_keepAliveTimeout_2134_; lean_object* v_currentTimeout_2135_; lean_object* v_headerTimeout_2136_; lean_object* v_response_2137_; lean_object* v_respStream_2138_; uint8_t v_handlerDispatched_2139_; lean_object* v_pendingHead_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2153_; 
v_machine_2132_ = lean_ctor_get(v___y_2082_, 0);
v_requestStream_2133_ = lean_ctor_get(v___y_2082_, 1);
v_keepAliveTimeout_2134_ = lean_ctor_get(v___y_2082_, 2);
v_currentTimeout_2135_ = lean_ctor_get(v___y_2082_, 3);
v_headerTimeout_2136_ = lean_ctor_get(v___y_2082_, 4);
v_response_2137_ = lean_ctor_get(v___y_2082_, 5);
v_respStream_2138_ = lean_ctor_get(v___y_2082_, 6);
v_handlerDispatched_2139_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*9 + 1);
v_pendingHead_2140_ = lean_ctor_get(v___y_2082_, 8);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___y_2082_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; 
v_unused_2154_ = lean_ctor_get(v___y_2082_, 7);
lean_dec(v_unused_2154_);
v___x_2142_ = v___y_2082_;
v_isShared_2143_ = v_isSharedCheck_2153_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_pendingHead_2140_);
lean_inc(v_respStream_2138_);
lean_inc(v_response_2137_);
lean_inc(v_headerTimeout_2136_);
lean_inc(v_currentTimeout_2135_);
lean_inc(v_keepAliveTimeout_2134_);
lean_inc(v_requestStream_2133_);
lean_inc(v_machine_2132_);
lean_dec(v___y_2082_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2153_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
uint8_t v___x_2144_; lean_object* v___x_2146_; 
v___x_2144_ = 1;
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 7, v_size_2128_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_machine_2132_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_requestStream_2133_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_keepAliveTimeout_2134_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_currentTimeout_2135_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_headerTimeout_2136_);
lean_ctor_set(v_reuseFailAlloc_2152_, 5, v_response_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 6, v_respStream_2138_);
lean_ctor_set(v_reuseFailAlloc_2152_, 7, v_size_2128_);
lean_ctor_set(v_reuseFailAlloc_2152_, 8, v_pendingHead_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*9 + 1, v_handlerDispatched_2139_);
v___x_2146_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*9, v___x_2144_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2146_);
v___x_2148_ = v___x_2130_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2156_; lean_object* v_onFailure_2157_; lean_object* v___f_2158_; lean_object* v___y_2160_; 
lean_dec_ref(v_connectionContext_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v___f_2077_);
lean_dec_ref(v___f_2076_);
lean_dec_ref(v_config_2072_);
v_err_2156_ = lean_ctor_get(v_a_2080_, 0);
lean_inc(v_err_2156_);
lean_dec_ref_known(v_a_2080_, 1);
v_onFailure_2157_ = lean_ctor_get(v_inst_2073_, 2);
lean_inc_ref(v_onFailure_2157_);
lean_dec_ref(v_inst_2073_);
v___f_2158_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2158_, 0, v___y_2082_);
lean_closure_set(v___f_2158_, 1, v___f_2074_);
switch(lean_obj_tag(v_err_2156_))
{
case 0:
{
lean_object* v___x_2166_; 
v___x_2166_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2160_ = v___x_2166_;
goto v___jp_2159_;
}
case 1:
{
lean_object* v___x_2167_; 
v___x_2167_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2160_ = v___x_2167_;
goto v___jp_2159_;
}
case 2:
{
lean_object* v___x_2168_; 
v___x_2168_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2160_ = v___x_2168_;
goto v___jp_2159_;
}
case 3:
{
lean_object* v___x_2169_; 
v___x_2169_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2160_ = v___x_2169_;
goto v___jp_2159_;
}
case 4:
{
lean_object* v___x_2170_; 
v___x_2170_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2160_ = v___x_2170_;
goto v___jp_2159_;
}
case 5:
{
lean_object* v___x_2171_; 
v___x_2171_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2160_ = v___x_2171_;
goto v___jp_2159_;
}
case 6:
{
lean_object* v___x_2172_; 
v___x_2172_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2160_ = v___x_2172_;
goto v___jp_2159_;
}
case 7:
{
lean_object* v___x_2173_; 
v___x_2173_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2160_ = v___x_2173_;
goto v___jp_2159_;
}
case 8:
{
lean_object* v___x_2174_; 
v___x_2174_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2160_ = v___x_2174_;
goto v___jp_2159_;
}
case 9:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2160_ = v___x_2175_;
goto v___jp_2159_;
}
case 10:
{
lean_object* v___x_2176_; 
v___x_2176_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2160_ = v___x_2176_;
goto v___jp_2159_;
}
default: 
{
lean_object* v_message_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_message_2177_ = lean_ctor_get(v_err_2156_, 0);
lean_inc_ref(v_message_2177_);
lean_dec_ref_known(v_err_2156_, 1);
v___x_2178_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2179_ = lean_string_append(v___x_2178_, v_message_2177_);
lean_dec_ref(v_message_2177_);
v___y_2160_ = v___x_2179_;
goto v___jp_2159_;
}
}
v___jp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2161_ = lean_mk_io_user_error(v___y_2160_);
v___x_2162_ = lean_apply_3(v_onFailure_2157_, v_handler_2075_, v___x_2161_, lean_box(0));
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = 0;
v___x_2165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2163_, v___x_2164_, v___x_2162_, v___f_2158_);
return v___x_2165_;
}
}
case 4:
{
lean_object* v_requestStream_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_5177__overap_2186_; lean_object* v___x_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v_connectionContext_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v___f_2077_);
lean_dec(v_handler_2075_);
lean_dec_ref(v___f_2074_);
lean_dec_ref(v_inst_2073_);
lean_dec_ref(v_config_2072_);
v_requestStream_2180_ = lean_ctor_get(v___y_2082_, 1);
lean_inc_ref_n(v_requestStream_2180_, 2);
v___x_2181_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2182_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2183_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2184_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2185_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2185_, 0, lean_box(0));
lean_closure_set(v___x_2185_, 1, lean_box(0));
lean_closure_set(v___x_2185_, 2, v___x_2181_);
lean_closure_set(v___x_2185_, 3, lean_box(0));
lean_closure_set(v___x_2185_, 4, lean_box(0));
lean_closure_set(v___x_2185_, 5, v___x_2184_);
lean_closure_set(v___x_2185_, 6, v___f_2076_);
v___x_5177__overap_2186_ = l_Std_Mutex_atomically___redArg(v___x_2181_, v___f_2182_, v___f_2183_, v_requestStream_2180_, v___x_2185_);
v___x_2187_ = lean_apply_1(v___x_5177__overap_2186_, lean_box(0));
lean_inc_ref(v___y_2082_);
v___f_2188_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2188_, 0, v___y_2082_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2189_, 0, v_requestStream_2180_);
lean_closure_set(v___f_2189_, 1, v___f_2188_);
lean_closure_set(v___f_2189_, 2, v___y_2082_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = 0;
v___x_2192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2190_, v___x_2191_, v___x_2187_, v___f_2189_);
return v___x_2192_;
}
case 6:
{
lean_object* v_machine_2193_; lean_object* v_requestStream_2194_; lean_object* v_respStream_2195_; uint8_t v_requiresData_2196_; lean_object* v_expectData_2197_; lean_object* v_pendingHead_2198_; lean_object* v___x_2199_; lean_object* v___f_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_5198__overap_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___f_2207_; lean_object* v___f_2208_; lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v___f_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v_connectionContext_2079_);
lean_dec_ref(v___f_2076_);
lean_dec(v_handler_2075_);
lean_dec_ref(v___f_2074_);
lean_dec_ref(v_inst_2073_);
v_machine_2193_ = lean_ctor_get(v___y_2082_, 0);
lean_inc_ref(v_machine_2193_);
v_requestStream_2194_ = lean_ctor_get(v___y_2082_, 1);
lean_inc_ref_n(v_requestStream_2194_, 2);
v_respStream_2195_ = lean_ctor_get(v___y_2082_, 6);
lean_inc(v_respStream_2195_);
v_requiresData_2196_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*9);
v_expectData_2197_ = lean_ctor_get(v___y_2082_, 7);
lean_inc(v_expectData_2197_);
v_pendingHead_2198_ = lean_ctor_get(v___y_2082_, 8);
lean_inc(v_pendingHead_2198_);
lean_dec_ref(v___y_2082_);
v___x_2199_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2200_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2201_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2202_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2203_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2203_, 0, lean_box(0));
lean_closure_set(v___x_2203_, 1, lean_box(0));
lean_closure_set(v___x_2203_, 2, v___x_2199_);
lean_closure_set(v___x_2203_, 3, lean_box(0));
lean_closure_set(v___x_2203_, 4, lean_box(0));
lean_closure_set(v___x_2203_, 5, v___x_2202_);
lean_closure_set(v___x_2203_, 6, v___f_2077_);
v___x_5198__overap_2204_ = l_Std_Mutex_atomically___redArg(v___x_2199_, v___f_2200_, v___f_2201_, v_requestStream_2194_, v___x_2203_);
v___x_2205_ = lean_apply_1(v___x_5198__overap_2204_, lean_box(0));
v___x_2206_ = lean_box(v_requiresData_2196_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2207_, 0, v_config_2072_);
lean_closure_set(v___f_2207_, 1, v_machine_2193_);
lean_closure_set(v___f_2207_, 2, v___x_2206_);
lean_closure_set(v___f_2207_, 3, v_expectData_2197_);
lean_closure_set(v___f_2207_, 4, v_pendingHead_2198_);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2208_, 0, v___f_2207_);
lean_inc_ref(v___f_2208_);
v___f_2209_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2209_, 0, v___f_2208_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2210_, 0, v_respStream_2195_);
lean_closure_set(v___f_2210_, 1, v_inst_2078_);
lean_closure_set(v___f_2210_, 2, v___f_2209_);
lean_closure_set(v___f_2210_, 3, v___f_2208_);
lean_inc_ref(v___f_2210_);
v___f_2211_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2211_, 0, v___f_2210_);
v___f_2212_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2212_, 0, v_requestStream_2194_);
lean_closure_set(v___f_2212_, 1, v___f_2211_);
lean_closure_set(v___f_2212_, 2, v___f_2210_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = 0;
v___x_2215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2213_, v___x_2214_, v___x_2205_, v___f_2212_);
return v___x_2215_;
}
case 7:
{
lean_object* v_pendingHead_2216_; 
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v___f_2077_);
lean_dec_ref(v___f_2076_);
lean_dec_ref(v___f_2074_);
v_pendingHead_2216_ = lean_ctor_get(v___y_2082_, 8);
if (lean_obj_tag(v_pendingHead_2216_) == 1)
{
lean_object* v_machine_2217_; lean_object* v_requestStream_2218_; lean_object* v_keepAliveTimeout_2219_; lean_object* v_currentTimeout_2220_; lean_object* v_headerTimeout_2221_; lean_object* v_response_2222_; lean_object* v_respStream_2223_; uint8_t v_requiresData_2224_; lean_object* v_expectData_2225_; uint8_t v_handlerDispatched_2226_; lean_object* v_val_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___f_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; 
lean_inc_ref(v_pendingHead_2216_);
v_machine_2217_ = lean_ctor_get(v___y_2082_, 0);
lean_inc_ref(v_machine_2217_);
v_requestStream_2218_ = lean_ctor_get(v___y_2082_, 1);
lean_inc_ref(v_requestStream_2218_);
v_keepAliveTimeout_2219_ = lean_ctor_get(v___y_2082_, 2);
lean_inc(v_keepAliveTimeout_2219_);
v_currentTimeout_2220_ = lean_ctor_get(v___y_2082_, 3);
lean_inc(v_currentTimeout_2220_);
v_headerTimeout_2221_ = lean_ctor_get(v___y_2082_, 4);
lean_inc(v_headerTimeout_2221_);
v_response_2222_ = lean_ctor_get(v___y_2082_, 5);
lean_inc_ref(v_response_2222_);
v_respStream_2223_ = lean_ctor_get(v___y_2082_, 6);
lean_inc(v_respStream_2223_);
v_requiresData_2224_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*9);
v_expectData_2225_ = lean_ctor_get(v___y_2082_, 7);
lean_inc(v_expectData_2225_);
v_handlerDispatched_2226_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2082_);
v_val_2227_ = lean_ctor_get(v_pendingHead_2216_, 0);
lean_inc(v_val_2227_);
v___x_2228_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2073_, v_handler_2075_, v_machine_2217_, v_val_2227_, v_config_2072_, v_connectionContext_2079_);
v___x_2229_ = lean_box(v_requiresData_2224_);
v___x_2230_ = lean_box(v_handlerDispatched_2226_);
v___f_2231_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2231_, 0, v_requestStream_2218_);
lean_closure_set(v___f_2231_, 1, v_keepAliveTimeout_2219_);
lean_closure_set(v___f_2231_, 2, v_currentTimeout_2220_);
lean_closure_set(v___f_2231_, 3, v_headerTimeout_2221_);
lean_closure_set(v___f_2231_, 4, v_response_2222_);
lean_closure_set(v___f_2231_, 5, v_respStream_2223_);
lean_closure_set(v___f_2231_, 6, v___x_2229_);
lean_closure_set(v___f_2231_, 7, v_expectData_2225_);
lean_closure_set(v___f_2231_, 8, v___x_2230_);
lean_closure_set(v___f_2231_, 9, v_pendingHead_2216_);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = 0;
v___x_2234_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2232_, v___x_2233_, v___x_2228_, v___f_2231_);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref(v_connectionContext_2079_);
lean_dec(v_handler_2075_);
lean_dec_ref(v_inst_2073_);
lean_dec_ref(v_config_2072_);
v___x_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___y_2082_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
default: 
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_a_2080_);
lean_dec_ref(v_connectionContext_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v___f_2077_);
lean_dec_ref(v___f_2076_);
lean_dec(v_handler_2075_);
lean_dec_ref(v___f_2074_);
lean_dec_ref(v_inst_2073_);
lean_dec_ref(v_config_2072_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2082_);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2241_, lean_object* v_inst_2242_, lean_object* v___f_2243_, lean_object* v_handler_2244_, lean_object* v___f_2245_, lean_object* v___f_2246_, lean_object* v_inst_2247_, lean_object* v_connectionContext_2248_, lean_object* v_a_2249_, lean_object* v_x_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2241_, v_inst_2242_, v___f_2243_, v_handler_2244_, v___f_2245_, v___f_2246_, v_inst_2247_, v_connectionContext_2248_, v_a_2249_, v_x_2250_, v___y_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_x_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_handler_2264_, lean_object* v_config_2265_, lean_object* v_connectionContext_2266_, lean_object* v_events_2267_, lean_object* v_state_2268_){
_start:
{
lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; size_t v_sz_2273_; size_t v___x_2274_; lean_object* v___x_4110__overap_2275_; lean_object* v___x_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2280_; 
v___f_2270_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2271_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2271_, 0, v_config_2265_);
lean_closure_set(v___f_2271_, 1, v_inst_2262_);
lean_closure_set(v___f_2271_, 2, v___f_2270_);
lean_closure_set(v___f_2271_, 3, v_handler_2264_);
lean_closure_set(v___f_2271_, 4, v___f_2270_);
lean_closure_set(v___f_2271_, 5, v___f_2270_);
lean_closure_set(v___f_2271_, 6, v_inst_2263_);
lean_closure_set(v___f_2271_, 7, v_connectionContext_2266_);
v___x_2272_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2273_ = lean_array_size(v_events_2267_);
v___x_2274_ = ((size_t)0ULL);
v___x_4110__overap_2275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2272_, v_events_2267_, v___f_2271_, v_sz_2273_, v___x_2274_, v_state_2268_);
v___x_2276_ = lean_apply_1(v___x_4110__overap_2275_, lean_box(0));
v___f_2277_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = 0;
v___x_2280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2278_, v___x_2279_, v___x_2276_, v___f_2277_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_handler_2283_, lean_object* v_config_2284_, lean_object* v_connectionContext_2285_, lean_object* v_events_2286_, lean_object* v_state_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2281_, v_inst_2282_, v_handler_2283_, v_config_2284_, v_connectionContext_2285_, v_events_2286_, v_state_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2290_, lean_object* v_00_u03b2_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_handler_2294_, lean_object* v_config_2295_, lean_object* v_connectionContext_2296_, lean_object* v_events_2297_, lean_object* v_state_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2292_, v_inst_2293_, v_handler_2294_, v_config_2295_, v_connectionContext_2296_, v_events_2297_, v_state_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2301_, lean_object* v_00_u03b2_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_handler_2305_, lean_object* v_config_2306_, lean_object* v_connectionContext_2307_, lean_object* v_events_2308_, lean_object* v_state_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2301_, v_00_u03b2_2302_, v_inst_2303_, v_inst_2304_, v_handler_2305_, v_config_2306_, v_connectionContext_2307_, v_events_2308_, v_state_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2312_){
_start:
{
if (lean_obj_tag(v_x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; 
v_a_2313_ = lean_ctor_get(v_x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v_x_2312_, 1);
v___x_2314_ = lean_task_pure(v_a_2313_);
return v___x_2314_;
}
else
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v_x_2312_, 0);
lean_inc_ref(v_a_2315_);
lean_dec_ref_known(v_x_2312_, 1);
return v_a_2315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2316_, lean_object* v_requestStream_2317_, lean_object* v_keepAliveTimeout_2318_, lean_object* v_currentTimeout_2319_, lean_object* v_headerTimeout_2320_, lean_object* v_response_2321_, lean_object* v_respStream_2322_, uint8_t v_requiresData_2323_, lean_object* v_expectData_2324_, lean_object* v_x_2325_){
_start:
{
if (lean_obj_tag(v_x_2325_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_expectData_2324_);
lean_dec(v_respStream_2322_);
lean_dec_ref(v_response_2321_);
lean_dec(v_headerTimeout_2320_);
lean_dec(v_currentTimeout_2319_);
lean_dec(v_keepAliveTimeout_2318_);
lean_dec_ref(v_requestStream_2317_);
lean_dec_ref(v_machine_2316_);
v_a_2327_ = lean_ctor_get(v_x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2329_ = v_x_2325_;
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v_x_2325_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
}
}
else
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2346_; 
v_isSharedCheck_2346_ = !lean_is_exclusive(v_x_2325_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_x_2325_, 0);
lean_dec(v_unused_2347_);
v___x_2337_ = v_x_2325_;
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v_x_2325_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2339_ = 1;
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2341_, 0, v_machine_2316_);
lean_ctor_set(v___x_2341_, 1, v_requestStream_2317_);
lean_ctor_set(v___x_2341_, 2, v_keepAliveTimeout_2318_);
lean_ctor_set(v___x_2341_, 3, v_currentTimeout_2319_);
lean_ctor_set(v___x_2341_, 4, v_headerTimeout_2320_);
lean_ctor_set(v___x_2341_, 5, v_response_2321_);
lean_ctor_set(v___x_2341_, 6, v_respStream_2322_);
lean_ctor_set(v___x_2341_, 7, v_expectData_2324_);
lean_ctor_set(v___x_2341_, 8, v___x_2340_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*9, v_requiresData_2323_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*9 + 1, v___x_2339_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2341_);
v___x_2343_ = v___x_2337_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2348_, lean_object* v_requestStream_2349_, lean_object* v_keepAliveTimeout_2350_, lean_object* v_currentTimeout_2351_, lean_object* v_headerTimeout_2352_, lean_object* v_response_2353_, lean_object* v_respStream_2354_, lean_object* v_requiresData_2355_, lean_object* v_expectData_2356_, lean_object* v_x_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v_requiresData_boxed_2359_; lean_object* v_res_2360_; 
v_requiresData_boxed_2359_ = lean_unbox(v_requiresData_2355_);
v_res_2360_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2348_, v_requestStream_2349_, v_keepAliveTimeout_2350_, v_currentTimeout_2351_, v_headerTimeout_2352_, v_response_2353_, v_respStream_2354_, v_requiresData_boxed_2359_, v_expectData_2356_, v_x_2357_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2361_, lean_object* v_response_2362_, lean_object* v___x_2363_, lean_object* v___f_2364_, lean_object* v_x_2365_){
_start:
{
if (lean_obj_tag(v_x_2365_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v___f_2364_);
lean_dec(v___x_2363_);
lean_dec_ref(v_response_2362_);
lean_dec_ref(v_toFunctor_2361_);
v_a_2367_ = lean_ctor_get(v_x_2365_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_x_2365_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2369_ = v_x_2365_;
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v_x_2365_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2390_; 
v_a_2376_ = lean_ctor_get(v_x_2365_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_x_2365_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2378_ = v_x_2365_;
v_isShared_2379_ = v_isSharedCheck_2390_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v_x_2365_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2390_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2380_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2380_, 0, lean_box(0));
lean_closure_set(v___x_2380_, 1, lean_box(0));
lean_closure_set(v___x_2380_, 2, v_toFunctor_2361_);
v___x_2381_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2381_, 0, lean_box(0));
lean_closure_set(v___x_2381_, 1, v_response_2362_);
v___x_2382_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2382_, 0, lean_box(0));
lean_closure_set(v___x_2382_, 1, lean_box(0));
lean_closure_set(v___x_2382_, 2, lean_box(0));
lean_closure_set(v___x_2382_, 3, v___x_2380_);
lean_closure_set(v___x_2382_, 4, v___x_2381_);
v___x_2383_ = 0;
lean_inc(v___x_2363_);
v___x_2384_ = l_BaseIO_chainTask___redArg(v_a_2376_, v___x_2382_, v___x_2363_, v___x_2383_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2384_);
v___x_2386_ = v___x_2378_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
v___x_2388_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2363_, v___x_2383_, v___x_2387_, v___f_2364_);
return v___x_2388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2391_, lean_object* v_response_2392_, lean_object* v___x_2393_, lean_object* v___f_2394_, lean_object* v_x_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2391_, v_response_2392_, v___x_2393_, v___f_2394_, v_x_2395_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2399_, lean_object* v_handler_2400_, lean_object* v_extensions_2401_, lean_object* v_connectionContext_2402_, lean_object* v_state_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v_toApplicative_2406_; lean_object* v_pendingHead_2407_; 
v___x_2405_ = l_instMonadBaseIO;
v_toApplicative_2406_ = lean_ctor_get(v___x_2405_, 0);
v_pendingHead_2407_ = lean_ctor_get(v_state_2403_, 8);
lean_inc(v_pendingHead_2407_);
if (lean_obj_tag(v_pendingHead_2407_) == 1)
{
lean_object* v_toFunctor_2408_; lean_object* v_machine_2409_; lean_object* v_requestStream_2410_; lean_object* v_keepAliveTimeout_2411_; lean_object* v_currentTimeout_2412_; lean_object* v_headerTimeout_2413_; lean_object* v_response_2414_; lean_object* v_respStream_2415_; uint8_t v_requiresData_2416_; lean_object* v_expectData_2417_; lean_object* v_val_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2440_; 
v_toFunctor_2408_ = lean_ctor_get(v_toApplicative_2406_, 0);
v_machine_2409_ = lean_ctor_get(v_state_2403_, 0);
lean_inc_ref(v_machine_2409_);
v_requestStream_2410_ = lean_ctor_get(v_state_2403_, 1);
lean_inc_ref(v_requestStream_2410_);
v_keepAliveTimeout_2411_ = lean_ctor_get(v_state_2403_, 2);
lean_inc(v_keepAliveTimeout_2411_);
v_currentTimeout_2412_ = lean_ctor_get(v_state_2403_, 3);
lean_inc(v_currentTimeout_2412_);
v_headerTimeout_2413_ = lean_ctor_get(v_state_2403_, 4);
lean_inc(v_headerTimeout_2413_);
v_response_2414_ = lean_ctor_get(v_state_2403_, 5);
lean_inc_ref(v_response_2414_);
v_respStream_2415_ = lean_ctor_get(v_state_2403_, 6);
lean_inc(v_respStream_2415_);
v_requiresData_2416_ = lean_ctor_get_uint8(v_state_2403_, sizeof(void*)*9);
v_expectData_2417_ = lean_ctor_get(v_state_2403_, 7);
lean_inc(v_expectData_2417_);
lean_dec_ref(v_state_2403_);
v_val_2418_ = lean_ctor_get(v_pendingHead_2407_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_pendingHead_2407_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2420_ = v_pendingHead_2407_;
v_isShared_2421_ = v_isSharedCheck_2440_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_val_2418_);
lean_dec(v_pendingHead_2407_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2440_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_onRequest_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
v_onRequest_2422_ = lean_ctor_get(v_inst_2399_, 1);
lean_inc_ref(v_onRequest_2422_);
lean_dec_ref(v_inst_2399_);
lean_inc_ref(v_requestStream_2410_);
v___x_2423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2423_, 0, v_val_2418_);
lean_ctor_set(v___x_2423_, 1, v_requestStream_2410_);
lean_ctor_set(v___x_2423_, 2, v_extensions_2401_);
v___x_2424_ = lean_apply_3(v_onRequest_2422_, v_handler_2400_, v___x_2423_, v_connectionContext_2402_);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2426_, 0, lean_box(0));
lean_closure_set(v___x_2426_, 1, v___x_2424_);
v___x_2427_ = lean_io_as_task(v___x_2426_, v___x_2425_);
v___f_2428_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2429_ = lean_box(v_requiresData_2416_);
lean_inc_ref(v_response_2414_);
v___f_2430_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2430_, 0, v_machine_2409_);
lean_closure_set(v___f_2430_, 1, v_requestStream_2410_);
lean_closure_set(v___f_2430_, 2, v_keepAliveTimeout_2411_);
lean_closure_set(v___f_2430_, 3, v_currentTimeout_2412_);
lean_closure_set(v___f_2430_, 4, v_headerTimeout_2413_);
lean_closure_set(v___f_2430_, 5, v_response_2414_);
lean_closure_set(v___f_2430_, 6, v_respStream_2415_);
lean_closure_set(v___f_2430_, 7, v___x_2429_);
lean_closure_set(v___f_2430_, 8, v_expectData_2417_);
lean_inc_ref(v_toFunctor_2408_);
v___f_2431_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2431_, 0, v_toFunctor_2408_);
lean_closure_set(v___f_2431_, 1, v_response_2414_);
lean_closure_set(v___f_2431_, 2, v___x_2425_);
lean_closure_set(v___f_2431_, 3, v___f_2430_);
v___x_2432_ = 1;
v___x_2433_ = lean_task_bind(v___x_2427_, v___f_2428_, v___x_2425_, v___x_2432_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2433_);
v___x_2435_ = v___x_2420_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
v___x_2437_ = 0;
v___x_2438_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2425_, v___x_2437_, v___x_2436_, v___f_2431_);
return v___x_2438_;
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v_pendingHead_2407_);
lean_dec_ref(v_connectionContext_2402_);
lean_dec(v_extensions_2401_);
lean_dec(v_handler_2400_);
lean_dec_ref(v_inst_2399_);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_state_2403_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2443_, lean_object* v_handler_2444_, lean_object* v_extensions_2445_, lean_object* v_connectionContext_2446_, lean_object* v_state_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2443_, v_handler_2444_, v_extensions_2445_, v_connectionContext_2446_, v_state_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2450_, lean_object* v_inst_2451_, lean_object* v_handler_2452_, lean_object* v_extensions_2453_, lean_object* v_connectionContext_2454_, lean_object* v_state_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2451_, v_handler_2452_, v_extensions_2453_, v_connectionContext_2454_, v_state_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2458_, lean_object* v_inst_2459_, lean_object* v_handler_2460_, lean_object* v_extensions_2461_, lean_object* v_connectionContext_2462_, lean_object* v_state_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2458_, v_inst_2459_, v_handler_2460_, v_extensions_2461_, v_connectionContext_2462_, v_state_2463_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2466_, lean_object* v_____r_2467_){
_start:
{
lean_object* v_writer_2469_; lean_object* v_reader_2470_; lean_object* v_config_2471_; lean_object* v_events_2472_; lean_object* v_error_2473_; lean_object* v_instant_2474_; uint8_t v_keepAlive_2475_; uint8_t v_forcedFlush_2476_; uint8_t v_pullBodyStalled_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2504_; 
v_writer_2469_ = lean_ctor_get(v_machine_2466_, 1);
v_reader_2470_ = lean_ctor_get(v_machine_2466_, 0);
v_config_2471_ = lean_ctor_get(v_machine_2466_, 2);
v_events_2472_ = lean_ctor_get(v_machine_2466_, 3);
v_error_2473_ = lean_ctor_get(v_machine_2466_, 4);
v_instant_2474_ = lean_ctor_get(v_machine_2466_, 5);
v_keepAlive_2475_ = lean_ctor_get_uint8(v_machine_2466_, sizeof(void*)*6);
v_forcedFlush_2476_ = lean_ctor_get_uint8(v_machine_2466_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2477_ = lean_ctor_get_uint8(v_machine_2466_, sizeof(void*)*6 + 2);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_machine_2466_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2479_ = v_machine_2466_;
v_isShared_2480_ = v_isSharedCheck_2504_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_instant_2474_);
lean_inc(v_error_2473_);
lean_inc(v_events_2472_);
lean_inc(v_config_2471_);
lean_inc(v_writer_2469_);
lean_inc(v_reader_2470_);
lean_dec(v_machine_2466_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2504_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_userData_2481_; lean_object* v_outputData_2482_; lean_object* v_state_2483_; lean_object* v_knownSize_2484_; lean_object* v_messageHead_2485_; uint8_t v_sentMessage_2486_; uint8_t v_omitBody_2487_; lean_object* v_userDataBytes_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2503_; 
v_userData_2481_ = lean_ctor_get(v_writer_2469_, 0);
v_outputData_2482_ = lean_ctor_get(v_writer_2469_, 1);
v_state_2483_ = lean_ctor_get(v_writer_2469_, 2);
v_knownSize_2484_ = lean_ctor_get(v_writer_2469_, 3);
v_messageHead_2485_ = lean_ctor_get(v_writer_2469_, 4);
v_sentMessage_2486_ = lean_ctor_get_uint8(v_writer_2469_, sizeof(void*)*6);
v_omitBody_2487_ = lean_ctor_get_uint8(v_writer_2469_, sizeof(void*)*6 + 2);
v_userDataBytes_2488_ = lean_ctor_get(v_writer_2469_, 5);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_writer_2469_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2490_ = v_writer_2469_;
v_isShared_2491_ = v_isSharedCheck_2503_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_userDataBytes_2488_);
lean_inc(v_messageHead_2485_);
lean_inc(v_knownSize_2484_);
lean_inc(v_state_2483_);
lean_inc(v_outputData_2482_);
lean_inc(v_userData_2481_);
lean_dec(v_writer_2469_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2503_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
uint8_t v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = 1;
if (v_isShared_2491_ == 0)
{
v___x_2494_ = v___x_2490_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_userData_2481_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_outputData_2482_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_state_2483_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_knownSize_2484_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_messageHead_2485_);
lean_ctor_set(v_reuseFailAlloc_2502_, 5, v_userDataBytes_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, sizeof(void*)*6, v_sentMessage_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, sizeof(void*)*6 + 2, v_omitBody_2487_);
v___x_2494_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2496_; 
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*6 + 1, v___x_2492_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2494_);
v___x_2496_ = v___x_2479_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_reader_2470_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_config_2471_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_events_2472_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_error_2473_);
lean_ctor_set(v_reuseFailAlloc_2501_, 5, v_instant_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2501_, sizeof(void*)*6, v_keepAlive_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2501_, sizeof(void*)*6 + 1, v_forcedFlush_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2501_, sizeof(void*)*6 + 2, v_pullBodyStalled_2477_);
v___x_2496_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2497_ = lean_box(0);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2505_, lean_object* v_____r_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2505_, v_____r_2506_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2509_, lean_object* v_x2_2510_){
_start:
{
lean_object* v_data_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_data_2511_ = lean_ctor_get(v_x2_2510_, 0);
v___x_2512_ = lean_byte_array_size(v_data_2511_);
v___x_2513_ = lean_nat_add(v_x1_2509_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2514_, lean_object* v_x2_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2514_, v_x2_2515_);
lean_dec_ref(v_x2_2515_);
lean_dec(v_x1_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2517_, lean_object* v_machine_2518_, lean_object* v_isClosed_2519_, lean_object* v___f_2520_, lean_object* v___f_2521_, lean_object* v_x_2522_){
_start:
{
lean_object* v___y_2525_; 
if (lean_obj_tag(v_x_2522_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v___f_2521_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v_isClosed_2519_);
lean_dec_ref(v_machine_2518_);
lean_dec(v_body_2517_);
v_a_2530_ = lean_ctor_get(v_x_2522_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_x_2522_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2532_ = v_x_2522_;
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v_x_2522_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2606_; 
v_a_2539_ = lean_ctor_get(v_x_2522_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_x_2522_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2541_ = v_x_2522_;
v_isShared_2542_ = v_isSharedCheck_2606_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v_x_2522_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2606_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
if (lean_obj_tag(v_a_2539_) == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
lean_dec_ref(v___f_2521_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v_isClosed_2519_);
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_body_2517_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_machine_2518_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2544_);
v___x_2546_ = v___x_2541_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
else
{
lean_object* v_val_2549_; 
lean_del_object(v___x_2541_);
v_val_2549_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_val_2549_);
lean_dec_ref_known(v_a_2539_, 1);
if (lean_obj_tag(v_val_2549_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; 
lean_dec_ref(v___f_2521_);
lean_dec_ref(v_machine_2518_);
v___x_2550_ = lean_apply_2(v_isClosed_2519_, v_body_2517_, lean_box(0));
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = 0;
v___x_2553_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2551_, v___x_2552_, v___x_2550_, v___f_2520_);
return v___x_2553_;
}
else
{
lean_object* v_val_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
lean_dec_ref(v___f_2520_);
lean_dec_ref(v_isClosed_2519_);
v_val_2554_ = lean_ctor_get(v_val_2549_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v_val_2549_, 1);
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_mk_empty_array_with_capacity(v___x_2555_);
v___x_2557_ = lean_array_push(v___x_2556_, v_val_2554_);
v___x_2558_ = lean_array_get_size(v___x_2557_);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_nat_dec_eq(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v_reader_2561_; lean_object* v_writer_2562_; lean_object* v_config_2563_; lean_object* v_events_2564_; lean_object* v_error_2565_; lean_object* v_instant_2566_; uint8_t v_keepAlive_2567_; uint8_t v_forcedFlush_2568_; uint8_t v_pullBodyStalled_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2605_; 
v_reader_2561_ = lean_ctor_get(v_machine_2518_, 0);
v_writer_2562_ = lean_ctor_get(v_machine_2518_, 1);
v_config_2563_ = lean_ctor_get(v_machine_2518_, 2);
v_events_2564_ = lean_ctor_get(v_machine_2518_, 3);
v_error_2565_ = lean_ctor_get(v_machine_2518_, 4);
v_instant_2566_ = lean_ctor_get(v_machine_2518_, 5);
v_keepAlive_2567_ = lean_ctor_get_uint8(v_machine_2518_, sizeof(void*)*6);
v_forcedFlush_2568_ = lean_ctor_get_uint8(v_machine_2518_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2569_ = lean_ctor_get_uint8(v_machine_2518_, sizeof(void*)*6 + 2);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_machine_2518_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2571_ = v_machine_2518_;
v_isShared_2572_ = v_isSharedCheck_2605_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_instant_2566_);
lean_inc(v_error_2565_);
lean_inc(v_events_2564_);
lean_inc(v_config_2563_);
lean_inc(v_writer_2562_);
lean_inc(v_reader_2561_);
lean_dec(v_machine_2518_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2605_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___y_2574_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2597_ = lean_nat_dec_lt(v___x_2559_, v___x_2558_);
if (v___x_2597_ == 0)
{
lean_dec_ref(v___f_2521_);
v___y_2574_ = v___x_2559_;
goto v___jp_2573_;
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_nat_dec_le(v___x_2558_, v___x_2558_);
if (v___x_2598_ == 0)
{
if (v___x_2597_ == 0)
{
lean_dec_ref(v___f_2521_);
v___y_2574_ = v___x_2559_;
goto v___jp_2573_;
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = lean_usize_of_nat(v___x_2558_);
lean_inc_ref(v___x_2557_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2596_, v___f_2521_, v___x_2557_, v___x_2599_, v___x_2600_, v___x_2559_);
v___y_2574_ = v___x_2601_;
goto v___jp_2573_;
}
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = ((size_t)0ULL);
v___x_2603_ = lean_usize_of_nat(v___x_2558_);
lean_inc_ref(v___x_2557_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2596_, v___f_2521_, v___x_2557_, v___x_2602_, v___x_2603_, v___x_2559_);
v___y_2574_ = v___x_2604_;
goto v___jp_2573_;
}
}
v___jp_2573_:
{
lean_object* v_userData_2575_; lean_object* v_outputData_2576_; lean_object* v_state_2577_; lean_object* v_knownSize_2578_; lean_object* v_messageHead_2579_; uint8_t v_sentMessage_2580_; uint8_t v_userClosedBody_2581_; uint8_t v_omitBody_2582_; lean_object* v_userDataBytes_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2595_; 
v_userData_2575_ = lean_ctor_get(v_writer_2562_, 0);
v_outputData_2576_ = lean_ctor_get(v_writer_2562_, 1);
v_state_2577_ = lean_ctor_get(v_writer_2562_, 2);
v_knownSize_2578_ = lean_ctor_get(v_writer_2562_, 3);
v_messageHead_2579_ = lean_ctor_get(v_writer_2562_, 4);
v_sentMessage_2580_ = lean_ctor_get_uint8(v_writer_2562_, sizeof(void*)*6);
v_userClosedBody_2581_ = lean_ctor_get_uint8(v_writer_2562_, sizeof(void*)*6 + 1);
v_omitBody_2582_ = lean_ctor_get_uint8(v_writer_2562_, sizeof(void*)*6 + 2);
v_userDataBytes_2583_ = lean_ctor_get(v_writer_2562_, 5);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_writer_2562_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2585_ = v_writer_2562_;
v_isShared_2586_ = v_isSharedCheck_2595_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_userDataBytes_2583_);
lean_inc(v_messageHead_2579_);
lean_inc(v_knownSize_2578_);
lean_inc(v_state_2577_);
lean_inc(v_outputData_2576_);
lean_inc(v_userData_2575_);
lean_dec(v_writer_2562_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2595_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2587_ = l_Array_append___redArg(v_userData_2575_, v___x_2557_);
lean_dec_ref(v___x_2557_);
v___x_2588_ = lean_nat_add(v_userDataBytes_2583_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec(v_userDataBytes_2583_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 5, v___x_2588_);
lean_ctor_set(v___x_2585_, 0, v___x_2587_);
v___x_2590_ = v___x_2585_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_outputData_2576_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_state_2577_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v_knownSize_2578_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v_messageHead_2579_);
lean_ctor_set(v_reuseFailAlloc_2594_, 5, v___x_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*6, v_sentMessage_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*6 + 1, v_userClosedBody_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*6 + 2, v_omitBody_2582_);
v___x_2590_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v___x_2590_);
v___x_2592_ = v___x_2571_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_reader_2561_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_config_2563_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_events_2564_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_error_2565_);
lean_ctor_set(v_reuseFailAlloc_2593_, 5, v_instant_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2593_, sizeof(void*)*6, v_keepAlive_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2593_, sizeof(void*)*6 + 1, v_forcedFlush_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2593_, sizeof(void*)*6 + 2, v_pullBodyStalled_2569_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
v___y_2525_ = v___x_2592_;
goto v___jp_2524_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2557_);
lean_dec_ref(v___f_2521_);
v___y_2525_ = v_machine_2518_;
goto v___jp_2524_;
}
}
}
}
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_body_2517_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___y_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2607_, lean_object* v_machine_2608_, lean_object* v_isClosed_2609_, lean_object* v___f_2610_, lean_object* v___f_2611_, lean_object* v_x_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2607_, v_machine_2608_, v_isClosed_2609_, v___f_2610_, v___f_2611_, v_x_2612_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2616_, lean_object* v_machine_2617_, lean_object* v_body_2618_){
_start:
{
lean_object* v_close_2620_; lean_object* v_isClosed_2621_; lean_object* v_tryRecv_2622_; lean_object* v___x_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; 
v_close_2620_ = lean_ctor_get(v_inst_2616_, 1);
lean_inc_ref(v_close_2620_);
v_isClosed_2621_ = lean_ctor_get(v_inst_2616_, 2);
lean_inc_ref(v_isClosed_2621_);
v_tryRecv_2622_ = lean_ctor_get(v_inst_2616_, 4);
lean_inc_ref(v_tryRecv_2622_);
lean_dec_ref(v_inst_2616_);
lean_inc_n(v_body_2618_, 2);
v___x_2623_ = lean_apply_2(v_tryRecv_2622_, v_body_2618_, lean_box(0));
lean_inc_ref(v_machine_2617_);
v___f_2624_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2624_, 0, v_machine_2617_);
lean_inc_ref(v___f_2624_);
v___f_2625_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2625_, 0, v___f_2624_);
v___f_2626_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2626_, 0, v_close_2620_);
lean_closure_set(v___f_2626_, 1, v_body_2618_);
lean_closure_set(v___f_2626_, 2, v___f_2625_);
lean_closure_set(v___f_2626_, 3, v___f_2624_);
v___f_2627_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2628_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2628_, 0, v_body_2618_);
lean_closure_set(v___f_2628_, 1, v_machine_2617_);
lean_closure_set(v___f_2628_, 2, v_isClosed_2621_);
lean_closure_set(v___f_2628_, 3, v___f_2626_);
lean_closure_set(v___f_2628_, 4, v___f_2627_);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = 0;
v___x_2631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2629_, v___x_2630_, v___x_2623_, v___f_2628_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2632_, lean_object* v_machine_2633_, lean_object* v_body_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2632_, v_machine_2633_, v_body_2634_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2637_, lean_object* v_inst_2638_, lean_object* v_machine_2639_, lean_object* v_body_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2638_, v_machine_2639_, v_body_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2643_, lean_object* v_inst_2644_, lean_object* v_machine_2645_, lean_object* v_body_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2643_, v_inst_2644_, v_machine_2645_, v_body_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2655_, lean_object* v_____r_2656_, lean_object* v_st_2657_){
_start:
{
lean_object* v_machine_2659_; lean_object* v_requestStream_2660_; lean_object* v_keepAliveTimeout_2661_; lean_object* v_currentTimeout_2662_; lean_object* v_headerTimeout_2663_; lean_object* v_response_2664_; lean_object* v_respStream_2665_; uint8_t v_requiresData_2666_; lean_object* v_expectData_2667_; uint8_t v_handlerDispatched_2668_; lean_object* v_pendingHead_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2751_; 
v_machine_2659_ = lean_ctor_get(v_st_2657_, 0);
v_requestStream_2660_ = lean_ctor_get(v_st_2657_, 1);
v_keepAliveTimeout_2661_ = lean_ctor_get(v_st_2657_, 2);
v_currentTimeout_2662_ = lean_ctor_get(v_st_2657_, 3);
v_headerTimeout_2663_ = lean_ctor_get(v_st_2657_, 4);
v_response_2664_ = lean_ctor_get(v_st_2657_, 5);
v_respStream_2665_ = lean_ctor_get(v_st_2657_, 6);
v_requiresData_2666_ = lean_ctor_get_uint8(v_st_2657_, sizeof(void*)*9);
v_expectData_2667_ = lean_ctor_get(v_st_2657_, 7);
v_handlerDispatched_2668_ = lean_ctor_get_uint8(v_st_2657_, sizeof(void*)*9 + 1);
v_pendingHead_2669_ = lean_ctor_get(v_st_2657_, 8);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_st_2657_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2671_ = v_st_2657_;
v_isShared_2672_ = v_isSharedCheck_2751_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_pendingHead_2669_);
lean_inc(v_expectData_2667_);
lean_inc(v_respStream_2665_);
lean_inc(v_response_2664_);
lean_inc(v_headerTimeout_2663_);
lean_inc(v_currentTimeout_2662_);
lean_inc(v_keepAliveTimeout_2661_);
lean_inc(v_requestStream_2660_);
lean_inc(v_machine_2659_);
lean_dec(v_st_2657_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2751_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___y_2674_; lean_object* v_reader_2683_; lean_object* v_state_2684_; 
v_reader_2683_ = lean_ctor_get(v_machine_2659_, 0);
lean_inc_ref(v_reader_2683_);
v_state_2684_ = lean_ctor_get(v_reader_2683_, 0);
lean_inc(v_state_2684_);
if (lean_obj_tag(v_state_2684_) == 6)
{
lean_dec_ref(v_reader_2683_);
lean_dec_ref(v_val_2655_);
v___y_2674_ = v_machine_2659_;
goto v___jp_2673_;
}
else
{
if (lean_obj_tag(v_state_2684_) == 7)
{
lean_dec_ref_known(v_state_2684_, 1);
lean_dec_ref(v_reader_2683_);
lean_dec_ref(v_val_2655_);
v___y_2674_ = v_machine_2659_;
goto v___jp_2673_;
}
else
{
lean_object* v_input_2685_; lean_object* v_writer_2686_; lean_object* v_config_2687_; lean_object* v_events_2688_; lean_object* v_error_2689_; lean_object* v_instant_2690_; uint8_t v_keepAlive_2691_; uint8_t v_forcedFlush_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2749_; 
v_input_2685_ = lean_ctor_get(v_reader_2683_, 1);
lean_inc_ref(v_input_2685_);
v_writer_2686_ = lean_ctor_get(v_machine_2659_, 1);
v_config_2687_ = lean_ctor_get(v_machine_2659_, 2);
v_events_2688_ = lean_ctor_get(v_machine_2659_, 3);
v_error_2689_ = lean_ctor_get(v_machine_2659_, 4);
v_instant_2690_ = lean_ctor_get(v_machine_2659_, 5);
v_keepAlive_2691_ = lean_ctor_get_uint8(v_machine_2659_, sizeof(void*)*6);
v_forcedFlush_2692_ = lean_ctor_get_uint8(v_machine_2659_, sizeof(void*)*6 + 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_machine_2659_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v_machine_2659_, 0);
lean_dec(v_unused_2750_);
v___x_2694_ = v_machine_2659_;
v_isShared_2695_ = v_isSharedCheck_2749_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_instant_2690_);
lean_inc(v_error_2689_);
lean_inc(v_events_2688_);
lean_inc(v_config_2687_);
lean_inc(v_writer_2686_);
lean_dec(v_machine_2659_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2749_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v_messageHead_2696_; lean_object* v_messageCount_2697_; lean_object* v_bodyBytesRead_2698_; lean_object* v_headerBytesRead_2699_; uint8_t v_noMoreInput_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2746_; 
v_messageHead_2696_ = lean_ctor_get(v_reader_2683_, 2);
v_messageCount_2697_ = lean_ctor_get(v_reader_2683_, 3);
v_bodyBytesRead_2698_ = lean_ctor_get(v_reader_2683_, 4);
v_headerBytesRead_2699_ = lean_ctor_get(v_reader_2683_, 5);
v_noMoreInput_2700_ = lean_ctor_get_uint8(v_reader_2683_, sizeof(void*)*6);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_reader_2683_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2747_ = lean_ctor_get(v_reader_2683_, 1);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_reader_2683_, 0);
lean_dec(v_unused_2748_);
v___x_2702_ = v_reader_2683_;
v_isShared_2703_ = v_isSharedCheck_2746_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_headerBytesRead_2699_);
lean_inc(v_bodyBytesRead_2698_);
lean_inc(v_messageCount_2697_);
lean_inc(v_messageHead_2696_);
lean_dec(v_reader_2683_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2746_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v_array_2704_; lean_object* v_idx_2705_; uint8_t v___x_2706_; lean_object* v___y_2708_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v_array_2704_ = lean_ctor_get(v_input_2685_, 0);
lean_inc_ref(v_array_2704_);
v_idx_2705_ = lean_ctor_get(v_input_2685_, 1);
lean_inc(v_idx_2705_);
lean_dec_ref(v_input_2685_);
v___x_2706_ = 0;
v___x_2737_ = lean_byte_array_size(v_array_2704_);
v___x_2738_ = lean_nat_dec_le(v___x_2737_, v_idx_2705_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2739_ = l_ByteArray_extract(v_array_2704_, v_idx_2705_, v___x_2737_);
lean_dec_ref(v_array_2704_);
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = lean_byte_array_size(v___x_2739_);
v___x_2742_ = lean_byte_array_size(v_val_2655_);
v___x_2743_ = lean_byte_array_copy_slice(v_val_2655_, v___x_2740_, v___x_2739_, v___x_2741_, v___x_2742_, v___x_2738_);
lean_dec_ref(v_val_2655_);
v___x_2744_ = l_ByteArray_mkIterator(v___x_2743_);
v___y_2708_ = v___x_2744_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2745_; 
lean_dec(v_idx_2705_);
lean_dec_ref(v_array_2704_);
v___x_2745_ = l_ByteArray_mkIterator(v_val_2655_);
v___y_2708_ = v___x_2745_;
goto v___jp_2707_;
}
v___jp_2707_:
{
lean_object* v_maxHeaderBytes_2709_; lean_object* v_maxStartLineLength_2710_; lean_object* v_maxChunkLineLength_2711_; lean_object* v_maxBodySize_2712_; lean_object* v_array_2713_; lean_object* v_idx_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_maxHeaderBytes_2709_ = lean_ctor_get(v_config_2687_, 2);
v_maxStartLineLength_2710_ = lean_ctor_get(v_config_2687_, 5);
v_maxChunkLineLength_2711_ = lean_ctor_get(v_config_2687_, 13);
v_maxBodySize_2712_ = lean_ctor_get(v_config_2687_, 15);
v_array_2713_ = lean_ctor_get(v___y_2708_, 0);
v_idx_2714_ = lean_ctor_get(v___y_2708_, 1);
v___x_2715_ = lean_nat_add(v_maxBodySize_2712_, v_maxHeaderBytes_2709_);
v___x_2716_ = lean_nat_add(v___x_2715_, v_maxStartLineLength_2710_);
lean_dec(v___x_2715_);
v___x_2717_ = lean_nat_add(v___x_2716_, v_maxChunkLineLength_2711_);
lean_dec(v___x_2716_);
v___x_2718_ = lean_byte_array_size(v_array_2713_);
v___x_2719_ = lean_nat_sub(v___x_2718_, v_idx_2714_);
v___x_2720_ = lean_nat_dec_lt(v___x_2717_, v___x_2719_);
lean_dec(v___x_2719_);
lean_dec(v___x_2717_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2722_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 1, v___y_2708_);
v___x_2722_ = v___x_2702_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_state_2684_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___y_2708_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_messageHead_2696_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_messageCount_2697_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_bodyBytesRead_2698_);
lean_ctor_set(v_reuseFailAlloc_2726_, 5, v_headerBytesRead_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, sizeof(void*)*6, v_noMoreInput_2700_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v_machine_2724_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2722_);
v_machine_2724_ = v___x_2694_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_writer_2686_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_config_2687_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_events_2688_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_error_2689_);
lean_ctor_set(v_reuseFailAlloc_2725_, 5, v_instant_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, sizeof(void*)*6, v_keepAlive_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, sizeof(void*)*6 + 1, v_forcedFlush_2692_);
v_machine_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_ctor_set_uint8(v_machine_2724_, sizeof(void*)*6 + 2, v___x_2706_);
v___y_2674_ = v_machine_2724_;
goto v___jp_2673_;
}
}
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
lean_dec(v_error_2689_);
lean_dec(v_state_2684_);
v___x_2727_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2728_ = lean_array_push(v_events_2688_, v___x_2727_);
v___x_2729_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 1, v___y_2708_);
lean_ctor_set(v___x_2702_, 0, v___x_2729_);
v___x_2731_ = v___x_2702_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___y_2708_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_messageHead_2696_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_messageCount_2697_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_bodyBytesRead_2698_);
lean_ctor_set(v_reuseFailAlloc_2736_, 5, v_headerBytesRead_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2736_, sizeof(void*)*6, v_noMoreInput_2700_);
v___x_2731_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 4, v___x_2732_);
lean_ctor_set(v___x_2694_, 3, v___x_2728_);
lean_ctor_set(v___x_2694_, 0, v___x_2731_);
v___x_2734_ = v___x_2694_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_writer_2686_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_config_2687_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2735_, 5, v_instant_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2735_, sizeof(void*)*6, v_keepAlive_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2735_, sizeof(void*)*6 + 1, v_forcedFlush_2692_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*6 + 2, v___x_2706_);
v___y_2674_ = v___x_2734_;
goto v___jp_2673_;
}
}
}
}
}
}
}
}
v___jp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___y_2674_);
v___x_2676_ = v___x_2671_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___y_2674_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_requestStream_2660_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_keepAliveTimeout_2661_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_currentTimeout_2662_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_headerTimeout_2663_);
lean_ctor_set(v_reuseFailAlloc_2682_, 5, v_response_2664_);
lean_ctor_set(v_reuseFailAlloc_2682_, 6, v_respStream_2665_);
lean_ctor_set(v_reuseFailAlloc_2682_, 7, v_expectData_2667_);
lean_ctor_set(v_reuseFailAlloc_2682_, 8, v_pendingHead_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2682_, sizeof(void*)*9, v_requiresData_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2682_, sizeof(void*)*9 + 1, v_handlerDispatched_2668_);
v___x_2676_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
uint8_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2677_ = 0;
v___x_2678_ = lean_box(v___x_2677_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2676_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2752_, lean_object* v_____r_2753_, lean_object* v_st_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2752_, v_____r_2753_, v_st_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2757_, lean_object* v_machine_2758_, lean_object* v_requestStream_2759_, lean_object* v_currentTimeout_2760_, lean_object* v_response_2761_, lean_object* v_respStream_2762_, uint8_t v_requiresData_2763_, lean_object* v_expectData_2764_, uint8_t v_handlerDispatched_2765_, lean_object* v_pendingHead_2766_, lean_object* v___f_2767_, lean_object* v_x_2768_){
_start:
{
if (lean_obj_tag(v_x_2768_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v___f_2767_);
lean_dec(v_pendingHead_2766_);
lean_dec(v_expectData_2764_);
lean_dec(v_respStream_2762_);
lean_dec_ref(v_response_2761_);
lean_dec(v_currentTimeout_2760_);
lean_dec_ref(v_requestStream_2759_);
lean_dec_ref(v_machine_2758_);
v_a_2770_ = lean_ctor_get(v_x_2768_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2768_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2772_ = v_x_2768_;
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v_x_2768_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v_headerTimeout_2780_; lean_object* v_second_2781_; lean_object* v_nano_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_second_2786_; lean_object* v_nano_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2779_ = lean_ctor_get(v_x_2768_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v_x_2768_, 1);
v_headerTimeout_2780_ = lean_ctor_get(v_config_2757_, 6);
v_second_2781_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_second_2781_);
v_nano_2782_ = lean_ctor_get(v_a_2779_, 1);
lean_inc(v_nano_2782_);
lean_dec(v_a_2779_);
v___x_2783_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2784_ = lean_int_mul(v_headerTimeout_2780_, v___x_2783_);
v___x_2785_ = l_Std_Time_Duration_ofNanoseconds(v___x_2784_);
lean_dec(v___x_2784_);
v_second_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_second_2786_);
v_nano_2787_ = lean_ctor_get(v___x_2785_, 1);
lean_inc(v_nano_2787_);
lean_dec_ref(v___x_2785_);
v___x_2788_ = lean_box(0);
v___x_2789_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2790_ = lean_int_mul(v_second_2781_, v___x_2789_);
lean_dec(v_second_2781_);
v___x_2791_ = lean_int_add(v___x_2790_, v_nano_2782_);
lean_dec(v_nano_2782_);
lean_dec(v___x_2790_);
v___x_2792_ = lean_int_mul(v_second_2786_, v___x_2789_);
lean_dec(v_second_2786_);
v___x_2793_ = lean_int_add(v___x_2792_, v_nano_2787_);
lean_dec(v_nano_2787_);
lean_dec(v___x_2792_);
v___x_2794_ = lean_int_add(v___x_2791_, v___x_2793_);
lean_dec(v___x_2793_);
lean_dec(v___x_2791_);
v___x_2795_ = l_Std_Time_Duration_ofNanoseconds(v___x_2794_);
lean_dec(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2797_, 0, v_machine_2758_);
lean_ctor_set(v___x_2797_, 1, v_requestStream_2759_);
lean_ctor_set(v___x_2797_, 2, v___x_2788_);
lean_ctor_set(v___x_2797_, 3, v_currentTimeout_2760_);
lean_ctor_set(v___x_2797_, 4, v___x_2796_);
lean_ctor_set(v___x_2797_, 5, v_response_2761_);
lean_ctor_set(v___x_2797_, 6, v_respStream_2762_);
lean_ctor_set(v___x_2797_, 7, v_expectData_2764_);
lean_ctor_set(v___x_2797_, 8, v_pendingHead_2766_);
lean_ctor_set_uint8(v___x_2797_, sizeof(void*)*9, v_requiresData_2763_);
lean_ctor_set_uint8(v___x_2797_, sizeof(void*)*9 + 1, v_handlerDispatched_2765_);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_apply_3(v___f_2767_, v___x_2798_, v___x_2797_, lean_box(0));
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2800_, lean_object* v_machine_2801_, lean_object* v_requestStream_2802_, lean_object* v_currentTimeout_2803_, lean_object* v_response_2804_, lean_object* v_respStream_2805_, lean_object* v_requiresData_2806_, lean_object* v_expectData_2807_, lean_object* v_handlerDispatched_2808_, lean_object* v_pendingHead_2809_, lean_object* v___f_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_){
_start:
{
uint8_t v_requiresData_boxed_2813_; uint8_t v_handlerDispatched_boxed_2814_; lean_object* v_res_2815_; 
v_requiresData_boxed_2813_ = lean_unbox(v_requiresData_2806_);
v_handlerDispatched_boxed_2814_ = lean_unbox(v_handlerDispatched_2808_);
v_res_2815_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2800_, v_machine_2801_, v_requestStream_2802_, v_currentTimeout_2803_, v_response_2804_, v_respStream_2805_, v_requiresData_boxed_2813_, v_expectData_2807_, v_handlerDispatched_boxed_2814_, v_pendingHead_2809_, v___f_2810_, v_x_2811_);
lean_dec_ref(v_config_2800_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2816_, lean_object* v_requestStream_2817_, lean_object* v_keepAliveTimeout_2818_, lean_object* v_currentTimeout_2819_, lean_object* v_headerTimeout_2820_, lean_object* v_response_2821_, uint8_t v_requiresData_2822_, lean_object* v_expectData_2823_, uint8_t v_handlerDispatched_2824_, lean_object* v_pendingHead_2825_, lean_object* v_____r_2826_){
_start:
{
lean_object* v_writer_2828_; lean_object* v_reader_2829_; lean_object* v_config_2830_; lean_object* v_events_2831_; lean_object* v_error_2832_; lean_object* v_instant_2833_; uint8_t v_keepAlive_2834_; uint8_t v_forcedFlush_2835_; uint8_t v_pullBodyStalled_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2866_; 
v_writer_2828_ = lean_ctor_get(v_machine_2816_, 1);
v_reader_2829_ = lean_ctor_get(v_machine_2816_, 0);
v_config_2830_ = lean_ctor_get(v_machine_2816_, 2);
v_events_2831_ = lean_ctor_get(v_machine_2816_, 3);
v_error_2832_ = lean_ctor_get(v_machine_2816_, 4);
v_instant_2833_ = lean_ctor_get(v_machine_2816_, 5);
v_keepAlive_2834_ = lean_ctor_get_uint8(v_machine_2816_, sizeof(void*)*6);
v_forcedFlush_2835_ = lean_ctor_get_uint8(v_machine_2816_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2836_ = lean_ctor_get_uint8(v_machine_2816_, sizeof(void*)*6 + 2);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_machine_2816_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2838_ = v_machine_2816_;
v_isShared_2839_ = v_isSharedCheck_2866_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_instant_2833_);
lean_inc(v_error_2832_);
lean_inc(v_events_2831_);
lean_inc(v_config_2830_);
lean_inc(v_writer_2828_);
lean_inc(v_reader_2829_);
lean_dec(v_machine_2816_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2866_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v_userData_2840_; lean_object* v_outputData_2841_; lean_object* v_state_2842_; lean_object* v_knownSize_2843_; lean_object* v_messageHead_2844_; uint8_t v_sentMessage_2845_; uint8_t v_omitBody_2846_; lean_object* v_userDataBytes_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2865_; 
v_userData_2840_ = lean_ctor_get(v_writer_2828_, 0);
v_outputData_2841_ = lean_ctor_get(v_writer_2828_, 1);
v_state_2842_ = lean_ctor_get(v_writer_2828_, 2);
v_knownSize_2843_ = lean_ctor_get(v_writer_2828_, 3);
v_messageHead_2844_ = lean_ctor_get(v_writer_2828_, 4);
v_sentMessage_2845_ = lean_ctor_get_uint8(v_writer_2828_, sizeof(void*)*6);
v_omitBody_2846_ = lean_ctor_get_uint8(v_writer_2828_, sizeof(void*)*6 + 2);
v_userDataBytes_2847_ = lean_ctor_get(v_writer_2828_, 5);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_writer_2828_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2849_ = v_writer_2828_;
v_isShared_2850_ = v_isSharedCheck_2865_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_userDataBytes_2847_);
lean_inc(v_messageHead_2844_);
lean_inc(v_knownSize_2843_);
lean_inc(v_state_2842_);
lean_inc(v_outputData_2841_);
lean_inc(v_userData_2840_);
lean_dec(v_writer_2828_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2865_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint8_t v___x_2851_; lean_object* v___x_2853_; 
v___x_2851_ = 1;
if (v_isShared_2850_ == 0)
{
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_userData_2840_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_outputData_2841_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_state_2842_);
lean_ctor_set(v_reuseFailAlloc_2864_, 3, v_knownSize_2843_);
lean_ctor_set(v_reuseFailAlloc_2864_, 4, v_messageHead_2844_);
lean_ctor_set(v_reuseFailAlloc_2864_, 5, v_userDataBytes_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*6, v_sentMessage_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*6 + 2, v_omitBody_2846_);
v___x_2853_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2855_; 
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*6 + 1, v___x_2851_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2853_);
v___x_2855_ = v___x_2838_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_reader_2829_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_config_2830_);
lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_events_2831_);
lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_error_2832_);
lean_ctor_set(v_reuseFailAlloc_2863_, 5, v_instant_2833_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*6, v_keepAlive_2834_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*6 + 1, v_forcedFlush_2835_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*6 + 2, v_pullBodyStalled_2836_);
v___x_2855_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v_requestStream_2817_);
lean_ctor_set(v___x_2857_, 2, v_keepAliveTimeout_2818_);
lean_ctor_set(v___x_2857_, 3, v_currentTimeout_2819_);
lean_ctor_set(v___x_2857_, 4, v_headerTimeout_2820_);
lean_ctor_set(v___x_2857_, 5, v_response_2821_);
lean_ctor_set(v___x_2857_, 6, v___x_2856_);
lean_ctor_set(v___x_2857_, 7, v_expectData_2823_);
lean_ctor_set(v___x_2857_, 8, v_pendingHead_2825_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*9, v_requiresData_2822_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*9 + 1, v_handlerDispatched_2824_);
v___x_2858_ = 0;
v___x_2859_ = lean_box(v___x_2858_);
v___x_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2857_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2867_, lean_object* v_requestStream_2868_, lean_object* v_keepAliveTimeout_2869_, lean_object* v_currentTimeout_2870_, lean_object* v_headerTimeout_2871_, lean_object* v_response_2872_, lean_object* v_requiresData_2873_, lean_object* v_expectData_2874_, lean_object* v_handlerDispatched_2875_, lean_object* v_pendingHead_2876_, lean_object* v_____r_2877_, lean_object* v___y_2878_){
_start:
{
uint8_t v_requiresData_boxed_2879_; uint8_t v_handlerDispatched_boxed_2880_; lean_object* v_res_2881_; 
v_requiresData_boxed_2879_ = lean_unbox(v_requiresData_2873_);
v_handlerDispatched_boxed_2880_ = lean_unbox(v_handlerDispatched_2875_);
v_res_2881_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2867_, v_requestStream_2868_, v_keepAliveTimeout_2869_, v_currentTimeout_2870_, v_headerTimeout_2871_, v_response_2872_, v_requiresData_boxed_2879_, v_expectData_2874_, v_handlerDispatched_boxed_2880_, v_pendingHead_2876_, v_____r_2877_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2882_, lean_object* v_x_2883_){
_start:
{
if (lean_obj_tag(v_x_2883_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v___f_2882_);
v_a_2885_ = lean_ctor_get(v_x_2883_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v_x_2883_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v_x_2883_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v_x_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2895_; 
v_a_2894_ = lean_ctor_get(v_x_2883_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v_x_2883_, 1);
v___x_2895_ = lean_apply_2(v___f_2882_, v_a_2894_, lean_box(0));
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2896_, v_x_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2900_, lean_object* v_val_2901_, lean_object* v___f_2902_, lean_object* v___f_2903_, lean_object* v_x_2904_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref(v___f_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v_val_2901_);
lean_dec_ref(v_close_2900_);
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
v___x_2917_ = lean_apply_2(v_close_2900_, v_val_2901_, lean_box(0));
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
lean_dec(v_val_2901_);
lean_dec_ref(v_close_2900_);
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_apply_2(v___f_2903_, v___x_2921_, lean_box(0));
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2923_, lean_object* v_val_2924_, lean_object* v___f_2925_, lean_object* v___f_2926_, lean_object* v_x_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2923_, v_val_2924_, v___f_2925_, v___f_2926_, v_x_2927_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2930_, lean_object* v_handler_2931_, lean_object* v_x_2932_){
_start:
{
if (lean_obj_tag(v_x_2932_) == 0)
{
lean_object* v_a_2934_; lean_object* v_onFailure_2935_; lean_object* v___x_2936_; 
v_a_2934_ = lean_ctor_get(v_x_2932_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v_x_2932_, 1);
v_onFailure_2935_ = lean_ctor_get(v_inst_2930_, 2);
lean_inc_ref(v_onFailure_2935_);
lean_dec_ref(v_inst_2930_);
v___x_2936_ = lean_apply_3(v_onFailure_2935_, v_handler_2931_, v_a_2934_, lean_box(0));
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; 
lean_dec(v_handler_2931_);
lean_dec_ref(v_inst_2930_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_x_2932_);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2938_, lean_object* v_handler_2939_, lean_object* v_x_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2938_, v_handler_2939_, v_x_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2943_, lean_object* v_____r_2944_){
_start:
{
uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2946_ = 0;
v___x_2947_ = lean_box(v___x_2946_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_st_2943_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2951_, lean_object* v_____r_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2951_, v_____r_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2955_, lean_object* v___f_2956_, lean_object* v___f_2957_, lean_object* v_x_2958_){
_start:
{
if (lean_obj_tag(v_x_2958_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___f_2956_);
lean_dec_ref(v_requestStream_2955_);
v_a_2960_ = lean_ctor_get(v_x_2958_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_x_2958_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2962_ = v_x_2958_;
v_isShared_2963_ = v_isSharedCheck_2968_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v_x_2958_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2968_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
return v___x_2966_;
}
}
}
else
{
lean_object* v_a_2969_; uint8_t v___x_2970_; 
v_a_2969_ = lean_ctor_get(v_x_2958_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v_x_2958_, 1);
v___x_2970_ = lean_unbox(v_a_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref(v___f_2957_);
v___x_2971_ = l_Std_Http_Body_Stream_close(v_requestStream_2955_);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_unbox(v_a_2969_);
lean_dec(v_a_2969_);
v___x_2974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2972_, v___x_2973_, v___x_2971_, v___f_2956_);
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec(v_a_2969_);
lean_dec_ref(v___f_2956_);
lean_dec_ref(v_requestStream_2955_);
v___x_2975_ = lean_box(0);
v___x_2976_ = lean_apply_2(v___f_2957_, v___x_2975_, lean_box(0));
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2977_, lean_object* v___f_2978_, lean_object* v___f_2979_, lean_object* v_x_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2977_, v___f_2978_, v___f_2979_, v_x_2980_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2983_, lean_object* v___f_2984_, lean_object* v___f_2985_, lean_object* v_requestStream_2986_, lean_object* v___f_2987_, lean_object* v_x_2988_){
_start:
{
if (lean_obj_tag(v_x_2988_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___f_2987_);
lean_dec_ref(v_requestStream_2986_);
lean_dec_ref(v___f_2985_);
lean_dec_ref(v___f_2984_);
v_a_2990_ = lean_ctor_get(v_x_2988_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_x_2988_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2992_ = v_x_2988_;
v_isShared_2993_ = v_isSharedCheck_2998_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v_x_2988_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2998_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
}
}
else
{
lean_dec_ref_known(v_x_2988_, 1);
if (v_final_2983_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec_ref(v___f_2987_);
lean_dec_ref(v_requestStream_2986_);
lean_dec_ref(v___f_2985_);
v___x_2999_ = lean_box(0);
v___x_3000_ = lean_apply_2(v___f_2984_, v___x_2999_, lean_box(0));
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; lean_object* v___f_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_7002__overap_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref(v___f_2984_);
v___x_3001_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3002_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3003_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3004_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3005_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3005_, 0, lean_box(0));
lean_closure_set(v___x_3005_, 1, lean_box(0));
lean_closure_set(v___x_3005_, 2, v___x_3001_);
lean_closure_set(v___x_3005_, 3, lean_box(0));
lean_closure_set(v___x_3005_, 4, lean_box(0));
lean_closure_set(v___x_3005_, 5, v___x_3004_);
lean_closure_set(v___x_3005_, 6, v___f_2985_);
v___x_7002__overap_3006_ = l_Std_Mutex_atomically___redArg(v___x_3001_, v___f_3002_, v___f_3003_, v_requestStream_2986_, v___x_3005_);
v___x_3007_ = lean_apply_1(v___x_7002__overap_3006_, lean_box(0));
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = 0;
v___x_3010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3008_, v___x_3009_, v___x_3007_, v___f_2987_);
return v___x_3010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3011_, lean_object* v___f_3012_, lean_object* v___f_3013_, lean_object* v_requestStream_3014_, lean_object* v___f_3015_, lean_object* v_x_3016_, lean_object* v___y_3017_){
_start:
{
uint8_t v_final_boxed_3018_; lean_object* v_res_3019_; 
v_final_boxed_3018_ = lean_unbox(v_final_3011_);
v_res_3019_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3018_, v___f_3012_, v___f_3013_, v_requestStream_3014_, v___f_3015_, v_x_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3020_, lean_object* v_x_3021_){
_start:
{
if (lean_obj_tag(v_x_3021_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v_state_3020_);
v_a_3023_ = lean_ctor_get(v_x_3021_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_x_3021_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3025_ = v_x_3021_;
v_isShared_3026_ = v_isSharedCheck_3031_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v_x_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3031_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
}
else
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3061_; 
v_isSharedCheck_3061_ = !lean_is_exclusive(v_x_3021_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v_x_3021_, 0);
lean_dec(v_unused_3062_);
v___x_3033_ = v_x_3021_;
v_isShared_3034_ = v_isSharedCheck_3061_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v_x_3021_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3061_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v_machine_3035_; lean_object* v_requestStream_3036_; lean_object* v_keepAliveTimeout_3037_; lean_object* v_currentTimeout_3038_; lean_object* v_headerTimeout_3039_; lean_object* v_response_3040_; lean_object* v_respStream_3041_; uint8_t v_requiresData_3042_; lean_object* v_expectData_3043_; lean_object* v_pendingHead_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3060_; 
v_machine_3035_ = lean_ctor_get(v_state_3020_, 0);
v_requestStream_3036_ = lean_ctor_get(v_state_3020_, 1);
v_keepAliveTimeout_3037_ = lean_ctor_get(v_state_3020_, 2);
v_currentTimeout_3038_ = lean_ctor_get(v_state_3020_, 3);
v_headerTimeout_3039_ = lean_ctor_get(v_state_3020_, 4);
v_response_3040_ = lean_ctor_get(v_state_3020_, 5);
v_respStream_3041_ = lean_ctor_get(v_state_3020_, 6);
v_requiresData_3042_ = lean_ctor_get_uint8(v_state_3020_, sizeof(void*)*9);
v_expectData_3043_ = lean_ctor_get(v_state_3020_, 7);
v_pendingHead_3044_ = lean_ctor_get(v_state_3020_, 8);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_state_3020_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3046_ = v_state_3020_;
v_isShared_3047_ = v_isSharedCheck_3060_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_pendingHead_3044_);
lean_inc(v_expectData_3043_);
lean_inc(v_respStream_3041_);
lean_inc(v_response_3040_);
lean_inc(v_headerTimeout_3039_);
lean_inc(v_currentTimeout_3038_);
lean_inc(v_keepAliveTimeout_3037_);
lean_inc(v_requestStream_3036_);
lean_inc(v_machine_3035_);
lean_dec(v_state_3020_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3060_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; lean_object* v___x_3052_; 
v___x_3048_ = lean_box(52);
v___x_3049_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3035_, v___x_3048_);
v___x_3050_ = 0;
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3049_);
v___x_3052_ = v___x_3046_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_requestStream_3036_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v_keepAliveTimeout_3037_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v_currentTimeout_3038_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v_headerTimeout_3039_);
lean_ctor_set(v_reuseFailAlloc_3059_, 5, v_response_3040_);
lean_ctor_set(v_reuseFailAlloc_3059_, 6, v_respStream_3041_);
lean_ctor_set(v_reuseFailAlloc_3059_, 7, v_expectData_3043_);
lean_ctor_set(v_reuseFailAlloc_3059_, 8, v_pendingHead_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3059_, sizeof(void*)*9, v_requiresData_3042_);
v___x_3052_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_ctor_set_uint8(v___x_3052_, sizeof(void*)*9 + 1, v___x_3050_);
v___x_3053_ = lean_box(v___x_3050_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3054_);
v___x_3056_ = v___x_3033_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3054_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3063_, lean_object* v_x_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3063_, v_x_3064_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3067_, lean_object* v_requestStream_3068_, lean_object* v_keepAliveTimeout_3069_, lean_object* v_currentTimeout_3070_, lean_object* v_headerTimeout_3071_, lean_object* v_response_3072_, lean_object* v_respStream_3073_, uint8_t v_requiresData_3074_, lean_object* v_expectData_3075_, lean_object* v_pendingHead_3076_, lean_object* v_____r_3077_){
_start:
{
uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3079_ = 0;
v___x_3080_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3080_, 0, v_machine_3067_);
lean_ctor_set(v___x_3080_, 1, v_requestStream_3068_);
lean_ctor_set(v___x_3080_, 2, v_keepAliveTimeout_3069_);
lean_ctor_set(v___x_3080_, 3, v_currentTimeout_3070_);
lean_ctor_set(v___x_3080_, 4, v_headerTimeout_3071_);
lean_ctor_set(v___x_3080_, 5, v_response_3072_);
lean_ctor_set(v___x_3080_, 6, v_respStream_3073_);
lean_ctor_set(v___x_3080_, 7, v_expectData_3075_);
lean_ctor_set(v___x_3080_, 8, v_pendingHead_3076_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*9, v_requiresData_3074_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*9 + 1, v___x_3079_);
v___x_3081_ = lean_box(v___x_3079_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3085_, lean_object* v_requestStream_3086_, lean_object* v_keepAliveTimeout_3087_, lean_object* v_currentTimeout_3088_, lean_object* v_headerTimeout_3089_, lean_object* v_response_3090_, lean_object* v_respStream_3091_, lean_object* v_requiresData_3092_, lean_object* v_expectData_3093_, lean_object* v_pendingHead_3094_, lean_object* v_____r_3095_, lean_object* v___y_3096_){
_start:
{
uint8_t v_requiresData_boxed_3097_; lean_object* v_res_3098_; 
v_requiresData_boxed_3097_ = lean_unbox(v_requiresData_3092_);
v_res_3098_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3085_, v_requestStream_3086_, v_keepAliveTimeout_3087_, v_currentTimeout_3088_, v_headerTimeout_3089_, v_response_3090_, v_respStream_3091_, v_requiresData_boxed_3097_, v_expectData_3093_, v_pendingHead_3094_, v_____r_3095_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3099_, lean_object* v_body_3100_, lean_object* v___f_3101_, lean_object* v___f_3102_, lean_object* v_x_3103_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v___f_3102_);
lean_dec_ref(v___f_3101_);
lean_dec(v_body_3100_);
lean_dec_ref(v_close_3099_);
v_a_3105_ = lean_ctor_get(v_x_3103_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_x_3103_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3107_ = v_x_3103_;
v_isShared_3108_ = v_isSharedCheck_3113_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v_x_3103_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3113_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
}
}
else
{
lean_object* v_a_3114_; uint8_t v___x_3115_; 
v_a_3114_ = lean_ctor_get(v_x_3103_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v_x_3103_, 1);
v___x_3115_ = lean_unbox(v_a_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; 
lean_dec_ref(v___f_3102_);
v___x_3116_ = lean_apply_2(v_close_3099_, v_body_3100_, lean_box(0));
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = lean_unbox(v_a_3114_);
lean_dec(v_a_3114_);
v___x_3119_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3117_, v___x_3118_, v___x_3116_, v___f_3101_);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_dec(v_a_3114_);
lean_dec_ref(v___f_3101_);
lean_dec(v_body_3100_);
lean_dec_ref(v_close_3099_);
v___x_3120_ = lean_box(0);
v___x_3121_ = lean_apply_2(v___f_3102_, v___x_3120_, lean_box(0));
return v___x_3121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3122_, lean_object* v_body_3123_, lean_object* v___f_3124_, lean_object* v___f_3125_, lean_object* v_x_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3122_, v_body_3123_, v___f_3124_, v___f_3125_, v_x_3126_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3129_, lean_object* v_keepAliveTimeout_3130_, lean_object* v_currentTimeout_3131_, lean_object* v_headerTimeout_3132_, lean_object* v_response_3133_, uint8_t v_requiresData_3134_, lean_object* v_expectData_3135_, uint8_t v___x_3136_, lean_object* v_pendingHead_3137_, lean_object* v_____x_3138_){
_start:
{
lean_object* v_fst_3140_; lean_object* v_snd_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3152_; 
v_fst_3140_ = lean_ctor_get(v_____x_3138_, 0);
v_snd_3141_ = lean_ctor_get(v_____x_3138_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_____x_3138_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3143_ = v_____x_3138_;
v_isShared_3144_ = v_isSharedCheck_3152_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_snd_3141_);
lean_inc(v_fst_3140_);
lean_dec(v_____x_3138_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3152_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3145_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3145_, 0, v_fst_3140_);
lean_ctor_set(v___x_3145_, 1, v_requestStream_3129_);
lean_ctor_set(v___x_3145_, 2, v_keepAliveTimeout_3130_);
lean_ctor_set(v___x_3145_, 3, v_currentTimeout_3131_);
lean_ctor_set(v___x_3145_, 4, v_headerTimeout_3132_);
lean_ctor_set(v___x_3145_, 5, v_response_3133_);
lean_ctor_set(v___x_3145_, 6, v_snd_3141_);
lean_ctor_set(v___x_3145_, 7, v_expectData_3135_);
lean_ctor_set(v___x_3145_, 8, v_pendingHead_3137_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*9, v_requiresData_3134_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*9 + 1, v___x_3136_);
v___x_3146_ = lean_box(v___x_3136_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 1, v___x_3146_);
lean_ctor_set(v___x_3143_, 0, v___x_3145_);
v___x_3148_ = v___x_3143_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3153_, lean_object* v_keepAliveTimeout_3154_, lean_object* v_currentTimeout_3155_, lean_object* v_headerTimeout_3156_, lean_object* v_response_3157_, lean_object* v_requiresData_3158_, lean_object* v_expectData_3159_, lean_object* v___x_3160_, lean_object* v_pendingHead_3161_, lean_object* v_____x_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_requiresData_boxed_3164_; uint8_t v___x_7758__boxed_3165_; lean_object* v_res_3166_; 
v_requiresData_boxed_3164_ = lean_unbox(v_requiresData_3158_);
v___x_7758__boxed_3165_ = lean_unbox(v___x_3160_);
v_res_3166_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3153_, v_keepAliveTimeout_3154_, v_currentTimeout_3155_, v_headerTimeout_3156_, v_response_3157_, v_requiresData_boxed_3164_, v_expectData_3159_, v___x_7758__boxed_3165_, v_pendingHead_3161_, v_____x_3162_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3167_, lean_object* v_x_3168_){
_start:
{
if (lean_obj_tag(v_x_3168_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v___f_3167_);
v_a_3170_ = lean_ctor_get(v_x_3168_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_x_3168_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3172_ = v_x_3168_;
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v_x_3168_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
return v___x_3176_;
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3180_; 
v_a_3179_ = lean_ctor_get(v_x_3168_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v_x_3168_, 1);
v___x_3180_ = lean_apply_2(v___f_3167_, v_a_3179_, lean_box(0));
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3181_, lean_object* v_x_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3181_, v_x_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3185_, lean_object* v___f_3186_, lean_object* v_inst_3187_, lean_object* v___f_3188_, lean_object* v_x_3189_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v___f_3188_);
lean_dec_ref(v_inst_3187_);
lean_dec_ref(v___f_3186_);
v_a_3191_ = lean_ctor_get(v_x_3189_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_x_3189_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3193_ = v_x_3189_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v_x_3189_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v_snd_3201_; 
v_a_3200_ = lean_ctor_get(v_x_3189_, 0);
v_snd_3201_ = lean_ctor_get(v_a_3200_, 1);
if (lean_obj_tag(v_snd_3201_) == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec_ref(v___f_3188_);
lean_dec_ref(v_inst_3187_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_x_3189_);
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3203_, v___x_3185_, v___x_3202_, v___f_3186_);
return v___x_3204_;
}
else
{
lean_object* v_fst_3205_; lean_object* v_val_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_inc_ref(v_snd_3201_);
lean_inc(v_a_3200_);
lean_dec_ref_known(v_x_3189_, 1);
lean_dec_ref(v___f_3186_);
v_fst_3205_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_fst_3205_);
lean_dec(v_a_3200_);
v_val_3206_ = lean_ctor_get(v_snd_3201_, 0);
lean_inc(v_val_3206_);
lean_dec_ref_known(v_snd_3201_, 1);
v___x_3207_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3187_, v_fst_3205_, v_val_3206_);
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3208_, v___x_3185_, v___x_3207_, v___f_3188_);
return v___x_3209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3210_, lean_object* v___f_3211_, lean_object* v_inst_3212_, lean_object* v___f_3213_, lean_object* v_x_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v___x_7824__boxed_3216_; lean_object* v_res_3217_; 
v___x_7824__boxed_3216_ = lean_unbox(v___x_3210_);
v_res_3217_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7824__boxed_3216_, v___f_3211_, v_inst_3212_, v___f_3213_, v_x_3214_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_state_3218_, lean_object* v_x_3219_){
_start:
{
if (lean_obj_tag(v_x_3219_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v_state_3218_);
v_a_3221_ = lean_ctor_get(v_x_3219_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_x_3219_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3223_ = v_x_3219_;
v_isShared_3224_ = v_isSharedCheck_3229_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v_x_3219_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3229_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
}
else
{
lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3259_; 
v_isSharedCheck_3259_ = !lean_is_exclusive(v_x_3219_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v_x_3219_, 0);
lean_dec(v_unused_3260_);
v___x_3231_ = v_x_3219_;
v_isShared_3232_ = v_isSharedCheck_3259_;
goto v_resetjp_3230_;
}
else
{
lean_dec(v_x_3219_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3259_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v_machine_3233_; lean_object* v_requestStream_3234_; lean_object* v_keepAliveTimeout_3235_; lean_object* v_currentTimeout_3236_; lean_object* v_headerTimeout_3237_; lean_object* v_response_3238_; lean_object* v_respStream_3239_; uint8_t v_requiresData_3240_; lean_object* v_expectData_3241_; lean_object* v_pendingHead_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3258_; 
v_machine_3233_ = lean_ctor_get(v_state_3218_, 0);
v_requestStream_3234_ = lean_ctor_get(v_state_3218_, 1);
v_keepAliveTimeout_3235_ = lean_ctor_get(v_state_3218_, 2);
v_currentTimeout_3236_ = lean_ctor_get(v_state_3218_, 3);
v_headerTimeout_3237_ = lean_ctor_get(v_state_3218_, 4);
v_response_3238_ = lean_ctor_get(v_state_3218_, 5);
v_respStream_3239_ = lean_ctor_get(v_state_3218_, 6);
v_requiresData_3240_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3241_ = lean_ctor_get(v_state_3218_, 7);
v_pendingHead_3242_ = lean_ctor_get(v_state_3218_, 8);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_state_3218_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3244_ = v_state_3218_;
v_isShared_3245_ = v_isSharedCheck_3258_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_pendingHead_3242_);
lean_inc(v_expectData_3241_);
lean_inc(v_respStream_3239_);
lean_inc(v_response_3238_);
lean_inc(v_headerTimeout_3237_);
lean_inc(v_currentTimeout_3236_);
lean_inc(v_keepAliveTimeout_3235_);
lean_inc(v_requestStream_3234_);
lean_inc(v_machine_3233_);
lean_dec(v_state_3218_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3258_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; lean_object* v___x_3250_; 
v___x_3246_ = lean_box(31);
v___x_3247_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3233_, v___x_3246_);
v___x_3248_ = 0;
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3247_);
v___x_3250_ = v___x_3244_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_requestStream_3234_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_keepAliveTimeout_3235_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_currentTimeout_3236_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_headerTimeout_3237_);
lean_ctor_set(v_reuseFailAlloc_3257_, 5, v_response_3238_);
lean_ctor_set(v_reuseFailAlloc_3257_, 6, v_respStream_3239_);
lean_ctor_set(v_reuseFailAlloc_3257_, 7, v_expectData_3241_);
lean_ctor_set(v_reuseFailAlloc_3257_, 8, v_pendingHead_3242_);
lean_ctor_set_uint8(v_reuseFailAlloc_3257_, sizeof(void*)*9, v_requiresData_3240_);
v___x_3250_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*9 + 1, v___x_3248_);
v___x_3251_ = lean_box(v___x_3248_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3252_);
v___x_3254_ = v___x_3231_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
return v___x_3255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_state_3261_, lean_object* v_x_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_state_3261_, v_x_3262_);
return v_res_3264_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3267_ = lean_mk_io_user_error(v___x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_handler_3270_, lean_object* v_config_3271_, lean_object* v_event_3272_, lean_object* v_state_3273_){
_start:
{
switch(lean_obj_tag(v_event_3272_))
{
case 0:
{
lean_object* v_x_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_handler_3270_);
lean_dec_ref(v_inst_3269_);
lean_dec_ref(v_inst_3268_);
v_x_3275_ = lean_ctor_get(v_event_3272_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_event_3272_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3277_ = v_event_3272_;
v_isShared_3278_ = v_isSharedCheck_3382_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_x_3275_);
lean_dec(v_event_3272_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3382_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
if (lean_obj_tag(v_x_3275_) == 0)
{
lean_object* v_machine_3279_; lean_object* v_reader_3280_; lean_object* v_requestStream_3281_; lean_object* v_keepAliveTimeout_3282_; lean_object* v_currentTimeout_3283_; lean_object* v_headerTimeout_3284_; lean_object* v_response_3285_; lean_object* v_respStream_3286_; uint8_t v_requiresData_3287_; lean_object* v_expectData_3288_; uint8_t v_handlerDispatched_3289_; lean_object* v_pendingHead_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v_config_3271_);
v_machine_3279_ = lean_ctor_get(v_state_3273_, 0);
lean_inc_ref(v_machine_3279_);
v_reader_3280_ = lean_ctor_get(v_machine_3279_, 0);
lean_inc_ref(v_reader_3280_);
v_requestStream_3281_ = lean_ctor_get(v_state_3273_, 1);
v_keepAliveTimeout_3282_ = lean_ctor_get(v_state_3273_, 2);
v_currentTimeout_3283_ = lean_ctor_get(v_state_3273_, 3);
v_headerTimeout_3284_ = lean_ctor_get(v_state_3273_, 4);
v_response_3285_ = lean_ctor_get(v_state_3273_, 5);
v_respStream_3286_ = lean_ctor_get(v_state_3273_, 6);
v_requiresData_3287_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3288_ = lean_ctor_get(v_state_3273_, 7);
v_handlerDispatched_3289_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9 + 1);
v_pendingHead_3290_ = lean_ctor_get(v_state_3273_, 8);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_state_3273_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_state_3273_, 0);
lean_dec(v_unused_3334_);
v___x_3292_ = v_state_3273_;
v_isShared_3293_ = v_isSharedCheck_3333_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_pendingHead_3290_);
lean_inc(v_expectData_3288_);
lean_inc(v_respStream_3286_);
lean_inc(v_response_3285_);
lean_inc(v_headerTimeout_3284_);
lean_inc(v_currentTimeout_3283_);
lean_inc(v_keepAliveTimeout_3282_);
lean_inc(v_requestStream_3281_);
lean_dec(v_state_3273_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3333_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_writer_3294_; lean_object* v_config_3295_; lean_object* v_events_3296_; lean_object* v_error_3297_; lean_object* v_instant_3298_; uint8_t v_keepAlive_3299_; uint8_t v_forcedFlush_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3331_; 
v_writer_3294_ = lean_ctor_get(v_machine_3279_, 1);
v_config_3295_ = lean_ctor_get(v_machine_3279_, 2);
v_events_3296_ = lean_ctor_get(v_machine_3279_, 3);
v_error_3297_ = lean_ctor_get(v_machine_3279_, 4);
v_instant_3298_ = lean_ctor_get(v_machine_3279_, 5);
v_keepAlive_3299_ = lean_ctor_get_uint8(v_machine_3279_, sizeof(void*)*6);
v_forcedFlush_3300_ = lean_ctor_get_uint8(v_machine_3279_, sizeof(void*)*6 + 1);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_machine_3279_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v_machine_3279_, 0);
lean_dec(v_unused_3332_);
v___x_3302_ = v_machine_3279_;
v_isShared_3303_ = v_isSharedCheck_3331_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_instant_3298_);
lean_inc(v_error_3297_);
lean_inc(v_events_3296_);
lean_inc(v_config_3295_);
lean_inc(v_writer_3294_);
lean_dec(v_machine_3279_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3331_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v_state_3304_; lean_object* v_input_3305_; lean_object* v_messageHead_3306_; lean_object* v_messageCount_3307_; lean_object* v_bodyBytesRead_3308_; lean_object* v_headerBytesRead_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3330_; 
v_state_3304_ = lean_ctor_get(v_reader_3280_, 0);
v_input_3305_ = lean_ctor_get(v_reader_3280_, 1);
v_messageHead_3306_ = lean_ctor_get(v_reader_3280_, 2);
v_messageCount_3307_ = lean_ctor_get(v_reader_3280_, 3);
v_bodyBytesRead_3308_ = lean_ctor_get(v_reader_3280_, 4);
v_headerBytesRead_3309_ = lean_ctor_get(v_reader_3280_, 5);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_reader_3280_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3311_ = v_reader_3280_;
v_isShared_3312_ = v_isSharedCheck_3330_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_headerBytesRead_3309_);
lean_inc(v_bodyBytesRead_3308_);
lean_inc(v_messageCount_3307_);
lean_inc(v_messageHead_3306_);
lean_inc(v_input_3305_);
lean_inc(v_state_3304_);
lean_dec(v_reader_3280_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3330_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
uint8_t v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = 1;
if (v_isShared_3312_ == 0)
{
v___x_3315_ = v___x_3311_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_state_3304_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_input_3305_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_messageHead_3306_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_messageCount_3307_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_bodyBytesRead_3308_);
lean_ctor_set(v_reuseFailAlloc_3329_, 5, v_headerBytesRead_3309_);
v___x_3315_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
uint8_t v___x_3316_; lean_object* v___x_3318_; 
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*6, v___x_3313_);
v___x_3316_ = 0;
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3315_);
v___x_3318_ = v___x_3302_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_writer_3294_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v_config_3295_);
lean_ctor_set(v_reuseFailAlloc_3328_, 3, v_events_3296_);
lean_ctor_set(v_reuseFailAlloc_3328_, 4, v_error_3297_);
lean_ctor_set(v_reuseFailAlloc_3328_, 5, v_instant_3298_);
lean_ctor_set_uint8(v_reuseFailAlloc_3328_, sizeof(void*)*6, v_keepAlive_3299_);
lean_ctor_set_uint8(v_reuseFailAlloc_3328_, sizeof(void*)*6 + 1, v_forcedFlush_3300_);
v___x_3318_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3320_; 
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*6 + 2, v___x_3316_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3318_);
v___x_3320_ = v___x_3292_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_requestStream_3281_);
lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_keepAliveTimeout_3282_);
lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_currentTimeout_3283_);
lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_headerTimeout_3284_);
lean_ctor_set(v_reuseFailAlloc_3327_, 5, v_response_3285_);
lean_ctor_set(v_reuseFailAlloc_3327_, 6, v_respStream_3286_);
lean_ctor_set(v_reuseFailAlloc_3327_, 7, v_expectData_3288_);
lean_ctor_set(v_reuseFailAlloc_3327_, 8, v_pendingHead_3290_);
lean_ctor_set_uint8(v_reuseFailAlloc_3327_, sizeof(void*)*9, v_requiresData_3287_);
lean_ctor_set_uint8(v_reuseFailAlloc_3327_, sizeof(void*)*9 + 1, v_handlerDispatched_3289_);
v___x_3320_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3321_ = lean_box(v___x_3316_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set_tag(v___x_3277_, 1);
lean_ctor_set(v___x_3277_, 0, v___x_3322_);
v___x_3324_ = v___x_3277_;
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
}
else
{
lean_object* v_val_3335_; lean_object* v_machine_3336_; lean_object* v_requestStream_3337_; lean_object* v_keepAliveTimeout_3338_; lean_object* v_currentTimeout_3339_; lean_object* v_response_3340_; lean_object* v_respStream_3341_; uint8_t v_requiresData_3342_; lean_object* v_expectData_3343_; uint8_t v_handlerDispatched_3344_; lean_object* v_pendingHead_3345_; lean_object* v___f_3346_; 
lean_del_object(v___x_3277_);
v_val_3335_ = lean_ctor_get(v_x_3275_, 0);
lean_inc_n(v_val_3335_, 2);
lean_dec_ref_known(v_x_3275_, 1);
v_machine_3336_ = lean_ctor_get(v_state_3273_, 0);
v_requestStream_3337_ = lean_ctor_get(v_state_3273_, 1);
v_keepAliveTimeout_3338_ = lean_ctor_get(v_state_3273_, 2);
lean_inc(v_keepAliveTimeout_3338_);
v_currentTimeout_3339_ = lean_ctor_get(v_state_3273_, 3);
v_response_3340_ = lean_ctor_get(v_state_3273_, 5);
v_respStream_3341_ = lean_ctor_get(v_state_3273_, 6);
v_requiresData_3342_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3343_ = lean_ctor_get(v_state_3273_, 7);
v_handlerDispatched_3344_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9 + 1);
v_pendingHead_3345_ = lean_ctor_get(v_state_3273_, 8);
v___f_3346_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3346_, 0, v_val_3335_);
if (lean_obj_tag(v_keepAliveTimeout_3338_) == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec_ref(v___f_3346_);
lean_dec_ref(v_config_3271_);
v___x_3347_ = lean_box(0);
v___x_3348_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3335_, v___x_3347_, v_state_3273_);
return v___x_3348_;
}
else
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3380_; 
lean_inc(v_pendingHead_3345_);
lean_inc(v_expectData_3343_);
lean_inc(v_respStream_3341_);
lean_inc_ref(v_response_3340_);
lean_inc(v_currentTimeout_3339_);
lean_inc_ref(v_requestStream_3337_);
lean_inc_ref(v_machine_3336_);
lean_dec(v_val_3335_);
lean_dec_ref(v_state_3273_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_keepAliveTimeout_3338_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v_keepAliveTimeout_3338_, 0);
lean_dec(v_unused_3381_);
v___x_3350_ = v_keepAliveTimeout_3338_;
v_isShared_3351_ = v_isSharedCheck_3380_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v_keepAliveTimeout_3338_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3380_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___f_3354_; lean_object* v_val_3356_; lean_object* v___x_3363_; 
v___x_3352_ = lean_box(v_requiresData_3342_);
v___x_3353_ = lean_box(v_handlerDispatched_3344_);
v___f_3354_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3354_, 0, v_config_3271_);
lean_closure_set(v___f_3354_, 1, v_machine_3336_);
lean_closure_set(v___f_3354_, 2, v_requestStream_3337_);
lean_closure_set(v___f_3354_, 3, v_currentTimeout_3339_);
lean_closure_set(v___f_3354_, 4, v_response_3340_);
lean_closure_set(v___f_3354_, 5, v_respStream_3341_);
lean_closure_set(v___f_3354_, 6, v___x_3352_);
lean_closure_set(v___f_3354_, 7, v_expectData_3343_);
lean_closure_set(v___f_3354_, 8, v___x_3353_);
lean_closure_set(v___f_3354_, 9, v_pendingHead_3345_);
lean_closure_set(v___f_3354_, 10, v___f_3346_);
v___x_3363_ = lean_get_current_time();
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 1);
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
v_val_3356_ = v___x_3369_;
goto v___jp_3355_;
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
v_a_3372_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3363_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3363_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 0);
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
v_val_3356_ = v___x_3377_;
goto v___jp_3355_;
}
}
}
v___jp_3355_:
{
lean_object* v___x_3358_; 
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 0);
lean_ctor_set(v___x_3350_, 0, v_val_3356_);
v___x_3358_ = v___x_3350_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_val_3356_);
v___x_3358_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = 0;
v___x_3361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3359_, v___x_3360_, v___x_3358_, v___f_3354_);
return v___x_3361_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_config_3271_);
lean_dec(v_handler_3270_);
lean_dec_ref(v_inst_3268_);
v_x_3383_ = lean_ctor_get(v_event_3272_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_event_3272_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3385_ = v_event_3272_;
v_isShared_3386_ = v_isSharedCheck_3498_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_x_3383_);
lean_dec(v_event_3272_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3498_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
if (lean_obj_tag(v_x_3383_) == 0)
{
lean_object* v_machine_3387_; lean_object* v_requestStream_3388_; lean_object* v_keepAliveTimeout_3389_; lean_object* v_currentTimeout_3390_; lean_object* v_headerTimeout_3391_; lean_object* v_response_3392_; lean_object* v_respStream_3393_; uint8_t v_requiresData_3394_; lean_object* v_expectData_3395_; uint8_t v_handlerDispatched_3396_; lean_object* v_pendingHead_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___f_3400_; 
lean_del_object(v___x_3385_);
v_machine_3387_ = lean_ctor_get(v_state_3273_, 0);
lean_inc_ref_n(v_machine_3387_, 2);
v_requestStream_3388_ = lean_ctor_get(v_state_3273_, 1);
lean_inc_ref_n(v_requestStream_3388_, 2);
v_keepAliveTimeout_3389_ = lean_ctor_get(v_state_3273_, 2);
lean_inc_n(v_keepAliveTimeout_3389_, 2);
v_currentTimeout_3390_ = lean_ctor_get(v_state_3273_, 3);
lean_inc_n(v_currentTimeout_3390_, 2);
v_headerTimeout_3391_ = lean_ctor_get(v_state_3273_, 4);
lean_inc_n(v_headerTimeout_3391_, 2);
v_response_3392_ = lean_ctor_get(v_state_3273_, 5);
lean_inc_ref_n(v_response_3392_, 2);
v_respStream_3393_ = lean_ctor_get(v_state_3273_, 6);
lean_inc(v_respStream_3393_);
v_requiresData_3394_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3395_ = lean_ctor_get(v_state_3273_, 7);
lean_inc_n(v_expectData_3395_, 2);
v_handlerDispatched_3396_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9 + 1);
v_pendingHead_3397_ = lean_ctor_get(v_state_3273_, 8);
lean_inc_n(v_pendingHead_3397_, 2);
lean_dec_ref(v_state_3273_);
v___x_3398_ = lean_box(v_requiresData_3394_);
v___x_3399_ = lean_box(v_handlerDispatched_3396_);
v___f_3400_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3400_, 0, v_machine_3387_);
lean_closure_set(v___f_3400_, 1, v_requestStream_3388_);
lean_closure_set(v___f_3400_, 2, v_keepAliveTimeout_3389_);
lean_closure_set(v___f_3400_, 3, v_currentTimeout_3390_);
lean_closure_set(v___f_3400_, 4, v_headerTimeout_3391_);
lean_closure_set(v___f_3400_, 5, v_response_3392_);
lean_closure_set(v___f_3400_, 6, v___x_3398_);
lean_closure_set(v___f_3400_, 7, v_expectData_3395_);
lean_closure_set(v___f_3400_, 8, v___x_3399_);
lean_closure_set(v___f_3400_, 9, v_pendingHead_3397_);
if (lean_obj_tag(v_respStream_3393_) == 1)
{
lean_object* v_val_3401_; lean_object* v_close_3402_; lean_object* v_isClosed_3403_; lean_object* v___x_3404_; lean_object* v___f_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; 
lean_dec(v_pendingHead_3397_);
lean_dec(v_expectData_3395_);
lean_dec_ref(v_response_3392_);
lean_dec(v_headerTimeout_3391_);
lean_dec(v_currentTimeout_3390_);
lean_dec(v_keepAliveTimeout_3389_);
lean_dec_ref(v_requestStream_3388_);
lean_dec_ref(v_machine_3387_);
v_val_3401_ = lean_ctor_get(v_respStream_3393_, 0);
lean_inc_n(v_val_3401_, 2);
lean_dec_ref_known(v_respStream_3393_, 1);
v_close_3402_ = lean_ctor_get(v_inst_3269_, 1);
lean_inc_ref(v_close_3402_);
v_isClosed_3403_ = lean_ctor_get(v_inst_3269_, 2);
lean_inc_ref(v_isClosed_3403_);
lean_dec_ref(v_inst_3269_);
v___x_3404_ = lean_apply_2(v_isClosed_3403_, v_val_3401_, lean_box(0));
lean_inc_ref(v___f_3400_);
v___f_3405_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3405_, 0, v___f_3400_);
v___f_3406_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3406_, 0, v_close_3402_);
lean_closure_set(v___f_3406_, 1, v_val_3401_);
lean_closure_set(v___f_3406_, 2, v___f_3405_);
lean_closure_set(v___f_3406_, 3, v___f_3400_);
v___x_3407_ = lean_unsigned_to_nat(0u);
v___x_3408_ = 0;
v___x_3409_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3407_, v___x_3408_, v___x_3404_, v___f_3406_);
return v___x_3409_;
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec_ref(v___f_3400_);
lean_dec(v_respStream_3393_);
lean_dec_ref(v_inst_3269_);
v___x_3410_ = lean_box(0);
v___x_3411_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3387_, v_requestStream_3388_, v_keepAliveTimeout_3389_, v_currentTimeout_3390_, v_headerTimeout_3391_, v_response_3392_, v_requiresData_3394_, v_expectData_3395_, v_handlerDispatched_3396_, v_pendingHead_3397_, v___x_3410_);
return v___x_3411_;
}
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3497_; 
lean_dec_ref(v_inst_3269_);
v_val_3412_ = lean_ctor_get(v_x_3383_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_x_3383_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3414_ = v_x_3383_;
v_isShared_3415_ = v_isSharedCheck_3497_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_val_3412_);
lean_dec(v_x_3383_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3497_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_machine_3416_; lean_object* v_requestStream_3417_; lean_object* v_keepAliveTimeout_3418_; lean_object* v_currentTimeout_3419_; lean_object* v_headerTimeout_3420_; lean_object* v_response_3421_; lean_object* v_respStream_3422_; uint8_t v_requiresData_3423_; lean_object* v_expectData_3424_; uint8_t v_handlerDispatched_3425_; lean_object* v_pendingHead_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3496_; 
v_machine_3416_ = lean_ctor_get(v_state_3273_, 0);
v_requestStream_3417_ = lean_ctor_get(v_state_3273_, 1);
v_keepAliveTimeout_3418_ = lean_ctor_get(v_state_3273_, 2);
v_currentTimeout_3419_ = lean_ctor_get(v_state_3273_, 3);
v_headerTimeout_3420_ = lean_ctor_get(v_state_3273_, 4);
v_response_3421_ = lean_ctor_get(v_state_3273_, 5);
v_respStream_3422_ = lean_ctor_get(v_state_3273_, 6);
v_requiresData_3423_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3424_ = lean_ctor_get(v_state_3273_, 7);
v_handlerDispatched_3425_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9 + 1);
v_pendingHead_3426_ = lean_ctor_get(v_state_3273_, 8);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_state_3273_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3428_ = v_state_3273_;
v_isShared_3429_ = v_isSharedCheck_3496_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_pendingHead_3426_);
lean_inc(v_expectData_3424_);
lean_inc(v_respStream_3422_);
lean_inc(v_response_3421_);
lean_inc(v_headerTimeout_3420_);
lean_inc(v_currentTimeout_3419_);
lean_inc(v_keepAliveTimeout_3418_);
lean_inc(v_requestStream_3417_);
lean_inc(v_machine_3416_);
lean_dec(v_state_3273_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3496_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___y_3431_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3444_ = lean_unsigned_to_nat(1u);
v___x_3445_ = lean_mk_empty_array_with_capacity(v___x_3444_);
v___x_3446_ = lean_array_push(v___x_3445_, v_val_3412_);
v___x_3447_ = lean_array_get_size(v___x_3446_);
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = lean_nat_dec_eq(v___x_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_object* v_reader_3450_; lean_object* v_writer_3451_; lean_object* v_config_3452_; lean_object* v_events_3453_; lean_object* v_error_3454_; lean_object* v_instant_3455_; uint8_t v_keepAlive_3456_; uint8_t v_forcedFlush_3457_; uint8_t v_pullBodyStalled_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3495_; 
v_reader_3450_ = lean_ctor_get(v_machine_3416_, 0);
v_writer_3451_ = lean_ctor_get(v_machine_3416_, 1);
v_config_3452_ = lean_ctor_get(v_machine_3416_, 2);
v_events_3453_ = lean_ctor_get(v_machine_3416_, 3);
v_error_3454_ = lean_ctor_get(v_machine_3416_, 4);
v_instant_3455_ = lean_ctor_get(v_machine_3416_, 5);
v_keepAlive_3456_ = lean_ctor_get_uint8(v_machine_3416_, sizeof(void*)*6);
v_forcedFlush_3457_ = lean_ctor_get_uint8(v_machine_3416_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3458_ = lean_ctor_get_uint8(v_machine_3416_, sizeof(void*)*6 + 2);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_machine_3416_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3460_ = v_machine_3416_;
v_isShared_3461_ = v_isSharedCheck_3495_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_instant_3455_);
lean_inc(v_error_3454_);
lean_inc(v_events_3453_);
lean_inc(v_config_3452_);
lean_inc(v_writer_3451_);
lean_inc(v_reader_3450_);
lean_dec(v_machine_3416_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3495_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___y_3463_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3485_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3486_ = lean_nat_dec_lt(v___x_3448_, v___x_3447_);
if (v___x_3486_ == 0)
{
v___y_3463_ = v___x_3448_;
goto v___jp_3462_;
}
else
{
lean_object* v___f_3487_; uint8_t v___x_3488_; 
v___f_3487_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3488_ = lean_nat_dec_le(v___x_3447_, v___x_3447_);
if (v___x_3488_ == 0)
{
if (v___x_3486_ == 0)
{
v___y_3463_ = v___x_3448_;
goto v___jp_3462_;
}
else
{
size_t v___x_3489_; size_t v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = ((size_t)0ULL);
v___x_3490_ = lean_usize_of_nat(v___x_3447_);
lean_inc_ref(v___x_3446_);
v___x_3491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3485_, v___f_3487_, v___x_3446_, v___x_3489_, v___x_3490_, v___x_3448_);
v___y_3463_ = v___x_3491_;
goto v___jp_3462_;
}
}
else
{
size_t v___x_3492_; size_t v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = ((size_t)0ULL);
v___x_3493_ = lean_usize_of_nat(v___x_3447_);
lean_inc_ref(v___x_3446_);
v___x_3494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3485_, v___f_3487_, v___x_3446_, v___x_3492_, v___x_3493_, v___x_3448_);
v___y_3463_ = v___x_3494_;
goto v___jp_3462_;
}
}
v___jp_3462_:
{
lean_object* v_userData_3464_; lean_object* v_outputData_3465_; lean_object* v_state_3466_; lean_object* v_knownSize_3467_; lean_object* v_messageHead_3468_; uint8_t v_sentMessage_3469_; uint8_t v_userClosedBody_3470_; uint8_t v_omitBody_3471_; lean_object* v_userDataBytes_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3484_; 
v_userData_3464_ = lean_ctor_get(v_writer_3451_, 0);
v_outputData_3465_ = lean_ctor_get(v_writer_3451_, 1);
v_state_3466_ = lean_ctor_get(v_writer_3451_, 2);
v_knownSize_3467_ = lean_ctor_get(v_writer_3451_, 3);
v_messageHead_3468_ = lean_ctor_get(v_writer_3451_, 4);
v_sentMessage_3469_ = lean_ctor_get_uint8(v_writer_3451_, sizeof(void*)*6);
v_userClosedBody_3470_ = lean_ctor_get_uint8(v_writer_3451_, sizeof(void*)*6 + 1);
v_omitBody_3471_ = lean_ctor_get_uint8(v_writer_3451_, sizeof(void*)*6 + 2);
v_userDataBytes_3472_ = lean_ctor_get(v_writer_3451_, 5);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_writer_3451_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3474_ = v_writer_3451_;
v_isShared_3475_ = v_isSharedCheck_3484_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_userDataBytes_3472_);
lean_inc(v_messageHead_3468_);
lean_inc(v_knownSize_3467_);
lean_inc(v_state_3466_);
lean_inc(v_outputData_3465_);
lean_inc(v_userData_3464_);
lean_dec(v_writer_3451_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3484_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3476_ = l_Array_append___redArg(v_userData_3464_, v___x_3446_);
lean_dec_ref(v___x_3446_);
v___x_3477_ = lean_nat_add(v_userDataBytes_3472_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec(v_userDataBytes_3472_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 5, v___x_3477_);
lean_ctor_set(v___x_3474_, 0, v___x_3476_);
v___x_3479_ = v___x_3474_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_outputData_3465_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_state_3466_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_knownSize_3467_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_messageHead_3468_);
lean_ctor_set(v_reuseFailAlloc_3483_, 5, v___x_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3483_, sizeof(void*)*6, v_sentMessage_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3483_, sizeof(void*)*6 + 1, v_userClosedBody_3470_);
lean_ctor_set_uint8(v_reuseFailAlloc_3483_, sizeof(void*)*6 + 2, v_omitBody_3471_);
v___x_3479_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3481_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v___x_3479_);
v___x_3481_ = v___x_3460_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_reader_3450_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_config_3452_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_events_3453_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v_error_3454_);
lean_ctor_set(v_reuseFailAlloc_3482_, 5, v_instant_3455_);
lean_ctor_set_uint8(v_reuseFailAlloc_3482_, sizeof(void*)*6, v_keepAlive_3456_);
lean_ctor_set_uint8(v_reuseFailAlloc_3482_, sizeof(void*)*6 + 1, v_forcedFlush_3457_);
lean_ctor_set_uint8(v_reuseFailAlloc_3482_, sizeof(void*)*6 + 2, v_pullBodyStalled_3458_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
v___y_3431_ = v___x_3481_;
goto v___jp_3430_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3446_);
v___y_3431_ = v_machine_3416_;
goto v___jp_3430_;
}
v___jp_3430_:
{
lean_object* v___x_3433_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___y_3431_);
v___x_3433_ = v___x_3428_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___y_3431_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_requestStream_3417_);
lean_ctor_set(v_reuseFailAlloc_3443_, 2, v_keepAliveTimeout_3418_);
lean_ctor_set(v_reuseFailAlloc_3443_, 3, v_currentTimeout_3419_);
lean_ctor_set(v_reuseFailAlloc_3443_, 4, v_headerTimeout_3420_);
lean_ctor_set(v_reuseFailAlloc_3443_, 5, v_response_3421_);
lean_ctor_set(v_reuseFailAlloc_3443_, 6, v_respStream_3422_);
lean_ctor_set(v_reuseFailAlloc_3443_, 7, v_expectData_3424_);
lean_ctor_set(v_reuseFailAlloc_3443_, 8, v_pendingHead_3426_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, sizeof(void*)*9, v_requiresData_3423_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, sizeof(void*)*9 + 1, v_handlerDispatched_3425_);
v___x_3433_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
uint8_t v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3434_ = 0;
v___x_3435_ = lean_box(v___x_3434_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3433_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3436_);
v___x_3438_ = v___x_3414_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3438_);
v___x_3440_ = v___x_3385_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
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
uint8_t v_x_3499_; 
lean_dec_ref(v_config_3271_);
lean_dec_ref(v_inst_3269_);
v_x_3499_ = lean_ctor_get_uint8(v_event_3272_, 0);
lean_dec_ref_known(v_event_3272_, 0);
if (v_x_3499_ == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_dec(v_handler_3270_);
lean_dec_ref(v_inst_3268_);
v___x_3500_ = lean_box(v_x_3499_);
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_state_3273_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
return v___x_3503_;
}
else
{
lean_object* v_machine_3504_; lean_object* v_requestStream_3505_; lean_object* v_keepAliveTimeout_3506_; lean_object* v_currentTimeout_3507_; lean_object* v_headerTimeout_3508_; lean_object* v_response_3509_; lean_object* v_respStream_3510_; uint8_t v_requiresData_3511_; lean_object* v_expectData_3512_; uint8_t v_handlerDispatched_3513_; lean_object* v_pendingHead_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3564_; 
v_machine_3504_ = lean_ctor_get(v_state_3273_, 0);
v_requestStream_3505_ = lean_ctor_get(v_state_3273_, 1);
v_keepAliveTimeout_3506_ = lean_ctor_get(v_state_3273_, 2);
v_currentTimeout_3507_ = lean_ctor_get(v_state_3273_, 3);
v_headerTimeout_3508_ = lean_ctor_get(v_state_3273_, 4);
v_response_3509_ = lean_ctor_get(v_state_3273_, 5);
v_respStream_3510_ = lean_ctor_get(v_state_3273_, 6);
v_requiresData_3511_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3512_ = lean_ctor_get(v_state_3273_, 7);
v_handlerDispatched_3513_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9 + 1);
v_pendingHead_3514_ = lean_ctor_get(v_state_3273_, 8);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_state_3273_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3516_ = v_state_3273_;
v_isShared_3517_ = v_isSharedCheck_3564_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_pendingHead_3514_);
lean_inc(v_expectData_3512_);
lean_inc(v_respStream_3510_);
lean_inc(v_response_3509_);
lean_inc(v_headerTimeout_3508_);
lean_inc(v_currentTimeout_3507_);
lean_inc(v_keepAliveTimeout_3506_);
lean_inc(v_requestStream_3505_);
lean_inc(v_machine_3504_);
lean_dec(v_state_3273_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3564_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v_fst_3520_; lean_object* v_snd_3521_; lean_object* v_reader_3522_; lean_object* v_writer_3523_; lean_object* v_config_3524_; lean_object* v_events_3525_; lean_object* v_error_3526_; lean_object* v_instant_3527_; uint8_t v_keepAlive_3528_; uint8_t v_forcedFlush_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3563_; 
v___x_3518_ = 0;
v___x_3519_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3518_, v_machine_3504_);
v_fst_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_fst_3520_);
v_snd_3521_ = lean_ctor_get(v___x_3519_, 1);
lean_inc(v_snd_3521_);
lean_dec_ref(v___x_3519_);
v_reader_3522_ = lean_ctor_get(v_fst_3520_, 0);
v_writer_3523_ = lean_ctor_get(v_fst_3520_, 1);
v_config_3524_ = lean_ctor_get(v_fst_3520_, 2);
v_events_3525_ = lean_ctor_get(v_fst_3520_, 3);
v_error_3526_ = lean_ctor_get(v_fst_3520_, 4);
v_instant_3527_ = lean_ctor_get(v_fst_3520_, 5);
v_keepAlive_3528_ = lean_ctor_get_uint8(v_fst_3520_, sizeof(void*)*6);
v_forcedFlush_3529_ = lean_ctor_get_uint8(v_fst_3520_, sizeof(void*)*6 + 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_fst_3520_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3531_ = v_fst_3520_;
v_isShared_3532_ = v_isSharedCheck_3563_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_instant_3527_);
lean_inc(v_error_3526_);
lean_inc(v_events_3525_);
lean_inc(v_config_3524_);
lean_inc(v_writer_3523_);
lean_inc(v_reader_3522_);
lean_dec(v_fst_3520_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3563_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___f_3533_; lean_object* v___f_3534_; uint8_t v___y_3536_; 
v___f_3533_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3533_, 0, v_inst_3268_);
lean_closure_set(v___f_3533_, 1, v_handler_3270_);
v___f_3534_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3521_) == 0)
{
uint8_t v_sentMessage_3559_; 
v_sentMessage_3559_ = lean_ctor_get_uint8(v_writer_3523_, sizeof(void*)*6);
if (v_sentMessage_3559_ == 0)
{
lean_object* v_state_3560_; 
v_state_3560_ = lean_ctor_get(v_reader_3522_, 0);
if (lean_obj_tag(v_state_3560_) == 2)
{
v___y_3536_ = v_x_3499_;
goto v___jp_3535_;
}
else
{
v___y_3536_ = v_sentMessage_3559_;
goto v___jp_3535_;
}
}
else
{
uint8_t v___x_3561_; 
v___x_3561_ = 0;
v___y_3536_ = v___x_3561_;
goto v___jp_3535_;
}
}
else
{
uint8_t v___x_3562_; 
v___x_3562_ = 0;
v___y_3536_ = v___x_3562_;
goto v___jp_3535_;
}
v___jp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3532_ == 0)
{
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_reader_3522_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_writer_3523_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_config_3524_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_events_3525_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_error_3526_);
lean_ctor_set(v_reuseFailAlloc_3558_, 5, v_instant_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3558_, sizeof(void*)*6, v_keepAlive_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3558_, sizeof(void*)*6 + 1, v_forcedFlush_3529_);
v___x_3538_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v_st_3540_; 
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*6 + 2, v___y_3536_);
lean_inc_ref(v_requestStream_3505_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3538_);
v_st_3540_ = v___x_3516_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_requestStream_3505_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_keepAliveTimeout_3506_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_currentTimeout_3507_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_headerTimeout_3508_);
lean_ctor_set(v_reuseFailAlloc_3557_, 5, v_response_3509_);
lean_ctor_set(v_reuseFailAlloc_3557_, 6, v_respStream_3510_);
lean_ctor_set(v_reuseFailAlloc_3557_, 7, v_expectData_3512_);
lean_ctor_set(v_reuseFailAlloc_3557_, 8, v_pendingHead_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3557_, sizeof(void*)*9, v_requiresData_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3557_, sizeof(void*)*9 + 1, v_handlerDispatched_3513_);
v_st_3540_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___f_3541_; 
lean_inc_ref(v_st_3540_);
v___f_3541_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3541_, 0, v_st_3540_);
if (lean_obj_tag(v_snd_3521_) == 1)
{
lean_object* v_val_3542_; uint8_t v_final_3543_; uint8_t v_incomplete_3544_; lean_object* v_chunk_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___f_3550_; lean_object* v___f_3551_; lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; 
lean_dec_ref(v_st_3540_);
v_val_3542_ = lean_ctor_get(v_snd_3521_, 0);
lean_inc(v_val_3542_);
lean_dec_ref_known(v_snd_3521_, 1);
v_final_3543_ = lean_ctor_get_uint8(v_val_3542_, sizeof(void*)*1);
v_incomplete_3544_ = lean_ctor_get_uint8(v_val_3542_, sizeof(void*)*1 + 1);
v_chunk_3545_ = lean_ctor_get(v_val_3542_, 0);
lean_inc_ref(v_chunk_3545_);
lean_dec(v_val_3542_);
lean_inc_ref_n(v_requestStream_3505_, 2);
v___x_3546_ = l_Std_Http_Body_Stream_send(v_requestStream_3505_, v_chunk_3545_, v_incomplete_3544_);
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = 0;
v___x_3549_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3547_, v___x_3548_, v___x_3546_, v___f_3533_);
lean_inc_ref_n(v___f_3541_, 2);
v___f_3550_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3550_, 0, v___f_3541_);
v___f_3551_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3551_, 0, v_requestStream_3505_);
lean_closure_set(v___f_3551_, 1, v___f_3550_);
lean_closure_set(v___f_3551_, 2, v___f_3541_);
v___x_3552_ = lean_box(v_final_3543_);
v___f_3553_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3553_, 0, v___x_3552_);
lean_closure_set(v___f_3553_, 1, v___f_3541_);
lean_closure_set(v___f_3553_, 2, v___f_3534_);
lean_closure_set(v___f_3553_, 3, v_requestStream_3505_);
lean_closure_set(v___f_3553_, 4, v___f_3551_);
v___x_3554_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3547_, v___x_3548_, v___x_3549_, v___f_3553_);
return v___x_3554_;
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec_ref(v___f_3541_);
lean_dec_ref(v___f_3533_);
lean_dec(v_snd_3521_);
lean_dec_ref(v_requestStream_3505_);
v___x_3555_ = lean_box(0);
v___x_3556_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3540_, v___x_3555_);
return v___x_3556_;
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
lean_object* v_x_3565_; 
v_x_3565_ = lean_ctor_get(v_event_3272_, 0);
lean_inc_ref(v_x_3565_);
lean_dec_ref_known(v_event_3272_, 1);
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v_onFailure_3567_; lean_object* v___x_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; 
lean_dec_ref(v_config_3271_);
lean_dec_ref(v_inst_3269_);
v_a_3566_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v_x_3565_, 1);
v_onFailure_3567_ = lean_ctor_get(v_inst_3268_, 2);
lean_inc_ref(v_onFailure_3567_);
lean_dec_ref(v_inst_3268_);
v___x_3568_ = lean_apply_3(v_onFailure_3567_, v_handler_3270_, v_a_3566_, lean_box(0));
v___f_3569_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3569_, 0, v_state_3273_);
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = 0;
v___x_3572_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3570_, v___x_3571_, v___x_3568_, v___f_3569_);
return v___x_3572_;
}
else
{
lean_object* v_machine_3573_; lean_object* v_reader_3574_; lean_object* v_state_3575_; 
lean_dec(v_handler_3270_);
lean_dec_ref(v_inst_3268_);
v_machine_3573_ = lean_ctor_get(v_state_3273_, 0);
lean_inc_ref(v_machine_3573_);
v_reader_3574_ = lean_ctor_get(v_machine_3573_, 0);
v_state_3575_ = lean_ctor_get(v_reader_3574_, 0);
if (lean_obj_tag(v_state_3575_) == 7)
{
lean_object* v_a_3576_; lean_object* v_requestStream_3577_; lean_object* v_keepAliveTimeout_3578_; lean_object* v_currentTimeout_3579_; lean_object* v_headerTimeout_3580_; lean_object* v_response_3581_; lean_object* v_respStream_3582_; uint8_t v_requiresData_3583_; lean_object* v_expectData_3584_; lean_object* v_pendingHead_3585_; lean_object* v_close_3586_; lean_object* v_isClosed_3587_; lean_object* v_body_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; 
lean_dec_ref(v_config_3271_);
v_a_3576_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v_x_3565_, 1);
v_requestStream_3577_ = lean_ctor_get(v_state_3273_, 1);
lean_inc_ref(v_requestStream_3577_);
v_keepAliveTimeout_3578_ = lean_ctor_get(v_state_3273_, 2);
lean_inc(v_keepAliveTimeout_3578_);
v_currentTimeout_3579_ = lean_ctor_get(v_state_3273_, 3);
lean_inc(v_currentTimeout_3579_);
v_headerTimeout_3580_ = lean_ctor_get(v_state_3273_, 4);
lean_inc(v_headerTimeout_3580_);
v_response_3581_ = lean_ctor_get(v_state_3273_, 5);
lean_inc_ref(v_response_3581_);
v_respStream_3582_ = lean_ctor_get(v_state_3273_, 6);
lean_inc(v_respStream_3582_);
v_requiresData_3583_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3584_ = lean_ctor_get(v_state_3273_, 7);
lean_inc(v_expectData_3584_);
v_pendingHead_3585_ = lean_ctor_get(v_state_3273_, 8);
lean_inc(v_pendingHead_3585_);
lean_dec_ref(v_state_3273_);
v_close_3586_ = lean_ctor_get(v_inst_3269_, 1);
lean_inc_ref(v_close_3586_);
v_isClosed_3587_ = lean_ctor_get(v_inst_3269_, 2);
lean_inc_ref(v_isClosed_3587_);
lean_dec_ref(v_inst_3269_);
v_body_3588_ = lean_ctor_get(v_a_3576_, 1);
lean_inc_n(v_body_3588_, 2);
lean_dec(v_a_3576_);
v___x_3589_ = lean_apply_2(v_isClosed_3587_, v_body_3588_, lean_box(0));
v___x_3590_ = lean_box(v_requiresData_3583_);
v___f_3591_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3591_, 0, v_machine_3573_);
lean_closure_set(v___f_3591_, 1, v_requestStream_3577_);
lean_closure_set(v___f_3591_, 2, v_keepAliveTimeout_3578_);
lean_closure_set(v___f_3591_, 3, v_currentTimeout_3579_);
lean_closure_set(v___f_3591_, 4, v_headerTimeout_3580_);
lean_closure_set(v___f_3591_, 5, v_response_3581_);
lean_closure_set(v___f_3591_, 6, v_respStream_3582_);
lean_closure_set(v___f_3591_, 7, v___x_3590_);
lean_closure_set(v___f_3591_, 8, v_expectData_3584_);
lean_closure_set(v___f_3591_, 9, v_pendingHead_3585_);
lean_inc_ref(v___f_3591_);
v___f_3592_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3592_, 0, v___f_3591_);
v___f_3593_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3593_, 0, v_close_3586_);
lean_closure_set(v___f_3593_, 1, v_body_3588_);
lean_closure_set(v___f_3593_, 2, v___f_3592_);
lean_closure_set(v___f_3593_, 3, v___f_3591_);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = 0;
v___x_3596_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3594_, v___x_3595_, v___x_3589_, v___f_3593_);
return v___x_3596_;
}
else
{
lean_object* v_a_3597_; lean_object* v_requestStream_3598_; lean_object* v_keepAliveTimeout_3599_; lean_object* v_currentTimeout_3600_; lean_object* v_headerTimeout_3601_; lean_object* v_response_3602_; uint8_t v_requiresData_3603_; lean_object* v_expectData_3604_; lean_object* v_pendingHead_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___f_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___f_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_a_3597_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v_x_3565_, 1);
v_requestStream_3598_ = lean_ctor_get(v_state_3273_, 1);
lean_inc_ref(v_requestStream_3598_);
v_keepAliveTimeout_3599_ = lean_ctor_get(v_state_3273_, 2);
lean_inc(v_keepAliveTimeout_3599_);
v_currentTimeout_3600_ = lean_ctor_get(v_state_3273_, 3);
lean_inc(v_currentTimeout_3600_);
v_headerTimeout_3601_ = lean_ctor_get(v_state_3273_, 4);
lean_inc(v_headerTimeout_3601_);
v_response_3602_ = lean_ctor_get(v_state_3273_, 5);
lean_inc_ref(v_response_3602_);
v_requiresData_3603_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3604_ = lean_ctor_get(v_state_3273_, 7);
lean_inc(v_expectData_3604_);
v_pendingHead_3605_ = lean_ctor_get(v_state_3273_, 8);
lean_inc(v_pendingHead_3605_);
lean_dec_ref(v_state_3273_);
lean_inc_ref(v_inst_3269_);
v___x_3606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3269_, v_config_3271_, v_machine_3573_, v_a_3597_);
v___x_3607_ = 0;
v___x_3608_ = lean_box(v_requiresData_3603_);
v___x_3609_ = lean_box(v___x_3607_);
v___f_3610_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3610_, 0, v_requestStream_3598_);
lean_closure_set(v___f_3610_, 1, v_keepAliveTimeout_3599_);
lean_closure_set(v___f_3610_, 2, v_currentTimeout_3600_);
lean_closure_set(v___f_3610_, 3, v_headerTimeout_3601_);
lean_closure_set(v___f_3610_, 4, v_response_3602_);
lean_closure_set(v___f_3610_, 5, v___x_3608_);
lean_closure_set(v___f_3610_, 6, v_expectData_3604_);
lean_closure_set(v___f_3610_, 7, v___x_3609_);
lean_closure_set(v___f_3610_, 8, v_pendingHead_3605_);
v___f_3611_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3611_, 0, v___f_3610_);
v___x_3612_ = lean_box(v___x_3607_);
lean_inc_ref(v___f_3611_);
v___f_3613_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 6, 4);
lean_closure_set(v___f_3613_, 0, v___x_3612_);
lean_closure_set(v___f_3613_, 1, v___f_3611_);
lean_closure_set(v___f_3613_, 2, v_inst_3269_);
lean_closure_set(v___f_3613_, 3, v___f_3611_);
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3614_, v___x_3607_, v___x_3606_, v___f_3613_);
return v___x_3615_;
}
}
}
case 4:
{
lean_object* v_onFailure_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; 
lean_dec_ref(v_config_3271_);
lean_dec_ref(v_inst_3269_);
v_onFailure_3616_ = lean_ctor_get(v_inst_3268_, 2);
lean_inc_ref(v_onFailure_3616_);
lean_dec_ref(v_inst_3268_);
v___x_3617_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_3618_ = lean_apply_3(v_onFailure_3616_, v_handler_3270_, v___x_3617_, lean_box(0));
v___f_3619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 3, 1);
lean_closure_set(v___f_3619_, 0, v_state_3273_);
v___x_3620_ = lean_unsigned_to_nat(0u);
v___x_3621_ = 0;
v___x_3622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3620_, v___x_3621_, v___x_3618_, v___f_3619_);
return v___x_3622_;
}
case 5:
{
lean_object* v_machine_3623_; lean_object* v_requestStream_3624_; lean_object* v_keepAliveTimeout_3625_; lean_object* v_currentTimeout_3626_; lean_object* v_headerTimeout_3627_; lean_object* v_response_3628_; lean_object* v_respStream_3629_; uint8_t v_requiresData_3630_; lean_object* v_expectData_3631_; lean_object* v_pendingHead_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_config_3271_);
lean_dec(v_handler_3270_);
lean_dec_ref(v_inst_3269_);
lean_dec_ref(v_inst_3268_);
v_machine_3623_ = lean_ctor_get(v_state_3273_, 0);
v_requestStream_3624_ = lean_ctor_get(v_state_3273_, 1);
v_keepAliveTimeout_3625_ = lean_ctor_get(v_state_3273_, 2);
v_currentTimeout_3626_ = lean_ctor_get(v_state_3273_, 3);
v_headerTimeout_3627_ = lean_ctor_get(v_state_3273_, 4);
v_response_3628_ = lean_ctor_get(v_state_3273_, 5);
v_respStream_3629_ = lean_ctor_get(v_state_3273_, 6);
v_requiresData_3630_ = lean_ctor_get_uint8(v_state_3273_, sizeof(void*)*9);
v_expectData_3631_ = lean_ctor_get(v_state_3273_, 7);
v_pendingHead_3632_ = lean_ctor_get(v_state_3273_, 8);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_state_3273_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3634_ = v_state_3273_;
v_isShared_3635_ = v_isSharedCheck_3646_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_pendingHead_3632_);
lean_inc(v_expectData_3631_);
lean_inc(v_respStream_3629_);
lean_inc(v_response_3628_);
lean_inc(v_headerTimeout_3627_);
lean_inc(v_currentTimeout_3626_);
lean_inc(v_keepAliveTimeout_3625_);
lean_inc(v_requestStream_3624_);
lean_inc(v_machine_3623_);
lean_dec(v_state_3273_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3646_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; lean_object* v___x_3640_; 
v___x_3636_ = lean_box(55);
v___x_3637_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3623_, v___x_3636_);
v___x_3638_ = 0;
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3637_);
v___x_3640_ = v___x_3634_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_requestStream_3624_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_keepAliveTimeout_3625_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_currentTimeout_3626_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_headerTimeout_3627_);
lean_ctor_set(v_reuseFailAlloc_3645_, 5, v_response_3628_);
lean_ctor_set(v_reuseFailAlloc_3645_, 6, v_respStream_3629_);
lean_ctor_set(v_reuseFailAlloc_3645_, 7, v_expectData_3631_);
lean_ctor_set(v_reuseFailAlloc_3645_, 8, v_pendingHead_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3645_, sizeof(void*)*9, v_requiresData_3630_);
v___x_3640_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_ctor_set_uint8(v___x_3640_, sizeof(void*)*9 + 1, v___x_3638_);
v___x_3641_ = lean_box(v___x_3638_);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
}
}
default: 
{
uint8_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec_ref(v_config_3271_);
lean_dec(v_handler_3270_);
lean_dec_ref(v_inst_3269_);
lean_dec_ref(v_inst_3268_);
v___x_3647_ = 1;
v___x_3648_ = lean_box(v___x_3647_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v_state_3273_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_handler_3654_, lean_object* v_config_3655_, lean_object* v_event_3656_, lean_object* v_state_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3652_, v_inst_3653_, v_handler_3654_, v_config_3655_, v_event_3656_, v_state_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3660_, lean_object* v_00_u03b2_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_handler_3664_, lean_object* v_config_3665_, lean_object* v_event_3666_, lean_object* v_state_3667_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3662_, v_inst_3663_, v_handler_3664_, v_config_3665_, v_event_3666_, v_state_3667_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3670_, lean_object* v_00_u03b2_3671_, lean_object* v_inst_3672_, lean_object* v_inst_3673_, lean_object* v_handler_3674_, lean_object* v_config_3675_, lean_object* v_event_3676_, lean_object* v_state_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3670_, v_00_u03b2_3671_, v_inst_3672_, v_inst_3673_, v_handler_3674_, v_config_3675_, v_event_3676_, v_state_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3680_, uint8_t v_handlerDispatched_3681_, lean_object* v_headerTimeout_3682_, lean_object* v_expectData_3683_, lean_object* v_respStream_3684_, lean_object* v_keepAliveTimeout_3685_, lean_object* v_currentTimeout_3686_, lean_object* v_response_3687_, lean_object* v_socket_3688_, uint8_t v_requiresData_3689_, uint8_t v_sentMessage_3690_, lean_object* v_reader_3691_, uint8_t v_requestBodyInterested_3692_, lean_object* v_requestBody_3693_){
_start:
{
lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3707_; 
if (v_requiresData_3689_ == 0)
{
if (v_handlerDispatched_3681_ == 0)
{
goto v___jp_3710_;
}
else
{
if (lean_obj_tag(v_respStream_3684_) == 0)
{
if (v_sentMessage_3690_ == 0)
{
lean_object* v_state_3714_; 
v_state_3714_ = lean_ctor_get(v_reader_3691_, 0);
if (lean_obj_tag(v_state_3714_) == 2)
{
if (v_requestBodyInterested_3692_ == 0)
{
lean_dec(v_socket_3688_);
goto v___jp_3712_;
}
else
{
goto v___jp_3710_;
}
}
else
{
lean_dec(v_socket_3688_);
goto v___jp_3712_;
}
}
else
{
goto v___jp_3710_;
}
}
else
{
goto v___jp_3710_;
}
}
}
else
{
goto v___jp_3710_;
}
v___jp_3695_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3703_, 0, v___y_3696_);
lean_ctor_set(v___x_3703_, 1, v___y_3698_);
lean_ctor_set(v___x_3703_, 2, v___y_3702_);
lean_ctor_set(v___x_3703_, 3, v___y_3699_);
lean_ctor_set(v___x_3703_, 4, v_requestBody_3693_);
lean_ctor_set(v___x_3703_, 5, v___y_3701_);
lean_ctor_set(v___x_3703_, 6, v___y_3700_);
lean_ctor_set(v___x_3703_, 7, v___y_3697_);
lean_ctor_set(v___x_3703_, 8, v_connectionContext_3680_);
v___x_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
v___jp_3706_:
{
if (v_handlerDispatched_3681_ == 0)
{
lean_object* v___x_3708_; 
lean_dec_ref(v_response_3687_);
v___x_3708_ = lean_box(0);
v___y_3696_ = v___y_3707_;
v___y_3697_ = v_headerTimeout_3682_;
v___y_3698_ = v_expectData_3683_;
v___y_3699_ = v_respStream_3684_;
v___y_3700_ = v_keepAliveTimeout_3685_;
v___y_3701_ = v_currentTimeout_3686_;
v___y_3702_ = v___x_3708_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3709_, 0, v_response_3687_);
v___y_3696_ = v___y_3707_;
v___y_3697_ = v_headerTimeout_3682_;
v___y_3698_ = v_expectData_3683_;
v___y_3699_ = v_respStream_3684_;
v___y_3700_ = v_keepAliveTimeout_3685_;
v___y_3701_ = v_currentTimeout_3686_;
v___y_3702_ = v___x_3709_;
goto v___jp_3695_;
}
}
v___jp_3710_:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v_socket_3688_);
v___y_3707_ = v___x_3711_;
goto v___jp_3706_;
}
v___jp_3712_:
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_box(0);
v___y_3707_ = v___x_3713_;
goto v___jp_3706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3715_, lean_object* v_handlerDispatched_3716_, lean_object* v_headerTimeout_3717_, lean_object* v_expectData_3718_, lean_object* v_respStream_3719_, lean_object* v_keepAliveTimeout_3720_, lean_object* v_currentTimeout_3721_, lean_object* v_response_3722_, lean_object* v_socket_3723_, lean_object* v_requiresData_3724_, lean_object* v_sentMessage_3725_, lean_object* v_reader_3726_, lean_object* v_requestBodyInterested_3727_, lean_object* v_requestBody_3728_, lean_object* v___y_3729_){
_start:
{
uint8_t v_handlerDispatched_boxed_3730_; uint8_t v_requiresData_boxed_3731_; uint8_t v_sentMessage_boxed_3732_; uint8_t v_requestBodyInterested_boxed_3733_; lean_object* v_res_3734_; 
v_handlerDispatched_boxed_3730_ = lean_unbox(v_handlerDispatched_3716_);
v_requiresData_boxed_3731_ = lean_unbox(v_requiresData_3724_);
v_sentMessage_boxed_3732_ = lean_unbox(v_sentMessage_3725_);
v_requestBodyInterested_boxed_3733_ = lean_unbox(v_requestBodyInterested_3727_);
v_res_3734_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3715_, v_handlerDispatched_boxed_3730_, v_headerTimeout_3717_, v_expectData_3718_, v_respStream_3719_, v_keepAliveTimeout_3720_, v_currentTimeout_3721_, v_response_3722_, v_socket_3723_, v_requiresData_boxed_3731_, v_sentMessage_boxed_3732_, v_reader_3726_, v_requestBodyInterested_boxed_3733_, v_requestBody_3728_);
lean_dec_ref(v_reader_3726_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3735_, lean_object* v_x_3736_){
_start:
{
if (lean_obj_tag(v_x_3736_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3746_; 
lean_dec_ref(v___f_3735_);
v_a_3738_ = lean_ctor_get(v_x_3736_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_x_3736_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3740_ = v_x_3736_;
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v_x_3736_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3748_; 
v_a_3747_ = lean_ctor_get(v_x_3736_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v_x_3736_, 1);
v___x_3748_ = lean_apply_2(v___f_3735_, v_a_3747_, lean_box(0));
return v___x_3748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3749_, lean_object* v_x_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3749_, v_x_3750_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3757_, uint8_t v_handlerDispatched_3758_, lean_object* v_headerTimeout_3759_, lean_object* v_expectData_3760_, lean_object* v_respStream_3761_, lean_object* v_keepAliveTimeout_3762_, lean_object* v_currentTimeout_3763_, lean_object* v_response_3764_, lean_object* v_socket_3765_, uint8_t v_requiresData_3766_, uint8_t v_sentMessage_3767_, lean_object* v_reader_3768_, uint8_t v_pullBodyStalled_3769_, uint8_t v_requestBodyOpen_3770_, lean_object* v_requestStream_3771_, uint8_t v_requestBodyInterested_3772_){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___f_3778_; lean_object* v___f_3779_; 
v___x_3774_ = lean_box(v_handlerDispatched_3758_);
v___x_3775_ = lean_box(v_requiresData_3766_);
v___x_3776_ = lean_box(v_sentMessage_3767_);
v___x_3777_ = lean_box(v_requestBodyInterested_3772_);
lean_inc_ref(v_reader_3768_);
v___f_3778_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3778_, 0, v_connectionContext_3757_);
lean_closure_set(v___f_3778_, 1, v___x_3774_);
lean_closure_set(v___f_3778_, 2, v_headerTimeout_3759_);
lean_closure_set(v___f_3778_, 3, v_expectData_3760_);
lean_closure_set(v___f_3778_, 4, v_respStream_3761_);
lean_closure_set(v___f_3778_, 5, v_keepAliveTimeout_3762_);
lean_closure_set(v___f_3778_, 6, v_currentTimeout_3763_);
lean_closure_set(v___f_3778_, 7, v_response_3764_);
lean_closure_set(v___f_3778_, 8, v_socket_3765_);
lean_closure_set(v___f_3778_, 9, v___x_3775_);
lean_closure_set(v___f_3778_, 10, v___x_3776_);
lean_closure_set(v___f_3778_, 11, v_reader_3768_);
lean_closure_set(v___f_3778_, 12, v___x_3777_);
v___f_3779_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3779_, 0, v___f_3778_);
if (v_sentMessage_3767_ == 0)
{
lean_object* v_state_3785_; 
v_state_3785_ = lean_ctor_get(v_reader_3768_, 0);
lean_inc(v_state_3785_);
lean_dec_ref(v_reader_3768_);
if (lean_obj_tag(v_state_3785_) == 2)
{
lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3796_; 
v_isSharedCheck_3796_ = !lean_is_exclusive(v_state_3785_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v_state_3785_, 0);
lean_dec(v_unused_3797_);
v___x_3787_ = v_state_3785_;
v_isShared_3788_ = v_isSharedCheck_3796_;
goto v_resetjp_3786_;
}
else
{
lean_dec(v_state_3785_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3796_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
if (v_pullBodyStalled_3769_ == 0)
{
if (v_requestBodyOpen_3770_ == 0)
{
lean_del_object(v___x_3787_);
lean_dec_ref(v_requestStream_3771_);
goto v___jp_3780_;
}
else
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set_tag(v___x_3787_, 1);
lean_ctor_set(v___x_3787_, 0, v_requestStream_3771_);
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_requestStream_3771_);
v___x_3790_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
v___x_3793_ = lean_unsigned_to_nat(0u);
v___x_3794_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3793_, v_pullBodyStalled_3769_, v___x_3792_, v___f_3779_);
return v___x_3794_;
}
}
}
else
{
lean_del_object(v___x_3787_);
lean_dec_ref(v_requestStream_3771_);
goto v___jp_3780_;
}
}
}
else
{
lean_dec(v_state_3785_);
lean_dec_ref(v_requestStream_3771_);
goto v___jp_3780_;
}
}
else
{
lean_dec_ref(v_requestStream_3771_);
lean_dec_ref(v_reader_3768_);
goto v___jp_3780_;
}
v___jp_3780_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; lean_object* v___x_3784_; 
v___x_3781_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = 0;
v___x_3784_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3782_, v___x_3783_, v___x_3781_, v___f_3779_);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3798_ = _args[0];
lean_object* v_handlerDispatched_3799_ = _args[1];
lean_object* v_headerTimeout_3800_ = _args[2];
lean_object* v_expectData_3801_ = _args[3];
lean_object* v_respStream_3802_ = _args[4];
lean_object* v_keepAliveTimeout_3803_ = _args[5];
lean_object* v_currentTimeout_3804_ = _args[6];
lean_object* v_response_3805_ = _args[7];
lean_object* v_socket_3806_ = _args[8];
lean_object* v_requiresData_3807_ = _args[9];
lean_object* v_sentMessage_3808_ = _args[10];
lean_object* v_reader_3809_ = _args[11];
lean_object* v_pullBodyStalled_3810_ = _args[12];
lean_object* v_requestBodyOpen_3811_ = _args[13];
lean_object* v_requestStream_3812_ = _args[14];
lean_object* v_requestBodyInterested_3813_ = _args[15];
lean_object* v___y_3814_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3815_; uint8_t v_requiresData_boxed_3816_; uint8_t v_sentMessage_boxed_3817_; uint8_t v_pullBodyStalled_boxed_3818_; uint8_t v_requestBodyOpen_boxed_3819_; uint8_t v_requestBodyInterested_boxed_3820_; lean_object* v_res_3821_; 
v_handlerDispatched_boxed_3815_ = lean_unbox(v_handlerDispatched_3799_);
v_requiresData_boxed_3816_ = lean_unbox(v_requiresData_3807_);
v_sentMessage_boxed_3817_ = lean_unbox(v_sentMessage_3808_);
v_pullBodyStalled_boxed_3818_ = lean_unbox(v_pullBodyStalled_3810_);
v_requestBodyOpen_boxed_3819_ = lean_unbox(v_requestBodyOpen_3811_);
v_requestBodyInterested_boxed_3820_ = lean_unbox(v_requestBodyInterested_3813_);
v_res_3821_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3798_, v_handlerDispatched_boxed_3815_, v_headerTimeout_3800_, v_expectData_3801_, v_respStream_3802_, v_keepAliveTimeout_3803_, v_currentTimeout_3804_, v_response_3805_, v_socket_3806_, v_requiresData_boxed_3816_, v_sentMessage_boxed_3817_, v_reader_3809_, v_pullBodyStalled_boxed_3818_, v_requestBodyOpen_boxed_3819_, v_requestStream_3812_, v_requestBodyInterested_boxed_3820_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3822_, lean_object* v_x_3823_){
_start:
{
if (lean_obj_tag(v_x_3823_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v___f_3822_);
v_a_3825_ = lean_ctor_get(v_x_3823_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_x_3823_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3827_ = v_x_3823_;
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v_x_3823_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
return v___x_3831_;
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3835_; 
v_a_3834_ = lean_ctor_get(v_x_3823_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v_x_3823_, 1);
v___x_3835_ = lean_apply_2(v___f_3822_, v_a_3834_, lean_box(0));
return v___x_3835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3836_, lean_object* v_x_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3836_, v_x_3837_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3845_, uint8_t v_handlerDispatched_3846_, lean_object* v_headerTimeout_3847_, lean_object* v_expectData_3848_, lean_object* v_respStream_3849_, lean_object* v_keepAliveTimeout_3850_, lean_object* v_currentTimeout_3851_, lean_object* v_response_3852_, lean_object* v_socket_3853_, uint8_t v_requiresData_3854_, uint8_t v_sentMessage_3855_, lean_object* v_reader_3856_, uint8_t v_pullBodyStalled_3857_, lean_object* v_requestStream_3858_, uint8_t v_requestBodyOpen_3859_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___f_3866_; lean_object* v___f_3867_; 
v___x_3861_ = lean_box(v_handlerDispatched_3846_);
v___x_3862_ = lean_box(v_requiresData_3854_);
v___x_3863_ = lean_box(v_sentMessage_3855_);
v___x_3864_ = lean_box(v_pullBodyStalled_3857_);
v___x_3865_ = lean_box(v_requestBodyOpen_3859_);
lean_inc_ref(v_requestStream_3858_);
lean_inc_ref(v_reader_3856_);
v___f_3866_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3866_, 0, v_connectionContext_3845_);
lean_closure_set(v___f_3866_, 1, v___x_3861_);
lean_closure_set(v___f_3866_, 2, v_headerTimeout_3847_);
lean_closure_set(v___f_3866_, 3, v_expectData_3848_);
lean_closure_set(v___f_3866_, 4, v_respStream_3849_);
lean_closure_set(v___f_3866_, 5, v_keepAliveTimeout_3850_);
lean_closure_set(v___f_3866_, 6, v_currentTimeout_3851_);
lean_closure_set(v___f_3866_, 7, v_response_3852_);
lean_closure_set(v___f_3866_, 8, v_socket_3853_);
lean_closure_set(v___f_3866_, 9, v___x_3862_);
lean_closure_set(v___f_3866_, 10, v___x_3863_);
lean_closure_set(v___f_3866_, 11, v_reader_3856_);
lean_closure_set(v___f_3866_, 12, v___x_3864_);
lean_closure_set(v___f_3866_, 13, v___x_3865_);
lean_closure_set(v___f_3866_, 14, v_requestStream_3858_);
v___f_3867_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3867_, 0, v___f_3866_);
if (v_sentMessage_3855_ == 0)
{
lean_object* v_state_3873_; 
v_state_3873_ = lean_ctor_get(v_reader_3856_, 0);
lean_inc(v_state_3873_);
lean_dec_ref(v_reader_3856_);
if (lean_obj_tag(v_state_3873_) == 2)
{
lean_dec_ref_known(v_state_3873_, 1);
if (v_requestBodyOpen_3859_ == 0)
{
lean_dec_ref(v_requestStream_3858_);
goto v___jp_3868_;
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3858_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v___x_3876_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3875_, v_sentMessage_3855_, v___x_3874_, v___f_3867_);
return v___x_3876_;
}
}
else
{
lean_dec(v_state_3873_);
lean_dec_ref(v_requestStream_3858_);
goto v___jp_3868_;
}
}
else
{
lean_dec_ref(v_requestStream_3858_);
lean_dec_ref(v_reader_3856_);
goto v___jp_3868_;
}
v___jp_3868_:
{
uint8_t v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3869_ = 0;
v___x_3870_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3871_ = lean_unsigned_to_nat(0u);
v___x_3872_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3871_, v___x_3869_, v___x_3870_, v___f_3867_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3877_, lean_object* v_handlerDispatched_3878_, lean_object* v_headerTimeout_3879_, lean_object* v_expectData_3880_, lean_object* v_respStream_3881_, lean_object* v_keepAliveTimeout_3882_, lean_object* v_currentTimeout_3883_, lean_object* v_response_3884_, lean_object* v_socket_3885_, lean_object* v_requiresData_3886_, lean_object* v_sentMessage_3887_, lean_object* v_reader_3888_, lean_object* v_pullBodyStalled_3889_, lean_object* v_requestStream_3890_, lean_object* v_requestBodyOpen_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v_handlerDispatched_boxed_3893_; uint8_t v_requiresData_boxed_3894_; uint8_t v_sentMessage_boxed_3895_; uint8_t v_pullBodyStalled_boxed_3896_; uint8_t v_requestBodyOpen_boxed_3897_; lean_object* v_res_3898_; 
v_handlerDispatched_boxed_3893_ = lean_unbox(v_handlerDispatched_3878_);
v_requiresData_boxed_3894_ = lean_unbox(v_requiresData_3886_);
v_sentMessage_boxed_3895_ = lean_unbox(v_sentMessage_3887_);
v_pullBodyStalled_boxed_3896_ = lean_unbox(v_pullBodyStalled_3889_);
v_requestBodyOpen_boxed_3897_ = lean_unbox(v_requestBodyOpen_3891_);
v_res_3898_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3877_, v_handlerDispatched_boxed_3893_, v_headerTimeout_3879_, v_expectData_3880_, v_respStream_3881_, v_keepAliveTimeout_3882_, v_currentTimeout_3883_, v_response_3884_, v_socket_3885_, v_requiresData_boxed_3894_, v_sentMessage_boxed_3895_, v_reader_3888_, v_pullBodyStalled_boxed_3896_, v_requestStream_3890_, v_requestBodyOpen_boxed_3897_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3899_, lean_object* v___f_3900_, uint8_t v___x_3901_, lean_object* v_x_3902_){
_start:
{
uint8_t v___y_3905_; 
if (lean_obj_tag(v_x_3902_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v___f_3900_);
v_a_3911_ = lean_ctor_get(v_x_3902_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_x_3902_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3913_ = v_x_3902_;
v_isShared_3914_ = v_isSharedCheck_3919_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v_x_3902_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3919_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
return v___x_3917_;
}
}
}
else
{
lean_object* v_a_3920_; uint8_t v___x_3921_; 
v_a_3920_ = lean_ctor_get(v_x_3902_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v_x_3902_, 1);
v___x_3921_ = lean_unbox(v_a_3920_);
lean_dec(v_a_3920_);
if (v___x_3921_ == 0)
{
v___y_3905_ = v___x_3901_;
goto v___jp_3904_;
}
else
{
v___y_3905_ = v_sentMessage_3899_;
goto v___jp_3904_;
}
}
v___jp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3906_ = lean_box(v___y_3905_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
v___x_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3909_, v_sentMessage_3899_, v___x_3908_, v___f_3900_);
return v___x_3910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3922_, lean_object* v___f_3923_, lean_object* v___x_3924_, lean_object* v_x_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v_sentMessage_boxed_3927_; uint8_t v___x_3791__boxed_3928_; lean_object* v_res_3929_; 
v_sentMessage_boxed_3927_ = lean_unbox(v_sentMessage_3922_);
v___x_3791__boxed_3928_ = lean_unbox(v___x_3924_);
v_res_3929_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3927_, v___f_3923_, v___x_3791__boxed_3928_, v_x_3925_);
return v_res_3929_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___f_3930_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3931_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3932_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3933_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3933_, 0, lean_box(0));
lean_closure_set(v___x_3933_, 1, lean_box(0));
lean_closure_set(v___x_3933_, 2, v___x_3932_);
lean_closure_set(v___x_3933_, 3, lean_box(0));
lean_closure_set(v___x_3933_, 4, lean_box(0));
lean_closure_set(v___x_3933_, 5, v___x_3931_);
lean_closure_set(v___x_3933_, 6, v___f_3930_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3934_, lean_object* v_connectionContext_3935_, lean_object* v_state_3936_){
_start:
{
lean_object* v_machine_3938_; lean_object* v_writer_3939_; lean_object* v_requestStream_3940_; lean_object* v_keepAliveTimeout_3941_; lean_object* v_currentTimeout_3942_; lean_object* v_headerTimeout_3943_; lean_object* v_response_3944_; lean_object* v_respStream_3945_; uint8_t v_requiresData_3946_; lean_object* v_expectData_3947_; uint8_t v_handlerDispatched_3948_; lean_object* v_reader_3949_; uint8_t v_pullBodyStalled_3950_; uint8_t v_sentMessage_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___f_3956_; lean_object* v___f_3957_; uint8_t v___y_3959_; 
v_machine_3938_ = lean_ctor_get(v_state_3936_, 0);
lean_inc_ref(v_machine_3938_);
v_writer_3939_ = lean_ctor_get(v_machine_3938_, 1);
lean_inc_ref(v_writer_3939_);
v_requestStream_3940_ = lean_ctor_get(v_state_3936_, 1);
lean_inc_ref_n(v_requestStream_3940_, 2);
v_keepAliveTimeout_3941_ = lean_ctor_get(v_state_3936_, 2);
lean_inc(v_keepAliveTimeout_3941_);
v_currentTimeout_3942_ = lean_ctor_get(v_state_3936_, 3);
lean_inc(v_currentTimeout_3942_);
v_headerTimeout_3943_ = lean_ctor_get(v_state_3936_, 4);
lean_inc(v_headerTimeout_3943_);
v_response_3944_ = lean_ctor_get(v_state_3936_, 5);
lean_inc_ref(v_response_3944_);
v_respStream_3945_ = lean_ctor_get(v_state_3936_, 6);
lean_inc(v_respStream_3945_);
v_requiresData_3946_ = lean_ctor_get_uint8(v_state_3936_, sizeof(void*)*9);
v_expectData_3947_ = lean_ctor_get(v_state_3936_, 7);
lean_inc(v_expectData_3947_);
v_handlerDispatched_3948_ = lean_ctor_get_uint8(v_state_3936_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3936_);
v_reader_3949_ = lean_ctor_get(v_machine_3938_, 0);
lean_inc_ref_n(v_reader_3949_, 2);
v_pullBodyStalled_3950_ = lean_ctor_get_uint8(v_machine_3938_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3938_);
v_sentMessage_3951_ = lean_ctor_get_uint8(v_writer_3939_, sizeof(void*)*6);
lean_dec_ref(v_writer_3939_);
v___x_3952_ = lean_box(v_handlerDispatched_3948_);
v___x_3953_ = lean_box(v_requiresData_3946_);
v___x_3954_ = lean_box(v_sentMessage_3951_);
v___x_3955_ = lean_box(v_pullBodyStalled_3950_);
v___f_3956_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3956_, 0, v_connectionContext_3935_);
lean_closure_set(v___f_3956_, 1, v___x_3952_);
lean_closure_set(v___f_3956_, 2, v_headerTimeout_3943_);
lean_closure_set(v___f_3956_, 3, v_expectData_3947_);
lean_closure_set(v___f_3956_, 4, v_respStream_3945_);
lean_closure_set(v___f_3956_, 5, v_keepAliveTimeout_3941_);
lean_closure_set(v___f_3956_, 6, v_currentTimeout_3942_);
lean_closure_set(v___f_3956_, 7, v_response_3944_);
lean_closure_set(v___f_3956_, 8, v_socket_3934_);
lean_closure_set(v___f_3956_, 9, v___x_3953_);
lean_closure_set(v___f_3956_, 10, v___x_3954_);
lean_closure_set(v___f_3956_, 11, v_reader_3949_);
lean_closure_set(v___f_3956_, 12, v___x_3955_);
lean_closure_set(v___f_3956_, 13, v_requestStream_3940_);
v___f_3957_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3957_, 0, v___f_3956_);
if (v_sentMessage_3951_ == 0)
{
lean_object* v_state_3965_; 
v_state_3965_ = lean_ctor_get(v_reader_3949_, 0);
lean_inc(v_state_3965_);
lean_dec_ref(v_reader_3949_);
if (lean_obj_tag(v_state_3965_) == 2)
{
lean_object* v___x_3966_; lean_object* v___f_3967_; lean_object* v___f_3968_; lean_object* v___x_3969_; lean_object* v___x_3305__overap_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___f_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec_ref_known(v_state_3965_, 1);
v___x_3966_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3967_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3968_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3969_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3305__overap_3970_ = l_Std_Mutex_atomically___redArg(v___x_3966_, v___f_3967_, v___f_3968_, v_requestStream_3940_, v___x_3969_);
v___x_3971_ = lean_apply_1(v___x_3305__overap_3970_, lean_box(0));
v___x_3972_ = 1;
v___x_3973_ = lean_box(v_sentMessage_3951_);
v___x_3974_ = lean_box(v___x_3972_);
v___f_3975_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3975_, 0, v___x_3973_);
lean_closure_set(v___f_3975_, 1, v___f_3957_);
lean_closure_set(v___f_3975_, 2, v___x_3974_);
v___x_3976_ = lean_unsigned_to_nat(0u);
v___x_3977_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3976_, v_sentMessage_3951_, v___x_3971_, v___f_3975_);
return v___x_3977_;
}
else
{
lean_dec(v_state_3965_);
lean_dec_ref(v_requestStream_3940_);
v___y_3959_ = v_sentMessage_3951_;
goto v___jp_3958_;
}
}
else
{
uint8_t v___x_3978_; 
lean_dec_ref(v_reader_3949_);
lean_dec_ref(v_requestStream_3940_);
v___x_3978_ = 0;
v___y_3959_ = v___x_3978_;
goto v___jp_3958_;
}
v___jp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3960_ = lean_box(v___y_3959_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3963_, v___y_3959_, v___x_3962_, v___f_3957_);
return v___x_3964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3979_, lean_object* v_connectionContext_3980_, lean_object* v_state_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3979_, v_connectionContext_3980_, v_state_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3984_, lean_object* v_00_u03b2_3985_, lean_object* v_inst_3986_, lean_object* v_socket_3987_, lean_object* v_connectionContext_3988_, lean_object* v_state_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3987_, v_connectionContext_3988_, v_state_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_3992_, lean_object* v_00_u03b2_3993_, lean_object* v_inst_3994_, lean_object* v_socket_3995_, lean_object* v_connectionContext_3996_, lean_object* v_state_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_3992_, v_00_u03b2_3993_, v_inst_3994_, v_socket_3995_, v_connectionContext_3996_, v_state_3997_);
lean_dec_ref(v_inst_3994_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4000_){
_start:
{
if (lean_obj_tag(v_x_4000_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
v_a_4002_ = lean_ctor_get(v_x_4000_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_x_4000_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4004_ = v_x_4000_;
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v_x_4000_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4029_; 
v_a_4011_ = lean_ctor_get(v_x_4000_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_x_4000_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4013_ = v_x_4000_;
v_isShared_4014_ = v_isSharedCheck_4029_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v_x_4000_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4029_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_snd_4015_; uint8_t v___x_4016_; 
v_snd_4015_ = lean_ctor_get(v_a_4011_, 1);
v___x_4016_ = lean_unbox(v_snd_4015_);
if (v___x_4016_ == 0)
{
lean_object* v_fst_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v_fst_4017_ = lean_ctor_get(v_a_4011_, 0);
lean_inc(v_fst_4017_);
lean_dec(v_a_4011_);
v___x_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_fst_4017_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4018_);
v___x_4020_ = v___x_4013_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
return v___x_4021_;
}
}
else
{
lean_object* v_fst_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
v_fst_4023_ = lean_ctor_get(v_a_4011_, 0);
lean_inc(v_fst_4023_);
lean_dec(v_a_4011_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_fst_4023_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4024_);
v___x_4026_ = v___x_4013_;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4030_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4033_){
_start:
{
if (lean_obj_tag(v_x_4033_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4043_; 
v_a_4035_ = lean_ctor_get(v_x_4033_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v_x_4033_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4037_ = v_x_4033_;
v_isShared_4038_ = v_isSharedCheck_4043_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v_x_4033_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4043_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
return v___x_4041_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4053_; 
v_a_4044_ = lean_ctor_get(v_x_4033_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_x_4033_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4046_ = v_x_4033_;
v_isShared_4047_ = v_isSharedCheck_4053_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v_x_4033_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4053_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v_a_4044_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v___x_4048_);
v___x_4050_ = v___x_4046_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4054_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4061_){
_start:
{
if (lean_obj_tag(v_x_4061_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4071_; 
v_a_4063_ = lean_ctor_get(v_x_4061_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v_x_4061_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4065_ = v_x_4061_;
v_isShared_4066_ = v_isSharedCheck_4071_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v_x_4061_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4071_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4069_; 
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
return v___x_4069_;
}
}
}
else
{
lean_object* v___x_4072_; 
lean_dec_ref_known(v_x_4061_, 1);
v___x_4072_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4073_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4076_, lean_object* v_handler_4077_, lean_object* v___f_4078_, lean_object* v_x_4079_){
_start:
{
if (lean_obj_tag(v_x_4079_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; lean_object* v___x_4085_; 
v_a_4081_ = lean_ctor_get(v_x_4079_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v_x_4079_, 1);
v___x_4082_ = lean_apply_3(v_onFailure_4076_, v_handler_4077_, v_a_4081_, lean_box(0));
v___x_4083_ = lean_unsigned_to_nat(0u);
v___x_4084_ = 0;
v___x_4085_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4083_, v___x_4084_, v___x_4082_, v___f_4078_);
return v___x_4085_;
}
else
{
lean_object* v___x_4086_; 
lean_dec_ref(v___f_4078_);
lean_dec(v_handler_4077_);
lean_dec_ref(v_onFailure_4076_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v_x_4079_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4087_, lean_object* v_handler_4088_, lean_object* v___f_4089_, lean_object* v_x_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4087_, v_handler_4088_, v___f_4089_, v_x_4090_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4093_, lean_object* v_socket_4094_, lean_object* v_____r_4095_){
_start:
{
lean_object* v_val_4098_; lean_object* v_close_4100_; lean_object* v___x_4101_; 
v_close_4100_ = lean_ctor_get(v_inst_4093_, 3);
lean_inc_ref(v_close_4100_);
lean_dec_ref(v_inst_4093_);
v___x_4101_ = lean_apply_2(v_close_4100_, v_socket_4094_, lean_box(0));
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4101_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4101_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set_tag(v___x_4104_, 1);
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
v_val_4098_ = v___x_4107_;
goto v___jp_4097_;
}
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
v_a_4110_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4101_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4101_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set_tag(v___x_4112_, 0);
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
v_val_4098_ = v___x_4115_;
goto v___jp_4097_;
}
}
}
v___jp_4097_:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_val_4098_);
return v___x_4099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4118_, lean_object* v_socket_4119_, lean_object* v_____r_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4118_, v_socket_4119_, v_____r_4120_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4123_, lean_object* v_x_4124_){
_start:
{
if (lean_obj_tag(v_x_4124_) == 0)
{
lean_object* v___x_4126_; 
lean_dec_ref(v___f_4123_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_x_4124_);
return v___x_4126_;
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4128_; 
v_a_4127_ = lean_ctor_get(v_x_4124_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v_x_4124_, 1);
v___x_4128_ = lean_apply_2(v___f_4123_, v_a_4127_, lean_box(0));
return v___x_4128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4129_, lean_object* v_x_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4129_, v_x_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4133_, lean_object* v_val_4134_, lean_object* v___f_4135_, lean_object* v___f_4136_, lean_object* v_x_4137_){
_start:
{
if (lean_obj_tag(v_x_4137_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v___f_4136_);
lean_dec_ref(v___f_4135_);
lean_dec(v_val_4134_);
lean_dec_ref(v_close_4133_);
v_a_4139_ = lean_ctor_get(v_x_4137_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_x_4137_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4141_ = v_x_4137_;
v_isShared_4142_ = v_isSharedCheck_4147_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v_x_4137_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4147_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
return v___x_4145_;
}
}
}
else
{
lean_object* v_a_4148_; uint8_t v___x_4149_; 
v_a_4148_ = lean_ctor_get(v_x_4137_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v_x_4137_, 1);
v___x_4149_ = lean_unbox(v_a_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; lean_object* v___x_4153_; 
lean_dec_ref(v___f_4136_);
v___x_4150_ = lean_apply_2(v_close_4133_, v_val_4134_, lean_box(0));
v___x_4151_ = lean_unsigned_to_nat(0u);
v___x_4152_ = lean_unbox(v_a_4148_);
lean_dec(v_a_4148_);
v___x_4153_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4151_, v___x_4152_, v___x_4150_, v___f_4135_);
return v___x_4153_;
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec(v_a_4148_);
lean_dec_ref(v___f_4135_);
lean_dec(v_val_4134_);
lean_dec_ref(v_close_4133_);
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_apply_2(v___f_4136_, v___x_4154_, lean_box(0));
return v___x_4155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4156_, lean_object* v_val_4157_, lean_object* v___f_4158_, lean_object* v___f_4159_, lean_object* v_x_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4156_, v_val_4157_, v___f_4158_, v___f_4159_, v_x_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4163_, lean_object* v_responseBodyInstance_4164_, lean_object* v___f_4165_, lean_object* v___f_4166_, lean_object* v_____r_4167_){
_start:
{
if (lean_obj_tag(v_respStream_4163_) == 1)
{
lean_object* v_val_4169_; lean_object* v_close_4170_; lean_object* v_isClosed_4171_; lean_object* v___x_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; lean_object* v___x_4176_; 
v_val_4169_ = lean_ctor_get(v_respStream_4163_, 0);
lean_inc_n(v_val_4169_, 2);
lean_dec_ref_known(v_respStream_4163_, 1);
v_close_4170_ = lean_ctor_get(v_responseBodyInstance_4164_, 1);
lean_inc_ref(v_close_4170_);
v_isClosed_4171_ = lean_ctor_get(v_responseBodyInstance_4164_, 2);
lean_inc_ref(v_isClosed_4171_);
lean_dec_ref(v_responseBodyInstance_4164_);
v___x_4172_ = lean_apply_2(v_isClosed_4171_, v_val_4169_, lean_box(0));
v___f_4173_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4173_, 0, v_close_4170_);
lean_closure_set(v___f_4173_, 1, v_val_4169_);
lean_closure_set(v___f_4173_, 2, v___f_4165_);
lean_closure_set(v___f_4173_, 3, v___f_4166_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = 0;
v___x_4176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4174_, v___x_4175_, v___x_4172_, v___f_4173_);
return v___x_4176_;
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec_ref(v___f_4165_);
lean_dec_ref(v_responseBodyInstance_4164_);
lean_dec(v_respStream_4163_);
v___x_4177_ = lean_box(0);
v___x_4178_ = lean_apply_2(v___f_4166_, v___x_4177_, lean_box(0));
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4179_, lean_object* v_responseBodyInstance_4180_, lean_object* v___f_4181_, lean_object* v___f_4182_, lean_object* v_____r_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4179_, v_responseBodyInstance_4180_, v___f_4181_, v___f_4182_, v_____r_4183_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4186_, lean_object* v___f_4187_, lean_object* v___f_4188_, lean_object* v_x_4189_){
_start:
{
if (lean_obj_tag(v_x_4189_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref(v___f_4188_);
lean_dec_ref(v___f_4187_);
lean_dec_ref(v_requestStream_4186_);
v_a_4191_ = lean_ctor_get(v_x_4189_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4193_ = v_x_4189_;
v_isShared_4194_ = v_isSharedCheck_4199_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v_x_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4199_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
}
else
{
lean_object* v_a_4200_; uint8_t v___x_4201_; 
v_a_4200_ = lean_ctor_get(v_x_4189_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v_x_4189_, 1);
v___x_4201_ = lean_unbox(v_a_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; 
lean_dec_ref(v___f_4188_);
v___x_4202_ = l_Std_Http_Body_Stream_close(v_requestStream_4186_);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_unbox(v_a_4200_);
lean_dec(v_a_4200_);
v___x_4205_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4203_, v___x_4204_, v___x_4202_, v___f_4187_);
return v___x_4205_;
}
else
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_dec(v_a_4200_);
lean_dec_ref(v___f_4187_);
lean_dec_ref(v_requestStream_4186_);
v___x_4206_ = lean_box(0);
v___x_4207_ = lean_apply_2(v___f_4188_, v___x_4206_, lean_box(0));
return v___x_4207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4208_, lean_object* v___f_4209_, lean_object* v___f_4210_, lean_object* v_x_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4208_, v___f_4209_, v___f_4210_, v_x_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4214_, lean_object* v_responseBodyInstance_4215_, lean_object* v___f_4216_, lean_object* v___f_4217_, lean_object* v_x_4218_){
_start:
{
if (lean_obj_tag(v_x_4218_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref(v___f_4217_);
lean_dec_ref(v___f_4216_);
lean_dec_ref(v_responseBodyInstance_4215_);
lean_dec_ref(v___f_4214_);
v_a_4220_ = lean_ctor_get(v_x_4218_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_x_4218_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4222_ = v_x_4218_;
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v_x_4218_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
return v___x_4226_;
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v_requestStream_4230_; lean_object* v_respStream_4231_; lean_object* v___x_4232_; lean_object* v___f_4233_; lean_object* v___f_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_5017__overap_4237_; lean_object* v___x_4238_; lean_object* v___f_4239_; lean_object* v___f_4240_; lean_object* v___f_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; 
v_a_4229_ = lean_ctor_get(v_x_4218_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v_x_4218_, 1);
v_requestStream_4230_ = lean_ctor_get(v_a_4229_, 1);
lean_inc_ref_n(v_requestStream_4230_, 2);
v_respStream_4231_ = lean_ctor_get(v_a_4229_, 6);
lean_inc(v_respStream_4231_);
lean_dec(v_a_4229_);
v___x_4232_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4233_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4234_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4235_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4236_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4236_, 0, lean_box(0));
lean_closure_set(v___x_4236_, 1, lean_box(0));
lean_closure_set(v___x_4236_, 2, v___x_4232_);
lean_closure_set(v___x_4236_, 3, lean_box(0));
lean_closure_set(v___x_4236_, 4, lean_box(0));
lean_closure_set(v___x_4236_, 5, v___x_4235_);
lean_closure_set(v___x_4236_, 6, v___f_4214_);
v___x_5017__overap_4237_ = l_Std_Mutex_atomically___redArg(v___x_4232_, v___f_4233_, v___f_4234_, v_requestStream_4230_, v___x_4236_);
v___x_4238_ = lean_apply_1(v___x_5017__overap_4237_, lean_box(0));
v___f_4239_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4239_, 0, v_respStream_4231_);
lean_closure_set(v___f_4239_, 1, v_responseBodyInstance_4215_);
lean_closure_set(v___f_4239_, 2, v___f_4216_);
lean_closure_set(v___f_4239_, 3, v___f_4217_);
lean_inc_ref(v___f_4239_);
v___f_4240_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4240_, 0, v___f_4239_);
v___f_4241_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4241_, 0, v_requestStream_4230_);
lean_closure_set(v___f_4241_, 1, v___f_4240_);
lean_closure_set(v___f_4241_, 2, v___f_4239_);
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = 0;
v___x_4244_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4242_, v___x_4243_, v___x_4238_, v___f_4241_);
return v___x_4244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4245_, lean_object* v_responseBodyInstance_4246_, lean_object* v___f_4247_, lean_object* v___f_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4245_, v_responseBodyInstance_4246_, v___f_4247_, v___f_4248_, v_x_4249_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4252_, lean_object* v_responseBodyInstance_4253_, lean_object* v_handler_4254_, lean_object* v_config_4255_, lean_object* v___x_4256_, uint8_t v___x_4257_, lean_object* v___f_4258_, lean_object* v_x_4259_){
_start:
{
if (lean_obj_tag(v_x_4259_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4269_; 
lean_dec_ref(v___f_4258_);
lean_dec_ref(v___x_4256_);
lean_dec_ref(v_config_4255_);
lean_dec(v_handler_4254_);
lean_dec_ref(v_responseBodyInstance_4253_);
lean_dec_ref(v_h_4252_);
v_a_4261_ = lean_ctor_get(v_x_4259_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v_x_4259_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4263_ = v_x_4259_;
v_isShared_4264_ = v_isSharedCheck_4269_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v_x_4259_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4269_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
return v___x_4267_;
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_a_4270_ = lean_ctor_get(v_x_4259_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v_x_4259_, 1);
v___x_4271_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4252_, v_responseBodyInstance_4253_, v_handler_4254_, v_config_4255_, v_a_4270_, v___x_4256_);
v___x_4272_ = lean_unsigned_to_nat(0u);
v___x_4273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4272_, v___x_4257_, v___x_4271_, v___f_4258_);
return v___x_4273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4274_, lean_object* v_responseBodyInstance_4275_, lean_object* v_handler_4276_, lean_object* v_config_4277_, lean_object* v___x_4278_, lean_object* v___x_4279_, lean_object* v___f_4280_, lean_object* v_x_4281_, lean_object* v___y_4282_){
_start:
{
uint8_t v___x_5688__boxed_4283_; lean_object* v_res_4284_; 
v___x_5688__boxed_4283_ = lean_unbox(v___x_4279_);
v_res_4284_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4274_, v_responseBodyInstance_4275_, v_handler_4276_, v_config_4277_, v___x_4278_, v___x_5688__boxed_4283_, v___f_4280_, v_x_4281_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4285_, lean_object* v_h_4286_, lean_object* v_responseBodyInstance_4287_, lean_object* v_config_4288_, lean_object* v_handler_4289_, uint8_t v___x_4290_, lean_object* v___f_4291_, lean_object* v_x_4292_){
_start:
{
if (lean_obj_tag(v_x_4292_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4302_; 
lean_dec_ref(v___f_4291_);
lean_dec(v_handler_4289_);
lean_dec_ref(v_config_4288_);
lean_dec_ref(v_responseBodyInstance_4287_);
lean_dec_ref(v_h_4286_);
lean_dec_ref(v_inst_4285_);
v_a_4294_ = lean_ctor_get(v_x_4292_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_x_4292_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4296_ = v_x_4292_;
v_isShared_4297_ = v_isSharedCheck_4302_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v_x_4292_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4302_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
lean_object* v___x_4300_; 
v___x_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4299_);
return v___x_4300_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_a_4303_ = lean_ctor_get(v_x_4292_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v_x_4292_, 1);
v___x_4304_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4285_, v_h_4286_, v_responseBodyInstance_4287_, v_config_4288_, v_handler_4289_, v_a_4303_);
v___x_4305_ = lean_unsigned_to_nat(0u);
v___x_4306_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4305_, v___x_4290_, v___x_4304_, v___f_4291_);
return v___x_4306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4307_, lean_object* v_h_4308_, lean_object* v_responseBodyInstance_4309_, lean_object* v_config_4310_, lean_object* v_handler_4311_, lean_object* v___x_4312_, lean_object* v___f_4313_, lean_object* v_x_4314_, lean_object* v___y_4315_){
_start:
{
uint8_t v___x_5729__boxed_4316_; lean_object* v_res_4317_; 
v___x_5729__boxed_4316_ = lean_unbox(v___x_4312_);
v_res_4317_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4307_, v_h_4308_, v_responseBodyInstance_4309_, v_config_4310_, v_handler_4311_, v___x_5729__boxed_4316_, v___f_4313_, v_x_4314_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4318_, lean_object* v_socket_4319_, lean_object* v_connectionContext_4320_, lean_object* v_h_4321_, lean_object* v_responseBodyInstance_4322_, lean_object* v_handler_4323_, lean_object* v_config_4324_, lean_object* v___f_4325_, lean_object* v_inst_4326_, lean_object* v_x_4327_){
_start:
{
if (lean_obj_tag(v_x_4327_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4337_; 
lean_dec_ref(v_inst_4326_);
lean_dec_ref(v___f_4325_);
lean_dec_ref(v_config_4324_);
lean_dec(v_handler_4323_);
lean_dec_ref(v_responseBodyInstance_4322_);
lean_dec_ref(v_h_4321_);
lean_dec_ref(v_connectionContext_4320_);
lean_dec(v_socket_4319_);
v_a_4329_ = lean_ctor_get(v_x_4327_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v_x_4327_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4331_ = v_x_4327_;
v_isShared_4332_ = v_isSharedCheck_4337_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v_x_4327_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4337_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4329_);
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
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4372_; 
v_a_4338_ = lean_ctor_get(v_x_4327_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v_x_4327_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4340_ = v_x_4327_;
v_isShared_4341_ = v_isSharedCheck_4372_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v_x_4327_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4372_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v_machine_4348_; lean_object* v_requestStream_4349_; lean_object* v_keepAliveTimeout_4350_; lean_object* v_currentTimeout_4351_; lean_object* v_headerTimeout_4352_; lean_object* v_response_4353_; lean_object* v_respStream_4354_; uint8_t v_requiresData_4355_; lean_object* v_expectData_4356_; uint8_t v_handlerDispatched_4357_; lean_object* v_pendingHead_4358_; 
v_machine_4348_ = lean_ctor_get(v_a_4338_, 0);
v_requestStream_4349_ = lean_ctor_get(v_a_4338_, 1);
v_keepAliveTimeout_4350_ = lean_ctor_get(v_a_4338_, 2);
v_currentTimeout_4351_ = lean_ctor_get(v_a_4338_, 3);
v_headerTimeout_4352_ = lean_ctor_get(v_a_4338_, 4);
v_response_4353_ = lean_ctor_get(v_a_4338_, 5);
v_respStream_4354_ = lean_ctor_get(v_a_4338_, 6);
v_requiresData_4355_ = lean_ctor_get_uint8(v_a_4338_, sizeof(void*)*9);
v_expectData_4356_ = lean_ctor_get(v_a_4338_, 7);
v_handlerDispatched_4357_ = lean_ctor_get_uint8(v_a_4338_, sizeof(void*)*9 + 1);
v_pendingHead_4358_ = lean_ctor_get(v_a_4338_, 8);
if (v_requiresData_4355_ == 0)
{
if (v_handlerDispatched_4357_ == 0)
{
if (lean_obj_tag(v_respStream_4354_) == 0)
{
lean_object* v_writer_4368_; uint8_t v_sentMessage_4369_; 
v_writer_4368_ = lean_ctor_get(v_machine_4348_, 1);
v_sentMessage_4369_ = lean_ctor_get_uint8(v_writer_4368_, sizeof(void*)*6);
if (v_sentMessage_4369_ == 0)
{
lean_object* v_reader_4370_; lean_object* v_state_4371_; 
v_reader_4370_ = lean_ctor_get(v_machine_4348_, 0);
v_state_4371_ = lean_ctor_get(v_reader_4370_, 0);
if (lean_obj_tag(v_state_4371_) == 2)
{
lean_inc(v_respStream_4354_);
lean_inc(v_pendingHead_4358_);
lean_inc(v_expectData_4356_);
lean_inc_ref(v_response_4353_);
lean_inc(v_headerTimeout_4352_);
lean_inc(v_currentTimeout_4351_);
lean_inc(v_keepAliveTimeout_4350_);
lean_inc_ref(v_requestStream_4349_);
lean_inc_ref(v_machine_4348_);
lean_del_object(v___x_4340_);
lean_dec(v_a_4338_);
goto v___jp_4359_;
}
else
{
lean_dec_ref(v_inst_4326_);
lean_dec_ref(v___f_4325_);
lean_dec_ref(v_config_4324_);
lean_dec(v_handler_4323_);
lean_dec_ref(v_responseBodyInstance_4322_);
lean_dec_ref(v_h_4321_);
lean_dec_ref(v_connectionContext_4320_);
lean_dec(v_socket_4319_);
goto v___jp_4342_;
}
}
else
{
lean_dec_ref(v_inst_4326_);
lean_dec_ref(v___f_4325_);
lean_dec_ref(v_config_4324_);
lean_dec(v_handler_4323_);
lean_dec_ref(v_responseBodyInstance_4322_);
lean_dec_ref(v_h_4321_);
lean_dec_ref(v_connectionContext_4320_);
lean_dec(v_socket_4319_);
goto v___jp_4342_;
}
}
else
{
lean_inc_ref(v_respStream_4354_);
lean_inc(v_pendingHead_4358_);
lean_inc(v_expectData_4356_);
lean_inc_ref(v_response_4353_);
lean_inc(v_headerTimeout_4352_);
lean_inc(v_currentTimeout_4351_);
lean_inc(v_keepAliveTimeout_4350_);
lean_inc_ref(v_requestStream_4349_);
lean_inc_ref(v_machine_4348_);
lean_del_object(v___x_4340_);
lean_dec(v_a_4338_);
goto v___jp_4359_;
}
}
else
{
lean_inc(v_pendingHead_4358_);
lean_inc(v_expectData_4356_);
lean_inc(v_respStream_4354_);
lean_inc_ref(v_response_4353_);
lean_inc(v_headerTimeout_4352_);
lean_inc(v_currentTimeout_4351_);
lean_inc(v_keepAliveTimeout_4350_);
lean_inc_ref(v_requestStream_4349_);
lean_inc_ref(v_machine_4348_);
lean_del_object(v___x_4340_);
lean_dec(v_a_4338_);
goto v___jp_4359_;
}
}
else
{
lean_inc(v_pendingHead_4358_);
lean_inc(v_expectData_4356_);
lean_inc(v_respStream_4354_);
lean_inc_ref(v_response_4353_);
lean_inc(v_headerTimeout_4352_);
lean_inc(v_currentTimeout_4351_);
lean_inc(v_keepAliveTimeout_4350_);
lean_inc_ref(v_requestStream_4349_);
lean_inc_ref(v_machine_4348_);
lean_del_object(v___x_4340_);
lean_dec(v_a_4338_);
goto v___jp_4359_;
}
v___jp_4342_:
{
lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4343_, 0, v_a_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4343_);
v___x_4345_ = v___x_4340_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4343_);
v___x_4345_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; 
v___x_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4345_);
return v___x_4346_;
}
}
v___jp_4359_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___f_4363_; lean_object* v___x_4364_; lean_object* v___f_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4360_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4360_, 0, v_machine_4348_);
lean_ctor_set(v___x_4360_, 1, v_requestStream_4349_);
lean_ctor_set(v___x_4360_, 2, v_keepAliveTimeout_4350_);
lean_ctor_set(v___x_4360_, 3, v_currentTimeout_4351_);
lean_ctor_set(v___x_4360_, 4, v_headerTimeout_4352_);
lean_ctor_set(v___x_4360_, 5, v_response_4353_);
lean_ctor_set(v___x_4360_, 6, v_respStream_4354_);
lean_ctor_set(v___x_4360_, 7, v_expectData_4356_);
lean_ctor_set(v___x_4360_, 8, v_pendingHead_4358_);
lean_ctor_set_uint8(v___x_4360_, sizeof(void*)*9, v___x_4318_);
lean_ctor_set_uint8(v___x_4360_, sizeof(void*)*9 + 1, v_handlerDispatched_4357_);
lean_inc_ref(v___x_4360_);
v___x_4361_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4319_, v_connectionContext_4320_, v___x_4360_);
v___x_4362_ = lean_box(v___x_4318_);
lean_inc_ref(v_config_4324_);
lean_inc(v_handler_4323_);
lean_inc_ref(v_responseBodyInstance_4322_);
lean_inc_ref(v_h_4321_);
v___f_4363_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4363_, 0, v_h_4321_);
lean_closure_set(v___f_4363_, 1, v_responseBodyInstance_4322_);
lean_closure_set(v___f_4363_, 2, v_handler_4323_);
lean_closure_set(v___f_4363_, 3, v_config_4324_);
lean_closure_set(v___f_4363_, 4, v___x_4360_);
lean_closure_set(v___f_4363_, 5, v___x_4362_);
lean_closure_set(v___f_4363_, 6, v___f_4325_);
v___x_4364_ = lean_box(v___x_4318_);
v___f_4365_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4365_, 0, v_inst_4326_);
lean_closure_set(v___f_4365_, 1, v_h_4321_);
lean_closure_set(v___f_4365_, 2, v_responseBodyInstance_4322_);
lean_closure_set(v___f_4365_, 3, v_config_4324_);
lean_closure_set(v___f_4365_, 4, v_handler_4323_);
lean_closure_set(v___f_4365_, 5, v___x_4364_);
lean_closure_set(v___f_4365_, 6, v___f_4363_);
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4366_, v___x_4318_, v___x_4361_, v___f_4365_);
return v___x_4367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4373_, lean_object* v_socket_4374_, lean_object* v_connectionContext_4375_, lean_object* v_h_4376_, lean_object* v_responseBodyInstance_4377_, lean_object* v_handler_4378_, lean_object* v_config_4379_, lean_object* v___f_4380_, lean_object* v_inst_4381_, lean_object* v_x_4382_, lean_object* v___y_4383_){
_start:
{
uint8_t v___x_5769__boxed_4384_; lean_object* v_res_4385_; 
v___x_5769__boxed_4384_ = lean_unbox(v___x_4373_);
v_res_4385_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5769__boxed_4384_, v_socket_4374_, v_connectionContext_4375_, v_h_4376_, v_responseBodyInstance_4377_, v_handler_4378_, v_config_4379_, v___f_4380_, v_inst_4381_, v_x_4382_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4386_, lean_object* v_handler_4387_, lean_object* v_extensions_4388_, lean_object* v_connectionContext_4389_, uint8_t v___x_4390_, lean_object* v___f_4391_, lean_object* v_x_4392_){
_start:
{
if (lean_obj_tag(v_x_4392_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4402_; 
lean_dec_ref(v___f_4391_);
lean_dec_ref(v_connectionContext_4389_);
lean_dec(v_extensions_4388_);
lean_dec(v_handler_4387_);
lean_dec_ref(v_h_4386_);
v_a_4394_ = lean_ctor_get(v_x_4392_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_x_4392_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4396_ = v_x_4392_;
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v_x_4392_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_a_4403_ = lean_ctor_get(v_x_4392_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v_x_4392_, 1);
v___x_4404_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4386_, v_handler_4387_, v_extensions_4388_, v_connectionContext_4389_, v_a_4403_);
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4405_, v___x_4390_, v___x_4404_, v___f_4391_);
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4407_, lean_object* v_handler_4408_, lean_object* v_extensions_4409_, lean_object* v_connectionContext_4410_, lean_object* v___x_4411_, lean_object* v___f_4412_, lean_object* v_x_4413_, lean_object* v___y_4414_){
_start:
{
uint8_t v___x_5844__boxed_4415_; lean_object* v_res_4416_; 
v___x_5844__boxed_4415_ = lean_unbox(v___x_4411_);
v_res_4416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4407_, v_handler_4408_, v_extensions_4409_, v_connectionContext_4410_, v___x_5844__boxed_4415_, v___f_4412_, v_x_4413_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4417_, lean_object* v_responseBodyInstance_4418_, lean_object* v_handler_4419_, lean_object* v_config_4420_, lean_object* v_connectionContext_4421_, lean_object* v_events_4422_, lean_object* v___x_4423_, uint8_t v___x_4424_, lean_object* v___f_4425_, lean_object* v_____r_4426_){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4417_, v_responseBodyInstance_4418_, v_handler_4419_, v_config_4420_, v_connectionContext_4421_, v_events_4422_, v___x_4423_);
v___x_4429_ = lean_unsigned_to_nat(0u);
v___x_4430_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4429_, v___x_4424_, v___x_4428_, v___f_4425_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4431_, lean_object* v_responseBodyInstance_4432_, lean_object* v_handler_4433_, lean_object* v_config_4434_, lean_object* v_connectionContext_4435_, lean_object* v_events_4436_, lean_object* v___x_4437_, lean_object* v___x_4438_, lean_object* v___f_4439_, lean_object* v_____r_4440_, lean_object* v___y_4441_){
_start:
{
uint8_t v___x_5883__boxed_4442_; lean_object* v_res_4443_; 
v___x_5883__boxed_4442_ = lean_unbox(v___x_4438_);
v_res_4443_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4431_, v_responseBodyInstance_4432_, v_handler_4433_, v_config_4434_, v_connectionContext_4435_, v_events_4436_, v___x_4437_, v___x_5883__boxed_4442_, v___f_4439_, v_____r_4440_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4444_, lean_object* v___f_4445_, lean_object* v_x_4446_){
_start:
{
if (lean_obj_tag(v_x_4446_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4456_; 
lean_dec_ref(v___f_4445_);
lean_dec_ref(v___x_4444_);
v_a_4448_ = lean_ctor_get(v_x_4446_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_x_4446_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4450_ = v_x_4446_;
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v_x_4446_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4468_; 
v_a_4457_ = lean_ctor_get(v_x_4446_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_x_4446_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4459_ = v_x_4446_;
v_isShared_4460_ = v_isSharedCheck_4468_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v_x_4446_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4468_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
if (lean_obj_tag(v_a_4457_) == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4463_; 
lean_dec_ref(v___f_4445_);
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4444_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4461_);
v___x_4463_ = v___x_4459_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
lean_object* v___x_4464_; 
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
}
else
{
lean_object* v_val_4466_; lean_object* v___x_4467_; 
lean_del_object(v___x_4459_);
lean_dec_ref(v___x_4444_);
v_val_4466_ = lean_ctor_get(v_a_4457_, 0);
lean_inc(v_val_4466_);
lean_dec_ref_known(v_a_4457_, 1);
v___x_4467_ = lean_apply_2(v___f_4445_, v_val_4466_, lean_box(0));
return v___x_4467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4469_, lean_object* v___f_4470_, lean_object* v_x_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4469_, v___f_4470_, v_x_4471_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4474_, lean_object* v_responseBodyInstance_4475_, lean_object* v_handler_4476_, lean_object* v_config_4477_, lean_object* v_connectionContext_4478_, uint8_t v___x_4479_, lean_object* v___f_4480_, lean_object* v_inst_4481_, lean_object* v_socket_4482_, lean_object* v___f_4483_, lean_object* v___f_4484_, lean_object* v_x_4485_, lean_object* v_____s_4486_){
_start:
{
lean_object* v_machine_4488_; lean_object* v_reader_4489_; lean_object* v_requestStream_4490_; lean_object* v_keepAliveTimeout_4491_; lean_object* v_currentTimeout_4492_; lean_object* v_headerTimeout_4493_; lean_object* v_response_4494_; lean_object* v_respStream_4495_; uint8_t v_requiresData_4496_; lean_object* v_expectData_4497_; uint8_t v_handlerDispatched_4498_; lean_object* v_pendingHead_4499_; lean_object* v_writer_4500_; lean_object* v_state_4501_; uint8_t v___x_4502_; 
v_machine_4488_ = lean_ctor_get(v_____s_4486_, 0);
v_reader_4489_ = lean_ctor_get(v_machine_4488_, 0);
v_requestStream_4490_ = lean_ctor_get(v_____s_4486_, 1);
v_keepAliveTimeout_4491_ = lean_ctor_get(v_____s_4486_, 2);
v_currentTimeout_4492_ = lean_ctor_get(v_____s_4486_, 3);
v_headerTimeout_4493_ = lean_ctor_get(v_____s_4486_, 4);
v_response_4494_ = lean_ctor_get(v_____s_4486_, 5);
v_respStream_4495_ = lean_ctor_get(v_____s_4486_, 6);
v_requiresData_4496_ = lean_ctor_get_uint8(v_____s_4486_, sizeof(void*)*9);
v_expectData_4497_ = lean_ctor_get(v_____s_4486_, 7);
v_handlerDispatched_4498_ = lean_ctor_get_uint8(v_____s_4486_, sizeof(void*)*9 + 1);
v_pendingHead_4499_ = lean_ctor_get(v_____s_4486_, 8);
v_writer_4500_ = lean_ctor_get(v_machine_4488_, 1);
v_state_4501_ = lean_ctor_get(v_reader_4489_, 0);
v___x_4502_ = 0;
if (lean_obj_tag(v_state_4501_) == 6)
{
lean_object* v_state_4524_; 
v_state_4524_ = lean_ctor_get(v_writer_4500_, 2);
if (lean_obj_tag(v_state_4524_) == 7)
{
lean_object* v_outputData_4525_; lean_object* v_size_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v_outputData_4525_ = lean_ctor_get(v_writer_4500_, 1);
v_size_4526_ = lean_ctor_get(v_outputData_4525_, 1);
v___x_4527_ = lean_unsigned_to_nat(0u);
v___x_4528_ = lean_nat_dec_eq(v_size_4526_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_inc(v_pendingHead_4499_);
lean_inc(v_expectData_4497_);
lean_inc(v_respStream_4495_);
lean_inc_ref(v_response_4494_);
lean_inc(v_headerTimeout_4493_);
lean_inc(v_currentTimeout_4492_);
lean_inc(v_keepAliveTimeout_4491_);
lean_inc_ref(v_requestStream_4490_);
lean_inc_ref(v_machine_4488_);
lean_dec_ref(v_____s_4486_);
goto v___jp_4503_;
}
else
{
if (v___x_4528_ == 0)
{
lean_inc(v_pendingHead_4499_);
lean_inc(v_expectData_4497_);
lean_inc(v_respStream_4495_);
lean_inc_ref(v_response_4494_);
lean_inc(v_headerTimeout_4493_);
lean_inc(v_currentTimeout_4492_);
lean_inc(v_keepAliveTimeout_4491_);
lean_inc_ref(v_requestStream_4490_);
lean_inc_ref(v_machine_4488_);
lean_dec_ref(v_____s_4486_);
goto v___jp_4503_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_dec_ref(v___f_4484_);
lean_dec_ref(v___f_4483_);
lean_dec(v_socket_4482_);
lean_dec_ref(v_inst_4481_);
lean_dec_ref(v___f_4480_);
lean_dec_ref(v_connectionContext_4478_);
lean_dec_ref(v_config_4477_);
lean_dec(v_handler_4476_);
lean_dec_ref(v_responseBodyInstance_4475_);
lean_dec_ref(v_h_4474_);
v___x_4529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4529_, 0, v_____s_4486_);
v___x_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
}
else
{
lean_inc(v_pendingHead_4499_);
lean_inc(v_expectData_4497_);
lean_inc(v_respStream_4495_);
lean_inc_ref(v_response_4494_);
lean_inc(v_headerTimeout_4493_);
lean_inc(v_currentTimeout_4492_);
lean_inc(v_keepAliveTimeout_4491_);
lean_inc_ref(v_requestStream_4490_);
lean_inc_ref(v_machine_4488_);
lean_dec_ref(v_____s_4486_);
goto v___jp_4503_;
}
}
else
{
lean_inc(v_pendingHead_4499_);
lean_inc(v_expectData_4497_);
lean_inc(v_respStream_4495_);
lean_inc_ref(v_response_4494_);
lean_inc(v_headerTimeout_4493_);
lean_inc(v_currentTimeout_4492_);
lean_inc(v_keepAliveTimeout_4491_);
lean_inc_ref(v_requestStream_4490_);
lean_inc_ref(v_machine_4488_);
lean_dec_ref(v_____s_4486_);
goto v___jp_4503_;
}
v___jp_4503_:
{
lean_object* v___x_4504_; lean_object* v_snd_4505_; lean_object* v_output_4506_; lean_object* v_fst_4507_; lean_object* v_events_4508_; lean_object* v_data_4509_; lean_object* v_size_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___f_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4504_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4502_, v_machine_4488_);
v_snd_4505_ = lean_ctor_get(v___x_4504_, 1);
lean_inc(v_snd_4505_);
v_output_4506_ = lean_ctor_get(v_snd_4505_, 1);
lean_inc_ref(v_output_4506_);
v_fst_4507_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_fst_4507_);
lean_dec_ref(v___x_4504_);
v_events_4508_ = lean_ctor_get(v_snd_4505_, 0);
lean_inc_ref_n(v_events_4508_, 2);
lean_dec(v_snd_4505_);
v_data_4509_ = lean_ctor_get(v_output_4506_, 0);
lean_inc_ref(v_data_4509_);
v_size_4510_ = lean_ctor_get(v_output_4506_, 1);
lean_inc(v_size_4510_);
lean_dec_ref(v_output_4506_);
v___x_4511_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4511_, 0, v_fst_4507_);
lean_ctor_set(v___x_4511_, 1, v_requestStream_4490_);
lean_ctor_set(v___x_4511_, 2, v_keepAliveTimeout_4491_);
lean_ctor_set(v___x_4511_, 3, v_currentTimeout_4492_);
lean_ctor_set(v___x_4511_, 4, v_headerTimeout_4493_);
lean_ctor_set(v___x_4511_, 5, v_response_4494_);
lean_ctor_set(v___x_4511_, 6, v_respStream_4495_);
lean_ctor_set(v___x_4511_, 7, v_expectData_4497_);
lean_ctor_set(v___x_4511_, 8, v_pendingHead_4499_);
lean_ctor_set_uint8(v___x_4511_, sizeof(void*)*9, v_requiresData_4496_);
lean_ctor_set_uint8(v___x_4511_, sizeof(void*)*9 + 1, v_handlerDispatched_4498_);
v___x_4512_ = lean_box(v___x_4479_);
lean_inc_ref(v___f_4480_);
lean_inc_ref(v___x_4511_);
lean_inc_ref(v_connectionContext_4478_);
lean_inc_ref(v_config_4477_);
lean_inc(v_handler_4476_);
lean_inc_ref(v_responseBodyInstance_4475_);
lean_inc_ref(v_h_4474_);
v___f_4513_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4513_, 0, v_h_4474_);
lean_closure_set(v___f_4513_, 1, v_responseBodyInstance_4475_);
lean_closure_set(v___f_4513_, 2, v_handler_4476_);
lean_closure_set(v___f_4513_, 3, v_config_4477_);
lean_closure_set(v___f_4513_, 4, v_connectionContext_4478_);
lean_closure_set(v___f_4513_, 5, v_events_4508_);
lean_closure_set(v___f_4513_, 6, v___x_4511_);
lean_closure_set(v___f_4513_, 7, v___x_4512_);
lean_closure_set(v___f_4513_, 8, v___f_4480_);
v___x_4514_ = lean_unsigned_to_nat(0u);
v___x_4515_ = lean_nat_dec_lt(v___x_4514_, v_size_4510_);
lean_dec(v_size_4510_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
lean_dec_ref(v___f_4513_);
lean_dec_ref(v_data_4509_);
lean_dec_ref(v___f_4484_);
lean_dec_ref(v___f_4483_);
lean_dec(v_socket_4482_);
lean_dec_ref(v_inst_4481_);
v___x_4516_ = lean_box(0);
v___x_4517_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4474_, v_responseBodyInstance_4475_, v_handler_4476_, v_config_4477_, v_connectionContext_4478_, v_events_4508_, v___x_4511_, v___x_4479_, v___f_4480_, v___x_4516_);
return v___x_4517_;
}
else
{
lean_object* v_sendAll_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___f_4522_; lean_object* v___x_4523_; 
lean_dec_ref(v_events_4508_);
lean_dec_ref(v___f_4480_);
lean_dec_ref(v_connectionContext_4478_);
lean_dec_ref(v_config_4477_);
lean_dec(v_handler_4476_);
lean_dec_ref(v_responseBodyInstance_4475_);
lean_dec_ref(v_h_4474_);
v_sendAll_4518_ = lean_ctor_get(v_inst_4481_, 1);
lean_inc_ref(v_sendAll_4518_);
lean_dec_ref(v_inst_4481_);
v___x_4519_ = lean_apply_3(v_sendAll_4518_, v_socket_4482_, v_data_4509_, lean_box(0));
v___x_4520_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4514_, v___x_4479_, v___x_4519_, v___f_4483_);
v___x_4521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4514_, v___x_4479_, v___x_4520_, v___f_4484_);
v___f_4522_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4522_, 0, v___x_4511_);
lean_closure_set(v___f_4522_, 1, v___f_4513_);
v___x_4523_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4514_, v___x_4479_, v___x_4521_, v___f_4522_);
return v___x_4523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4532_, lean_object* v_responseBodyInstance_4533_, lean_object* v_handler_4534_, lean_object* v_config_4535_, lean_object* v_connectionContext_4536_, lean_object* v___x_4537_, lean_object* v___f_4538_, lean_object* v_inst_4539_, lean_object* v_socket_4540_, lean_object* v___f_4541_, lean_object* v___f_4542_, lean_object* v_x_4543_, lean_object* v_____s_4544_, lean_object* v___y_4545_){
_start:
{
uint8_t v___x_5957__boxed_4546_; lean_object* v_res_4547_; 
v___x_5957__boxed_4546_ = lean_unbox(v___x_4537_);
v_res_4547_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4532_, v_responseBodyInstance_4533_, v_handler_4534_, v_config_4535_, v_connectionContext_4536_, v___x_5957__boxed_4546_, v___f_4538_, v_inst_4539_, v_socket_4540_, v___f_4541_, v___f_4542_, v_x_4543_, v_____s_4544_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4548_, lean_object* v_x_4549_){
_start:
{
if (lean_obj_tag(v_x_4549_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4559_; 
v_a_4551_ = lean_ctor_get(v_x_4549_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_x_4549_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4553_ = v_x_4549_;
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v_x_4549_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4557_; 
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
return v___x_4557_;
}
}
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
lean_dec_ref_known(v_x_4549_, 1);
v___x_4560_ = l_IO_Promise_result_x21___redArg(v_a_4548_);
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
return v___x_4561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4562_, lean_object* v_x_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4562_, v_x_4563_);
lean_dec(v_a_4562_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4566_, lean_object* v___x_4567_, lean_object* v___x_4568_, uint8_t v___x_4569_, lean_object* v_x_4570_){
_start:
{
if (lean_obj_tag(v_x_4570_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v___x_4568_);
lean_dec(v___x_4567_);
lean_dec_ref(v___f_4566_);
v_a_4572_ = lean_ctor_get(v_x_4570_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_x_4570_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4574_ = v_x_4570_;
v_isShared_4575_ = v_isSharedCheck_4580_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v_x_4570_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4580_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
lean_object* v___x_4578_; 
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4592_; 
v_a_4581_ = lean_ctor_get(v_x_4570_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_x_4570_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4583_ = v_x_4570_;
v_isShared_4584_ = v_isSharedCheck_4592_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v_x_4570_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4592_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v___f_4586_; lean_object* v___x_4588_; 
lean_inc(v_a_4581_);
lean_inc(v___x_4567_);
v___x_4585_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4566_, v___x_4567_, v_a_4581_, v___x_4568_);
v___f_4586_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4586_, 0, v_a_4581_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4585_);
v___x_4588_ = v___x_4583_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4585_);
v___x_4588_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
v___x_4590_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4567_, v___x_4569_, v___x_4589_, v___f_4586_);
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4593_, lean_object* v___x_4594_, lean_object* v___x_4595_, lean_object* v___x_4596_, lean_object* v_x_4597_, lean_object* v___y_4598_){
_start:
{
uint8_t v___x_6060__boxed_4599_; lean_object* v_res_4600_; 
v___x_6060__boxed_4599_ = lean_unbox(v___x_4596_);
v_res_4600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4593_, v___x_4594_, v___x_4595_, v___x_6060__boxed_4599_, v_x_4597_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4601_, lean_object* v_machine_4602_, lean_object* v_a_4603_, lean_object* v___x_4604_, lean_object* v_socket_4605_, lean_object* v_connectionContext_4606_, lean_object* v_h_4607_, lean_object* v_responseBodyInstance_4608_, lean_object* v_handler_4609_, lean_object* v___f_4610_, lean_object* v_inst_4611_, lean_object* v_extensions_4612_, lean_object* v___f_4613_, lean_object* v___f_4614_, lean_object* v___f_4615_, lean_object* v_x_4616_){
_start:
{
if (lean_obj_tag(v_x_4616_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4626_; 
lean_dec_ref(v___f_4615_);
lean_dec_ref(v___f_4614_);
lean_dec_ref(v___f_4613_);
lean_dec(v_extensions_4612_);
lean_dec_ref(v_inst_4611_);
lean_dec_ref(v___f_4610_);
lean_dec(v_handler_4609_);
lean_dec_ref(v_responseBodyInstance_4608_);
lean_dec_ref(v_h_4607_);
lean_dec_ref(v_connectionContext_4606_);
lean_dec(v_socket_4605_);
lean_dec(v___x_4604_);
lean_dec_ref(v_a_4603_);
lean_dec_ref(v_machine_4602_);
lean_dec_ref(v_config_4601_);
v_a_4618_ = lean_ctor_get(v_x_4616_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_x_4616_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4620_ = v_x_4616_;
v_isShared_4621_ = v_isSharedCheck_4626_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v_x_4616_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4626_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
return v___x_4624_;
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4652_; 
v_a_4627_ = lean_ctor_get(v_x_4616_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v_x_4616_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4629_ = v_x_4616_;
v_isShared_4630_ = v_isSharedCheck_4652_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v_x_4616_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4652_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v_keepAliveTimeout_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___f_4638_; lean_object* v___x_4639_; lean_object* v___f_4640_; lean_object* v___x_4641_; lean_object* v___f_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___f_4645_; lean_object* v___x_4647_; 
v_keepAliveTimeout_4631_ = lean_ctor_get(v_config_4601_, 5);
lean_inc_n(v_keepAliveTimeout_4631_, 2);
v___x_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_keepAliveTimeout_4631_);
v___x_4633_ = lean_box(0);
v___x_4634_ = 0;
v___x_4635_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4635_, 0, v_machine_4602_);
lean_ctor_set(v___x_4635_, 1, v_a_4603_);
lean_ctor_set(v___x_4635_, 2, v___x_4632_);
lean_ctor_set(v___x_4635_, 3, v_keepAliveTimeout_4631_);
lean_ctor_set(v___x_4635_, 4, v___x_4633_);
lean_ctor_set(v___x_4635_, 5, v_a_4627_);
lean_ctor_set(v___x_4635_, 6, v___x_4633_);
lean_ctor_set(v___x_4635_, 7, v___x_4604_);
lean_ctor_set(v___x_4635_, 8, v___x_4633_);
lean_ctor_set_uint8(v___x_4635_, sizeof(void*)*9, v___x_4634_);
lean_ctor_set_uint8(v___x_4635_, sizeof(void*)*9 + 1, v___x_4634_);
v___x_4636_ = lean_io_promise_new();
v___x_4637_ = lean_box(v___x_4634_);
lean_inc_ref(v_inst_4611_);
lean_inc_ref(v_config_4601_);
lean_inc_n(v_handler_4609_, 2);
lean_inc_ref(v_responseBodyInstance_4608_);
lean_inc_ref_n(v_h_4607_, 2);
lean_inc_ref_n(v_connectionContext_4606_, 2);
lean_inc(v_socket_4605_);
v___f_4638_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4638_, 0, v___x_4637_);
lean_closure_set(v___f_4638_, 1, v_socket_4605_);
lean_closure_set(v___f_4638_, 2, v_connectionContext_4606_);
lean_closure_set(v___f_4638_, 3, v_h_4607_);
lean_closure_set(v___f_4638_, 4, v_responseBodyInstance_4608_);
lean_closure_set(v___f_4638_, 5, v_handler_4609_);
lean_closure_set(v___f_4638_, 6, v_config_4601_);
lean_closure_set(v___f_4638_, 7, v___f_4610_);
lean_closure_set(v___f_4638_, 8, v_inst_4611_);
v___x_4639_ = lean_box(v___x_4634_);
v___f_4640_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4640_, 0, v_h_4607_);
lean_closure_set(v___f_4640_, 1, v_handler_4609_);
lean_closure_set(v___f_4640_, 2, v_extensions_4612_);
lean_closure_set(v___f_4640_, 3, v_connectionContext_4606_);
lean_closure_set(v___f_4640_, 4, v___x_4639_);
lean_closure_set(v___f_4640_, 5, v___f_4638_);
v___x_4641_ = lean_box(v___x_4634_);
v___f_4642_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4642_, 0, v_h_4607_);
lean_closure_set(v___f_4642_, 1, v_responseBodyInstance_4608_);
lean_closure_set(v___f_4642_, 2, v_handler_4609_);
lean_closure_set(v___f_4642_, 3, v_config_4601_);
lean_closure_set(v___f_4642_, 4, v_connectionContext_4606_);
lean_closure_set(v___f_4642_, 5, v___x_4641_);
lean_closure_set(v___f_4642_, 6, v___f_4640_);
lean_closure_set(v___f_4642_, 7, v_inst_4611_);
lean_closure_set(v___f_4642_, 8, v_socket_4605_);
lean_closure_set(v___f_4642_, 9, v___f_4613_);
lean_closure_set(v___f_4642_, 10, v___f_4614_);
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = lean_box(v___x_4634_);
v___f_4645_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4645_, 0, v___f_4642_);
lean_closure_set(v___f_4645_, 1, v___x_4643_);
lean_closure_set(v___f_4645_, 2, v___x_4635_);
lean_closure_set(v___f_4645_, 3, v___x_4644_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4636_);
v___x_4647_ = v___x_4629_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4636_);
v___x_4647_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
v___x_4649_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4643_, v___x_4634_, v___x_4648_, v___f_4645_);
v___x_4650_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4643_, v___x_4634_, v___x_4649_, v___f_4615_);
return v___x_4650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4653_ = _args[0];
lean_object* v_machine_4654_ = _args[1];
lean_object* v_a_4655_ = _args[2];
lean_object* v___x_4656_ = _args[3];
lean_object* v_socket_4657_ = _args[4];
lean_object* v_connectionContext_4658_ = _args[5];
lean_object* v_h_4659_ = _args[6];
lean_object* v_responseBodyInstance_4660_ = _args[7];
lean_object* v_handler_4661_ = _args[8];
lean_object* v___f_4662_ = _args[9];
lean_object* v_inst_4663_ = _args[10];
lean_object* v_extensions_4664_ = _args[11];
lean_object* v___f_4665_ = _args[12];
lean_object* v___f_4666_ = _args[13];
lean_object* v___f_4667_ = _args[14];
lean_object* v_x_4668_ = _args[15];
lean_object* v___y_4669_ = _args[16];
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4653_, v_machine_4654_, v_a_4655_, v___x_4656_, v_socket_4657_, v_connectionContext_4658_, v_h_4659_, v_responseBodyInstance_4660_, v_handler_4661_, v___f_4662_, v_inst_4663_, v_extensions_4664_, v___f_4665_, v___f_4666_, v___f_4667_, v_x_4668_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4671_, lean_object* v_machine_4672_, lean_object* v_socket_4673_, lean_object* v_connectionContext_4674_, lean_object* v_h_4675_, lean_object* v_responseBodyInstance_4676_, lean_object* v_handler_4677_, lean_object* v___f_4678_, lean_object* v_inst_4679_, lean_object* v_extensions_4680_, lean_object* v___f_4681_, lean_object* v___f_4682_, lean_object* v___f_4683_, lean_object* v_x_4684_){
_start:
{
if (lean_obj_tag(v_x_4684_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v___f_4683_);
lean_dec_ref(v___f_4682_);
lean_dec_ref(v___f_4681_);
lean_dec(v_extensions_4680_);
lean_dec_ref(v_inst_4679_);
lean_dec_ref(v___f_4678_);
lean_dec(v_handler_4677_);
lean_dec_ref(v_responseBodyInstance_4676_);
lean_dec_ref(v_h_4675_);
lean_dec_ref(v_connectionContext_4674_);
lean_dec(v_socket_4673_);
lean_dec_ref(v_machine_4672_);
lean_dec_ref(v_config_4671_);
v_a_4686_ = lean_ctor_get(v_x_4684_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_x_4684_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4688_ = v_x_4684_;
v_isShared_4689_ = v_isSharedCheck_4694_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v_x_4684_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4694_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
lean_object* v___x_4692_; 
v___x_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
return v___x_4692_;
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4709_; 
v_a_4695_ = lean_ctor_get(v_x_4684_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_x_4684_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4697_ = v_x_4684_;
v_isShared_4698_ = v_isSharedCheck_4709_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v_x_4684_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4709_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___f_4701_; lean_object* v___x_4703_; 
v___x_4699_ = lean_box(0);
v___x_4700_ = l_Std_CloseableChannel_new___redArg(v___x_4699_);
v___f_4701_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4701_, 0, v_config_4671_);
lean_closure_set(v___f_4701_, 1, v_machine_4672_);
lean_closure_set(v___f_4701_, 2, v_a_4695_);
lean_closure_set(v___f_4701_, 3, v___x_4699_);
lean_closure_set(v___f_4701_, 4, v_socket_4673_);
lean_closure_set(v___f_4701_, 5, v_connectionContext_4674_);
lean_closure_set(v___f_4701_, 6, v_h_4675_);
lean_closure_set(v___f_4701_, 7, v_responseBodyInstance_4676_);
lean_closure_set(v___f_4701_, 8, v_handler_4677_);
lean_closure_set(v___f_4701_, 9, v___f_4678_);
lean_closure_set(v___f_4701_, 10, v_inst_4679_);
lean_closure_set(v___f_4701_, 11, v_extensions_4680_);
lean_closure_set(v___f_4701_, 12, v___f_4681_);
lean_closure_set(v___f_4701_, 13, v___f_4682_);
lean_closure_set(v___f_4701_, 14, v___f_4683_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 0, v___x_4700_);
v___x_4703_ = v___x_4697_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4700_);
v___x_4703_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4707_; 
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = 0;
v___x_4707_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4705_, v___x_4706_, v___x_4704_, v___f_4701_);
return v___x_4707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4710_, lean_object* v_machine_4711_, lean_object* v_socket_4712_, lean_object* v_connectionContext_4713_, lean_object* v_h_4714_, lean_object* v_responseBodyInstance_4715_, lean_object* v_handler_4716_, lean_object* v___f_4717_, lean_object* v_inst_4718_, lean_object* v_extensions_4719_, lean_object* v___f_4720_, lean_object* v___f_4721_, lean_object* v___f_4722_, lean_object* v_x_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4710_, v_machine_4711_, v_socket_4712_, v_connectionContext_4713_, v_h_4714_, v_responseBodyInstance_4715_, v_handler_4716_, v___f_4717_, v_inst_4718_, v_extensions_4719_, v___f_4720_, v___f_4721_, v___f_4722_, v_x_4723_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4729_, lean_object* v_h_4730_, lean_object* v_connection_4731_, lean_object* v_config_4732_, lean_object* v_connectionContext_4733_, lean_object* v_handler_4734_){
_start:
{
lean_object* v_responseBodyInstance_4736_; lean_object* v_onFailure_4737_; lean_object* v___x_4738_; lean_object* v_socket_4739_; lean_object* v_machine_4740_; lean_object* v_extensions_4741_; lean_object* v___f_4742_; lean_object* v___f_4743_; lean_object* v___f_4744_; lean_object* v___f_4745_; lean_object* v___f_4746_; lean_object* v___f_4747_; lean_object* v___f_4748_; lean_object* v___f_4749_; lean_object* v___f_4750_; lean_object* v___x_4751_; uint8_t v___x_4752_; lean_object* v___x_4753_; 
v_responseBodyInstance_4736_ = lean_ctor_get(v_h_4730_, 0);
lean_inc_ref_n(v_responseBodyInstance_4736_, 2);
v_onFailure_4737_ = lean_ctor_get(v_h_4730_, 2);
v___x_4738_ = l_Std_Http_Body_mkStream();
v_socket_4739_ = lean_ctor_get(v_connection_4731_, 0);
lean_inc_n(v_socket_4739_, 2);
v_machine_4740_ = lean_ctor_get(v_connection_4731_, 1);
lean_inc_ref(v_machine_4740_);
v_extensions_4741_ = lean_ctor_get(v_connection_4731_, 2);
lean_inc(v_extensions_4741_);
lean_dec_ref(v_connection_4731_);
v___f_4742_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4743_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4744_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4745_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4734_);
lean_inc_ref(v_onFailure_4737_);
v___f_4746_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4746_, 0, v_onFailure_4737_);
lean_closure_set(v___f_4746_, 1, v_handler_4734_);
lean_closure_set(v___f_4746_, 2, v___f_4745_);
lean_inc_ref(v_inst_4729_);
v___f_4747_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4747_, 0, v_inst_4729_);
lean_closure_set(v___f_4747_, 1, v_socket_4739_);
lean_inc_ref(v___f_4747_);
v___f_4748_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4748_, 0, v___f_4747_);
v___f_4749_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4749_, 0, v___f_4742_);
lean_closure_set(v___f_4749_, 1, v_responseBodyInstance_4736_);
lean_closure_set(v___f_4749_, 2, v___f_4748_);
lean_closure_set(v___f_4749_, 3, v___f_4747_);
v___f_4750_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4750_, 0, v_config_4732_);
lean_closure_set(v___f_4750_, 1, v_machine_4740_);
lean_closure_set(v___f_4750_, 2, v_socket_4739_);
lean_closure_set(v___f_4750_, 3, v_connectionContext_4733_);
lean_closure_set(v___f_4750_, 4, v_h_4730_);
lean_closure_set(v___f_4750_, 5, v_responseBodyInstance_4736_);
lean_closure_set(v___f_4750_, 6, v_handler_4734_);
lean_closure_set(v___f_4750_, 7, v___f_4743_);
lean_closure_set(v___f_4750_, 8, v_inst_4729_);
lean_closure_set(v___f_4750_, 9, v_extensions_4741_);
lean_closure_set(v___f_4750_, 10, v___f_4744_);
lean_closure_set(v___f_4750_, 11, v___f_4746_);
lean_closure_set(v___f_4750_, 12, v___f_4749_);
v___x_4751_ = lean_unsigned_to_nat(0u);
v___x_4752_ = 0;
v___x_4753_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4751_, v___x_4752_, v___x_4738_, v___f_4750_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4754_, lean_object* v_h_4755_, lean_object* v_connection_4756_, lean_object* v_config_4757_, lean_object* v_connectionContext_4758_, lean_object* v_handler_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4754_, v_h_4755_, v_connection_4756_, v_config_4757_, v_connectionContext_4758_, v_handler_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4762_, lean_object* v_00_u03c3_4763_, lean_object* v_inst_4764_, lean_object* v_h_4765_, lean_object* v_connection_4766_, lean_object* v_config_4767_, lean_object* v_connectionContext_4768_, lean_object* v_handler_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4764_, v_h_4765_, v_connection_4766_, v_config_4767_, v_connectionContext_4768_, v_handler_4769_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4772_, lean_object* v_00_u03c3_4773_, lean_object* v_inst_4774_, lean_object* v_h_4775_, lean_object* v_connection_4776_, lean_object* v_config_4777_, lean_object* v_connectionContext_4778_, lean_object* v_handler_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4772_, v_00_u03c3_4773_, v_inst_4774_, v_h_4775_, v_connection_4776_, v_config_4777_, v_connectionContext_4778_, v_handler_4779_);
return v_res_4781_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = 0;
v___x_4783_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4782_);
return v___x_4783_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_unsigned_to_nat(4096u);
v___x_4785_ = lean_mk_empty_byte_array(v___x_4784_);
return v___x_4785_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4787_ = l_ByteArray_mkIterator(v___x_4786_);
return v___x_4787_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4788_ = 0;
v___x_4789_ = lean_unsigned_to_nat(0u);
v___x_4790_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4791_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4792_ = lean_box(0);
v___x_4793_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
lean_ctor_set(v___x_4793_, 1, v___x_4791_);
lean_ctor_set(v___x_4793_, 2, v___x_4790_);
lean_ctor_set(v___x_4793_, 3, v___x_4789_);
lean_ctor_set(v___x_4793_, 4, v___x_4789_);
lean_ctor_set(v___x_4793_, 5, v___x_4789_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*6, v___x_4788_);
return v___x_4793_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = 1;
v___x_4802_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4801_);
return v___x_4802_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = 0;
v___x_4805_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4806_ = lean_box(0);
v___x_4807_ = lean_box(0);
v___x_4808_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4809_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4810_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4810_, 0, v___x_4809_);
lean_ctor_set(v___x_4810_, 1, v___x_4808_);
lean_ctor_set(v___x_4810_, 2, v___x_4807_);
lean_ctor_set(v___x_4810_, 3, v___x_4806_);
lean_ctor_set(v___x_4810_, 4, v___x_4805_);
lean_ctor_set(v___x_4810_, 5, v___x_4803_);
lean_ctor_set_uint8(v___x_4810_, sizeof(void*)*6, v___x_4804_);
lean_ctor_set_uint8(v___x_4810_, sizeof(void*)*6 + 1, v___x_4804_);
lean_ctor_set_uint8(v___x_4810_, sizeof(void*)*6 + 2, v___x_4804_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4811_, lean_object* v_client_4812_, lean_object* v_extensions_4813_, lean_object* v_inst_4814_, lean_object* v_inst_4815_, lean_object* v_handler_4816_, lean_object* v_x_4817_){
_start:
{
if (lean_obj_tag(v_x_4817_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4827_; 
lean_dec(v_handler_4816_);
lean_dec_ref(v_inst_4815_);
lean_dec_ref(v_inst_4814_);
lean_dec(v_extensions_4813_);
lean_dec(v_client_4812_);
lean_dec_ref(v_config_4811_);
v_a_4819_ = lean_ctor_get(v_x_4817_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v_x_4817_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4821_ = v_x_4817_;
v_isShared_4822_ = v_isSharedCheck_4827_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v_x_4817_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4827_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; 
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
}
}
else
{
lean_object* v_a_4828_; uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v_enableKeepAlive_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_a_4828_ = lean_ctor_get(v_x_4817_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v_x_4817_, 1);
v___x_4829_ = 0;
v___x_4830_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4831_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4832_ = lean_box(0);
v___x_4833_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4834_ = l_Std_Http_Config_toH1Config(v_config_4811_);
v_enableKeepAlive_4835_ = lean_ctor_get_uint8(v___x_4834_, sizeof(void*)*18);
v___x_4836_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4836_, 0, v___x_4830_);
lean_ctor_set(v___x_4836_, 1, v___x_4833_);
lean_ctor_set(v___x_4836_, 2, v___x_4834_);
lean_ctor_set(v___x_4836_, 3, v___x_4831_);
lean_ctor_set(v___x_4836_, 4, v___x_4832_);
lean_ctor_set(v___x_4836_, 5, v___x_4832_);
lean_ctor_set_uint8(v___x_4836_, sizeof(void*)*6, v_enableKeepAlive_4835_);
lean_ctor_set_uint8(v___x_4836_, sizeof(void*)*6 + 1, v___x_4829_);
lean_ctor_set_uint8(v___x_4836_, sizeof(void*)*6 + 2, v___x_4829_);
v___x_4837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4837_, 0, v_client_4812_);
lean_ctor_set(v___x_4837_, 1, v___x_4836_);
lean_ctor_set(v___x_4837_, 2, v_extensions_4813_);
v___x_4838_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4814_, v_inst_4815_, v___x_4837_, v_config_4811_, v_a_4828_, v_handler_4816_);
return v___x_4838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4839_, lean_object* v_client_4840_, lean_object* v_extensions_4841_, lean_object* v_inst_4842_, lean_object* v_inst_4843_, lean_object* v_handler_4844_, lean_object* v_x_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4839_, v_client_4840_, v_extensions_4841_, v_inst_4842_, v_inst_4843_, v_handler_4844_, v_x_4845_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_client_4850_, lean_object* v_handler_4851_, lean_object* v_config_4852_, lean_object* v_extensions_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v___f_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; lean_object* v___x_4861_; 
v___f_4856_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4856_, 0, v_config_4852_);
lean_closure_set(v___f_4856_, 1, v_client_4850_);
lean_closure_set(v___f_4856_, 2, v_extensions_4853_);
lean_closure_set(v___f_4856_, 3, v_inst_4848_);
lean_closure_set(v___f_4856_, 4, v_inst_4849_);
lean_closure_set(v___f_4856_, 5, v_handler_4851_);
lean_inc_ref(v_a_4854_);
v___x_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4857_, 0, v_a_4854_);
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = 0;
v___x_4861_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4859_, v___x_4860_, v___x_4858_, v___f_4856_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4862_, lean_object* v_inst_4863_, lean_object* v_client_4864_, lean_object* v_handler_4865_, lean_object* v_config_4866_, lean_object* v_extensions_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4862_, v_inst_4863_, v_client_4864_, v_handler_4865_, v_config_4866_, v_extensions_4867_, v_a_4868_);
lean_dec_ref(v_a_4868_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4871_, lean_object* v_00_u03c3_4872_, lean_object* v_inst_4873_, lean_object* v_inst_4874_, lean_object* v_client_4875_, lean_object* v_handler_4876_, lean_object* v_config_4877_, lean_object* v_extensions_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4873_, v_inst_4874_, v_client_4875_, v_handler_4876_, v_config_4877_, v_extensions_4878_, v_a_4879_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4882_, lean_object* v_00_u03c3_4883_, lean_object* v_inst_4884_, lean_object* v_inst_4885_, lean_object* v_client_4886_, lean_object* v_handler_4887_, lean_object* v_config_4888_, lean_object* v_extensions_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l_Std_Http_Server_serveConnection(v_t_4882_, v_00_u03c3_4883_, v_inst_4884_, v_inst_4885_, v_client_4886_, v_handler_4887_, v_config_4888_, v_extensions_4889_, v_a_4890_);
lean_dec_ref(v_a_4890_);
return v_res_4892_;
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
