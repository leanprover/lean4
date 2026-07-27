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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1184_, uint8_t v___x_1185_, lean_object* v___f_1186_, lean_object* v___f_1187_, lean_object* v_x1_1188_, lean_object* v_x2_1189_){
_start:
{
lean_object* v_fst_1190_; uint8_t v___x_1191_; 
v_fst_1190_ = lean_ctor_get(v_x2_1189_, 0);
lean_inc(v_fst_1190_);
v___x_1191_ = lean_string_dec_eq(v___x_1184_, v_fst_1190_);
if (v___x_1191_ == 0)
{
if (v___x_1185_ == 0)
{
lean_dec(v_fst_1190_);
lean_dec_ref(v_x2_1189_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___f_1186_);
return v_x1_1188_;
}
else
{
lean_object* v_entries_1192_; lean_object* v_indexes_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1204_; 
v_entries_1192_ = lean_ctor_get(v_x1_1188_, 0);
v_indexes_1193_ = lean_ctor_get(v_x1_1188_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x1_1188_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1195_ = v_x1_1188_;
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_indexes_1193_);
lean_inc(v_entries_1192_);
lean_dec(v_x1_1188_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_i_1197_; lean_object* v_f_1198_; lean_object* v_entries_1199_; lean_object* v_indexes_1200_; lean_object* v___x_1202_; 
v_i_1197_ = lean_array_get_size(v_entries_1192_);
v_f_1198_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1198_, 0, v_i_1197_);
v_entries_1199_ = lean_array_push(v_entries_1192_, v_x2_1189_);
v_indexes_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1186_, v___f_1187_, v_indexes_1193_, v_fst_1190_, v_f_1198_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_indexes_1200_);
lean_ctor_set(v___x_1195_, 0, v_entries_1199_);
v___x_1202_ = v___x_1195_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_entries_1199_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_indexes_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_dec(v_fst_1190_);
lean_dec_ref(v_x2_1189_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___f_1186_);
return v_x1_1188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v___f_1207_, lean_object* v___f_1208_, lean_object* v_x1_1209_, lean_object* v_x2_1210_){
_start:
{
uint8_t v___x_2375__boxed_1211_; lean_object* v_res_1212_; 
v___x_2375__boxed_1211_ = lean_unbox(v___x_1206_);
v_res_1212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1205_, v___x_2375__boxed_1211_, v___f_1207_, v___f_1208_, v_x1_1209_, v_x2_1210_);
lean_dec_ref(v___x_1205_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1234_, lean_object* v_body_1235_, lean_object* v_isClosed_1236_, lean_object* v_close_1237_, lean_object* v_x_1238_){
_start:
{
lean_object* v___y_1241_; uint8_t v_omitBody_1242_; lean_object* v___y_1255_; uint8_t v___y_1290_; lean_object* v___y_1291_; uint8_t v___y_1292_; 
if (lean_obj_tag(v_x_1238_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_close_1237_);
lean_dec_ref(v_isClosed_1236_);
lean_dec(v_body_1235_);
lean_dec_ref(v___y_1234_);
v_a_1295_ = lean_ctor_get(v_x_1238_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_x_1238_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1297_ = v_x_1238_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v_x_1238_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
}
else
{
lean_object* v_writer_1304_; lean_object* v_a_1305_; lean_object* v_reader_1306_; lean_object* v_config_1307_; lean_object* v_events_1308_; lean_object* v_error_1309_; lean_object* v_instant_1310_; uint8_t v_keepAlive_1311_; uint8_t v_forcedFlush_1312_; uint8_t v_pullBodyStalled_1313_; lean_object* v_userData_1314_; lean_object* v_outputData_1315_; lean_object* v_state_1316_; lean_object* v_knownSize_1317_; lean_object* v_messageHead_1318_; uint8_t v_sentMessage_1319_; uint8_t v_userClosedBody_1320_; uint8_t v_omitBody_1321_; lean_object* v_userDataBytes_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1438_; 
v_writer_1304_ = lean_ctor_get(v___y_1234_, 1);
lean_inc_ref(v_writer_1304_);
v_a_1305_ = lean_ctor_get(v_x_1238_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v_x_1238_, 1);
v_reader_1306_ = lean_ctor_get(v___y_1234_, 0);
v_config_1307_ = lean_ctor_get(v___y_1234_, 2);
v_events_1308_ = lean_ctor_get(v___y_1234_, 3);
v_error_1309_ = lean_ctor_get(v___y_1234_, 4);
v_instant_1310_ = lean_ctor_get(v___y_1234_, 5);
v_keepAlive_1311_ = lean_ctor_get_uint8(v___y_1234_, sizeof(void*)*6);
v_forcedFlush_1312_ = lean_ctor_get_uint8(v___y_1234_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1313_ = lean_ctor_get_uint8(v___y_1234_, sizeof(void*)*6 + 2);
v_userData_1314_ = lean_ctor_get(v_writer_1304_, 0);
v_outputData_1315_ = lean_ctor_get(v_writer_1304_, 1);
v_state_1316_ = lean_ctor_get(v_writer_1304_, 2);
v_knownSize_1317_ = lean_ctor_get(v_writer_1304_, 3);
v_messageHead_1318_ = lean_ctor_get(v_writer_1304_, 4);
v_sentMessage_1319_ = lean_ctor_get_uint8(v_writer_1304_, sizeof(void*)*6);
v_userClosedBody_1320_ = lean_ctor_get_uint8(v_writer_1304_, sizeof(void*)*6 + 1);
v_omitBody_1321_ = lean_ctor_get_uint8(v_writer_1304_, sizeof(void*)*6 + 2);
v_userDataBytes_1322_ = lean_ctor_get(v_writer_1304_, 5);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_writer_1304_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1324_ = v_writer_1304_;
v_isShared_1325_ = v_isSharedCheck_1438_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_userDataBytes_1322_);
lean_inc(v_messageHead_1318_);
lean_inc(v_knownSize_1317_);
lean_inc(v_state_1316_);
lean_inc(v_outputData_1315_);
lean_inc(v_userData_1314_);
lean_dec(v_writer_1304_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1438_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; uint8_t v___y_1356_; uint8_t v___y_1357_; uint8_t v___y_1358_; lean_object* v___y_1359_; uint8_t v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; uint8_t v___x_1387_; uint8_t v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1401_; uint8_t v___y_1402_; uint8_t v___y_1403_; uint8_t v___y_1416_; uint8_t v___y_1417_; uint8_t v___y_1420_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1387_ = 0;
v___x_1436_ = lean_box(1);
v___x_1437_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1316_, v___x_1436_);
if (v___x_1437_ == 0)
{
v___y_1420_ = v___x_1437_;
goto v___jp_1419_;
}
else
{
if (v_sentMessage_1319_ == 0)
{
v___y_1420_ = v___x_1437_;
goto v___jp_1419_;
}
else
{
lean_del_object(v___x_1324_);
lean_dec(v_userDataBytes_1322_);
lean_dec(v_messageHead_1318_);
lean_dec(v_knownSize_1317_);
lean_dec(v_state_1316_);
lean_dec_ref(v_outputData_1315_);
lean_dec_ref(v_userData_1314_);
lean_dec(v_a_1305_);
v___y_1241_ = v___y_1234_;
v_omitBody_1242_ = v_omitBody_1321_;
goto v___jp_1240_;
}
}
v___jp_1326_:
{
lean_object* v_message_1329_; lean_object* v___x_2151__overap_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_message_1329_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1327_, v_a_1305_, v___y_1328_);
v___x_2151__overap_1330_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1327_);
v___x_1331_ = lean_apply_2(v___x_2151__overap_1330_, v_outputData_1315_, v_message_1329_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1331_);
v___x_1333_ = v___x_1324_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_userData_1314_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_state_1316_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_knownSize_1317_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_messageHead_1318_);
lean_ctor_set(v_reuseFailAlloc_1335_, 5, v_userDataBytes_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*6, v_sentMessage_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*6 + 1, v_userClosedBody_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*6 + 2, v_omitBody_1321_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1334_, 0, v_reader_1306_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
lean_ctor_set(v___x_1334_, 2, v_config_1307_);
lean_ctor_set(v___x_1334_, 3, v_events_1308_);
lean_ctor_set(v___x_1334_, 4, v_error_1309_);
lean_ctor_set(v___x_1334_, 5, v_instant_1310_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*6, v_keepAlive_1311_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*6 + 1, v_forcedFlush_1312_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*6 + 2, v_pullBodyStalled_1313_);
v___y_1241_ = v___x_1334_;
v_omitBody_1242_ = v_omitBody_1321_;
goto v___jp_1240_;
}
}
v___jp_1336_:
{
lean_object* v_entries_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_entries_1342_ = lean_ctor_get(v___y_1339_, 0);
lean_inc_ref(v_entries_1342_);
lean_dec_ref(v___y_1339_);
v___x_1343_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1340_, v___y_1337_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v___y_1340_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_array_get_size(v_entries_1342_);
v___x_1346_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_1347_ = lean_nat_dec_lt(v___x_1344_, v___x_1345_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v_entries_1342_);
lean_dec_ref(v___y_1338_);
v___y_1327_ = v___y_1341_;
v___y_1328_ = v___x_1343_;
goto v___jp_1326_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_nat_dec_le(v___x_1345_, v___x_1345_);
if (v___x_1348_ == 0)
{
if (v___x_1347_ == 0)
{
lean_dec_ref(v_entries_1342_);
lean_dec_ref(v___y_1338_);
v___y_1327_ = v___y_1341_;
v___y_1328_ = v___x_1343_;
goto v___jp_1326_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1345_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1346_, v___y_1338_, v_entries_1342_, v___x_1349_, v___x_1350_, v___x_1343_);
v___y_1327_ = v___y_1341_;
v___y_1328_ = v___x_1351_;
goto v___jp_1326_;
}
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1345_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1346_, v___y_1338_, v_entries_1342_, v___x_1352_, v___x_1353_, v___x_1343_);
v___y_1327_ = v___y_1341_;
v___y_1328_ = v___x_1354_;
goto v___jp_1326_;
}
}
}
v___jp_1355_:
{
lean_object* v___x_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; uint8_t v___x_1365_; 
v___x_1360_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1361_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___f_1362_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___x_1363_ = lean_box(v___y_1356_);
v___f_1364_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1364_, 0, v___x_1360_);
lean_closure_set(v___f_1364_, 1, v___x_1363_);
lean_closure_set(v___f_1364_, 2, v___f_1361_);
lean_closure_set(v___f_1364_, 3, v___f_1362_);
v___x_1365_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1361_, v___f_1362_, v___x_1360_, v___y_1359_);
if (v___x_1365_ == 0)
{
if (v___y_1357_ == 0)
{
v___y_1337_ = v___f_1362_;
v___y_1338_ = v___f_1364_;
v___y_1339_ = v___y_1359_;
v___y_1340_ = v___f_1361_;
v___y_1341_ = v___y_1358_;
goto v___jp_1336_;
}
else
{
lean_dec_ref(v___f_1364_);
v___y_1327_ = v___y_1358_;
v___y_1328_ = v___y_1359_;
goto v___jp_1326_;
}
}
else
{
v___y_1337_ = v___f_1362_;
v___y_1338_ = v___f_1364_;
v___y_1339_ = v___y_1359_;
v___y_1340_ = v___f_1361_;
v___y_1341_ = v___y_1358_;
goto v___jp_1336_;
}
}
v___jp_1366_:
{
lean_object* v_entries_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_entries_1374_ = lean_ctor_get(v___y_1368_, 0);
lean_inc_ref(v_entries_1374_);
lean_dec_ref(v___y_1368_);
v___x_1375_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___y_1373_, v___y_1369_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v___y_1373_);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_entries_1374_);
v___x_1378_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_1379_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v_entries_1374_);
lean_dec_ref(v___y_1370_);
v___y_1356_ = v___y_1367_;
v___y_1357_ = v___y_1371_;
v___y_1358_ = v___y_1372_;
v___y_1359_ = v___x_1375_;
goto v___jp_1355_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_le(v___x_1377_, v___x_1377_);
if (v___x_1380_ == 0)
{
if (v___x_1379_ == 0)
{
lean_dec_ref(v_entries_1374_);
lean_dec_ref(v___y_1370_);
v___y_1356_ = v___y_1367_;
v___y_1357_ = v___y_1371_;
v___y_1358_ = v___y_1372_;
v___y_1359_ = v___x_1375_;
goto v___jp_1355_;
}
else
{
size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = lean_usize_of_nat(v___x_1377_);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1378_, v___y_1370_, v_entries_1374_, v___x_1381_, v___x_1382_, v___x_1375_);
v___y_1356_ = v___y_1367_;
v___y_1357_ = v___y_1371_;
v___y_1358_ = v___y_1372_;
v___y_1359_ = v___x_1383_;
goto v___jp_1355_;
}
}
else
{
size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = lean_usize_of_nat(v___x_1377_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1378_, v___y_1370_, v_entries_1374_, v___x_1384_, v___x_1385_, v___x_1375_);
v___y_1356_ = v___y_1367_;
v___y_1357_ = v___y_1371_;
v___y_1358_ = v___y_1372_;
v___y_1359_ = v___x_1386_;
goto v___jp_1355_;
}
}
}
v___jp_1388_:
{
lean_object* v_headerSize_1395_; lean_object* v_machine_1396_; lean_object* v_machine_1397_; lean_object* v_reader_1398_; lean_object* v_state_1399_; 
v_headerSize_1395_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1391_, v_a_1305_, v___y_1389_);
v_machine_1396_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1387_, v___y_1393_, v_headerSize_1395_, v___y_1394_);
v_machine_1397_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1387_, v_machine_1396_, v_a_1305_);
lean_dec(v_a_1305_);
v_reader_1398_ = lean_ctor_get(v_machine_1397_, 0);
lean_inc_ref(v_reader_1398_);
v_state_1399_ = lean_ctor_get(v_reader_1398_, 0);
lean_inc(v_state_1399_);
lean_dec_ref(v_reader_1398_);
if (lean_obj_tag(v_state_1399_) == 7)
{
lean_dec_ref_known(v_state_1399_, 1);
v___y_1290_ = v___y_1392_;
v___y_1291_ = v_machine_1397_;
v___y_1292_ = v___y_1390_;
goto v___jp_1289_;
}
else
{
lean_dec(v_state_1399_);
v___y_1290_ = v___y_1392_;
v___y_1291_ = v_machine_1397_;
v___y_1292_ = v___y_1389_;
goto v___jp_1289_;
}
}
v___jp_1400_:
{
uint8_t v___x_1404_; lean_object* v___x_1405_; lean_object* v_indexes_1406_; lean_object* v___x_1407_; lean_object* v_machine_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___f_1411_; uint8_t v___x_1412_; 
v___x_1404_ = 1;
v___x_1405_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1404_, v_a_1305_);
v_indexes_1406_ = lean_ctor_get(v___x_1405_, 1);
lean_inc_ref(v_indexes_1406_);
lean_dec_ref(v___x_1405_);
lean_inc(v_a_1305_);
v___x_1407_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1407_, 0, v_userData_1314_);
lean_ctor_set(v___x_1407_, 1, v_outputData_1315_);
lean_ctor_set(v___x_1407_, 2, v_state_1316_);
lean_ctor_set(v___x_1407_, 3, v_knownSize_1317_);
lean_ctor_set(v___x_1407_, 4, v_a_1305_);
lean_ctor_set(v___x_1407_, 5, v_userDataBytes_1322_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*6, v___y_1402_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*6 + 1, v_userClosedBody_1320_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*6 + 2, v_omitBody_1321_);
v_machine_1408_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1408_, 0, v_reader_1306_);
lean_ctor_set(v_machine_1408_, 1, v___x_1407_);
lean_ctor_set(v_machine_1408_, 2, v_config_1307_);
lean_ctor_set(v_machine_1408_, 3, v_events_1308_);
lean_ctor_set(v_machine_1408_, 4, v_error_1309_);
lean_ctor_set(v_machine_1408_, 5, v_instant_1310_);
lean_ctor_set_uint8(v_machine_1408_, sizeof(void*)*6, v_keepAlive_1311_);
lean_ctor_set_uint8(v_machine_1408_, sizeof(void*)*6 + 1, v_forcedFlush_1312_);
lean_ctor_set_uint8(v_machine_1408_, sizeof(void*)*6 + 2, v_pullBodyStalled_1313_);
v___x_1409_ = l_Std_Http_Header_Name_contentLength;
v___f_1410_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___f_1411_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1410_, v___f_1411_, v_indexes_1406_, v___x_1409_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1410_, v___f_1411_, v_indexes_1406_, v___x_1413_);
lean_dec_ref(v_indexes_1406_);
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___x_1404_;
v___y_1392_ = v___y_1403_;
v___y_1393_ = v_machine_1408_;
v___y_1394_ = v___x_1414_;
goto v___jp_1388_;
}
else
{
lean_dec_ref(v_indexes_1406_);
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___x_1404_;
v___y_1392_ = v___y_1403_;
v___y_1393_ = v_machine_1408_;
v___y_1394_ = v___x_1412_;
goto v___jp_1388_;
}
}
v___jp_1415_:
{
lean_object* v_state_1418_; 
v_state_1418_ = lean_ctor_get(v_reader_1306_, 0);
if (lean_obj_tag(v_state_1418_) == 7)
{
v___y_1401_ = v___y_1417_;
v___y_1402_ = v___y_1416_;
v___y_1403_ = v___y_1416_;
goto v___jp_1400_;
}
else
{
v___y_1401_ = v___y_1417_;
v___y_1402_ = v___y_1416_;
v___y_1403_ = v___y_1417_;
goto v___jp_1400_;
}
}
v___jp_1419_:
{
if (v___y_1420_ == 0)
{
lean_del_object(v___x_1324_);
lean_dec(v_userDataBytes_1322_);
lean_dec(v_messageHead_1318_);
lean_dec(v_knownSize_1317_);
lean_dec(v_state_1316_);
lean_dec_ref(v_outputData_1315_);
lean_dec_ref(v_userData_1314_);
lean_dec(v_a_1305_);
v___y_1241_ = v___y_1234_;
v_omitBody_1242_ = v_omitBody_1321_;
goto v___jp_1240_;
}
else
{
lean_object* v_status_1421_; uint8_t v___x_1422_; uint16_t v___x_1423_; uint16_t v___x_1424_; uint8_t v___x_1425_; 
lean_inc(v_instant_1310_);
lean_inc(v_error_1309_);
lean_inc_ref(v_events_1308_);
lean_inc_ref(v_config_1307_);
lean_inc_ref(v_reader_1306_);
lean_dec_ref(v___y_1234_);
v_status_1421_ = lean_ctor_get(v_a_1305_, 0);
v___x_1422_ = 0;
v___x_1423_ = 100;
v___x_1424_ = l_Std_Http_Status_toCode(v_status_1421_);
v___x_1425_ = lean_uint16_dec_le(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_del_object(v___x_1324_);
lean_dec(v_messageHead_1318_);
v___y_1416_ = v___y_1420_;
v___y_1417_ = v___x_1422_;
goto v___jp_1415_;
}
else
{
uint16_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = 200;
v___x_1427_ = lean_uint16_dec_lt(v___x_1424_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_del_object(v___x_1324_);
lean_dec(v_messageHead_1318_);
v___y_1416_ = v___y_1420_;
v___y_1417_ = v___x_1422_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___f_1434_; uint8_t v___x_1435_; 
v___x_1428_ = 1;
v___x_1429_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1428_, v_a_1305_);
v___x_1430_ = l_Std_Http_Header_Name_contentLength;
v___f_1431_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___f_1432_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___x_1433_ = lean_box(v___x_1427_);
v___f_1434_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1434_, 0, v___x_1430_);
lean_closure_set(v___f_1434_, 1, v___x_1433_);
lean_closure_set(v___f_1434_, 2, v___f_1431_);
lean_closure_set(v___f_1434_, 3, v___f_1432_);
v___x_1435_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1431_, v___f_1432_, v___x_1430_, v___x_1429_);
if (v___x_1435_ == 0)
{
if (v___x_1427_ == 0)
{
v___y_1367_ = v___x_1427_;
v___y_1368_ = v___x_1429_;
v___y_1369_ = v___f_1432_;
v___y_1370_ = v___f_1434_;
v___y_1371_ = v___x_1427_;
v___y_1372_ = v___x_1428_;
v___y_1373_ = v___f_1431_;
goto v___jp_1366_;
}
else
{
lean_dec_ref(v___f_1434_);
v___y_1356_ = v___x_1427_;
v___y_1357_ = v___x_1427_;
v___y_1358_ = v___x_1428_;
v___y_1359_ = v___x_1429_;
goto v___jp_1355_;
}
}
else
{
v___y_1367_ = v___x_1427_;
v___y_1368_ = v___x_1429_;
v___y_1369_ = v___f_1432_;
v___y_1370_ = v___f_1434_;
v___y_1371_ = v___x_1427_;
v___y_1372_ = v___x_1428_;
v___y_1373_ = v___f_1431_;
goto v___jp_1366_;
}
}
}
}
}
}
}
v___jp_1240_:
{
if (v_omitBody_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v_close_1237_);
lean_dec_ref(v_isClosed_1236_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_body_1235_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1241_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
lean_inc(v_body_1235_);
v___x_1247_ = lean_apply_2(v_isClosed_1236_, v_body_1235_, lean_box(0));
v___f_1248_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1248_, 0, v___y_1241_);
lean_inc_ref(v___f_1248_);
v___f_1249_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1249_, 0, v___f_1248_);
v___f_1250_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1250_, 0, v_close_1237_);
lean_closure_set(v___f_1250_, 1, v_body_1235_);
lean_closure_set(v___f_1250_, 2, v___f_1249_);
lean_closure_set(v___f_1250_, 3, v___f_1248_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = 0;
v___x_1253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1251_, v___x_1252_, v___x_1247_, v___f_1250_);
return v___x_1253_;
}
}
v___jp_1254_:
{
lean_object* v_writer_1256_; lean_object* v_reader_1257_; lean_object* v_config_1258_; lean_object* v_events_1259_; lean_object* v_error_1260_; lean_object* v_instant_1261_; uint8_t v_keepAlive_1262_; uint8_t v_forcedFlush_1263_; uint8_t v_pullBodyStalled_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1288_; 
v_writer_1256_ = lean_ctor_get(v___y_1255_, 1);
v_reader_1257_ = lean_ctor_get(v___y_1255_, 0);
v_config_1258_ = lean_ctor_get(v___y_1255_, 2);
v_events_1259_ = lean_ctor_get(v___y_1255_, 3);
v_error_1260_ = lean_ctor_get(v___y_1255_, 4);
v_instant_1261_ = lean_ctor_get(v___y_1255_, 5);
v_keepAlive_1262_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*6);
v_forcedFlush_1263_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1264_ = lean_ctor_get_uint8(v___y_1255_, sizeof(void*)*6 + 2);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___y_1255_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1266_ = v___y_1255_;
v_isShared_1267_ = v_isSharedCheck_1288_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_instant_1261_);
lean_inc(v_error_1260_);
lean_inc(v_events_1259_);
lean_inc(v_config_1258_);
lean_inc(v_writer_1256_);
lean_inc(v_reader_1257_);
lean_dec(v___y_1255_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1288_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_userData_1268_; lean_object* v_outputData_1269_; lean_object* v_knownSize_1270_; lean_object* v_messageHead_1271_; uint8_t v_sentMessage_1272_; uint8_t v_userClosedBody_1273_; uint8_t v_omitBody_1274_; lean_object* v_userDataBytes_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1286_; 
v_userData_1268_ = lean_ctor_get(v_writer_1256_, 0);
v_outputData_1269_ = lean_ctor_get(v_writer_1256_, 1);
v_knownSize_1270_ = lean_ctor_get(v_writer_1256_, 3);
v_messageHead_1271_ = lean_ctor_get(v_writer_1256_, 4);
v_sentMessage_1272_ = lean_ctor_get_uint8(v_writer_1256_, sizeof(void*)*6);
v_userClosedBody_1273_ = lean_ctor_get_uint8(v_writer_1256_, sizeof(void*)*6 + 1);
v_omitBody_1274_ = lean_ctor_get_uint8(v_writer_1256_, sizeof(void*)*6 + 2);
v_userDataBytes_1275_ = lean_ctor_get(v_writer_1256_, 5);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_writer_1256_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v_writer_1256_, 2);
lean_dec(v_unused_1287_);
v___x_1277_ = v_writer_1256_;
v_isShared_1278_ = v_isSharedCheck_1286_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_userDataBytes_1275_);
lean_inc(v_messageHead_1271_);
lean_inc(v_knownSize_1270_);
lean_inc(v_outputData_1269_);
lean_inc(v_userData_1268_);
lean_dec(v_writer_1256_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1286_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_box(2);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 2, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_userData_1268_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_outputData_1269_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_knownSize_1270_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_messageHead_1271_);
lean_ctor_set(v_reuseFailAlloc_1285_, 5, v_userDataBytes_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*6, v_sentMessage_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*6 + 1, v_userClosedBody_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*6 + 2, v_omitBody_1274_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1281_);
v___x_1283_ = v___x_1266_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_reader_1257_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_config_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_events_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_error_1260_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_instant_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*6, v_keepAlive_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*6 + 1, v_forcedFlush_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*6 + 2, v_pullBodyStalled_1264_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v___y_1241_ = v___x_1283_;
v_omitBody_1242_ = v_omitBody_1274_;
goto v___jp_1240_;
}
}
}
}
}
v___jp_1289_:
{
if (v___y_1292_ == 0)
{
v___y_1255_ = v___y_1291_;
goto v___jp_1254_;
}
else
{
if (v___y_1290_ == 0)
{
lean_object* v_writer_1293_; uint8_t v_omitBody_1294_; 
v_writer_1293_ = lean_ctor_get(v___y_1291_, 1);
v_omitBody_1294_ = lean_ctor_get_uint8(v_writer_1293_, sizeof(void*)*6 + 2);
v___y_1241_ = v___y_1291_;
v_omitBody_1242_ = v_omitBody_1294_;
goto v___jp_1240_;
}
else
{
v___y_1255_ = v___y_1291_;
goto v___jp_1254_;
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
v___x_1577_ = lean_st_ref_set(v___y_1563_, v___x_1576_);
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
lean_object* v_machine_1724_; lean_object* v_requestStream_1725_; lean_object* v_keepAliveTimeout_1726_; lean_object* v_currentTimeout_1727_; lean_object* v_headerTimeout_1728_; lean_object* v_response_1729_; lean_object* v_respStream_1730_; lean_object* v_expectData_1731_; uint8_t v_handlerDispatched_1732_; lean_object* v___x_1733_; lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_4933__overap_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; 
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
v___x_4933__overap_1738_ = l_Std_Mutex_atomically___redArg(v___x_1733_, v___f_1734_, v___f_1735_, v_requestStream_1725_, v___x_1737_);
v___x_1739_ = lean_apply_1(v___x_4933__overap_1738_, lean_box(0));
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
lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___f_2068_; lean_object* v___x_5126__overap_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___f_2065_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2065_, 0, v___x_2064_);
v___x_2066_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2067_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2068_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5126__overap_2069_ = l_Std_Mutex_atomically___redArg(v___x_2066_, v___f_2067_, v___f_2068_, v_requestStream_2047_, v___f_2065_);
v___x_2070_ = lean_apply_1(v___x_5126__overap_2069_, lean_box(0));
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
lean_object* v_requestStream_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_5182__overap_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
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
v___x_5182__overap_2144_ = l_Std_Mutex_atomically___redArg(v___x_2139_, v___f_2140_, v___f_2141_, v_requestStream_2138_, v___x_2143_);
v___x_2145_ = lean_apply_1(v___x_5182__overap_2144_, lean_box(0));
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
lean_object* v_machine_2151_; lean_object* v_requestStream_2152_; lean_object* v_respStream_2153_; uint8_t v_requiresData_2154_; lean_object* v_expectData_2155_; lean_object* v_pendingHead_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_5203__overap_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
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
v___x_5203__overap_2162_ = l_Std_Mutex_atomically___redArg(v___x_2157_, v___f_2158_, v___f_2159_, v_requestStream_2152_, v___x_2161_);
v___x_2163_ = lean_apply_1(v___x_5203__overap_2162_, lean_box(0));
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
lean_object* v___f_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; size_t v_sz_2231_; size_t v___x_2232_; lean_object* v___x_4114__overap_2233_; lean_object* v___x_2234_; lean_object* v___f_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; 
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
v___x_4114__overap_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2230_, v_events_2225_, v___f_2229_, v_sz_2231_, v___x_2232_, v_state_2226_);
v___x_2234_ = lean_apply_1(v___x_4114__overap_2233_, lean_box(0));
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
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2564_; 
v_a_2497_ = lean_ctor_get(v_x_2480_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2499_ = v_x_2480_;
v_isShared_2500_ = v_isSharedCheck_2564_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v_x_2480_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2564_;
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
lean_object* v_reader_2519_; lean_object* v_writer_2520_; lean_object* v_config_2521_; lean_object* v_events_2522_; lean_object* v_error_2523_; lean_object* v_instant_2524_; uint8_t v_keepAlive_2525_; uint8_t v_forcedFlush_2526_; uint8_t v_pullBodyStalled_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2563_; 
v_reader_2519_ = lean_ctor_get(v_machine_2476_, 0);
v_writer_2520_ = lean_ctor_get(v_machine_2476_, 1);
v_config_2521_ = lean_ctor_get(v_machine_2476_, 2);
v_events_2522_ = lean_ctor_get(v_machine_2476_, 3);
v_error_2523_ = lean_ctor_get(v_machine_2476_, 4);
v_instant_2524_ = lean_ctor_get(v_machine_2476_, 5);
v_keepAlive_2525_ = lean_ctor_get_uint8(v_machine_2476_, sizeof(void*)*6);
v_forcedFlush_2526_ = lean_ctor_get_uint8(v_machine_2476_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2527_ = lean_ctor_get_uint8(v_machine_2476_, sizeof(void*)*6 + 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_machine_2476_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2529_ = v_machine_2476_;
v_isShared_2530_ = v_isSharedCheck_2563_;
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
v_isShared_2530_ = v_isSharedCheck_2563_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___y_2532_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_2555_ = lean_nat_dec_lt(v___x_2517_, v___x_2516_);
if (v___x_2555_ == 0)
{
lean_dec_ref(v___f_2479_);
v___y_2532_ = v___x_2517_;
goto v___jp_2531_;
}
else
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_nat_dec_le(v___x_2516_, v___x_2516_);
if (v___x_2556_ == 0)
{
if (v___x_2555_ == 0)
{
lean_dec_ref(v___f_2479_);
v___y_2532_ = v___x_2517_;
goto v___jp_2531_;
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2554_, v___f_2479_, v___x_2515_, v___x_2557_, v___x_2558_, v___x_2517_);
v___y_2532_ = v___x_2559_;
goto v___jp_2531_;
}
}
else
{
size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = lean_usize_of_nat(v___x_2516_);
lean_inc_ref(v___x_2515_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2554_, v___f_2479_, v___x_2515_, v___x_2560_, v___x_2561_, v___x_2517_);
v___y_2532_ = v___x_2562_;
goto v___jp_2531_;
}
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2565_, lean_object* v_machine_2566_, lean_object* v_isClosed_2567_, lean_object* v___f_2568_, lean_object* v___f_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2565_, v_machine_2566_, v_isClosed_2567_, v___f_2568_, v___f_2569_, v_x_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2574_, lean_object* v_machine_2575_, lean_object* v_body_2576_){
_start:
{
lean_object* v_close_2578_; lean_object* v_isClosed_2579_; lean_object* v_tryRecv_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___f_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; 
v_close_2578_ = lean_ctor_get(v_inst_2574_, 1);
lean_inc_ref(v_close_2578_);
v_isClosed_2579_ = lean_ctor_get(v_inst_2574_, 2);
lean_inc_ref(v_isClosed_2579_);
v_tryRecv_2580_ = lean_ctor_get(v_inst_2574_, 4);
lean_inc_ref(v_tryRecv_2580_);
lean_dec_ref(v_inst_2574_);
lean_inc_n(v_body_2576_, 2);
v___x_2581_ = lean_apply_2(v_tryRecv_2580_, v_body_2576_, lean_box(0));
lean_inc_ref(v_machine_2575_);
v___f_2582_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2582_, 0, v_machine_2575_);
lean_inc_ref(v___f_2582_);
v___f_2583_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2583_, 0, v___f_2582_);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2584_, 0, v_close_2578_);
lean_closure_set(v___f_2584_, 1, v_body_2576_);
lean_closure_set(v___f_2584_, 2, v___f_2583_);
lean_closure_set(v___f_2584_, 3, v___f_2582_);
v___f_2585_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2586_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2586_, 0, v_body_2576_);
lean_closure_set(v___f_2586_, 1, v_machine_2575_);
lean_closure_set(v___f_2586_, 2, v_isClosed_2579_);
lean_closure_set(v___f_2586_, 3, v___f_2584_);
lean_closure_set(v___f_2586_, 4, v___f_2585_);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = 0;
v___x_2589_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2587_, v___x_2588_, v___x_2581_, v___f_2586_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2590_, lean_object* v_machine_2591_, lean_object* v_body_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2590_, v_machine_2591_, v_body_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2595_, lean_object* v_inst_2596_, lean_object* v_machine_2597_, lean_object* v_body_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2596_, v_machine_2597_, v_body_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2601_, lean_object* v_inst_2602_, lean_object* v_machine_2603_, lean_object* v_body_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2601_, v_inst_2602_, v_machine_2603_, v_body_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2613_, lean_object* v_____r_2614_, lean_object* v_st_2615_){
_start:
{
lean_object* v_machine_2617_; lean_object* v_requestStream_2618_; lean_object* v_keepAliveTimeout_2619_; lean_object* v_currentTimeout_2620_; lean_object* v_headerTimeout_2621_; lean_object* v_response_2622_; lean_object* v_respStream_2623_; uint8_t v_requiresData_2624_; lean_object* v_expectData_2625_; uint8_t v_handlerDispatched_2626_; lean_object* v_pendingHead_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2709_; 
v_machine_2617_ = lean_ctor_get(v_st_2615_, 0);
v_requestStream_2618_ = lean_ctor_get(v_st_2615_, 1);
v_keepAliveTimeout_2619_ = lean_ctor_get(v_st_2615_, 2);
v_currentTimeout_2620_ = lean_ctor_get(v_st_2615_, 3);
v_headerTimeout_2621_ = lean_ctor_get(v_st_2615_, 4);
v_response_2622_ = lean_ctor_get(v_st_2615_, 5);
v_respStream_2623_ = lean_ctor_get(v_st_2615_, 6);
v_requiresData_2624_ = lean_ctor_get_uint8(v_st_2615_, sizeof(void*)*9);
v_expectData_2625_ = lean_ctor_get(v_st_2615_, 7);
v_handlerDispatched_2626_ = lean_ctor_get_uint8(v_st_2615_, sizeof(void*)*9 + 1);
v_pendingHead_2627_ = lean_ctor_get(v_st_2615_, 8);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_st_2615_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2629_ = v_st_2615_;
v_isShared_2630_ = v_isSharedCheck_2709_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_pendingHead_2627_);
lean_inc(v_expectData_2625_);
lean_inc(v_respStream_2623_);
lean_inc(v_response_2622_);
lean_inc(v_headerTimeout_2621_);
lean_inc(v_currentTimeout_2620_);
lean_inc(v_keepAliveTimeout_2619_);
lean_inc(v_requestStream_2618_);
lean_inc(v_machine_2617_);
lean_dec(v_st_2615_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2709_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___y_2632_; lean_object* v_reader_2641_; lean_object* v_state_2642_; 
v_reader_2641_ = lean_ctor_get(v_machine_2617_, 0);
lean_inc_ref(v_reader_2641_);
v_state_2642_ = lean_ctor_get(v_reader_2641_, 0);
lean_inc(v_state_2642_);
if (lean_obj_tag(v_state_2642_) == 6)
{
lean_dec_ref(v_reader_2641_);
lean_dec_ref(v_val_2613_);
v___y_2632_ = v_machine_2617_;
goto v___jp_2631_;
}
else
{
if (lean_obj_tag(v_state_2642_) == 7)
{
lean_dec_ref_known(v_state_2642_, 1);
lean_dec_ref(v_reader_2641_);
lean_dec_ref(v_val_2613_);
v___y_2632_ = v_machine_2617_;
goto v___jp_2631_;
}
else
{
lean_object* v_input_2643_; lean_object* v_writer_2644_; lean_object* v_config_2645_; lean_object* v_events_2646_; lean_object* v_error_2647_; lean_object* v_instant_2648_; uint8_t v_keepAlive_2649_; uint8_t v_forcedFlush_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2707_; 
v_input_2643_ = lean_ctor_get(v_reader_2641_, 1);
lean_inc_ref(v_input_2643_);
v_writer_2644_ = lean_ctor_get(v_machine_2617_, 1);
v_config_2645_ = lean_ctor_get(v_machine_2617_, 2);
v_events_2646_ = lean_ctor_get(v_machine_2617_, 3);
v_error_2647_ = lean_ctor_get(v_machine_2617_, 4);
v_instant_2648_ = lean_ctor_get(v_machine_2617_, 5);
v_keepAlive_2649_ = lean_ctor_get_uint8(v_machine_2617_, sizeof(void*)*6);
v_forcedFlush_2650_ = lean_ctor_get_uint8(v_machine_2617_, sizeof(void*)*6 + 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_machine_2617_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v_machine_2617_, 0);
lean_dec(v_unused_2708_);
v___x_2652_ = v_machine_2617_;
v_isShared_2653_ = v_isSharedCheck_2707_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_instant_2648_);
lean_inc(v_error_2647_);
lean_inc(v_events_2646_);
lean_inc(v_config_2645_);
lean_inc(v_writer_2644_);
lean_dec(v_machine_2617_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2707_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_messageHead_2654_; lean_object* v_messageCount_2655_; lean_object* v_bodyBytesRead_2656_; lean_object* v_headerBytesRead_2657_; uint8_t v_noMoreInput_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2704_; 
v_messageHead_2654_ = lean_ctor_get(v_reader_2641_, 2);
v_messageCount_2655_ = lean_ctor_get(v_reader_2641_, 3);
v_bodyBytesRead_2656_ = lean_ctor_get(v_reader_2641_, 4);
v_headerBytesRead_2657_ = lean_ctor_get(v_reader_2641_, 5);
v_noMoreInput_2658_ = lean_ctor_get_uint8(v_reader_2641_, sizeof(void*)*6);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_reader_2641_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2705_ = lean_ctor_get(v_reader_2641_, 1);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_reader_2641_, 0);
lean_dec(v_unused_2706_);
v___x_2660_ = v_reader_2641_;
v_isShared_2661_ = v_isSharedCheck_2704_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_headerBytesRead_2657_);
lean_inc(v_bodyBytesRead_2656_);
lean_inc(v_messageCount_2655_);
lean_inc(v_messageHead_2654_);
lean_dec(v_reader_2641_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2704_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_array_2662_; lean_object* v_idx_2663_; uint8_t v___x_2664_; lean_object* v___y_2666_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v_array_2662_ = lean_ctor_get(v_input_2643_, 0);
lean_inc_ref(v_array_2662_);
v_idx_2663_ = lean_ctor_get(v_input_2643_, 1);
lean_inc(v_idx_2663_);
lean_dec_ref(v_input_2643_);
v___x_2664_ = 0;
v___x_2695_ = lean_byte_array_size(v_array_2662_);
v___x_2696_ = lean_nat_dec_le(v___x_2695_, v_idx_2663_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = l_ByteArray_extract(v_array_2662_, v_idx_2663_, v___x_2695_);
lean_dec_ref(v_array_2662_);
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = lean_byte_array_size(v___x_2697_);
v___x_2700_ = lean_byte_array_size(v_val_2613_);
v___x_2701_ = lean_byte_array_copy_slice(v_val_2613_, v___x_2698_, v___x_2697_, v___x_2699_, v___x_2700_, v___x_2696_);
lean_dec_ref(v_val_2613_);
v___x_2702_ = l_ByteArray_mkIterator(v___x_2701_);
v___y_2666_ = v___x_2702_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2703_; 
lean_dec(v_idx_2663_);
lean_dec_ref(v_array_2662_);
v___x_2703_ = l_ByteArray_mkIterator(v_val_2613_);
v___y_2666_ = v___x_2703_;
goto v___jp_2665_;
}
v___jp_2665_:
{
lean_object* v_maxHeaderBytes_2667_; lean_object* v_maxStartLineLength_2668_; lean_object* v_maxChunkLineLength_2669_; lean_object* v_maxBodySize_2670_; lean_object* v_array_2671_; lean_object* v_idx_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_maxHeaderBytes_2667_ = lean_ctor_get(v_config_2645_, 2);
v_maxStartLineLength_2668_ = lean_ctor_get(v_config_2645_, 5);
v_maxChunkLineLength_2669_ = lean_ctor_get(v_config_2645_, 13);
v_maxBodySize_2670_ = lean_ctor_get(v_config_2645_, 15);
v_array_2671_ = lean_ctor_get(v___y_2666_, 0);
v_idx_2672_ = lean_ctor_get(v___y_2666_, 1);
v___x_2673_ = lean_nat_add(v_maxBodySize_2670_, v_maxHeaderBytes_2667_);
v___x_2674_ = lean_nat_add(v___x_2673_, v_maxStartLineLength_2668_);
lean_dec(v___x_2673_);
v___x_2675_ = lean_nat_add(v___x_2674_, v_maxChunkLineLength_2669_);
lean_dec(v___x_2674_);
v___x_2676_ = lean_byte_array_size(v_array_2671_);
v___x_2677_ = lean_nat_sub(v___x_2676_, v_idx_2672_);
v___x_2678_ = lean_nat_dec_lt(v___x_2675_, v___x_2677_);
lean_dec(v___x_2677_);
lean_dec(v___x_2675_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2680_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___y_2666_);
v___x_2680_ = v___x_2660_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_state_2642_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___y_2666_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_messageHead_2654_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_messageCount_2655_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_bodyBytesRead_2656_);
lean_ctor_set(v_reuseFailAlloc_2684_, 5, v_headerBytesRead_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2684_, sizeof(void*)*6, v_noMoreInput_2658_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v_machine_2682_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2680_);
v_machine_2682_ = v___x_2652_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_writer_2644_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_config_2645_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_events_2646_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_error_2647_);
lean_ctor_set(v_reuseFailAlloc_2683_, 5, v_instant_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2683_, sizeof(void*)*6, v_keepAlive_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2683_, sizeof(void*)*6 + 1, v_forcedFlush_2650_);
v_machine_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_ctor_set_uint8(v_machine_2682_, sizeof(void*)*6 + 2, v___x_2664_);
v___y_2632_ = v_machine_2682_;
goto v___jp_2631_;
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec(v_error_2647_);
lean_dec(v_state_2642_);
v___x_2685_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2686_ = lean_array_push(v_events_2646_, v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___y_2666_);
lean_ctor_set(v___x_2660_, 0, v___x_2687_);
v___x_2689_ = v___x_2660_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___y_2666_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_messageHead_2654_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_messageCount_2655_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v_bodyBytesRead_2656_);
lean_ctor_set(v_reuseFailAlloc_2694_, 5, v_headerBytesRead_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2694_, sizeof(void*)*6, v_noMoreInput_2658_);
v___x_2689_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 4, v___x_2690_);
lean_ctor_set(v___x_2652_, 3, v___x_2686_);
lean_ctor_set(v___x_2652_, 0, v___x_2689_);
v___x_2692_ = v___x_2652_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_writer_2644_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_config_2645_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2693_, 5, v_instant_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2693_, sizeof(void*)*6, v_keepAlive_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2693_, sizeof(void*)*6 + 1, v_forcedFlush_2650_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*6 + 2, v___x_2664_);
v___y_2632_ = v___x_2692_;
goto v___jp_2631_;
}
}
}
}
}
}
}
}
v___jp_2631_:
{
lean_object* v___x_2634_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___y_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___y_2632_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_requestStream_2618_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_keepAliveTimeout_2619_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_currentTimeout_2620_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_headerTimeout_2621_);
lean_ctor_set(v_reuseFailAlloc_2640_, 5, v_response_2622_);
lean_ctor_set(v_reuseFailAlloc_2640_, 6, v_respStream_2623_);
lean_ctor_set(v_reuseFailAlloc_2640_, 7, v_expectData_2625_);
lean_ctor_set(v_reuseFailAlloc_2640_, 8, v_pendingHead_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, sizeof(void*)*9, v_requiresData_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, sizeof(void*)*9 + 1, v_handlerDispatched_2626_);
v___x_2634_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2635_ = 0;
v___x_2636_ = lean_box(v___x_2635_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2634_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2710_, lean_object* v_____r_2711_, lean_object* v_st_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2710_, v_____r_2711_, v_st_2712_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2715_, lean_object* v_machine_2716_, lean_object* v_requestStream_2717_, lean_object* v_currentTimeout_2718_, lean_object* v_response_2719_, lean_object* v_respStream_2720_, uint8_t v_requiresData_2721_, lean_object* v_expectData_2722_, uint8_t v_handlerDispatched_2723_, lean_object* v_pendingHead_2724_, lean_object* v___f_2725_, lean_object* v_x_2726_){
_start:
{
if (lean_obj_tag(v_x_2726_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v___f_2725_);
lean_dec(v_pendingHead_2724_);
lean_dec(v_expectData_2722_);
lean_dec(v_respStream_2720_);
lean_dec_ref(v_response_2719_);
lean_dec(v_currentTimeout_2718_);
lean_dec_ref(v_requestStream_2717_);
lean_dec_ref(v_machine_2716_);
v_a_2728_ = lean_ctor_get(v_x_2726_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_x_2726_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2730_ = v_x_2726_;
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v_x_2726_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2728_);
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
else
{
lean_object* v_a_2737_; lean_object* v_headerTimeout_2738_; lean_object* v_second_2739_; lean_object* v_nano_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_second_2744_; lean_object* v_nano_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_a_2737_ = lean_ctor_get(v_x_2726_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v_x_2726_, 1);
v_headerTimeout_2738_ = lean_ctor_get(v_config_2715_, 6);
v_second_2739_ = lean_ctor_get(v_a_2737_, 0);
lean_inc(v_second_2739_);
v_nano_2740_ = lean_ctor_get(v_a_2737_, 1);
lean_inc(v_nano_2740_);
lean_dec(v_a_2737_);
v___x_2741_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2742_ = lean_int_mul(v_headerTimeout_2738_, v___x_2741_);
v___x_2743_ = l_Std_Time_Duration_ofNanoseconds(v___x_2742_);
lean_dec(v___x_2742_);
v_second_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_second_2744_);
v_nano_2745_ = lean_ctor_get(v___x_2743_, 1);
lean_inc(v_nano_2745_);
lean_dec_ref(v___x_2743_);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2748_ = lean_int_mul(v_second_2739_, v___x_2747_);
lean_dec(v_second_2739_);
v___x_2749_ = lean_int_add(v___x_2748_, v_nano_2740_);
lean_dec(v_nano_2740_);
lean_dec(v___x_2748_);
v___x_2750_ = lean_int_mul(v_second_2744_, v___x_2747_);
lean_dec(v_second_2744_);
v___x_2751_ = lean_int_add(v___x_2750_, v_nano_2745_);
lean_dec(v_nano_2745_);
lean_dec(v___x_2750_);
v___x_2752_ = lean_int_add(v___x_2749_, v___x_2751_);
lean_dec(v___x_2751_);
lean_dec(v___x_2749_);
v___x_2753_ = l_Std_Time_Duration_ofNanoseconds(v___x_2752_);
lean_dec(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2755_, 0, v_machine_2716_);
lean_ctor_set(v___x_2755_, 1, v_requestStream_2717_);
lean_ctor_set(v___x_2755_, 2, v___x_2746_);
lean_ctor_set(v___x_2755_, 3, v_currentTimeout_2718_);
lean_ctor_set(v___x_2755_, 4, v___x_2754_);
lean_ctor_set(v___x_2755_, 5, v_response_2719_);
lean_ctor_set(v___x_2755_, 6, v_respStream_2720_);
lean_ctor_set(v___x_2755_, 7, v_expectData_2722_);
lean_ctor_set(v___x_2755_, 8, v_pendingHead_2724_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*9, v_requiresData_2721_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*9 + 1, v_handlerDispatched_2723_);
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_apply_3(v___f_2725_, v___x_2756_, v___x_2755_, lean_box(0));
return v___x_2757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2758_, lean_object* v_machine_2759_, lean_object* v_requestStream_2760_, lean_object* v_currentTimeout_2761_, lean_object* v_response_2762_, lean_object* v_respStream_2763_, lean_object* v_requiresData_2764_, lean_object* v_expectData_2765_, lean_object* v_handlerDispatched_2766_, lean_object* v_pendingHead_2767_, lean_object* v___f_2768_, lean_object* v_x_2769_, lean_object* v___y_2770_){
_start:
{
uint8_t v_requiresData_boxed_2771_; uint8_t v_handlerDispatched_boxed_2772_; lean_object* v_res_2773_; 
v_requiresData_boxed_2771_ = lean_unbox(v_requiresData_2764_);
v_handlerDispatched_boxed_2772_ = lean_unbox(v_handlerDispatched_2766_);
v_res_2773_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2758_, v_machine_2759_, v_requestStream_2760_, v_currentTimeout_2761_, v_response_2762_, v_respStream_2763_, v_requiresData_boxed_2771_, v_expectData_2765_, v_handlerDispatched_boxed_2772_, v_pendingHead_2767_, v___f_2768_, v_x_2769_);
lean_dec_ref(v_config_2758_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2774_, lean_object* v_requestStream_2775_, lean_object* v_keepAliveTimeout_2776_, lean_object* v_currentTimeout_2777_, lean_object* v_headerTimeout_2778_, lean_object* v_response_2779_, uint8_t v_requiresData_2780_, lean_object* v_expectData_2781_, uint8_t v_handlerDispatched_2782_, lean_object* v_pendingHead_2783_, lean_object* v_____r_2784_){
_start:
{
lean_object* v_writer_2786_; lean_object* v_reader_2787_; lean_object* v_config_2788_; lean_object* v_events_2789_; lean_object* v_error_2790_; lean_object* v_instant_2791_; uint8_t v_keepAlive_2792_; uint8_t v_forcedFlush_2793_; uint8_t v_pullBodyStalled_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2824_; 
v_writer_2786_ = lean_ctor_get(v_machine_2774_, 1);
v_reader_2787_ = lean_ctor_get(v_machine_2774_, 0);
v_config_2788_ = lean_ctor_get(v_machine_2774_, 2);
v_events_2789_ = lean_ctor_get(v_machine_2774_, 3);
v_error_2790_ = lean_ctor_get(v_machine_2774_, 4);
v_instant_2791_ = lean_ctor_get(v_machine_2774_, 5);
v_keepAlive_2792_ = lean_ctor_get_uint8(v_machine_2774_, sizeof(void*)*6);
v_forcedFlush_2793_ = lean_ctor_get_uint8(v_machine_2774_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2794_ = lean_ctor_get_uint8(v_machine_2774_, sizeof(void*)*6 + 2);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_machine_2774_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2796_ = v_machine_2774_;
v_isShared_2797_ = v_isSharedCheck_2824_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_instant_2791_);
lean_inc(v_error_2790_);
lean_inc(v_events_2789_);
lean_inc(v_config_2788_);
lean_inc(v_writer_2786_);
lean_inc(v_reader_2787_);
lean_dec(v_machine_2774_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2824_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v_userData_2798_; lean_object* v_outputData_2799_; lean_object* v_state_2800_; lean_object* v_knownSize_2801_; lean_object* v_messageHead_2802_; uint8_t v_sentMessage_2803_; uint8_t v_omitBody_2804_; lean_object* v_userDataBytes_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2823_; 
v_userData_2798_ = lean_ctor_get(v_writer_2786_, 0);
v_outputData_2799_ = lean_ctor_get(v_writer_2786_, 1);
v_state_2800_ = lean_ctor_get(v_writer_2786_, 2);
v_knownSize_2801_ = lean_ctor_get(v_writer_2786_, 3);
v_messageHead_2802_ = lean_ctor_get(v_writer_2786_, 4);
v_sentMessage_2803_ = lean_ctor_get_uint8(v_writer_2786_, sizeof(void*)*6);
v_omitBody_2804_ = lean_ctor_get_uint8(v_writer_2786_, sizeof(void*)*6 + 2);
v_userDataBytes_2805_ = lean_ctor_get(v_writer_2786_, 5);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_writer_2786_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2807_ = v_writer_2786_;
v_isShared_2808_ = v_isSharedCheck_2823_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_userDataBytes_2805_);
lean_inc(v_messageHead_2802_);
lean_inc(v_knownSize_2801_);
lean_inc(v_state_2800_);
lean_inc(v_outputData_2799_);
lean_inc(v_userData_2798_);
lean_dec(v_writer_2786_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2823_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
uint8_t v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = 1;
if (v_isShared_2808_ == 0)
{
v___x_2811_ = v___x_2807_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_userData_2798_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_outputData_2799_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_state_2800_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_knownSize_2801_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_messageHead_2802_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_userDataBytes_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*6, v_sentMessage_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*6 + 2, v_omitBody_2804_);
v___x_2811_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*6 + 1, v___x_2809_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2811_);
v___x_2813_ = v___x_2796_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_reader_2787_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_config_2788_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v_events_2789_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v_error_2790_);
lean_ctor_set(v_reuseFailAlloc_2821_, 5, v_instant_2791_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*6, v_keepAlive_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*6 + 1, v_forcedFlush_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*6 + 2, v_pullBodyStalled_2794_);
v___x_2813_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2814_ = lean_box(0);
v___x_2815_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v_requestStream_2775_);
lean_ctor_set(v___x_2815_, 2, v_keepAliveTimeout_2776_);
lean_ctor_set(v___x_2815_, 3, v_currentTimeout_2777_);
lean_ctor_set(v___x_2815_, 4, v_headerTimeout_2778_);
lean_ctor_set(v___x_2815_, 5, v_response_2779_);
lean_ctor_set(v___x_2815_, 6, v___x_2814_);
lean_ctor_set(v___x_2815_, 7, v_expectData_2781_);
lean_ctor_set(v___x_2815_, 8, v_pendingHead_2783_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*9, v_requiresData_2780_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*9 + 1, v_handlerDispatched_2782_);
v___x_2816_ = 0;
v___x_2817_ = lean_box(v___x_2816_);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2815_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2825_, lean_object* v_requestStream_2826_, lean_object* v_keepAliveTimeout_2827_, lean_object* v_currentTimeout_2828_, lean_object* v_headerTimeout_2829_, lean_object* v_response_2830_, lean_object* v_requiresData_2831_, lean_object* v_expectData_2832_, lean_object* v_handlerDispatched_2833_, lean_object* v_pendingHead_2834_, lean_object* v_____r_2835_, lean_object* v___y_2836_){
_start:
{
uint8_t v_requiresData_boxed_2837_; uint8_t v_handlerDispatched_boxed_2838_; lean_object* v_res_2839_; 
v_requiresData_boxed_2837_ = lean_unbox(v_requiresData_2831_);
v_handlerDispatched_boxed_2838_ = lean_unbox(v_handlerDispatched_2833_);
v_res_2839_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2825_, v_requestStream_2826_, v_keepAliveTimeout_2827_, v_currentTimeout_2828_, v_headerTimeout_2829_, v_response_2830_, v_requiresData_boxed_2837_, v_expectData_2832_, v_handlerDispatched_boxed_2838_, v_pendingHead_2834_, v_____r_2835_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2840_, lean_object* v_x_2841_){
_start:
{
if (lean_obj_tag(v_x_2841_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v___f_2840_);
v_a_2843_ = lean_ctor_get(v_x_2841_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_x_2841_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2845_ = v_x_2841_;
v_isShared_2846_ = v_isSharedCheck_2851_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v_x_2841_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2851_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2853_; 
v_a_2852_ = lean_ctor_get(v_x_2841_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v_x_2841_, 1);
v___x_2853_ = lean_apply_2(v___f_2840_, v_a_2852_, lean_box(0));
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2854_, lean_object* v_x_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2854_, v_x_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2858_, lean_object* v_val_2859_, lean_object* v___f_2860_, lean_object* v___f_2861_, lean_object* v_x_2862_){
_start:
{
if (lean_obj_tag(v_x_2862_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2872_; 
lean_dec_ref(v___f_2861_);
lean_dec_ref(v___f_2860_);
lean_dec(v_val_2859_);
lean_dec_ref(v_close_2858_);
v_a_2864_ = lean_ctor_get(v_x_2862_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2866_ = v_x_2862_;
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v_x_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2873_; uint8_t v___x_2874_; 
v_a_2873_ = lean_ctor_get(v_x_2862_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v_x_2862_, 1);
v___x_2874_ = lean_unbox(v_a_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; 
lean_dec_ref(v___f_2861_);
v___x_2875_ = lean_apply_2(v_close_2858_, v_val_2859_, lean_box(0));
v___x_2876_ = lean_unsigned_to_nat(0u);
v___x_2877_ = lean_unbox(v_a_2873_);
lean_dec(v_a_2873_);
v___x_2878_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2876_, v___x_2877_, v___x_2875_, v___f_2860_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_dec(v_a_2873_);
lean_dec_ref(v___f_2860_);
lean_dec(v_val_2859_);
lean_dec_ref(v_close_2858_);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_apply_2(v___f_2861_, v___x_2879_, lean_box(0));
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2881_, lean_object* v_val_2882_, lean_object* v___f_2883_, lean_object* v___f_2884_, lean_object* v_x_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2881_, v_val_2882_, v___f_2883_, v___f_2884_, v_x_2885_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2888_, lean_object* v_handler_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2890_) == 0)
{
lean_object* v_a_2892_; lean_object* v_onFailure_2893_; lean_object* v___x_2894_; 
v_a_2892_ = lean_ctor_get(v_x_2890_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v_x_2890_, 1);
v_onFailure_2893_ = lean_ctor_get(v_inst_2888_, 2);
lean_inc_ref(v_onFailure_2893_);
lean_dec_ref(v_inst_2888_);
v___x_2894_ = lean_apply_3(v_onFailure_2893_, v_handler_2889_, v_a_2892_, lean_box(0));
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; 
lean_dec(v_handler_2889_);
lean_dec_ref(v_inst_2888_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_x_2890_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2896_, lean_object* v_handler_2897_, lean_object* v_x_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2896_, v_handler_2897_, v_x_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2901_, lean_object* v_____r_2902_){
_start:
{
uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2904_ = 0;
v___x_2905_ = lean_box(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v_st_2901_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2909_, lean_object* v_____r_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2909_, v_____r_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2913_, lean_object* v___f_2914_, lean_object* v___f_2915_, lean_object* v_x_2916_){
_start:
{
if (lean_obj_tag(v_x_2916_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v___f_2915_);
lean_dec_ref(v___f_2914_);
lean_dec_ref(v_requestStream_2913_);
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
lean_dec_ref_known(v_x_2916_, 1);
v___x_2928_ = lean_unbox(v_a_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; 
lean_dec_ref(v___f_2915_);
v___x_2929_ = l_Std_Http_Body_Stream_close(v_requestStream_2913_);
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
lean_dec_ref(v_requestStream_2913_);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_apply_2(v___f_2915_, v___x_2933_, lean_box(0));
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2935_, lean_object* v___f_2936_, lean_object* v___f_2937_, lean_object* v_x_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2935_, v___f_2936_, v___f_2937_, v_x_2938_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_2941_, lean_object* v___f_2942_, lean_object* v___f_2943_, lean_object* v_requestStream_2944_, lean_object* v___f_2945_, lean_object* v_x_2946_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v___f_2945_);
lean_dec_ref(v_requestStream_2944_);
lean_dec_ref(v___f_2943_);
lean_dec_ref(v___f_2942_);
v_a_2948_ = lean_ctor_get(v_x_2946_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2950_ = v_x_2946_;
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v_x_2946_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
}
else
{
lean_dec_ref_known(v_x_2946_, 1);
if (v_final_2941_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec_ref(v___f_2945_);
lean_dec_ref(v_requestStream_2944_);
lean_dec_ref(v___f_2943_);
v___x_2957_ = lean_box(0);
v___x_2958_ = lean_apply_2(v___f_2942_, v___x_2957_, lean_box(0));
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_7913__overap_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; 
lean_dec_ref(v___f_2942_);
v___x_2959_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2960_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2961_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2962_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2963_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2963_, 0, lean_box(0));
lean_closure_set(v___x_2963_, 1, lean_box(0));
lean_closure_set(v___x_2963_, 2, v___x_2959_);
lean_closure_set(v___x_2963_, 3, lean_box(0));
lean_closure_set(v___x_2963_, 4, lean_box(0));
lean_closure_set(v___x_2963_, 5, v___x_2962_);
lean_closure_set(v___x_2963_, 6, v___f_2943_);
v___x_7913__overap_2964_ = l_Std_Mutex_atomically___redArg(v___x_2959_, v___f_2960_, v___f_2961_, v_requestStream_2944_, v___x_2963_);
v___x_2965_ = lean_apply_1(v___x_7913__overap_2964_, lean_box(0));
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = 0;
v___x_2968_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2966_, v___x_2967_, v___x_2965_, v___f_2945_);
return v___x_2968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_2969_, lean_object* v___f_2970_, lean_object* v___f_2971_, lean_object* v_requestStream_2972_, lean_object* v___f_2973_, lean_object* v_x_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v_final_boxed_2976_; lean_object* v_res_2977_; 
v_final_boxed_2976_ = lean_unbox(v_final_2969_);
v_res_2977_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_2976_, v___f_2970_, v___f_2971_, v_requestStream_2972_, v___f_2973_, v_x_2974_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2978_, lean_object* v_x_2979_){
_start:
{
if (lean_obj_tag(v_x_2979_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v_state_2978_);
v_a_2981_ = lean_ctor_get(v_x_2979_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_x_2979_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2983_ = v_x_2979_;
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v_x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
}
else
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3019_; 
v_isSharedCheck_3019_ = !lean_is_exclusive(v_x_2979_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_x_2979_, 0);
lean_dec(v_unused_3020_);
v___x_2991_ = v_x_2979_;
v_isShared_2992_ = v_isSharedCheck_3019_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v_x_2979_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3019_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v_machine_2993_; lean_object* v_requestStream_2994_; lean_object* v_keepAliveTimeout_2995_; lean_object* v_currentTimeout_2996_; lean_object* v_headerTimeout_2997_; lean_object* v_response_2998_; lean_object* v_respStream_2999_; uint8_t v_requiresData_3000_; lean_object* v_expectData_3001_; lean_object* v_pendingHead_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3018_; 
v_machine_2993_ = lean_ctor_get(v_state_2978_, 0);
v_requestStream_2994_ = lean_ctor_get(v_state_2978_, 1);
v_keepAliveTimeout_2995_ = lean_ctor_get(v_state_2978_, 2);
v_currentTimeout_2996_ = lean_ctor_get(v_state_2978_, 3);
v_headerTimeout_2997_ = lean_ctor_get(v_state_2978_, 4);
v_response_2998_ = lean_ctor_get(v_state_2978_, 5);
v_respStream_2999_ = lean_ctor_get(v_state_2978_, 6);
v_requiresData_3000_ = lean_ctor_get_uint8(v_state_2978_, sizeof(void*)*9);
v_expectData_3001_ = lean_ctor_get(v_state_2978_, 7);
v_pendingHead_3002_ = lean_ctor_get(v_state_2978_, 8);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_state_2978_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3004_ = v_state_2978_;
v_isShared_3005_ = v_isSharedCheck_3018_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_pendingHead_3002_);
lean_inc(v_expectData_3001_);
lean_inc(v_respStream_2999_);
lean_inc(v_response_2998_);
lean_inc(v_headerTimeout_2997_);
lean_inc(v_currentTimeout_2996_);
lean_inc(v_keepAliveTimeout_2995_);
lean_inc(v_requestStream_2994_);
lean_inc(v_machine_2993_);
lean_dec(v_state_2978_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3018_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; lean_object* v___x_3010_; 
v___x_3006_ = lean_box(52);
v___x_3007_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2993_, v___x_3006_);
v___x_3008_ = 0;
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3007_);
v___x_3010_ = v___x_3004_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_requestStream_2994_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v_keepAliveTimeout_2995_);
lean_ctor_set(v_reuseFailAlloc_3017_, 3, v_currentTimeout_2996_);
lean_ctor_set(v_reuseFailAlloc_3017_, 4, v_headerTimeout_2997_);
lean_ctor_set(v_reuseFailAlloc_3017_, 5, v_response_2998_);
lean_ctor_set(v_reuseFailAlloc_3017_, 6, v_respStream_2999_);
lean_ctor_set(v_reuseFailAlloc_3017_, 7, v_expectData_3001_);
lean_ctor_set(v_reuseFailAlloc_3017_, 8, v_pendingHead_3002_);
lean_ctor_set_uint8(v_reuseFailAlloc_3017_, sizeof(void*)*9, v_requiresData_3000_);
v___x_3010_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*9 + 1, v___x_3008_);
v___x_3011_ = lean_box(v___x_3008_);
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_3012_);
v___x_3014_ = v___x_2991_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3021_, v_x_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3025_, lean_object* v_requestStream_3026_, lean_object* v_keepAliveTimeout_3027_, lean_object* v_currentTimeout_3028_, lean_object* v_headerTimeout_3029_, lean_object* v_response_3030_, lean_object* v_respStream_3031_, uint8_t v_requiresData_3032_, lean_object* v_expectData_3033_, lean_object* v_pendingHead_3034_, lean_object* v_____r_3035_){
_start:
{
uint8_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3037_ = 0;
v___x_3038_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3038_, 0, v_machine_3025_);
lean_ctor_set(v___x_3038_, 1, v_requestStream_3026_);
lean_ctor_set(v___x_3038_, 2, v_keepAliveTimeout_3027_);
lean_ctor_set(v___x_3038_, 3, v_currentTimeout_3028_);
lean_ctor_set(v___x_3038_, 4, v_headerTimeout_3029_);
lean_ctor_set(v___x_3038_, 5, v_response_3030_);
lean_ctor_set(v___x_3038_, 6, v_respStream_3031_);
lean_ctor_set(v___x_3038_, 7, v_expectData_3033_);
lean_ctor_set(v___x_3038_, 8, v_pendingHead_3034_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*9, v_requiresData_3032_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*9 + 1, v___x_3037_);
v___x_3039_ = lean_box(v___x_3037_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3043_, lean_object* v_requestStream_3044_, lean_object* v_keepAliveTimeout_3045_, lean_object* v_currentTimeout_3046_, lean_object* v_headerTimeout_3047_, lean_object* v_response_3048_, lean_object* v_respStream_3049_, lean_object* v_requiresData_3050_, lean_object* v_expectData_3051_, lean_object* v_pendingHead_3052_, lean_object* v_____r_3053_, lean_object* v___y_3054_){
_start:
{
uint8_t v_requiresData_boxed_3055_; lean_object* v_res_3056_; 
v_requiresData_boxed_3055_ = lean_unbox(v_requiresData_3050_);
v_res_3056_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3043_, v_requestStream_3044_, v_keepAliveTimeout_3045_, v_currentTimeout_3046_, v_headerTimeout_3047_, v_response_3048_, v_respStream_3049_, v_requiresData_boxed_3055_, v_expectData_3051_, v_pendingHead_3052_, v_____r_3053_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3057_, lean_object* v_body_3058_, lean_object* v___f_3059_, lean_object* v___f_3060_, lean_object* v_x_3061_){
_start:
{
if (lean_obj_tag(v_x_3061_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v___f_3060_);
lean_dec_ref(v___f_3059_);
lean_dec(v_body_3058_);
lean_dec_ref(v_close_3057_);
v_a_3063_ = lean_ctor_get(v_x_3061_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_x_3061_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3065_ = v_x_3061_;
v_isShared_3066_ = v_isSharedCheck_3071_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v_x_3061_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3071_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3063_);
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
else
{
lean_object* v_a_3072_; uint8_t v___x_3073_; 
v_a_3072_ = lean_ctor_get(v_x_3061_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v_x_3061_, 1);
v___x_3073_ = lean_unbox(v_a_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; 
lean_dec_ref(v___f_3060_);
v___x_3074_ = lean_apply_2(v_close_3057_, v_body_3058_, lean_box(0));
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_unbox(v_a_3072_);
lean_dec(v_a_3072_);
v___x_3077_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3075_, v___x_3076_, v___x_3074_, v___f_3059_);
return v___x_3077_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec(v_a_3072_);
lean_dec_ref(v___f_3059_);
lean_dec(v_body_3058_);
lean_dec_ref(v_close_3057_);
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_apply_2(v___f_3060_, v___x_3078_, lean_box(0));
return v___x_3079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3080_, lean_object* v_body_3081_, lean_object* v___f_3082_, lean_object* v___f_3083_, lean_object* v_x_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3080_, v_body_3081_, v___f_3082_, v___f_3083_, v_x_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3087_, lean_object* v_keepAliveTimeout_3088_, lean_object* v_currentTimeout_3089_, lean_object* v_headerTimeout_3090_, lean_object* v_response_3091_, uint8_t v_requiresData_3092_, lean_object* v_expectData_3093_, uint8_t v___x_3094_, lean_object* v_pendingHead_3095_, lean_object* v_____x_3096_){
_start:
{
lean_object* v_snd_3098_; lean_object* v_fst_3099_; lean_object* v_fst_3100_; lean_object* v_snd_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3111_; 
v_snd_3098_ = lean_ctor_get(v_____x_3096_, 1);
lean_inc(v_snd_3098_);
v_fst_3099_ = lean_ctor_get(v_____x_3096_, 0);
lean_inc(v_fst_3099_);
lean_dec_ref(v_____x_3096_);
v_fst_3100_ = lean_ctor_get(v_snd_3098_, 0);
v_snd_3101_ = lean_ctor_get(v_snd_3098_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_snd_3098_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3103_ = v_snd_3098_;
v_isShared_3104_ = v_isSharedCheck_3111_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_snd_3101_);
lean_inc(v_fst_3100_);
lean_dec(v_snd_3098_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3111_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3105_, 0, v_fst_3099_);
lean_ctor_set(v___x_3105_, 1, v_requestStream_3087_);
lean_ctor_set(v___x_3105_, 2, v_keepAliveTimeout_3088_);
lean_ctor_set(v___x_3105_, 3, v_currentTimeout_3089_);
lean_ctor_set(v___x_3105_, 4, v_headerTimeout_3090_);
lean_ctor_set(v___x_3105_, 5, v_response_3091_);
lean_ctor_set(v___x_3105_, 6, v_fst_3100_);
lean_ctor_set(v___x_3105_, 7, v_expectData_3093_);
lean_ctor_set(v___x_3105_, 8, v_pendingHead_3095_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*9, v_requiresData_3092_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*9 + 1, v___x_3094_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3107_ = v___x_3103_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_snd_3101_);
v___x_3107_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3112_, lean_object* v_keepAliveTimeout_3113_, lean_object* v_currentTimeout_3114_, lean_object* v_headerTimeout_3115_, lean_object* v_response_3116_, lean_object* v_requiresData_3117_, lean_object* v_expectData_3118_, lean_object* v___x_3119_, lean_object* v_pendingHead_3120_, lean_object* v_____x_3121_, lean_object* v___y_3122_){
_start:
{
uint8_t v_requiresData_boxed_3123_; uint8_t v___x_8729__boxed_3124_; lean_object* v_res_3125_; 
v_requiresData_boxed_3123_ = lean_unbox(v_requiresData_3117_);
v___x_8729__boxed_3124_ = lean_unbox(v___x_3119_);
v_res_3125_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3112_, v_keepAliveTimeout_3113_, v_currentTimeout_3114_, v_headerTimeout_3115_, v_response_3116_, v_requiresData_boxed_3123_, v_expectData_3118_, v___x_8729__boxed_3124_, v_pendingHead_3120_, v_____x_3121_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3126_, lean_object* v_x_3127_){
_start:
{
if (lean_obj_tag(v_x_3127_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v___f_3126_);
v_a_3129_ = lean_ctor_get(v_x_3127_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_x_3127_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3131_ = v_x_3127_;
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v_x_3127_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v_x_3127_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v_x_3127_, 1);
v___x_3139_ = lean_apply_2(v___f_3126_, v_a_3138_, lean_box(0));
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3140_, lean_object* v_x_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3140_, v_x_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3144_, lean_object* v_x_3145_){
_start:
{
if (lean_obj_tag(v_x_3145_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3155_; 
v_a_3147_ = lean_ctor_get(v_x_3145_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_x_3145_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3149_ = v_x_3145_;
v_isShared_3150_ = v_isSharedCheck_3155_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v_x_3145_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3155_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3175_; 
v_a_3156_ = lean_ctor_get(v_x_3145_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_x_3145_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3158_ = v_x_3145_;
v_isShared_3159_ = v_isSharedCheck_3175_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v_x_3145_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3175_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v_fst_3160_; lean_object* v_snd_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3174_; 
v_fst_3160_ = lean_ctor_get(v_a_3156_, 0);
v_snd_3161_ = lean_ctor_get(v_a_3156_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_a_3156_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3163_ = v_a_3156_;
v_isShared_3164_ = v_isSharedCheck_3174_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_snd_3161_);
lean_inc(v_fst_3160_);
lean_dec(v_a_3156_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3174_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_box(v___x_3144_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3165_);
lean_ctor_set(v___x_3163_, 0, v_snd_3161_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_snd_3161_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_fst_3160_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 0, v___x_3168_);
v___x_3170_ = v___x_3158_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3176_, lean_object* v_x_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v___x_8797__boxed_3179_; lean_object* v_res_3180_; 
v___x_8797__boxed_3179_ = lean_unbox(v___x_3176_);
v_res_3180_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_8797__boxed_3179_, v_x_3177_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3181_, uint8_t v___x_3182_, lean_object* v_fst_3183_, lean_object* v_x_3184_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v_fst_3183_);
lean_dec(v_snd_3181_);
v_a_3186_ = lean_ctor_get(v_x_3184_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_x_3184_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3188_ = v_x_3184_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v_x_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
}
}
else
{
lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3205_; 
v_isSharedCheck_3205_ = !lean_is_exclusive(v_x_3184_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v_x_3184_, 0);
lean_dec(v_unused_3206_);
v___x_3196_ = v_x_3184_;
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v_x_3184_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3198_ = lean_box(v___x_3182_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_snd_3181_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_fst_3183_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3200_);
v___x_3202_ = v___x_3196_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3200_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3207_, lean_object* v___x_3208_, lean_object* v_fst_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_8865__boxed_3212_; lean_object* v_res_3213_; 
v___x_8865__boxed_3212_ = lean_unbox(v___x_3208_);
v_res_3213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3207_, v___x_8865__boxed_3212_, v_fst_3209_, v_x_3210_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3214_, lean_object* v_handler_3215_, uint8_t v___x_3216_, lean_object* v___f_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3218_) == 0)
{
lean_object* v_a_3220_; lean_object* v_onFailure_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_a_3220_ = lean_ctor_get(v_x_3218_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v_x_3218_, 1);
v_onFailure_3221_ = lean_ctor_get(v_inst_3214_, 2);
lean_inc_ref(v_onFailure_3221_);
lean_dec_ref(v_inst_3214_);
v___x_3222_ = lean_apply_3(v_onFailure_3221_, v_handler_3215_, v_a_3220_, lean_box(0));
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3223_, v___x_3216_, v___x_3222_, v___f_3217_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; 
lean_dec_ref(v___f_3217_);
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3214_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v_x_3218_);
return v___x_3225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3226_, lean_object* v_handler_3227_, lean_object* v___x_3228_, lean_object* v___f_3229_, lean_object* v_x_3230_, lean_object* v___y_3231_){
_start:
{
uint8_t v___x_8923__boxed_3232_; lean_object* v_res_3233_; 
v___x_8923__boxed_3232_ = lean_unbox(v___x_3228_);
v_res_3233_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3226_, v_handler_3227_, v___x_8923__boxed_3232_, v___f_3229_, v_x_3230_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3234_, lean_object* v___f_3235_, lean_object* v_inst_3236_, lean_object* v___f_3237_, uint8_t v___x_3238_, lean_object* v_inst_3239_, lean_object* v_handler_3240_, lean_object* v___f_3241_, lean_object* v_x_3242_){
_start:
{
if (lean_obj_tag(v_x_3242_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___f_3241_);
lean_dec(v_handler_3240_);
lean_dec_ref(v_inst_3239_);
lean_dec_ref(v___f_3237_);
lean_dec_ref(v_inst_3236_);
lean_dec_ref(v___f_3235_);
v_a_3244_ = lean_ctor_get(v_x_3242_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_x_3242_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3246_ = v_x_3242_;
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v_x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3286_; 
v_a_3253_ = lean_ctor_get(v_x_3242_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_x_3242_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3255_ = v_x_3242_;
v_isShared_3256_ = v_isSharedCheck_3286_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v_x_3242_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3286_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v_snd_3257_; 
v_snd_3257_ = lean_ctor_get(v_a_3253_, 1);
lean_inc(v_snd_3257_);
if (lean_obj_tag(v_snd_3257_) == 0)
{
lean_object* v_fst_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v___f_3241_);
lean_dec(v_handler_3240_);
lean_dec_ref(v_inst_3239_);
lean_dec_ref(v___f_3237_);
lean_dec_ref(v_inst_3236_);
v_fst_3258_ = lean_ctor_get(v_a_3253_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_a_3253_);
if (v_isSharedCheck_3273_ == 0)
{
lean_object* v_unused_3274_; 
v_unused_3274_ = lean_ctor_get(v_a_3253_, 1);
lean_dec(v_unused_3274_);
v___x_3260_ = v_a_3253_;
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_fst_3258_);
lean_dec(v_a_3253_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3262_ = lean_box(v___x_3234_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v___x_3262_);
lean_ctor_set(v___x_3260_, 0, v_snd_3257_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_snd_3257_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v_fst_3258_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3265_);
v___x_3267_ = v___x_3255_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
v___x_3269_ = lean_unsigned_to_nat(0u);
v___x_3270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3269_, v___x_3234_, v___x_3268_, v___f_3235_);
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_fst_3275_; lean_object* v_val_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_del_object(v___x_3255_);
lean_dec_ref(v___f_3235_);
v_fst_3275_ = lean_ctor_get(v_a_3253_, 0);
lean_inc_n(v_fst_3275_, 2);
lean_dec(v_a_3253_);
v_val_3276_ = lean_ctor_get(v_snd_3257_, 0);
lean_inc(v_val_3276_);
v___x_3277_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3236_, v_fst_3275_, v_val_3276_);
v___x_3278_ = lean_unsigned_to_nat(0u);
v___x_3279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3278_, v___x_3234_, v___x_3277_, v___f_3237_);
v___x_3280_ = lean_box(v___x_3238_);
v___f_3281_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3281_, 0, v_snd_3257_);
lean_closure_set(v___f_3281_, 1, v___x_3280_);
lean_closure_set(v___f_3281_, 2, v_fst_3275_);
v___x_3282_ = lean_box(v___x_3234_);
v___f_3283_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3283_, 0, v_inst_3239_);
lean_closure_set(v___f_3283_, 1, v_handler_3240_);
lean_closure_set(v___f_3283_, 2, v___x_3282_);
lean_closure_set(v___f_3283_, 3, v___f_3281_);
v___x_3284_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3278_, v___x_3234_, v___x_3279_, v___f_3283_);
v___x_3285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3278_, v___x_3234_, v___x_3284_, v___f_3241_);
return v___x_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3287_, lean_object* v___f_3288_, lean_object* v_inst_3289_, lean_object* v___f_3290_, lean_object* v___x_3291_, lean_object* v_inst_3292_, lean_object* v_handler_3293_, lean_object* v___f_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v___x_8948__boxed_3297_; uint8_t v___x_8952__boxed_3298_; lean_object* v_res_3299_; 
v___x_8948__boxed_3297_ = lean_unbox(v___x_3287_);
v___x_8952__boxed_3298_ = lean_unbox(v___x_3291_);
v_res_3299_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8948__boxed_3297_, v___f_3288_, v_inst_3289_, v___f_3290_, v___x_8952__boxed_3298_, v_inst_3292_, v_handler_3293_, v___f_3294_, v_x_3295_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3300_, lean_object* v_x_3301_){
_start:
{
if (lean_obj_tag(v_x_3301_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref(v_state_3300_);
v_a_3303_ = lean_ctor_get(v_x_3301_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_x_3301_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3305_ = v_x_3301_;
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v_x_3301_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; 
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
}
}
else
{
lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v_x_3301_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v_x_3301_, 0);
lean_dec(v_unused_3342_);
v___x_3313_ = v_x_3301_;
v_isShared_3314_ = v_isSharedCheck_3341_;
goto v_resetjp_3312_;
}
else
{
lean_dec(v_x_3301_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3341_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_machine_3315_; lean_object* v_requestStream_3316_; lean_object* v_keepAliveTimeout_3317_; lean_object* v_currentTimeout_3318_; lean_object* v_headerTimeout_3319_; lean_object* v_response_3320_; lean_object* v_respStream_3321_; uint8_t v_requiresData_3322_; lean_object* v_expectData_3323_; lean_object* v_pendingHead_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3340_; 
v_machine_3315_ = lean_ctor_get(v_state_3300_, 0);
v_requestStream_3316_ = lean_ctor_get(v_state_3300_, 1);
v_keepAliveTimeout_3317_ = lean_ctor_get(v_state_3300_, 2);
v_currentTimeout_3318_ = lean_ctor_get(v_state_3300_, 3);
v_headerTimeout_3319_ = lean_ctor_get(v_state_3300_, 4);
v_response_3320_ = lean_ctor_get(v_state_3300_, 5);
v_respStream_3321_ = lean_ctor_get(v_state_3300_, 6);
v_requiresData_3322_ = lean_ctor_get_uint8(v_state_3300_, sizeof(void*)*9);
v_expectData_3323_ = lean_ctor_get(v_state_3300_, 7);
v_pendingHead_3324_ = lean_ctor_get(v_state_3300_, 8);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_state_3300_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3326_ = v_state_3300_;
v_isShared_3327_ = v_isSharedCheck_3340_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_pendingHead_3324_);
lean_inc(v_expectData_3323_);
lean_inc(v_respStream_3321_);
lean_inc(v_response_3320_);
lean_inc(v_headerTimeout_3319_);
lean_inc(v_currentTimeout_3318_);
lean_inc(v_keepAliveTimeout_3317_);
lean_inc(v_requestStream_3316_);
lean_inc(v_machine_3315_);
lean_dec(v_state_3300_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3340_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; lean_object* v___x_3332_; 
v___x_3328_ = lean_box(31);
v___x_3329_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3315_, v___x_3328_);
v___x_3330_ = 0;
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3329_);
v___x_3332_ = v___x_3326_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_requestStream_3316_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_keepAliveTimeout_3317_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_currentTimeout_3318_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v_headerTimeout_3319_);
lean_ctor_set(v_reuseFailAlloc_3339_, 5, v_response_3320_);
lean_ctor_set(v_reuseFailAlloc_3339_, 6, v_respStream_3321_);
lean_ctor_set(v_reuseFailAlloc_3339_, 7, v_expectData_3323_);
lean_ctor_set(v_reuseFailAlloc_3339_, 8, v_pendingHead_3324_);
lean_ctor_set_uint8(v_reuseFailAlloc_3339_, sizeof(void*)*9, v_requiresData_3322_);
v___x_3332_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_ctor_set_uint8(v___x_3332_, sizeof(void*)*9 + 1, v___x_3330_);
v___x_3333_ = lean_box(v___x_3330_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3334_);
v___x_3336_ = v___x_3313_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3343_, v_x_3344_);
return v_res_3346_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3352_ = lean_mk_io_user_error(v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_handler_3355_, lean_object* v_config_3356_, lean_object* v_event_3357_, lean_object* v_state_3358_){
_start:
{
switch(lean_obj_tag(v_event_3357_))
{
case 0:
{
lean_object* v_x_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3354_);
lean_dec_ref(v_inst_3353_);
v_x_3360_ = lean_ctor_get(v_event_3357_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_event_3357_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3362_ = v_event_3357_;
v_isShared_3363_ = v_isSharedCheck_3467_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_x_3360_);
lean_dec(v_event_3357_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3467_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
if (lean_obj_tag(v_x_3360_) == 0)
{
lean_object* v_machine_3364_; lean_object* v_reader_3365_; lean_object* v_requestStream_3366_; lean_object* v_keepAliveTimeout_3367_; lean_object* v_currentTimeout_3368_; lean_object* v_headerTimeout_3369_; lean_object* v_response_3370_; lean_object* v_respStream_3371_; uint8_t v_requiresData_3372_; lean_object* v_expectData_3373_; uint8_t v_handlerDispatched_3374_; lean_object* v_pendingHead_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_config_3356_);
v_machine_3364_ = lean_ctor_get(v_state_3358_, 0);
lean_inc_ref(v_machine_3364_);
v_reader_3365_ = lean_ctor_get(v_machine_3364_, 0);
lean_inc_ref(v_reader_3365_);
v_requestStream_3366_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3367_ = lean_ctor_get(v_state_3358_, 2);
v_currentTimeout_3368_ = lean_ctor_get(v_state_3358_, 3);
v_headerTimeout_3369_ = lean_ctor_get(v_state_3358_, 4);
v_response_3370_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3371_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3372_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3373_ = lean_ctor_get(v_state_3358_, 7);
v_handlerDispatched_3374_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9 + 1);
v_pendingHead_3375_ = lean_ctor_get(v_state_3358_, 8);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v_state_3358_, 0);
lean_dec(v_unused_3419_);
v___x_3377_ = v_state_3358_;
v_isShared_3378_ = v_isSharedCheck_3418_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_pendingHead_3375_);
lean_inc(v_expectData_3373_);
lean_inc(v_respStream_3371_);
lean_inc(v_response_3370_);
lean_inc(v_headerTimeout_3369_);
lean_inc(v_currentTimeout_3368_);
lean_inc(v_keepAliveTimeout_3367_);
lean_inc(v_requestStream_3366_);
lean_dec(v_state_3358_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3418_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v_writer_3379_; lean_object* v_config_3380_; lean_object* v_events_3381_; lean_object* v_error_3382_; lean_object* v_instant_3383_; uint8_t v_keepAlive_3384_; uint8_t v_forcedFlush_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3416_; 
v_writer_3379_ = lean_ctor_get(v_machine_3364_, 1);
v_config_3380_ = lean_ctor_get(v_machine_3364_, 2);
v_events_3381_ = lean_ctor_get(v_machine_3364_, 3);
v_error_3382_ = lean_ctor_get(v_machine_3364_, 4);
v_instant_3383_ = lean_ctor_get(v_machine_3364_, 5);
v_keepAlive_3384_ = lean_ctor_get_uint8(v_machine_3364_, sizeof(void*)*6);
v_forcedFlush_3385_ = lean_ctor_get_uint8(v_machine_3364_, sizeof(void*)*6 + 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_machine_3364_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; 
v_unused_3417_ = lean_ctor_get(v_machine_3364_, 0);
lean_dec(v_unused_3417_);
v___x_3387_ = v_machine_3364_;
v_isShared_3388_ = v_isSharedCheck_3416_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_instant_3383_);
lean_inc(v_error_3382_);
lean_inc(v_events_3381_);
lean_inc(v_config_3380_);
lean_inc(v_writer_3379_);
lean_dec(v_machine_3364_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3416_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_state_3389_; lean_object* v_input_3390_; lean_object* v_messageHead_3391_; lean_object* v_messageCount_3392_; lean_object* v_bodyBytesRead_3393_; lean_object* v_headerBytesRead_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3415_; 
v_state_3389_ = lean_ctor_get(v_reader_3365_, 0);
v_input_3390_ = lean_ctor_get(v_reader_3365_, 1);
v_messageHead_3391_ = lean_ctor_get(v_reader_3365_, 2);
v_messageCount_3392_ = lean_ctor_get(v_reader_3365_, 3);
v_bodyBytesRead_3393_ = lean_ctor_get(v_reader_3365_, 4);
v_headerBytesRead_3394_ = lean_ctor_get(v_reader_3365_, 5);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_reader_3365_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3396_ = v_reader_3365_;
v_isShared_3397_ = v_isSharedCheck_3415_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_headerBytesRead_3394_);
lean_inc(v_bodyBytesRead_3393_);
lean_inc(v_messageCount_3392_);
lean_inc(v_messageHead_3391_);
lean_inc(v_input_3390_);
lean_inc(v_state_3389_);
lean_dec(v_reader_3365_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3415_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
uint8_t v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = 1;
if (v_isShared_3397_ == 0)
{
v___x_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_state_3389_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_input_3390_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_messageHead_3391_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_messageCount_3392_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_bodyBytesRead_3393_);
lean_ctor_set(v_reuseFailAlloc_3414_, 5, v_headerBytesRead_3394_);
v___x_3400_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
uint8_t v___x_3401_; lean_object* v___x_3403_; 
lean_ctor_set_uint8(v___x_3400_, sizeof(void*)*6, v___x_3398_);
v___x_3401_ = 0;
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3400_);
v___x_3403_ = v___x_3387_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_writer_3379_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_config_3380_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_events_3381_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v_error_3382_);
lean_ctor_set(v_reuseFailAlloc_3413_, 5, v_instant_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3413_, sizeof(void*)*6, v_keepAlive_3384_);
lean_ctor_set_uint8(v_reuseFailAlloc_3413_, sizeof(void*)*6 + 1, v_forcedFlush_3385_);
v___x_3403_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3405_; 
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*6 + 2, v___x_3401_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3403_);
v___x_3405_ = v___x_3377_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_requestStream_3366_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_keepAliveTimeout_3367_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_currentTimeout_3368_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_headerTimeout_3369_);
lean_ctor_set(v_reuseFailAlloc_3412_, 5, v_response_3370_);
lean_ctor_set(v_reuseFailAlloc_3412_, 6, v_respStream_3371_);
lean_ctor_set(v_reuseFailAlloc_3412_, 7, v_expectData_3373_);
lean_ctor_set(v_reuseFailAlloc_3412_, 8, v_pendingHead_3375_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*9, v_requiresData_3372_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*9 + 1, v_handlerDispatched_3374_);
v___x_3405_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3406_ = lean_box(v___x_3401_);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 1);
lean_ctor_set(v___x_3362_, 0, v___x_3407_);
v___x_3409_ = v___x_3362_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
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
lean_object* v_val_3420_; lean_object* v_machine_3421_; lean_object* v_requestStream_3422_; lean_object* v_keepAliveTimeout_3423_; lean_object* v_currentTimeout_3424_; lean_object* v_response_3425_; lean_object* v_respStream_3426_; uint8_t v_requiresData_3427_; lean_object* v_expectData_3428_; uint8_t v_handlerDispatched_3429_; lean_object* v_pendingHead_3430_; lean_object* v___f_3431_; 
lean_del_object(v___x_3362_);
v_val_3420_ = lean_ctor_get(v_x_3360_, 0);
lean_inc_n(v_val_3420_, 2);
lean_dec_ref_known(v_x_3360_, 1);
v_machine_3421_ = lean_ctor_get(v_state_3358_, 0);
v_requestStream_3422_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3423_ = lean_ctor_get(v_state_3358_, 2);
lean_inc(v_keepAliveTimeout_3423_);
v_currentTimeout_3424_ = lean_ctor_get(v_state_3358_, 3);
v_response_3425_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3426_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3427_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3428_ = lean_ctor_get(v_state_3358_, 7);
v_handlerDispatched_3429_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9 + 1);
v_pendingHead_3430_ = lean_ctor_get(v_state_3358_, 8);
v___f_3431_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3431_, 0, v_val_3420_);
if (lean_obj_tag(v_keepAliveTimeout_3423_) == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v___f_3431_);
lean_dec_ref(v_config_3356_);
v___x_3432_ = lean_box(0);
v___x_3433_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3420_, v___x_3432_, v_state_3358_);
return v___x_3433_;
}
else
{
lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3465_; 
lean_inc(v_pendingHead_3430_);
lean_inc(v_expectData_3428_);
lean_inc(v_respStream_3426_);
lean_inc_ref(v_response_3425_);
lean_inc(v_currentTimeout_3424_);
lean_inc_ref(v_requestStream_3422_);
lean_inc_ref(v_machine_3421_);
lean_dec(v_val_3420_);
lean_dec_ref(v_state_3358_);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_keepAliveTimeout_3423_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_keepAliveTimeout_3423_, 0);
lean_dec(v_unused_3466_);
v___x_3435_ = v_keepAliveTimeout_3423_;
v_isShared_3436_ = v_isSharedCheck_3465_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v_keepAliveTimeout_3423_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3465_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___f_3439_; lean_object* v_val_3441_; lean_object* v___x_3448_; 
v___x_3437_ = lean_box(v_requiresData_3427_);
v___x_3438_ = lean_box(v_handlerDispatched_3429_);
v___f_3439_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3439_, 0, v_config_3356_);
lean_closure_set(v___f_3439_, 1, v_machine_3421_);
lean_closure_set(v___f_3439_, 2, v_requestStream_3422_);
lean_closure_set(v___f_3439_, 3, v_currentTimeout_3424_);
lean_closure_set(v___f_3439_, 4, v_response_3425_);
lean_closure_set(v___f_3439_, 5, v_respStream_3426_);
lean_closure_set(v___f_3439_, 6, v___x_3437_);
lean_closure_set(v___f_3439_, 7, v_expectData_3428_);
lean_closure_set(v___f_3439_, 8, v___x_3438_);
lean_closure_set(v___f_3439_, 9, v_pendingHead_3430_);
lean_closure_set(v___f_3439_, 10, v___f_3431_);
v___x_3448_ = lean_get_current_time();
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set_tag(v___x_3451_, 1);
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
v_val_3441_ = v___x_3454_;
goto v___jp_3440_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3448_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3448_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 0);
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_val_3441_ = v___x_3462_;
goto v___jp_3440_;
}
}
}
v___jp_3440_:
{
lean_object* v___x_3443_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 0);
lean_ctor_set(v___x_3435_, 0, v_val_3441_);
v___x_3443_ = v___x_3435_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_val_3441_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = 0;
v___x_3446_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3444_, v___x_3445_, v___x_3443_, v___f_3439_);
return v___x_3446_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3583_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3353_);
v_x_3468_ = lean_ctor_get(v_event_3357_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_event_3357_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3470_ = v_event_3357_;
v_isShared_3471_ = v_isSharedCheck_3583_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_x_3468_);
lean_dec(v_event_3357_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3583_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
if (lean_obj_tag(v_x_3468_) == 0)
{
lean_object* v_machine_3472_; lean_object* v_requestStream_3473_; lean_object* v_keepAliveTimeout_3474_; lean_object* v_currentTimeout_3475_; lean_object* v_headerTimeout_3476_; lean_object* v_response_3477_; lean_object* v_respStream_3478_; uint8_t v_requiresData_3479_; lean_object* v_expectData_3480_; uint8_t v_handlerDispatched_3481_; lean_object* v_pendingHead_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___f_3485_; 
lean_del_object(v___x_3470_);
v_machine_3472_ = lean_ctor_get(v_state_3358_, 0);
lean_inc_ref_n(v_machine_3472_, 2);
v_requestStream_3473_ = lean_ctor_get(v_state_3358_, 1);
lean_inc_ref_n(v_requestStream_3473_, 2);
v_keepAliveTimeout_3474_ = lean_ctor_get(v_state_3358_, 2);
lean_inc_n(v_keepAliveTimeout_3474_, 2);
v_currentTimeout_3475_ = lean_ctor_get(v_state_3358_, 3);
lean_inc_n(v_currentTimeout_3475_, 2);
v_headerTimeout_3476_ = lean_ctor_get(v_state_3358_, 4);
lean_inc_n(v_headerTimeout_3476_, 2);
v_response_3477_ = lean_ctor_get(v_state_3358_, 5);
lean_inc_ref_n(v_response_3477_, 2);
v_respStream_3478_ = lean_ctor_get(v_state_3358_, 6);
lean_inc(v_respStream_3478_);
v_requiresData_3479_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3480_ = lean_ctor_get(v_state_3358_, 7);
lean_inc_n(v_expectData_3480_, 2);
v_handlerDispatched_3481_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9 + 1);
v_pendingHead_3482_ = lean_ctor_get(v_state_3358_, 8);
lean_inc_n(v_pendingHead_3482_, 2);
lean_dec_ref(v_state_3358_);
v___x_3483_ = lean_box(v_requiresData_3479_);
v___x_3484_ = lean_box(v_handlerDispatched_3481_);
v___f_3485_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3485_, 0, v_machine_3472_);
lean_closure_set(v___f_3485_, 1, v_requestStream_3473_);
lean_closure_set(v___f_3485_, 2, v_keepAliveTimeout_3474_);
lean_closure_set(v___f_3485_, 3, v_currentTimeout_3475_);
lean_closure_set(v___f_3485_, 4, v_headerTimeout_3476_);
lean_closure_set(v___f_3485_, 5, v_response_3477_);
lean_closure_set(v___f_3485_, 6, v___x_3483_);
lean_closure_set(v___f_3485_, 7, v_expectData_3480_);
lean_closure_set(v___f_3485_, 8, v___x_3484_);
lean_closure_set(v___f_3485_, 9, v_pendingHead_3482_);
if (lean_obj_tag(v_respStream_3478_) == 1)
{
lean_object* v_val_3486_; lean_object* v_close_3487_; lean_object* v_isClosed_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; lean_object* v___x_3494_; 
lean_dec(v_pendingHead_3482_);
lean_dec(v_expectData_3480_);
lean_dec_ref(v_response_3477_);
lean_dec(v_headerTimeout_3476_);
lean_dec(v_currentTimeout_3475_);
lean_dec(v_keepAliveTimeout_3474_);
lean_dec_ref(v_requestStream_3473_);
lean_dec_ref(v_machine_3472_);
v_val_3486_ = lean_ctor_get(v_respStream_3478_, 0);
lean_inc_n(v_val_3486_, 2);
lean_dec_ref_known(v_respStream_3478_, 1);
v_close_3487_ = lean_ctor_get(v_inst_3354_, 1);
lean_inc_ref(v_close_3487_);
v_isClosed_3488_ = lean_ctor_get(v_inst_3354_, 2);
lean_inc_ref(v_isClosed_3488_);
lean_dec_ref(v_inst_3354_);
v___x_3489_ = lean_apply_2(v_isClosed_3488_, v_val_3486_, lean_box(0));
lean_inc_ref(v___f_3485_);
v___f_3490_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3490_, 0, v___f_3485_);
v___f_3491_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3491_, 0, v_close_3487_);
lean_closure_set(v___f_3491_, 1, v_val_3486_);
lean_closure_set(v___f_3491_, 2, v___f_3490_);
lean_closure_set(v___f_3491_, 3, v___f_3485_);
v___x_3492_ = lean_unsigned_to_nat(0u);
v___x_3493_ = 0;
v___x_3494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3492_, v___x_3493_, v___x_3489_, v___f_3491_);
return v___x_3494_;
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec_ref(v___f_3485_);
lean_dec(v_respStream_3478_);
lean_dec_ref(v_inst_3354_);
v___x_3495_ = lean_box(0);
v___x_3496_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3472_, v_requestStream_3473_, v_keepAliveTimeout_3474_, v_currentTimeout_3475_, v_headerTimeout_3476_, v_response_3477_, v_requiresData_3479_, v_expectData_3480_, v_handlerDispatched_3481_, v_pendingHead_3482_, v___x_3495_);
return v___x_3496_;
}
}
else
{
lean_object* v_val_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v_inst_3354_);
v_val_3497_ = lean_ctor_get(v_x_3468_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_x_3468_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3499_ = v_x_3468_;
v_isShared_3500_ = v_isSharedCheck_3582_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_val_3497_);
lean_dec(v_x_3468_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3582_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_machine_3501_; lean_object* v_requestStream_3502_; lean_object* v_keepAliveTimeout_3503_; lean_object* v_currentTimeout_3504_; lean_object* v_headerTimeout_3505_; lean_object* v_response_3506_; lean_object* v_respStream_3507_; uint8_t v_requiresData_3508_; lean_object* v_expectData_3509_; uint8_t v_handlerDispatched_3510_; lean_object* v_pendingHead_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3581_; 
v_machine_3501_ = lean_ctor_get(v_state_3358_, 0);
v_requestStream_3502_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3503_ = lean_ctor_get(v_state_3358_, 2);
v_currentTimeout_3504_ = lean_ctor_get(v_state_3358_, 3);
v_headerTimeout_3505_ = lean_ctor_get(v_state_3358_, 4);
v_response_3506_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3507_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3508_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3509_ = lean_ctor_get(v_state_3358_, 7);
v_handlerDispatched_3510_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9 + 1);
v_pendingHead_3511_ = lean_ctor_get(v_state_3358_, 8);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3513_ = v_state_3358_;
v_isShared_3514_ = v_isSharedCheck_3581_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_pendingHead_3511_);
lean_inc(v_expectData_3509_);
lean_inc(v_respStream_3507_);
lean_inc(v_response_3506_);
lean_inc(v_headerTimeout_3505_);
lean_inc(v_currentTimeout_3504_);
lean_inc(v_keepAliveTimeout_3503_);
lean_inc(v_requestStream_3502_);
lean_inc(v_machine_3501_);
lean_dec(v_state_3358_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3581_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___y_3516_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3529_ = lean_unsigned_to_nat(1u);
v___x_3530_ = lean_mk_empty_array_with_capacity(v___x_3529_);
v___x_3531_ = lean_array_push(v___x_3530_, v_val_3497_);
v___x_3532_ = lean_array_get_size(v___x_3531_);
v___x_3533_ = lean_unsigned_to_nat(0u);
v___x_3534_ = lean_nat_dec_eq(v___x_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v_reader_3535_; lean_object* v_writer_3536_; lean_object* v_config_3537_; lean_object* v_events_3538_; lean_object* v_error_3539_; lean_object* v_instant_3540_; uint8_t v_keepAlive_3541_; uint8_t v_forcedFlush_3542_; uint8_t v_pullBodyStalled_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3580_; 
v_reader_3535_ = lean_ctor_get(v_machine_3501_, 0);
v_writer_3536_ = lean_ctor_get(v_machine_3501_, 1);
v_config_3537_ = lean_ctor_get(v_machine_3501_, 2);
v_events_3538_ = lean_ctor_get(v_machine_3501_, 3);
v_error_3539_ = lean_ctor_get(v_machine_3501_, 4);
v_instant_3540_ = lean_ctor_get(v_machine_3501_, 5);
v_keepAlive_3541_ = lean_ctor_get_uint8(v_machine_3501_, sizeof(void*)*6);
v_forcedFlush_3542_ = lean_ctor_get_uint8(v_machine_3501_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3543_ = lean_ctor_get_uint8(v_machine_3501_, sizeof(void*)*6 + 2);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_machine_3501_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3545_ = v_machine_3501_;
v_isShared_3546_ = v_isSharedCheck_3580_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_instant_3540_);
lean_inc(v_error_3539_);
lean_inc(v_events_3538_);
lean_inc(v_config_3537_);
lean_inc(v_writer_3536_);
lean_inc(v_reader_3535_);
lean_dec(v_machine_3501_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3580_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___y_3548_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9));
v___x_3571_ = lean_nat_dec_lt(v___x_3533_, v___x_3532_);
if (v___x_3571_ == 0)
{
v___y_3548_ = v___x_3533_;
goto v___jp_3547_;
}
else
{
lean_object* v___f_3572_; uint8_t v___x_3573_; 
v___f_3572_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3573_ = lean_nat_dec_le(v___x_3532_, v___x_3532_);
if (v___x_3573_ == 0)
{
if (v___x_3571_ == 0)
{
v___y_3548_ = v___x_3533_;
goto v___jp_3547_;
}
else
{
size_t v___x_3574_; size_t v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = ((size_t)0ULL);
v___x_3575_ = lean_usize_of_nat(v___x_3532_);
lean_inc_ref(v___x_3531_);
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3570_, v___f_3572_, v___x_3531_, v___x_3574_, v___x_3575_, v___x_3533_);
v___y_3548_ = v___x_3576_;
goto v___jp_3547_;
}
}
else
{
size_t v___x_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = ((size_t)0ULL);
v___x_3578_ = lean_usize_of_nat(v___x_3532_);
lean_inc_ref(v___x_3531_);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3570_, v___f_3572_, v___x_3531_, v___x_3577_, v___x_3578_, v___x_3533_);
v___y_3548_ = v___x_3579_;
goto v___jp_3547_;
}
}
v___jp_3547_:
{
lean_object* v_userData_3549_; lean_object* v_outputData_3550_; lean_object* v_state_3551_; lean_object* v_knownSize_3552_; lean_object* v_messageHead_3553_; uint8_t v_sentMessage_3554_; uint8_t v_userClosedBody_3555_; uint8_t v_omitBody_3556_; lean_object* v_userDataBytes_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3569_; 
v_userData_3549_ = lean_ctor_get(v_writer_3536_, 0);
v_outputData_3550_ = lean_ctor_get(v_writer_3536_, 1);
v_state_3551_ = lean_ctor_get(v_writer_3536_, 2);
v_knownSize_3552_ = lean_ctor_get(v_writer_3536_, 3);
v_messageHead_3553_ = lean_ctor_get(v_writer_3536_, 4);
v_sentMessage_3554_ = lean_ctor_get_uint8(v_writer_3536_, sizeof(void*)*6);
v_userClosedBody_3555_ = lean_ctor_get_uint8(v_writer_3536_, sizeof(void*)*6 + 1);
v_omitBody_3556_ = lean_ctor_get_uint8(v_writer_3536_, sizeof(void*)*6 + 2);
v_userDataBytes_3557_ = lean_ctor_get(v_writer_3536_, 5);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_writer_3536_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3559_ = v_writer_3536_;
v_isShared_3560_ = v_isSharedCheck_3569_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_userDataBytes_3557_);
lean_inc(v_messageHead_3553_);
lean_inc(v_knownSize_3552_);
lean_inc(v_state_3551_);
lean_inc(v_outputData_3550_);
lean_inc(v_userData_3549_);
lean_dec(v_writer_3536_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3569_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3561_ = l_Array_append___redArg(v_userData_3549_, v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3562_ = lean_nat_add(v_userDataBytes_3557_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec(v_userDataBytes_3557_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 5, v___x_3562_);
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3564_ = v___x_3559_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_outputData_3550_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_state_3551_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_knownSize_3552_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_messageHead_3553_);
lean_ctor_set(v_reuseFailAlloc_3568_, 5, v___x_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3568_, sizeof(void*)*6, v_sentMessage_3554_);
lean_ctor_set_uint8(v_reuseFailAlloc_3568_, sizeof(void*)*6 + 1, v_userClosedBody_3555_);
lean_ctor_set_uint8(v_reuseFailAlloc_3568_, sizeof(void*)*6 + 2, v_omitBody_3556_);
v___x_3564_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3566_; 
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v___x_3564_);
v___x_3566_ = v___x_3545_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_reader_3535_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_config_3537_);
lean_ctor_set(v_reuseFailAlloc_3567_, 3, v_events_3538_);
lean_ctor_set(v_reuseFailAlloc_3567_, 4, v_error_3539_);
lean_ctor_set(v_reuseFailAlloc_3567_, 5, v_instant_3540_);
lean_ctor_set_uint8(v_reuseFailAlloc_3567_, sizeof(void*)*6, v_keepAlive_3541_);
lean_ctor_set_uint8(v_reuseFailAlloc_3567_, sizeof(void*)*6 + 1, v_forcedFlush_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3567_, sizeof(void*)*6 + 2, v_pullBodyStalled_3543_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
v___y_3516_ = v___x_3566_;
goto v___jp_3515_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3531_);
v___y_3516_ = v_machine_3501_;
goto v___jp_3515_;
}
v___jp_3515_:
{
lean_object* v___x_3518_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___y_3516_);
v___x_3518_ = v___x_3513_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___y_3516_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_requestStream_3502_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_keepAliveTimeout_3503_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_currentTimeout_3504_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v_headerTimeout_3505_);
lean_ctor_set(v_reuseFailAlloc_3528_, 5, v_response_3506_);
lean_ctor_set(v_reuseFailAlloc_3528_, 6, v_respStream_3507_);
lean_ctor_set(v_reuseFailAlloc_3528_, 7, v_expectData_3509_);
lean_ctor_set(v_reuseFailAlloc_3528_, 8, v_pendingHead_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*9, v_requiresData_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*9 + 1, v_handlerDispatched_3510_);
v___x_3518_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3519_ = 0;
v___x_3520_ = lean_box(v___x_3519_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3518_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3521_);
v___x_3523_ = v___x_3499_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3523_);
v___x_3525_ = v___x_3470_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
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
uint8_t v_x_3584_; 
lean_dec_ref(v_config_3356_);
lean_dec_ref(v_inst_3354_);
v_x_3584_ = lean_ctor_get_uint8(v_event_3357_, 0);
lean_dec_ref_known(v_event_3357_, 0);
if (v_x_3584_ == 0)
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3353_);
v___x_3585_ = lean_box(v_x_3584_);
v___x_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3586_, 0, v_state_3358_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
else
{
lean_object* v_machine_3589_; lean_object* v_requestStream_3590_; lean_object* v_keepAliveTimeout_3591_; lean_object* v_currentTimeout_3592_; lean_object* v_headerTimeout_3593_; lean_object* v_response_3594_; lean_object* v_respStream_3595_; uint8_t v_requiresData_3596_; lean_object* v_expectData_3597_; uint8_t v_handlerDispatched_3598_; lean_object* v_pendingHead_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3649_; 
v_machine_3589_ = lean_ctor_get(v_state_3358_, 0);
v_requestStream_3590_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3591_ = lean_ctor_get(v_state_3358_, 2);
v_currentTimeout_3592_ = lean_ctor_get(v_state_3358_, 3);
v_headerTimeout_3593_ = lean_ctor_get(v_state_3358_, 4);
v_response_3594_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3595_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3596_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3597_ = lean_ctor_get(v_state_3358_, 7);
v_handlerDispatched_3598_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9 + 1);
v_pendingHead_3599_ = lean_ctor_get(v_state_3358_, 8);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3601_ = v_state_3358_;
v_isShared_3602_ = v_isSharedCheck_3649_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_pendingHead_3599_);
lean_inc(v_expectData_3597_);
lean_inc(v_respStream_3595_);
lean_inc(v_response_3594_);
lean_inc(v_headerTimeout_3593_);
lean_inc(v_currentTimeout_3592_);
lean_inc(v_keepAliveTimeout_3591_);
lean_inc(v_requestStream_3590_);
lean_inc(v_machine_3589_);
lean_dec(v_state_3358_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3649_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v_fst_3605_; lean_object* v_snd_3606_; lean_object* v_reader_3607_; lean_object* v_writer_3608_; lean_object* v_config_3609_; lean_object* v_events_3610_; lean_object* v_error_3611_; lean_object* v_instant_3612_; uint8_t v_keepAlive_3613_; uint8_t v_forcedFlush_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3648_; 
v___x_3603_ = 0;
v___x_3604_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3603_, v_machine_3589_);
v_fst_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_fst_3605_);
v_snd_3606_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_snd_3606_);
lean_dec_ref(v___x_3604_);
v_reader_3607_ = lean_ctor_get(v_fst_3605_, 0);
v_writer_3608_ = lean_ctor_get(v_fst_3605_, 1);
v_config_3609_ = lean_ctor_get(v_fst_3605_, 2);
v_events_3610_ = lean_ctor_get(v_fst_3605_, 3);
v_error_3611_ = lean_ctor_get(v_fst_3605_, 4);
v_instant_3612_ = lean_ctor_get(v_fst_3605_, 5);
v_keepAlive_3613_ = lean_ctor_get_uint8(v_fst_3605_, sizeof(void*)*6);
v_forcedFlush_3614_ = lean_ctor_get_uint8(v_fst_3605_, sizeof(void*)*6 + 1);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_fst_3605_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3616_ = v_fst_3605_;
v_isShared_3617_ = v_isSharedCheck_3648_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_instant_3612_);
lean_inc(v_error_3611_);
lean_inc(v_events_3610_);
lean_inc(v_config_3609_);
lean_inc(v_writer_3608_);
lean_inc(v_reader_3607_);
lean_dec(v_fst_3605_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3648_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___f_3618_; lean_object* v___f_3619_; uint8_t v___y_3621_; 
v___f_3618_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3618_, 0, v_inst_3353_);
lean_closure_set(v___f_3618_, 1, v_handler_3355_);
v___f_3619_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3606_) == 0)
{
uint8_t v_sentMessage_3644_; 
v_sentMessage_3644_ = lean_ctor_get_uint8(v_writer_3608_, sizeof(void*)*6);
if (v_sentMessage_3644_ == 0)
{
lean_object* v_state_3645_; 
v_state_3645_ = lean_ctor_get(v_reader_3607_, 0);
if (lean_obj_tag(v_state_3645_) == 2)
{
v___y_3621_ = v_x_3584_;
goto v___jp_3620_;
}
else
{
v___y_3621_ = v_sentMessage_3644_;
goto v___jp_3620_;
}
}
else
{
uint8_t v___x_3646_; 
v___x_3646_ = 0;
v___y_3621_ = v___x_3646_;
goto v___jp_3620_;
}
}
else
{
uint8_t v___x_3647_; 
v___x_3647_ = 0;
v___y_3621_ = v___x_3647_;
goto v___jp_3620_;
}
v___jp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3617_ == 0)
{
v___x_3623_ = v___x_3616_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_reader_3607_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_writer_3608_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_config_3609_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_events_3610_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_error_3611_);
lean_ctor_set(v_reuseFailAlloc_3643_, 5, v_instant_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3643_, sizeof(void*)*6, v_keepAlive_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3643_, sizeof(void*)*6 + 1, v_forcedFlush_3614_);
v___x_3623_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v_st_3625_; 
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*6 + 2, v___y_3621_);
lean_inc_ref(v_requestStream_3590_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3623_);
v_st_3625_ = v___x_3601_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_requestStream_3590_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_keepAliveTimeout_3591_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v_currentTimeout_3592_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v_headerTimeout_3593_);
lean_ctor_set(v_reuseFailAlloc_3642_, 5, v_response_3594_);
lean_ctor_set(v_reuseFailAlloc_3642_, 6, v_respStream_3595_);
lean_ctor_set(v_reuseFailAlloc_3642_, 7, v_expectData_3597_);
lean_ctor_set(v_reuseFailAlloc_3642_, 8, v_pendingHead_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3642_, sizeof(void*)*9, v_requiresData_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3642_, sizeof(void*)*9 + 1, v_handlerDispatched_3598_);
v_st_3625_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___f_3626_; 
lean_inc_ref(v_st_3625_);
v___f_3626_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3626_, 0, v_st_3625_);
if (lean_obj_tag(v_snd_3606_) == 1)
{
lean_object* v_val_3627_; uint8_t v_final_3628_; uint8_t v_incomplete_3629_; lean_object* v_chunk_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___f_3635_; lean_object* v___f_3636_; lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___x_3639_; 
lean_dec_ref(v_st_3625_);
v_val_3627_ = lean_ctor_get(v_snd_3606_, 0);
lean_inc(v_val_3627_);
lean_dec_ref_known(v_snd_3606_, 1);
v_final_3628_ = lean_ctor_get_uint8(v_val_3627_, sizeof(void*)*1);
v_incomplete_3629_ = lean_ctor_get_uint8(v_val_3627_, sizeof(void*)*1 + 1);
v_chunk_3630_ = lean_ctor_get(v_val_3627_, 0);
lean_inc_ref(v_chunk_3630_);
lean_dec(v_val_3627_);
lean_inc_ref_n(v_requestStream_3590_, 2);
v___x_3631_ = l_Std_Http_Body_Stream_send(v_requestStream_3590_, v_chunk_3630_, v_incomplete_3629_);
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = 0;
v___x_3634_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3632_, v___x_3633_, v___x_3631_, v___f_3618_);
lean_inc_ref_n(v___f_3626_, 2);
v___f_3635_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3635_, 0, v___f_3626_);
v___f_3636_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3636_, 0, v_requestStream_3590_);
lean_closure_set(v___f_3636_, 1, v___f_3635_);
lean_closure_set(v___f_3636_, 2, v___f_3626_);
v___x_3637_ = lean_box(v_final_3628_);
v___f_3638_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3638_, 0, v___x_3637_);
lean_closure_set(v___f_3638_, 1, v___f_3626_);
lean_closure_set(v___f_3638_, 2, v___f_3619_);
lean_closure_set(v___f_3638_, 3, v_requestStream_3590_);
lean_closure_set(v___f_3638_, 4, v___f_3636_);
v___x_3639_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3632_, v___x_3633_, v___x_3634_, v___f_3638_);
return v___x_3639_;
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec_ref(v___f_3626_);
lean_dec_ref(v___f_3618_);
lean_dec(v_snd_3606_);
lean_dec_ref(v_requestStream_3590_);
v___x_3640_ = lean_box(0);
v___x_3641_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3625_, v___x_3640_);
return v___x_3641_;
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
lean_object* v_x_3650_; 
v_x_3650_ = lean_ctor_get(v_event_3357_, 0);
lean_inc_ref(v_x_3650_);
lean_dec_ref_known(v_event_3357_, 1);
if (lean_obj_tag(v_x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v_onFailure_3652_; lean_object* v___x_3653_; lean_object* v___f_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; lean_object* v___x_3657_; 
lean_dec_ref(v_config_3356_);
lean_dec_ref(v_inst_3354_);
v_a_3651_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v_x_3650_, 1);
v_onFailure_3652_ = lean_ctor_get(v_inst_3353_, 2);
lean_inc_ref(v_onFailure_3652_);
lean_dec_ref(v_inst_3353_);
v___x_3653_ = lean_apply_3(v_onFailure_3652_, v_handler_3355_, v_a_3651_, lean_box(0));
v___f_3654_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3654_, 0, v_state_3358_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = 0;
v___x_3657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3655_, v___x_3656_, v___x_3653_, v___f_3654_);
return v___x_3657_;
}
else
{
lean_object* v_machine_3658_; lean_object* v_reader_3659_; lean_object* v_state_3660_; 
v_machine_3658_ = lean_ctor_get(v_state_3358_, 0);
lean_inc_ref(v_machine_3658_);
v_reader_3659_ = lean_ctor_get(v_machine_3658_, 0);
v_state_3660_ = lean_ctor_get(v_reader_3659_, 0);
if (lean_obj_tag(v_state_3660_) == 7)
{
lean_object* v_a_3661_; lean_object* v_requestStream_3662_; lean_object* v_keepAliveTimeout_3663_; lean_object* v_currentTimeout_3664_; lean_object* v_headerTimeout_3665_; lean_object* v_response_3666_; lean_object* v_respStream_3667_; uint8_t v_requiresData_3668_; lean_object* v_expectData_3669_; lean_object* v_pendingHead_3670_; lean_object* v_close_3671_; lean_object* v_isClosed_3672_; lean_object* v_body_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___f_3676_; lean_object* v___f_3677_; lean_object* v___f_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3353_);
v_a_3661_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v_x_3650_, 1);
v_requestStream_3662_ = lean_ctor_get(v_state_3358_, 1);
lean_inc_ref(v_requestStream_3662_);
v_keepAliveTimeout_3663_ = lean_ctor_get(v_state_3358_, 2);
lean_inc(v_keepAliveTimeout_3663_);
v_currentTimeout_3664_ = lean_ctor_get(v_state_3358_, 3);
lean_inc(v_currentTimeout_3664_);
v_headerTimeout_3665_ = lean_ctor_get(v_state_3358_, 4);
lean_inc(v_headerTimeout_3665_);
v_response_3666_ = lean_ctor_get(v_state_3358_, 5);
lean_inc_ref(v_response_3666_);
v_respStream_3667_ = lean_ctor_get(v_state_3358_, 6);
lean_inc(v_respStream_3667_);
v_requiresData_3668_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3669_ = lean_ctor_get(v_state_3358_, 7);
lean_inc(v_expectData_3669_);
v_pendingHead_3670_ = lean_ctor_get(v_state_3358_, 8);
lean_inc(v_pendingHead_3670_);
lean_dec_ref(v_state_3358_);
v_close_3671_ = lean_ctor_get(v_inst_3354_, 1);
lean_inc_ref(v_close_3671_);
v_isClosed_3672_ = lean_ctor_get(v_inst_3354_, 2);
lean_inc_ref(v_isClosed_3672_);
lean_dec_ref(v_inst_3354_);
v_body_3673_ = lean_ctor_get(v_a_3661_, 1);
lean_inc_n(v_body_3673_, 2);
lean_dec(v_a_3661_);
v___x_3674_ = lean_apply_2(v_isClosed_3672_, v_body_3673_, lean_box(0));
v___x_3675_ = lean_box(v_requiresData_3668_);
v___f_3676_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3676_, 0, v_machine_3658_);
lean_closure_set(v___f_3676_, 1, v_requestStream_3662_);
lean_closure_set(v___f_3676_, 2, v_keepAliveTimeout_3663_);
lean_closure_set(v___f_3676_, 3, v_currentTimeout_3664_);
lean_closure_set(v___f_3676_, 4, v_headerTimeout_3665_);
lean_closure_set(v___f_3676_, 5, v_response_3666_);
lean_closure_set(v___f_3676_, 6, v_respStream_3667_);
lean_closure_set(v___f_3676_, 7, v___x_3675_);
lean_closure_set(v___f_3676_, 8, v_expectData_3669_);
lean_closure_set(v___f_3676_, 9, v_pendingHead_3670_);
lean_inc_ref(v___f_3676_);
v___f_3677_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3677_, 0, v___f_3676_);
v___f_3678_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3678_, 0, v_close_3671_);
lean_closure_set(v___f_3678_, 1, v_body_3673_);
lean_closure_set(v___f_3678_, 2, v___f_3677_);
lean_closure_set(v___f_3678_, 3, v___f_3676_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = 0;
v___x_3681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3679_, v___x_3680_, v___x_3674_, v___f_3678_);
return v___x_3681_;
}
else
{
lean_object* v_a_3682_; lean_object* v_requestStream_3683_; lean_object* v_keepAliveTimeout_3684_; lean_object* v_currentTimeout_3685_; lean_object* v_headerTimeout_3686_; lean_object* v_response_3687_; uint8_t v_requiresData_3688_; lean_object* v_expectData_3689_; lean_object* v_pendingHead_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_a_3682_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v_x_3650_, 1);
v_requestStream_3683_ = lean_ctor_get(v_state_3358_, 1);
lean_inc_ref(v_requestStream_3683_);
v_keepAliveTimeout_3684_ = lean_ctor_get(v_state_3358_, 2);
lean_inc(v_keepAliveTimeout_3684_);
v_currentTimeout_3685_ = lean_ctor_get(v_state_3358_, 3);
lean_inc(v_currentTimeout_3685_);
v_headerTimeout_3686_ = lean_ctor_get(v_state_3358_, 4);
lean_inc(v_headerTimeout_3686_);
v_response_3687_ = lean_ctor_get(v_state_3358_, 5);
lean_inc_ref(v_response_3687_);
v_requiresData_3688_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3689_ = lean_ctor_get(v_state_3358_, 7);
lean_inc(v_expectData_3689_);
v_pendingHead_3690_ = lean_ctor_get(v_state_3358_, 8);
lean_inc(v_pendingHead_3690_);
lean_dec_ref(v_state_3358_);
lean_inc_ref(v_inst_3354_);
v___x_3691_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3354_, v_config_3356_, v_machine_3658_, v_a_3682_);
v___x_3692_ = 0;
v___x_3693_ = lean_box(v_requiresData_3688_);
v___x_3694_ = lean_box(v___x_3692_);
v___f_3695_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3695_, 0, v_requestStream_3683_);
lean_closure_set(v___f_3695_, 1, v_keepAliveTimeout_3684_);
lean_closure_set(v___f_3695_, 2, v_currentTimeout_3685_);
lean_closure_set(v___f_3695_, 3, v_headerTimeout_3686_);
lean_closure_set(v___f_3695_, 4, v_response_3687_);
lean_closure_set(v___f_3695_, 5, v___x_3693_);
lean_closure_set(v___f_3695_, 6, v_expectData_3689_);
lean_closure_set(v___f_3695_, 7, v___x_3694_);
lean_closure_set(v___f_3695_, 8, v_pendingHead_3690_);
v___f_3696_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3696_, 0, v___f_3695_);
v___f_3697_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3698_ = 1;
v___x_3699_ = lean_box(v___x_3692_);
v___x_3700_ = lean_box(v___x_3698_);
lean_inc_ref(v___f_3696_);
v___f_3701_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3701_, 0, v___x_3699_);
lean_closure_set(v___f_3701_, 1, v___f_3696_);
lean_closure_set(v___f_3701_, 2, v_inst_3354_);
lean_closure_set(v___f_3701_, 3, v___f_3697_);
lean_closure_set(v___f_3701_, 4, v___x_3700_);
lean_closure_set(v___f_3701_, 5, v_inst_3353_);
lean_closure_set(v___f_3701_, 6, v_handler_3355_);
lean_closure_set(v___f_3701_, 7, v___f_3696_);
v___x_3702_ = lean_unsigned_to_nat(0u);
v___x_3703_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3702_, v___x_3692_, v___x_3691_, v___f_3701_);
return v___x_3703_;
}
}
}
case 4:
{
lean_object* v_onFailure_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
lean_dec_ref(v_config_3356_);
lean_dec_ref(v_inst_3354_);
v_onFailure_3704_ = lean_ctor_get(v_inst_3353_, 2);
lean_inc_ref(v_onFailure_3704_);
lean_dec_ref(v_inst_3353_);
v___x_3705_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3706_ = lean_apply_3(v_onFailure_3704_, v_handler_3355_, v___x_3705_, lean_box(0));
v___f_3707_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3707_, 0, v_state_3358_);
v___x_3708_ = lean_unsigned_to_nat(0u);
v___x_3709_ = 0;
v___x_3710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3708_, v___x_3709_, v___x_3706_, v___f_3707_);
return v___x_3710_;
}
case 5:
{
lean_object* v_machine_3711_; lean_object* v_requestStream_3712_; lean_object* v_keepAliveTimeout_3713_; lean_object* v_currentTimeout_3714_; lean_object* v_headerTimeout_3715_; lean_object* v_response_3716_; lean_object* v_respStream_3717_; uint8_t v_requiresData_3718_; lean_object* v_expectData_3719_; lean_object* v_pendingHead_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3734_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3354_);
lean_dec_ref(v_inst_3353_);
v_machine_3711_ = lean_ctor_get(v_state_3358_, 0);
v_requestStream_3712_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3713_ = lean_ctor_get(v_state_3358_, 2);
v_currentTimeout_3714_ = lean_ctor_get(v_state_3358_, 3);
v_headerTimeout_3715_ = lean_ctor_get(v_state_3358_, 4);
v_response_3716_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3717_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3718_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3719_ = lean_ctor_get(v_state_3358_, 7);
v_pendingHead_3720_ = lean_ctor_get(v_state_3358_, 8);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3722_ = v_state_3358_;
v_isShared_3723_ = v_isSharedCheck_3734_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_pendingHead_3720_);
lean_inc(v_expectData_3719_);
lean_inc(v_respStream_3717_);
lean_inc(v_response_3716_);
lean_inc(v_headerTimeout_3715_);
lean_inc(v_currentTimeout_3714_);
lean_inc(v_keepAliveTimeout_3713_);
lean_inc(v_requestStream_3712_);
lean_inc(v_machine_3711_);
lean_dec(v_state_3358_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3734_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3728_; 
v___x_3724_ = lean_box(55);
v___x_3725_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3711_, v___x_3724_);
v___x_3726_ = 0;
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3725_);
v___x_3728_ = v___x_3722_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_requestStream_3712_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_keepAliveTimeout_3713_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_currentTimeout_3714_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_headerTimeout_3715_);
lean_ctor_set(v_reuseFailAlloc_3733_, 5, v_response_3716_);
lean_ctor_set(v_reuseFailAlloc_3733_, 6, v_respStream_3717_);
lean_ctor_set(v_reuseFailAlloc_3733_, 7, v_expectData_3719_);
lean_ctor_set(v_reuseFailAlloc_3733_, 8, v_pendingHead_3720_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*9, v_requiresData_3718_);
v___x_3728_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_ctor_set_uint8(v___x_3728_, sizeof(void*)*9 + 1, v___x_3726_);
v___x_3729_ = lean_box(v___x_3726_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
}
default: 
{
uint8_t v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3354_);
lean_dec_ref(v_inst_3353_);
v___x_3735_ = 1;
v___x_3736_ = lean_box(v___x_3735_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v_state_3358_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3740_, lean_object* v_inst_3741_, lean_object* v_handler_3742_, lean_object* v_config_3743_, lean_object* v_event_3744_, lean_object* v_state_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3740_, v_inst_3741_, v_handler_3742_, v_config_3743_, v_event_3744_, v_state_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3748_, lean_object* v_00_u03b2_3749_, lean_object* v_inst_3750_, lean_object* v_inst_3751_, lean_object* v_handler_3752_, lean_object* v_config_3753_, lean_object* v_event_3754_, lean_object* v_state_3755_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3750_, v_inst_3751_, v_handler_3752_, v_config_3753_, v_event_3754_, v_state_3755_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3758_, lean_object* v_00_u03b2_3759_, lean_object* v_inst_3760_, lean_object* v_inst_3761_, lean_object* v_handler_3762_, lean_object* v_config_3763_, lean_object* v_event_3764_, lean_object* v_state_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3758_, v_00_u03b2_3759_, v_inst_3760_, v_inst_3761_, v_handler_3762_, v_config_3763_, v_event_3764_, v_state_3765_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3768_, uint8_t v_handlerDispatched_3769_, lean_object* v_respStream_3770_, lean_object* v_headerTimeout_3771_, lean_object* v_keepAliveTimeout_3772_, lean_object* v_expectData_3773_, lean_object* v_currentTimeout_3774_, lean_object* v_response_3775_, lean_object* v_socket_3776_, uint8_t v_requiresData_3777_, uint8_t v_sentMessage_3778_, lean_object* v_reader_3779_, uint8_t v_requestBodyInterested_3780_, lean_object* v_requestBody_3781_){
_start:
{
lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3795_; 
if (v_requiresData_3777_ == 0)
{
if (v_handlerDispatched_3769_ == 0)
{
goto v___jp_3798_;
}
else
{
if (lean_obj_tag(v_respStream_3770_) == 0)
{
if (v_sentMessage_3778_ == 0)
{
lean_object* v_state_3802_; 
v_state_3802_ = lean_ctor_get(v_reader_3779_, 0);
if (lean_obj_tag(v_state_3802_) == 2)
{
if (v_requestBodyInterested_3780_ == 0)
{
lean_dec(v_socket_3776_);
goto v___jp_3800_;
}
else
{
goto v___jp_3798_;
}
}
else
{
lean_dec(v_socket_3776_);
goto v___jp_3800_;
}
}
else
{
goto v___jp_3798_;
}
}
else
{
goto v___jp_3798_;
}
}
}
else
{
goto v___jp_3798_;
}
v___jp_3783_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3791_, 0, v___y_3784_);
lean_ctor_set(v___x_3791_, 1, v___y_3788_);
lean_ctor_set(v___x_3791_, 2, v___y_3790_);
lean_ctor_set(v___x_3791_, 3, v___y_3785_);
lean_ctor_set(v___x_3791_, 4, v_requestBody_3781_);
lean_ctor_set(v___x_3791_, 5, v___y_3789_);
lean_ctor_set(v___x_3791_, 6, v___y_3787_);
lean_ctor_set(v___x_3791_, 7, v___y_3786_);
lean_ctor_set(v___x_3791_, 8, v_connectionContext_3768_);
v___x_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
v___jp_3794_:
{
if (v_handlerDispatched_3769_ == 0)
{
lean_object* v___x_3796_; 
lean_dec_ref(v_response_3775_);
v___x_3796_ = lean_box(0);
v___y_3784_ = v___y_3795_;
v___y_3785_ = v_respStream_3770_;
v___y_3786_ = v_headerTimeout_3771_;
v___y_3787_ = v_keepAliveTimeout_3772_;
v___y_3788_ = v_expectData_3773_;
v___y_3789_ = v_currentTimeout_3774_;
v___y_3790_ = v___x_3796_;
goto v___jp_3783_;
}
else
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_response_3775_);
v___y_3784_ = v___y_3795_;
v___y_3785_ = v_respStream_3770_;
v___y_3786_ = v_headerTimeout_3771_;
v___y_3787_ = v_keepAliveTimeout_3772_;
v___y_3788_ = v_expectData_3773_;
v___y_3789_ = v_currentTimeout_3774_;
v___y_3790_ = v___x_3797_;
goto v___jp_3783_;
}
}
v___jp_3798_:
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_socket_3776_);
v___y_3795_ = v___x_3799_;
goto v___jp_3794_;
}
v___jp_3800_:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_box(0);
v___y_3795_ = v___x_3801_;
goto v___jp_3794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3803_, lean_object* v_handlerDispatched_3804_, lean_object* v_respStream_3805_, lean_object* v_headerTimeout_3806_, lean_object* v_keepAliveTimeout_3807_, lean_object* v_expectData_3808_, lean_object* v_currentTimeout_3809_, lean_object* v_response_3810_, lean_object* v_socket_3811_, lean_object* v_requiresData_3812_, lean_object* v_sentMessage_3813_, lean_object* v_reader_3814_, lean_object* v_requestBodyInterested_3815_, lean_object* v_requestBody_3816_, lean_object* v___y_3817_){
_start:
{
uint8_t v_handlerDispatched_boxed_3818_; uint8_t v_requiresData_boxed_3819_; uint8_t v_sentMessage_boxed_3820_; uint8_t v_requestBodyInterested_boxed_3821_; lean_object* v_res_3822_; 
v_handlerDispatched_boxed_3818_ = lean_unbox(v_handlerDispatched_3804_);
v_requiresData_boxed_3819_ = lean_unbox(v_requiresData_3812_);
v_sentMessage_boxed_3820_ = lean_unbox(v_sentMessage_3813_);
v_requestBodyInterested_boxed_3821_ = lean_unbox(v_requestBodyInterested_3815_);
v_res_3822_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3803_, v_handlerDispatched_boxed_3818_, v_respStream_3805_, v_headerTimeout_3806_, v_keepAliveTimeout_3807_, v_expectData_3808_, v_currentTimeout_3809_, v_response_3810_, v_socket_3811_, v_requiresData_boxed_3819_, v_sentMessage_boxed_3820_, v_reader_3814_, v_requestBodyInterested_boxed_3821_, v_requestBody_3816_);
lean_dec_ref(v_reader_3814_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3823_, lean_object* v_x_3824_){
_start:
{
if (lean_obj_tag(v_x_3824_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v___f_3823_);
v_a_3826_ = lean_ctor_get(v_x_3824_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_x_3824_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3828_ = v_x_3824_;
v_isShared_3829_ = v_isSharedCheck_3834_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v_x_3824_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3834_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3836_; 
v_a_3835_ = lean_ctor_get(v_x_3824_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v_x_3824_, 1);
v___x_3836_ = lean_apply_2(v___f_3823_, v_a_3835_, lean_box(0));
return v___x_3836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3837_, lean_object* v_x_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3837_, v_x_3838_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3845_, uint8_t v_handlerDispatched_3846_, lean_object* v_respStream_3847_, lean_object* v_headerTimeout_3848_, lean_object* v_keepAliveTimeout_3849_, lean_object* v_expectData_3850_, lean_object* v_currentTimeout_3851_, lean_object* v_response_3852_, lean_object* v_socket_3853_, uint8_t v_requiresData_3854_, uint8_t v_sentMessage_3855_, lean_object* v_reader_3856_, uint8_t v_pullBodyStalled_3857_, uint8_t v_requestBodyOpen_3858_, lean_object* v_requestStream_3859_, uint8_t v_requestBodyInterested_3860_){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___f_3866_; lean_object* v___f_3867_; 
v___x_3862_ = lean_box(v_handlerDispatched_3846_);
v___x_3863_ = lean_box(v_requiresData_3854_);
v___x_3864_ = lean_box(v_sentMessage_3855_);
v___x_3865_ = lean_box(v_requestBodyInterested_3860_);
lean_inc_ref(v_reader_3856_);
v___f_3866_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3866_, 0, v_connectionContext_3845_);
lean_closure_set(v___f_3866_, 1, v___x_3862_);
lean_closure_set(v___f_3866_, 2, v_respStream_3847_);
lean_closure_set(v___f_3866_, 3, v_headerTimeout_3848_);
lean_closure_set(v___f_3866_, 4, v_keepAliveTimeout_3849_);
lean_closure_set(v___f_3866_, 5, v_expectData_3850_);
lean_closure_set(v___f_3866_, 6, v_currentTimeout_3851_);
lean_closure_set(v___f_3866_, 7, v_response_3852_);
lean_closure_set(v___f_3866_, 8, v_socket_3853_);
lean_closure_set(v___f_3866_, 9, v___x_3863_);
lean_closure_set(v___f_3866_, 10, v___x_3864_);
lean_closure_set(v___f_3866_, 11, v_reader_3856_);
lean_closure_set(v___f_3866_, 12, v___x_3865_);
v___f_3867_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3867_, 0, v___f_3866_);
if (v_sentMessage_3855_ == 0)
{
lean_object* v_state_3873_; 
v_state_3873_ = lean_ctor_get(v_reader_3856_, 0);
lean_inc(v_state_3873_);
lean_dec_ref(v_reader_3856_);
if (lean_obj_tag(v_state_3873_) == 2)
{
lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3884_; 
v_isSharedCheck_3884_ = !lean_is_exclusive(v_state_3873_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; 
v_unused_3885_ = lean_ctor_get(v_state_3873_, 0);
lean_dec(v_unused_3885_);
v___x_3875_ = v_state_3873_;
v_isShared_3876_ = v_isSharedCheck_3884_;
goto v_resetjp_3874_;
}
else
{
lean_dec(v_state_3873_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3884_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
if (v_pullBodyStalled_3857_ == 0)
{
if (v_requestBodyOpen_3858_ == 0)
{
lean_del_object(v___x_3875_);
lean_dec_ref(v_requestStream_3859_);
goto v___jp_3868_;
}
else
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 1);
lean_ctor_set(v___x_3875_, 0, v_requestStream_3859_);
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_requestStream_3859_);
v___x_3878_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3881_, v_pullBodyStalled_3857_, v___x_3880_, v___f_3867_);
return v___x_3882_;
}
}
}
else
{
lean_del_object(v___x_3875_);
lean_dec_ref(v_requestStream_3859_);
goto v___jp_3868_;
}
}
}
else
{
lean_dec(v_state_3873_);
lean_dec_ref(v_requestStream_3859_);
goto v___jp_3868_;
}
}
else
{
lean_dec_ref(v_requestStream_3859_);
lean_dec_ref(v_reader_3856_);
goto v___jp_3868_;
}
v___jp_3868_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; 
v___x_3869_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3870_ = lean_unsigned_to_nat(0u);
v___x_3871_ = 0;
v___x_3872_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3870_, v___x_3871_, v___x_3869_, v___f_3867_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3886_ = _args[0];
lean_object* v_handlerDispatched_3887_ = _args[1];
lean_object* v_respStream_3888_ = _args[2];
lean_object* v_headerTimeout_3889_ = _args[3];
lean_object* v_keepAliveTimeout_3890_ = _args[4];
lean_object* v_expectData_3891_ = _args[5];
lean_object* v_currentTimeout_3892_ = _args[6];
lean_object* v_response_3893_ = _args[7];
lean_object* v_socket_3894_ = _args[8];
lean_object* v_requiresData_3895_ = _args[9];
lean_object* v_sentMessage_3896_ = _args[10];
lean_object* v_reader_3897_ = _args[11];
lean_object* v_pullBodyStalled_3898_ = _args[12];
lean_object* v_requestBodyOpen_3899_ = _args[13];
lean_object* v_requestStream_3900_ = _args[14];
lean_object* v_requestBodyInterested_3901_ = _args[15];
lean_object* v___y_3902_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3903_; uint8_t v_requiresData_boxed_3904_; uint8_t v_sentMessage_boxed_3905_; uint8_t v_pullBodyStalled_boxed_3906_; uint8_t v_requestBodyOpen_boxed_3907_; uint8_t v_requestBodyInterested_boxed_3908_; lean_object* v_res_3909_; 
v_handlerDispatched_boxed_3903_ = lean_unbox(v_handlerDispatched_3887_);
v_requiresData_boxed_3904_ = lean_unbox(v_requiresData_3895_);
v_sentMessage_boxed_3905_ = lean_unbox(v_sentMessage_3896_);
v_pullBodyStalled_boxed_3906_ = lean_unbox(v_pullBodyStalled_3898_);
v_requestBodyOpen_boxed_3907_ = lean_unbox(v_requestBodyOpen_3899_);
v_requestBodyInterested_boxed_3908_ = lean_unbox(v_requestBodyInterested_3901_);
v_res_3909_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3886_, v_handlerDispatched_boxed_3903_, v_respStream_3888_, v_headerTimeout_3889_, v_keepAliveTimeout_3890_, v_expectData_3891_, v_currentTimeout_3892_, v_response_3893_, v_socket_3894_, v_requiresData_boxed_3904_, v_sentMessage_boxed_3905_, v_reader_3897_, v_pullBodyStalled_boxed_3906_, v_requestBodyOpen_boxed_3907_, v_requestStream_3900_, v_requestBodyInterested_boxed_3908_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3910_, lean_object* v_x_3911_){
_start:
{
if (lean_obj_tag(v_x_3911_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref(v___f_3910_);
v_a_3913_ = lean_ctor_get(v_x_3911_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_x_3911_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3915_ = v_x_3911_;
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v_x_3911_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
return v___x_3919_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3923_; 
v_a_3922_ = lean_ctor_get(v_x_3911_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v_x_3911_, 1);
v___x_3923_ = lean_apply_2(v___f_3910_, v_a_3922_, lean_box(0));
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3924_, lean_object* v_x_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3924_, v_x_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3933_, uint8_t v_handlerDispatched_3934_, lean_object* v_respStream_3935_, lean_object* v_headerTimeout_3936_, lean_object* v_keepAliveTimeout_3937_, lean_object* v_expectData_3938_, lean_object* v_currentTimeout_3939_, lean_object* v_response_3940_, lean_object* v_socket_3941_, uint8_t v_requiresData_3942_, uint8_t v_sentMessage_3943_, lean_object* v_reader_3944_, uint8_t v_pullBodyStalled_3945_, lean_object* v_requestStream_3946_, uint8_t v_requestBodyOpen_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___f_3954_; lean_object* v___f_3955_; 
v___x_3949_ = lean_box(v_handlerDispatched_3934_);
v___x_3950_ = lean_box(v_requiresData_3942_);
v___x_3951_ = lean_box(v_sentMessage_3943_);
v___x_3952_ = lean_box(v_pullBodyStalled_3945_);
v___x_3953_ = lean_box(v_requestBodyOpen_3947_);
lean_inc_ref(v_requestStream_3946_);
lean_inc_ref(v_reader_3944_);
v___f_3954_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3954_, 0, v_connectionContext_3933_);
lean_closure_set(v___f_3954_, 1, v___x_3949_);
lean_closure_set(v___f_3954_, 2, v_respStream_3935_);
lean_closure_set(v___f_3954_, 3, v_headerTimeout_3936_);
lean_closure_set(v___f_3954_, 4, v_keepAliveTimeout_3937_);
lean_closure_set(v___f_3954_, 5, v_expectData_3938_);
lean_closure_set(v___f_3954_, 6, v_currentTimeout_3939_);
lean_closure_set(v___f_3954_, 7, v_response_3940_);
lean_closure_set(v___f_3954_, 8, v_socket_3941_);
lean_closure_set(v___f_3954_, 9, v___x_3950_);
lean_closure_set(v___f_3954_, 10, v___x_3951_);
lean_closure_set(v___f_3954_, 11, v_reader_3944_);
lean_closure_set(v___f_3954_, 12, v___x_3952_);
lean_closure_set(v___f_3954_, 13, v___x_3953_);
lean_closure_set(v___f_3954_, 14, v_requestStream_3946_);
v___f_3955_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3955_, 0, v___f_3954_);
if (v_sentMessage_3943_ == 0)
{
lean_object* v_state_3961_; 
v_state_3961_ = lean_ctor_get(v_reader_3944_, 0);
lean_inc(v_state_3961_);
lean_dec_ref(v_reader_3944_);
if (lean_obj_tag(v_state_3961_) == 2)
{
lean_dec_ref_known(v_state_3961_, 1);
if (v_requestBodyOpen_3947_ == 0)
{
lean_dec_ref(v_requestStream_3946_);
goto v___jp_3956_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3946_);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3963_, v_sentMessage_3943_, v___x_3962_, v___f_3955_);
return v___x_3964_;
}
}
else
{
lean_dec(v_state_3961_);
lean_dec_ref(v_requestStream_3946_);
goto v___jp_3956_;
}
}
else
{
lean_dec_ref(v_requestStream_3946_);
lean_dec_ref(v_reader_3944_);
goto v___jp_3956_;
}
v___jp_3956_:
{
uint8_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3957_ = 0;
v___x_3958_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3959_ = lean_unsigned_to_nat(0u);
v___x_3960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3959_, v___x_3957_, v___x_3958_, v___f_3955_);
return v___x_3960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3965_, lean_object* v_handlerDispatched_3966_, lean_object* v_respStream_3967_, lean_object* v_headerTimeout_3968_, lean_object* v_keepAliveTimeout_3969_, lean_object* v_expectData_3970_, lean_object* v_currentTimeout_3971_, lean_object* v_response_3972_, lean_object* v_socket_3973_, lean_object* v_requiresData_3974_, lean_object* v_sentMessage_3975_, lean_object* v_reader_3976_, lean_object* v_pullBodyStalled_3977_, lean_object* v_requestStream_3978_, lean_object* v_requestBodyOpen_3979_, lean_object* v___y_3980_){
_start:
{
uint8_t v_handlerDispatched_boxed_3981_; uint8_t v_requiresData_boxed_3982_; uint8_t v_sentMessage_boxed_3983_; uint8_t v_pullBodyStalled_boxed_3984_; uint8_t v_requestBodyOpen_boxed_3985_; lean_object* v_res_3986_; 
v_handlerDispatched_boxed_3981_ = lean_unbox(v_handlerDispatched_3966_);
v_requiresData_boxed_3982_ = lean_unbox(v_requiresData_3974_);
v_sentMessage_boxed_3983_ = lean_unbox(v_sentMessage_3975_);
v_pullBodyStalled_boxed_3984_ = lean_unbox(v_pullBodyStalled_3977_);
v_requestBodyOpen_boxed_3985_ = lean_unbox(v_requestBodyOpen_3979_);
v_res_3986_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3965_, v_handlerDispatched_boxed_3981_, v_respStream_3967_, v_headerTimeout_3968_, v_keepAliveTimeout_3969_, v_expectData_3970_, v_currentTimeout_3971_, v_response_3972_, v_socket_3973_, v_requiresData_boxed_3982_, v_sentMessage_boxed_3983_, v_reader_3976_, v_pullBodyStalled_boxed_3984_, v_requestStream_3978_, v_requestBodyOpen_boxed_3985_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3987_, lean_object* v___f_3988_, uint8_t v___x_3989_, lean_object* v_x_3990_){
_start:
{
uint8_t v___y_3993_; 
if (lean_obj_tag(v_x_3990_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v___f_3988_);
v_a_3999_ = lean_ctor_get(v_x_3990_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_x_3990_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4001_ = v_x_3990_;
v_isShared_4002_ = v_isSharedCheck_4007_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v_x_3990_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4007_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
return v___x_4005_;
}
}
}
else
{
lean_object* v_a_4008_; uint8_t v___x_4009_; 
v_a_4008_ = lean_ctor_get(v_x_3990_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v_x_3990_, 1);
v___x_4009_ = lean_unbox(v_a_4008_);
lean_dec(v_a_4008_);
if (v___x_4009_ == 0)
{
v___y_3993_ = v___x_3989_;
goto v___jp_3992_;
}
else
{
v___y_3993_ = v_sentMessage_3987_;
goto v___jp_3992_;
}
}
v___jp_3992_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3994_ = lean_box(v___y_3993_);
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
v___x_3997_ = lean_unsigned_to_nat(0u);
v___x_3998_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3997_, v_sentMessage_3987_, v___x_3996_, v___f_3988_);
return v___x_3998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4010_, lean_object* v___f_4011_, lean_object* v___x_4012_, lean_object* v_x_4013_, lean_object* v___y_4014_){
_start:
{
uint8_t v_sentMessage_boxed_4015_; uint8_t v___x_3791__boxed_4016_; lean_object* v_res_4017_; 
v_sentMessage_boxed_4015_ = lean_unbox(v_sentMessage_4010_);
v___x_3791__boxed_4016_ = lean_unbox(v___x_4012_);
v_res_4017_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4015_, v___f_4011_, v___x_3791__boxed_4016_, v_x_4013_);
return v_res_4017_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___f_4018_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4019_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4020_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4021_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4021_, 0, lean_box(0));
lean_closure_set(v___x_4021_, 1, lean_box(0));
lean_closure_set(v___x_4021_, 2, v___x_4020_);
lean_closure_set(v___x_4021_, 3, lean_box(0));
lean_closure_set(v___x_4021_, 4, lean_box(0));
lean_closure_set(v___x_4021_, 5, v___x_4019_);
lean_closure_set(v___x_4021_, 6, v___f_4018_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4022_, lean_object* v_connectionContext_4023_, lean_object* v_state_4024_){
_start:
{
lean_object* v_machine_4026_; lean_object* v_writer_4027_; lean_object* v_requestStream_4028_; lean_object* v_keepAliveTimeout_4029_; lean_object* v_currentTimeout_4030_; lean_object* v_headerTimeout_4031_; lean_object* v_response_4032_; lean_object* v_respStream_4033_; uint8_t v_requiresData_4034_; lean_object* v_expectData_4035_; uint8_t v_handlerDispatched_4036_; lean_object* v_reader_4037_; uint8_t v_pullBodyStalled_4038_; uint8_t v_sentMessage_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___f_4044_; lean_object* v___f_4045_; uint8_t v___y_4047_; 
v_machine_4026_ = lean_ctor_get(v_state_4024_, 0);
lean_inc_ref(v_machine_4026_);
v_writer_4027_ = lean_ctor_get(v_machine_4026_, 1);
lean_inc_ref(v_writer_4027_);
v_requestStream_4028_ = lean_ctor_get(v_state_4024_, 1);
lean_inc_ref_n(v_requestStream_4028_, 2);
v_keepAliveTimeout_4029_ = lean_ctor_get(v_state_4024_, 2);
lean_inc(v_keepAliveTimeout_4029_);
v_currentTimeout_4030_ = lean_ctor_get(v_state_4024_, 3);
lean_inc(v_currentTimeout_4030_);
v_headerTimeout_4031_ = lean_ctor_get(v_state_4024_, 4);
lean_inc(v_headerTimeout_4031_);
v_response_4032_ = lean_ctor_get(v_state_4024_, 5);
lean_inc_ref(v_response_4032_);
v_respStream_4033_ = lean_ctor_get(v_state_4024_, 6);
lean_inc(v_respStream_4033_);
v_requiresData_4034_ = lean_ctor_get_uint8(v_state_4024_, sizeof(void*)*9);
v_expectData_4035_ = lean_ctor_get(v_state_4024_, 7);
lean_inc(v_expectData_4035_);
v_handlerDispatched_4036_ = lean_ctor_get_uint8(v_state_4024_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4024_);
v_reader_4037_ = lean_ctor_get(v_machine_4026_, 0);
lean_inc_ref_n(v_reader_4037_, 2);
v_pullBodyStalled_4038_ = lean_ctor_get_uint8(v_machine_4026_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4026_);
v_sentMessage_4039_ = lean_ctor_get_uint8(v_writer_4027_, sizeof(void*)*6);
lean_dec_ref(v_writer_4027_);
v___x_4040_ = lean_box(v_handlerDispatched_4036_);
v___x_4041_ = lean_box(v_requiresData_4034_);
v___x_4042_ = lean_box(v_sentMessage_4039_);
v___x_4043_ = lean_box(v_pullBodyStalled_4038_);
v___f_4044_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4044_, 0, v_connectionContext_4023_);
lean_closure_set(v___f_4044_, 1, v___x_4040_);
lean_closure_set(v___f_4044_, 2, v_respStream_4033_);
lean_closure_set(v___f_4044_, 3, v_headerTimeout_4031_);
lean_closure_set(v___f_4044_, 4, v_keepAliveTimeout_4029_);
lean_closure_set(v___f_4044_, 5, v_expectData_4035_);
lean_closure_set(v___f_4044_, 6, v_currentTimeout_4030_);
lean_closure_set(v___f_4044_, 7, v_response_4032_);
lean_closure_set(v___f_4044_, 8, v_socket_4022_);
lean_closure_set(v___f_4044_, 9, v___x_4041_);
lean_closure_set(v___f_4044_, 10, v___x_4042_);
lean_closure_set(v___f_4044_, 11, v_reader_4037_);
lean_closure_set(v___f_4044_, 12, v___x_4043_);
lean_closure_set(v___f_4044_, 13, v_requestStream_4028_);
v___f_4045_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4045_, 0, v___f_4044_);
if (v_sentMessage_4039_ == 0)
{
lean_object* v_state_4053_; 
v_state_4053_ = lean_ctor_get(v_reader_4037_, 0);
lean_inc(v_state_4053_);
lean_dec_ref(v_reader_4037_);
if (lean_obj_tag(v_state_4053_) == 2)
{
lean_object* v___x_4054_; lean_object* v___f_4055_; lean_object* v___f_4056_; lean_object* v___x_4057_; lean_object* v___x_3305__overap_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_dec_ref_known(v_state_4053_, 1);
v___x_4054_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4055_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4056_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4057_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3305__overap_4058_ = l_Std_Mutex_atomically___redArg(v___x_4054_, v___f_4055_, v___f_4056_, v_requestStream_4028_, v___x_4057_);
v___x_4059_ = lean_apply_1(v___x_3305__overap_4058_, lean_box(0));
v___x_4060_ = 1;
v___x_4061_ = lean_box(v_sentMessage_4039_);
v___x_4062_ = lean_box(v___x_4060_);
v___f_4063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4063_, 0, v___x_4061_);
lean_closure_set(v___f_4063_, 1, v___f_4045_);
lean_closure_set(v___f_4063_, 2, v___x_4062_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4064_, v_sentMessage_4039_, v___x_4059_, v___f_4063_);
return v___x_4065_;
}
else
{
lean_dec(v_state_4053_);
lean_dec_ref(v_requestStream_4028_);
v___y_4047_ = v_sentMessage_4039_;
goto v___jp_4046_;
}
}
else
{
uint8_t v___x_4066_; 
lean_dec_ref(v_reader_4037_);
lean_dec_ref(v_requestStream_4028_);
v___x_4066_ = 0;
v___y_4047_ = v___x_4066_;
goto v___jp_4046_;
}
v___jp_4046_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4048_ = lean_box(v___y_4047_);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4051_, v___y_4047_, v___x_4050_, v___f_4045_);
return v___x_4052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4067_, lean_object* v_connectionContext_4068_, lean_object* v_state_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4067_, v_connectionContext_4068_, v_state_4069_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4072_, lean_object* v_00_u03b2_4073_, lean_object* v_inst_4074_, lean_object* v_socket_4075_, lean_object* v_connectionContext_4076_, lean_object* v_state_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4075_, v_connectionContext_4076_, v_state_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4080_, lean_object* v_00_u03b2_4081_, lean_object* v_inst_4082_, lean_object* v_socket_4083_, lean_object* v_connectionContext_4084_, lean_object* v_state_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4080_, v_00_u03b2_4081_, v_inst_4082_, v_socket_4083_, v_connectionContext_4084_, v_state_4085_);
lean_dec_ref(v_inst_4082_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4088_){
_start:
{
if (lean_obj_tag(v_x_4088_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4098_; 
v_a_4090_ = lean_ctor_get(v_x_4088_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4092_ = v_x_4088_;
v_isShared_4093_ = v_isSharedCheck_4098_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v_x_4088_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4098_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
return v___x_4096_;
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4117_; 
v_a_4099_ = lean_ctor_get(v_x_4088_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4101_ = v_x_4088_;
v_isShared_4102_ = v_isSharedCheck_4117_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v_x_4088_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4117_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v_snd_4103_; uint8_t v___x_4104_; 
v_snd_4103_ = lean_ctor_get(v_a_4099_, 1);
v___x_4104_ = lean_unbox(v_snd_4103_);
if (v___x_4104_ == 0)
{
lean_object* v_fst_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v_fst_4105_ = lean_ctor_get(v_a_4099_, 0);
lean_inc(v_fst_4105_);
lean_dec(v_a_4099_);
v___x_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_fst_4105_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4106_);
v___x_4108_ = v___x_4101_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
else
{
lean_object* v_fst_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v_fst_4111_ = lean_ctor_get(v_a_4099_, 0);
lean_inc(v_fst_4111_);
lean_dec(v_a_4099_);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_fst_4111_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4112_);
v___x_4114_ = v___x_4101_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4112_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4121_){
_start:
{
if (lean_obj_tag(v_x_4121_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4131_; 
v_a_4123_ = lean_ctor_get(v_x_4121_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v_x_4121_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4125_ = v_x_4121_;
v_isShared_4126_ = v_isSharedCheck_4131_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v_x_4121_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4131_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
return v___x_4129_;
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4141_; 
v_a_4132_ = lean_ctor_get(v_x_4121_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_x_4121_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4134_ = v_x_4121_;
v_isShared_4135_ = v_isSharedCheck_4141_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v_x_4121_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4141_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_a_4132_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v___x_4136_);
v___x_4138_ = v___x_4134_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
return v___x_4139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4142_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4149_){
_start:
{
if (lean_obj_tag(v_x_4149_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4159_; 
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
lean_object* v___x_4160_; 
lean_dec_ref_known(v_x_4149_, 1);
v___x_4160_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4161_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4164_, lean_object* v_handler_4165_, lean_object* v___f_4166_, lean_object* v_x_4167_){
_start:
{
if (lean_obj_tag(v_x_4167_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; lean_object* v___x_4173_; 
v_a_4169_ = lean_ctor_get(v_x_4167_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v_x_4167_, 1);
v___x_4170_ = lean_apply_3(v_onFailure_4164_, v_handler_4165_, v_a_4169_, lean_box(0));
v___x_4171_ = lean_unsigned_to_nat(0u);
v___x_4172_ = 0;
v___x_4173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4171_, v___x_4172_, v___x_4170_, v___f_4166_);
return v___x_4173_;
}
else
{
lean_object* v___x_4174_; 
lean_dec_ref(v___f_4166_);
lean_dec(v_handler_4165_);
lean_dec_ref(v_onFailure_4164_);
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v_x_4167_);
return v___x_4174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4175_, lean_object* v_handler_4176_, lean_object* v___f_4177_, lean_object* v_x_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4175_, v_handler_4176_, v___f_4177_, v_x_4178_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4181_, lean_object* v_socket_4182_, lean_object* v_____r_4183_){
_start:
{
lean_object* v_val_4186_; lean_object* v_close_4188_; lean_object* v___x_4189_; 
v_close_4188_ = lean_ctor_get(v_inst_4181_, 3);
lean_inc_ref(v_close_4188_);
lean_dec_ref(v_inst_4181_);
v___x_4189_ = lean_apply_2(v_close_4188_, v_socket_4182_, lean_box(0));
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 1);
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
v_val_4186_ = v___x_4195_;
goto v___jp_4185_;
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_a_4198_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4189_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4189_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 0);
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
v_val_4186_ = v___x_4203_;
goto v___jp_4185_;
}
}
}
v___jp_4185_:
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_val_4186_);
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4206_, lean_object* v_socket_4207_, lean_object* v_____r_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4206_, v_socket_4207_, v_____r_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4211_, lean_object* v_x_4212_){
_start:
{
if (lean_obj_tag(v_x_4212_) == 0)
{
lean_object* v___x_4214_; 
lean_dec_ref(v___f_4211_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_x_4212_);
return v___x_4214_;
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4216_; 
v_a_4215_ = lean_ctor_get(v_x_4212_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v_x_4212_, 1);
v___x_4216_ = lean_apply_2(v___f_4211_, v_a_4215_, lean_box(0));
return v___x_4216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4217_, v_x_4218_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4221_, lean_object* v_val_4222_, lean_object* v___f_4223_, lean_object* v___f_4224_, lean_object* v_x_4225_){
_start:
{
if (lean_obj_tag(v_x_4225_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4235_; 
lean_dec_ref(v___f_4224_);
lean_dec_ref(v___f_4223_);
lean_dec(v_val_4222_);
lean_dec_ref(v_close_4221_);
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
lean_object* v_a_4236_; uint8_t v___x_4237_; 
v_a_4236_ = lean_ctor_get(v_x_4225_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v_x_4225_, 1);
v___x_4237_ = lean_unbox(v_a_4236_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; 
lean_dec_ref(v___f_4224_);
v___x_4238_ = lean_apply_2(v_close_4221_, v_val_4222_, lean_box(0));
v___x_4239_ = lean_unsigned_to_nat(0u);
v___x_4240_ = lean_unbox(v_a_4236_);
lean_dec(v_a_4236_);
v___x_4241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4239_, v___x_4240_, v___x_4238_, v___f_4223_);
return v___x_4241_;
}
else
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
lean_dec(v_a_4236_);
lean_dec_ref(v___f_4223_);
lean_dec(v_val_4222_);
lean_dec_ref(v_close_4221_);
v___x_4242_ = lean_box(0);
v___x_4243_ = lean_apply_2(v___f_4224_, v___x_4242_, lean_box(0));
return v___x_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4244_, lean_object* v_val_4245_, lean_object* v___f_4246_, lean_object* v___f_4247_, lean_object* v_x_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4244_, v_val_4245_, v___f_4246_, v___f_4247_, v_x_4248_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4251_, lean_object* v_responseBodyInstance_4252_, lean_object* v___f_4253_, lean_object* v___f_4254_, lean_object* v_____r_4255_){
_start:
{
if (lean_obj_tag(v_respStream_4251_) == 1)
{
lean_object* v_val_4257_; lean_object* v_close_4258_; lean_object* v_isClosed_4259_; lean_object* v___x_4260_; lean_object* v___f_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; 
v_val_4257_ = lean_ctor_get(v_respStream_4251_, 0);
lean_inc_n(v_val_4257_, 2);
lean_dec_ref_known(v_respStream_4251_, 1);
v_close_4258_ = lean_ctor_get(v_responseBodyInstance_4252_, 1);
lean_inc_ref(v_close_4258_);
v_isClosed_4259_ = lean_ctor_get(v_responseBodyInstance_4252_, 2);
lean_inc_ref(v_isClosed_4259_);
lean_dec_ref(v_responseBodyInstance_4252_);
v___x_4260_ = lean_apply_2(v_isClosed_4259_, v_val_4257_, lean_box(0));
v___f_4261_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4261_, 0, v_close_4258_);
lean_closure_set(v___f_4261_, 1, v_val_4257_);
lean_closure_set(v___f_4261_, 2, v___f_4253_);
lean_closure_set(v___f_4261_, 3, v___f_4254_);
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = 0;
v___x_4264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4262_, v___x_4263_, v___x_4260_, v___f_4261_);
return v___x_4264_;
}
else
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_dec_ref(v___f_4253_);
lean_dec_ref(v_responseBodyInstance_4252_);
lean_dec(v_respStream_4251_);
v___x_4265_ = lean_box(0);
v___x_4266_ = lean_apply_2(v___f_4254_, v___x_4265_, lean_box(0));
return v___x_4266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4267_, lean_object* v_responseBodyInstance_4268_, lean_object* v___f_4269_, lean_object* v___f_4270_, lean_object* v_____r_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4267_, v_responseBodyInstance_4268_, v___f_4269_, v___f_4270_, v_____r_4271_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4274_, lean_object* v___f_4275_, lean_object* v___f_4276_, lean_object* v_x_4277_){
_start:
{
if (lean_obj_tag(v_x_4277_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v___f_4276_);
lean_dec_ref(v___f_4275_);
lean_dec_ref(v_requestStream_4274_);
v_a_4279_ = lean_ctor_get(v_x_4277_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_x_4277_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4281_ = v_x_4277_;
v_isShared_4282_ = v_isSharedCheck_4287_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v_x_4277_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4287_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; 
v___x_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
return v___x_4285_;
}
}
}
else
{
lean_object* v_a_4288_; uint8_t v___x_4289_; 
v_a_4288_ = lean_ctor_get(v_x_4277_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v_x_4277_, 1);
v___x_4289_ = lean_unbox(v_a_4288_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; lean_object* v___x_4293_; 
lean_dec_ref(v___f_4276_);
v___x_4290_ = l_Std_Http_Body_Stream_close(v_requestStream_4274_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_unbox(v_a_4288_);
lean_dec(v_a_4288_);
v___x_4293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4291_, v___x_4292_, v___x_4290_, v___f_4275_);
return v___x_4293_;
}
else
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
lean_dec(v_a_4288_);
lean_dec_ref(v___f_4275_);
lean_dec_ref(v_requestStream_4274_);
v___x_4294_ = lean_box(0);
v___x_4295_ = lean_apply_2(v___f_4276_, v___x_4294_, lean_box(0));
return v___x_4295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4296_, lean_object* v___f_4297_, lean_object* v___f_4298_, lean_object* v_x_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4296_, v___f_4297_, v___f_4298_, v_x_4299_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4302_, lean_object* v_responseBodyInstance_4303_, lean_object* v___f_4304_, lean_object* v___f_4305_, lean_object* v_x_4306_){
_start:
{
if (lean_obj_tag(v_x_4306_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v___f_4305_);
lean_dec_ref(v___f_4304_);
lean_dec_ref(v_responseBodyInstance_4303_);
lean_dec_ref(v___f_4302_);
v_a_4308_ = lean_ctor_get(v_x_4306_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_x_4306_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4310_ = v_x_4306_;
v_isShared_4311_ = v_isSharedCheck_4316_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v_x_4306_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4316_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
return v___x_4314_;
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v_requestStream_4318_; lean_object* v_respStream_4319_; lean_object* v___x_4320_; lean_object* v___f_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_5017__overap_4325_; lean_object* v___x_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; lean_object* v___x_4332_; 
v_a_4317_ = lean_ctor_get(v_x_4306_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v_x_4306_, 1);
v_requestStream_4318_ = lean_ctor_get(v_a_4317_, 1);
lean_inc_ref_n(v_requestStream_4318_, 2);
v_respStream_4319_ = lean_ctor_get(v_a_4317_, 6);
lean_inc(v_respStream_4319_);
lean_dec(v_a_4317_);
v___x_4320_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4321_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4322_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4323_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4324_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4324_, 0, lean_box(0));
lean_closure_set(v___x_4324_, 1, lean_box(0));
lean_closure_set(v___x_4324_, 2, v___x_4320_);
lean_closure_set(v___x_4324_, 3, lean_box(0));
lean_closure_set(v___x_4324_, 4, lean_box(0));
lean_closure_set(v___x_4324_, 5, v___x_4323_);
lean_closure_set(v___x_4324_, 6, v___f_4302_);
v___x_5017__overap_4325_ = l_Std_Mutex_atomically___redArg(v___x_4320_, v___f_4321_, v___f_4322_, v_requestStream_4318_, v___x_4324_);
v___x_4326_ = lean_apply_1(v___x_5017__overap_4325_, lean_box(0));
v___f_4327_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4327_, 0, v_respStream_4319_);
lean_closure_set(v___f_4327_, 1, v_responseBodyInstance_4303_);
lean_closure_set(v___f_4327_, 2, v___f_4304_);
lean_closure_set(v___f_4327_, 3, v___f_4305_);
lean_inc_ref(v___f_4327_);
v___f_4328_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4328_, 0, v___f_4327_);
v___f_4329_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4329_, 0, v_requestStream_4318_);
lean_closure_set(v___f_4329_, 1, v___f_4328_);
lean_closure_set(v___f_4329_, 2, v___f_4327_);
v___x_4330_ = lean_unsigned_to_nat(0u);
v___x_4331_ = 0;
v___x_4332_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4330_, v___x_4331_, v___x_4326_, v___f_4329_);
return v___x_4332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4333_, lean_object* v_responseBodyInstance_4334_, lean_object* v___f_4335_, lean_object* v___f_4336_, lean_object* v_x_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4333_, v_responseBodyInstance_4334_, v___f_4335_, v___f_4336_, v_x_4337_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4340_, lean_object* v_responseBodyInstance_4341_, lean_object* v_handler_4342_, lean_object* v_config_4343_, lean_object* v___x_4344_, uint8_t v___x_4345_, lean_object* v___f_4346_, lean_object* v_x_4347_){
_start:
{
if (lean_obj_tag(v_x_4347_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4357_; 
lean_dec_ref(v___f_4346_);
lean_dec_ref(v___x_4344_);
lean_dec_ref(v_config_4343_);
lean_dec(v_handler_4342_);
lean_dec_ref(v_responseBodyInstance_4341_);
lean_dec_ref(v_h_4340_);
v_a_4349_ = lean_ctor_get(v_x_4347_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_x_4347_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4351_ = v_x_4347_;
v_isShared_4352_ = v_isSharedCheck_4357_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v_x_4347_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4357_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
return v___x_4355_;
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v_a_4358_ = lean_ctor_get(v_x_4347_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v_x_4347_, 1);
v___x_4359_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4340_, v_responseBodyInstance_4341_, v_handler_4342_, v_config_4343_, v_a_4358_, v___x_4344_);
v___x_4360_ = lean_unsigned_to_nat(0u);
v___x_4361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4360_, v___x_4345_, v___x_4359_, v___f_4346_);
return v___x_4361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4362_, lean_object* v_responseBodyInstance_4363_, lean_object* v_handler_4364_, lean_object* v_config_4365_, lean_object* v___x_4366_, lean_object* v___x_4367_, lean_object* v___f_4368_, lean_object* v_x_4369_, lean_object* v___y_4370_){
_start:
{
uint8_t v___x_5688__boxed_4371_; lean_object* v_res_4372_; 
v___x_5688__boxed_4371_ = lean_unbox(v___x_4367_);
v_res_4372_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4362_, v_responseBodyInstance_4363_, v_handler_4364_, v_config_4365_, v___x_4366_, v___x_5688__boxed_4371_, v___f_4368_, v_x_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4373_, lean_object* v_h_4374_, lean_object* v_responseBodyInstance_4375_, lean_object* v_config_4376_, lean_object* v_handler_4377_, uint8_t v___x_4378_, lean_object* v___f_4379_, lean_object* v_x_4380_){
_start:
{
if (lean_obj_tag(v_x_4380_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4390_; 
lean_dec_ref(v___f_4379_);
lean_dec(v_handler_4377_);
lean_dec_ref(v_config_4376_);
lean_dec_ref(v_responseBodyInstance_4375_);
lean_dec_ref(v_h_4374_);
lean_dec_ref(v_inst_4373_);
v_a_4382_ = lean_ctor_get(v_x_4380_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_x_4380_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4384_ = v_x_4380_;
v_isShared_4385_ = v_isSharedCheck_4390_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v_x_4380_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4390_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4388_; 
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
return v___x_4388_;
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v_a_4391_ = lean_ctor_get(v_x_4380_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v_x_4380_, 1);
v___x_4392_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4373_, v_h_4374_, v_responseBodyInstance_4375_, v_config_4376_, v_handler_4377_, v_a_4391_);
v___x_4393_ = lean_unsigned_to_nat(0u);
v___x_4394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4393_, v___x_4378_, v___x_4392_, v___f_4379_);
return v___x_4394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4395_, lean_object* v_h_4396_, lean_object* v_responseBodyInstance_4397_, lean_object* v_config_4398_, lean_object* v_handler_4399_, lean_object* v___x_4400_, lean_object* v___f_4401_, lean_object* v_x_4402_, lean_object* v___y_4403_){
_start:
{
uint8_t v___x_5729__boxed_4404_; lean_object* v_res_4405_; 
v___x_5729__boxed_4404_ = lean_unbox(v___x_4400_);
v_res_4405_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4395_, v_h_4396_, v_responseBodyInstance_4397_, v_config_4398_, v_handler_4399_, v___x_5729__boxed_4404_, v___f_4401_, v_x_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4406_, lean_object* v_socket_4407_, lean_object* v_connectionContext_4408_, lean_object* v_h_4409_, lean_object* v_responseBodyInstance_4410_, lean_object* v_handler_4411_, lean_object* v_config_4412_, lean_object* v___f_4413_, lean_object* v_inst_4414_, lean_object* v_x_4415_){
_start:
{
if (lean_obj_tag(v_x_4415_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v_inst_4414_);
lean_dec_ref(v___f_4413_);
lean_dec_ref(v_config_4412_);
lean_dec(v_handler_4411_);
lean_dec_ref(v_responseBodyInstance_4410_);
lean_dec_ref(v_h_4409_);
lean_dec_ref(v_connectionContext_4408_);
lean_dec(v_socket_4407_);
v_a_4417_ = lean_ctor_get(v_x_4415_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v_x_4415_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4419_ = v_x_4415_;
v_isShared_4420_ = v_isSharedCheck_4425_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v_x_4415_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4425_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4423_; 
v___x_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
return v___x_4423_;
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4460_; 
v_a_4426_ = lean_ctor_get(v_x_4415_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_x_4415_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4428_ = v_x_4415_;
v_isShared_4429_ = v_isSharedCheck_4460_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v_x_4415_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4460_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v_machine_4436_; lean_object* v_requestStream_4437_; lean_object* v_keepAliveTimeout_4438_; lean_object* v_currentTimeout_4439_; lean_object* v_headerTimeout_4440_; lean_object* v_response_4441_; lean_object* v_respStream_4442_; uint8_t v_requiresData_4443_; lean_object* v_expectData_4444_; uint8_t v_handlerDispatched_4445_; lean_object* v_pendingHead_4446_; 
v_machine_4436_ = lean_ctor_get(v_a_4426_, 0);
v_requestStream_4437_ = lean_ctor_get(v_a_4426_, 1);
v_keepAliveTimeout_4438_ = lean_ctor_get(v_a_4426_, 2);
v_currentTimeout_4439_ = lean_ctor_get(v_a_4426_, 3);
v_headerTimeout_4440_ = lean_ctor_get(v_a_4426_, 4);
v_response_4441_ = lean_ctor_get(v_a_4426_, 5);
v_respStream_4442_ = lean_ctor_get(v_a_4426_, 6);
v_requiresData_4443_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*9);
v_expectData_4444_ = lean_ctor_get(v_a_4426_, 7);
v_handlerDispatched_4445_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*9 + 1);
v_pendingHead_4446_ = lean_ctor_get(v_a_4426_, 8);
if (v_requiresData_4443_ == 0)
{
if (v_handlerDispatched_4445_ == 0)
{
if (lean_obj_tag(v_respStream_4442_) == 0)
{
lean_object* v_writer_4456_; uint8_t v_sentMessage_4457_; 
v_writer_4456_ = lean_ctor_get(v_machine_4436_, 1);
v_sentMessage_4457_ = lean_ctor_get_uint8(v_writer_4456_, sizeof(void*)*6);
if (v_sentMessage_4457_ == 0)
{
lean_object* v_reader_4458_; lean_object* v_state_4459_; 
v_reader_4458_ = lean_ctor_get(v_machine_4436_, 0);
v_state_4459_ = lean_ctor_get(v_reader_4458_, 0);
if (lean_obj_tag(v_state_4459_) == 2)
{
lean_inc(v_respStream_4442_);
lean_inc(v_pendingHead_4446_);
lean_inc(v_expectData_4444_);
lean_inc_ref(v_response_4441_);
lean_inc(v_headerTimeout_4440_);
lean_inc(v_currentTimeout_4439_);
lean_inc(v_keepAliveTimeout_4438_);
lean_inc_ref(v_requestStream_4437_);
lean_inc_ref(v_machine_4436_);
lean_del_object(v___x_4428_);
lean_dec(v_a_4426_);
goto v___jp_4447_;
}
else
{
lean_dec_ref(v_inst_4414_);
lean_dec_ref(v___f_4413_);
lean_dec_ref(v_config_4412_);
lean_dec(v_handler_4411_);
lean_dec_ref(v_responseBodyInstance_4410_);
lean_dec_ref(v_h_4409_);
lean_dec_ref(v_connectionContext_4408_);
lean_dec(v_socket_4407_);
goto v___jp_4430_;
}
}
else
{
lean_dec_ref(v_inst_4414_);
lean_dec_ref(v___f_4413_);
lean_dec_ref(v_config_4412_);
lean_dec(v_handler_4411_);
lean_dec_ref(v_responseBodyInstance_4410_);
lean_dec_ref(v_h_4409_);
lean_dec_ref(v_connectionContext_4408_);
lean_dec(v_socket_4407_);
goto v___jp_4430_;
}
}
else
{
lean_inc_ref(v_respStream_4442_);
lean_inc(v_pendingHead_4446_);
lean_inc(v_expectData_4444_);
lean_inc_ref(v_response_4441_);
lean_inc(v_headerTimeout_4440_);
lean_inc(v_currentTimeout_4439_);
lean_inc(v_keepAliveTimeout_4438_);
lean_inc_ref(v_requestStream_4437_);
lean_inc_ref(v_machine_4436_);
lean_del_object(v___x_4428_);
lean_dec(v_a_4426_);
goto v___jp_4447_;
}
}
else
{
lean_inc(v_pendingHead_4446_);
lean_inc(v_expectData_4444_);
lean_inc(v_respStream_4442_);
lean_inc_ref(v_response_4441_);
lean_inc(v_headerTimeout_4440_);
lean_inc(v_currentTimeout_4439_);
lean_inc(v_keepAliveTimeout_4438_);
lean_inc_ref(v_requestStream_4437_);
lean_inc_ref(v_machine_4436_);
lean_del_object(v___x_4428_);
lean_dec(v_a_4426_);
goto v___jp_4447_;
}
}
else
{
lean_inc(v_pendingHead_4446_);
lean_inc(v_expectData_4444_);
lean_inc(v_respStream_4442_);
lean_inc_ref(v_response_4441_);
lean_inc(v_headerTimeout_4440_);
lean_inc(v_currentTimeout_4439_);
lean_inc(v_keepAliveTimeout_4438_);
lean_inc_ref(v_requestStream_4437_);
lean_inc_ref(v_machine_4436_);
lean_del_object(v___x_4428_);
lean_dec(v_a_4426_);
goto v___jp_4447_;
}
v___jp_4430_:
{
lean_object* v___x_4431_; lean_object* v___x_4433_; 
v___x_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4431_, 0, v_a_4426_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4431_);
v___x_4433_ = v___x_4428_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4434_; 
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
return v___x_4434_;
}
}
v___jp_4447_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___f_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4448_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4448_, 0, v_machine_4436_);
lean_ctor_set(v___x_4448_, 1, v_requestStream_4437_);
lean_ctor_set(v___x_4448_, 2, v_keepAliveTimeout_4438_);
lean_ctor_set(v___x_4448_, 3, v_currentTimeout_4439_);
lean_ctor_set(v___x_4448_, 4, v_headerTimeout_4440_);
lean_ctor_set(v___x_4448_, 5, v_response_4441_);
lean_ctor_set(v___x_4448_, 6, v_respStream_4442_);
lean_ctor_set(v___x_4448_, 7, v_expectData_4444_);
lean_ctor_set(v___x_4448_, 8, v_pendingHead_4446_);
lean_ctor_set_uint8(v___x_4448_, sizeof(void*)*9, v___x_4406_);
lean_ctor_set_uint8(v___x_4448_, sizeof(void*)*9 + 1, v_handlerDispatched_4445_);
lean_inc_ref(v___x_4448_);
v___x_4449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4407_, v_connectionContext_4408_, v___x_4448_);
v___x_4450_ = lean_box(v___x_4406_);
lean_inc_ref(v_config_4412_);
lean_inc(v_handler_4411_);
lean_inc_ref(v_responseBodyInstance_4410_);
lean_inc_ref(v_h_4409_);
v___f_4451_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4451_, 0, v_h_4409_);
lean_closure_set(v___f_4451_, 1, v_responseBodyInstance_4410_);
lean_closure_set(v___f_4451_, 2, v_handler_4411_);
lean_closure_set(v___f_4451_, 3, v_config_4412_);
lean_closure_set(v___f_4451_, 4, v___x_4448_);
lean_closure_set(v___f_4451_, 5, v___x_4450_);
lean_closure_set(v___f_4451_, 6, v___f_4413_);
v___x_4452_ = lean_box(v___x_4406_);
v___f_4453_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4453_, 0, v_inst_4414_);
lean_closure_set(v___f_4453_, 1, v_h_4409_);
lean_closure_set(v___f_4453_, 2, v_responseBodyInstance_4410_);
lean_closure_set(v___f_4453_, 3, v_config_4412_);
lean_closure_set(v___f_4453_, 4, v_handler_4411_);
lean_closure_set(v___f_4453_, 5, v___x_4452_);
lean_closure_set(v___f_4453_, 6, v___f_4451_);
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4455_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4454_, v___x_4406_, v___x_4449_, v___f_4453_);
return v___x_4455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4461_, lean_object* v_socket_4462_, lean_object* v_connectionContext_4463_, lean_object* v_h_4464_, lean_object* v_responseBodyInstance_4465_, lean_object* v_handler_4466_, lean_object* v_config_4467_, lean_object* v___f_4468_, lean_object* v_inst_4469_, lean_object* v_x_4470_, lean_object* v___y_4471_){
_start:
{
uint8_t v___x_5769__boxed_4472_; lean_object* v_res_4473_; 
v___x_5769__boxed_4472_ = lean_unbox(v___x_4461_);
v_res_4473_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5769__boxed_4472_, v_socket_4462_, v_connectionContext_4463_, v_h_4464_, v_responseBodyInstance_4465_, v_handler_4466_, v_config_4467_, v___f_4468_, v_inst_4469_, v_x_4470_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4474_, lean_object* v_handler_4475_, lean_object* v_extensions_4476_, lean_object* v_connectionContext_4477_, uint8_t v___x_4478_, lean_object* v___f_4479_, lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4480_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref(v___f_4479_);
lean_dec_ref(v_connectionContext_4477_);
lean_dec(v_extensions_4476_);
lean_dec(v_handler_4475_);
lean_dec_ref(v_h_4474_);
v_a_4482_ = lean_ctor_get(v_x_4480_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_x_4480_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4484_ = v_x_4480_;
v_isShared_4485_ = v_isSharedCheck_4490_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v_x_4480_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4490_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; 
v___x_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
return v___x_4488_;
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v_a_4491_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v_x_4480_, 1);
v___x_4492_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4474_, v_handler_4475_, v_extensions_4476_, v_connectionContext_4477_, v_a_4491_);
v___x_4493_ = lean_unsigned_to_nat(0u);
v___x_4494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4493_, v___x_4478_, v___x_4492_, v___f_4479_);
return v___x_4494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4495_, lean_object* v_handler_4496_, lean_object* v_extensions_4497_, lean_object* v_connectionContext_4498_, lean_object* v___x_4499_, lean_object* v___f_4500_, lean_object* v_x_4501_, lean_object* v___y_4502_){
_start:
{
uint8_t v___x_5844__boxed_4503_; lean_object* v_res_4504_; 
v___x_5844__boxed_4503_ = lean_unbox(v___x_4499_);
v_res_4504_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4495_, v_handler_4496_, v_extensions_4497_, v_connectionContext_4498_, v___x_5844__boxed_4503_, v___f_4500_, v_x_4501_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4505_, lean_object* v_responseBodyInstance_4506_, lean_object* v_handler_4507_, lean_object* v_config_4508_, lean_object* v_connectionContext_4509_, lean_object* v_events_4510_, lean_object* v___x_4511_, uint8_t v___x_4512_, lean_object* v___f_4513_, lean_object* v_____r_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4516_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4505_, v_responseBodyInstance_4506_, v_handler_4507_, v_config_4508_, v_connectionContext_4509_, v_events_4510_, v___x_4511_);
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4517_, v___x_4512_, v___x_4516_, v___f_4513_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4519_, lean_object* v_responseBodyInstance_4520_, lean_object* v_handler_4521_, lean_object* v_config_4522_, lean_object* v_connectionContext_4523_, lean_object* v_events_4524_, lean_object* v___x_4525_, lean_object* v___x_4526_, lean_object* v___f_4527_, lean_object* v_____r_4528_, lean_object* v___y_4529_){
_start:
{
uint8_t v___x_5883__boxed_4530_; lean_object* v_res_4531_; 
v___x_5883__boxed_4530_ = lean_unbox(v___x_4526_);
v_res_4531_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4519_, v_responseBodyInstance_4520_, v_handler_4521_, v_config_4522_, v_connectionContext_4523_, v_events_4524_, v___x_4525_, v___x_5883__boxed_4530_, v___f_4527_, v_____r_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4532_, lean_object* v___f_4533_, lean_object* v_x_4534_){
_start:
{
if (lean_obj_tag(v_x_4534_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4544_; 
lean_dec_ref(v___f_4533_);
lean_dec_ref(v___x_4532_);
v_a_4536_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4538_ = v_x_4534_;
v_isShared_4539_ = v_isSharedCheck_4544_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v_x_4534_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4544_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4556_; 
v_a_4545_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4547_ = v_x_4534_;
v_isShared_4548_ = v_isSharedCheck_4556_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v_x_4534_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4556_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
if (lean_obj_tag(v_a_4545_) == 0)
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
lean_dec_ref(v___f_4533_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4532_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v___x_4549_);
v___x_4551_ = v___x_4547_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4552_; 
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
return v___x_4552_;
}
}
else
{
lean_object* v_val_4554_; lean_object* v___x_4555_; 
lean_del_object(v___x_4547_);
lean_dec_ref(v___x_4532_);
v_val_4554_ = lean_ctor_get(v_a_4545_, 0);
lean_inc(v_val_4554_);
lean_dec_ref_known(v_a_4545_, 1);
v___x_4555_ = lean_apply_2(v___f_4533_, v_val_4554_, lean_box(0));
return v___x_4555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4557_, lean_object* v___f_4558_, lean_object* v_x_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4557_, v___f_4558_, v_x_4559_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4562_, lean_object* v_responseBodyInstance_4563_, lean_object* v_handler_4564_, lean_object* v_config_4565_, lean_object* v_connectionContext_4566_, uint8_t v___x_4567_, lean_object* v___f_4568_, lean_object* v_inst_4569_, lean_object* v_socket_4570_, lean_object* v___f_4571_, lean_object* v___f_4572_, lean_object* v_x_4573_, lean_object* v_____s_4574_){
_start:
{
lean_object* v_machine_4576_; lean_object* v_reader_4577_; lean_object* v_requestStream_4578_; lean_object* v_keepAliveTimeout_4579_; lean_object* v_currentTimeout_4580_; lean_object* v_headerTimeout_4581_; lean_object* v_response_4582_; lean_object* v_respStream_4583_; uint8_t v_requiresData_4584_; lean_object* v_expectData_4585_; uint8_t v_handlerDispatched_4586_; lean_object* v_pendingHead_4587_; lean_object* v_writer_4588_; lean_object* v_state_4589_; uint8_t v___x_4590_; 
v_machine_4576_ = lean_ctor_get(v_____s_4574_, 0);
v_reader_4577_ = lean_ctor_get(v_machine_4576_, 0);
v_requestStream_4578_ = lean_ctor_get(v_____s_4574_, 1);
v_keepAliveTimeout_4579_ = lean_ctor_get(v_____s_4574_, 2);
v_currentTimeout_4580_ = lean_ctor_get(v_____s_4574_, 3);
v_headerTimeout_4581_ = lean_ctor_get(v_____s_4574_, 4);
v_response_4582_ = lean_ctor_get(v_____s_4574_, 5);
v_respStream_4583_ = lean_ctor_get(v_____s_4574_, 6);
v_requiresData_4584_ = lean_ctor_get_uint8(v_____s_4574_, sizeof(void*)*9);
v_expectData_4585_ = lean_ctor_get(v_____s_4574_, 7);
v_handlerDispatched_4586_ = lean_ctor_get_uint8(v_____s_4574_, sizeof(void*)*9 + 1);
v_pendingHead_4587_ = lean_ctor_get(v_____s_4574_, 8);
v_writer_4588_ = lean_ctor_get(v_machine_4576_, 1);
v_state_4589_ = lean_ctor_get(v_reader_4577_, 0);
v___x_4590_ = 0;
if (lean_obj_tag(v_state_4589_) == 6)
{
lean_object* v_state_4612_; 
v_state_4612_ = lean_ctor_get(v_writer_4588_, 2);
if (lean_obj_tag(v_state_4612_) == 7)
{
lean_object* v_outputData_4613_; lean_object* v_size_4614_; lean_object* v___x_4615_; uint8_t v___x_4616_; 
v_outputData_4613_ = lean_ctor_get(v_writer_4588_, 1);
v_size_4614_ = lean_ctor_get(v_outputData_4613_, 1);
v___x_4615_ = lean_unsigned_to_nat(0u);
v___x_4616_ = lean_nat_dec_eq(v_size_4614_, v___x_4615_);
if (v___x_4616_ == 0)
{
lean_inc(v_pendingHead_4587_);
lean_inc(v_expectData_4585_);
lean_inc(v_respStream_4583_);
lean_inc_ref(v_response_4582_);
lean_inc(v_headerTimeout_4581_);
lean_inc(v_currentTimeout_4580_);
lean_inc(v_keepAliveTimeout_4579_);
lean_inc_ref(v_requestStream_4578_);
lean_inc_ref(v_machine_4576_);
lean_dec_ref(v_____s_4574_);
goto v___jp_4591_;
}
else
{
if (v___x_4616_ == 0)
{
lean_inc(v_pendingHead_4587_);
lean_inc(v_expectData_4585_);
lean_inc(v_respStream_4583_);
lean_inc_ref(v_response_4582_);
lean_inc(v_headerTimeout_4581_);
lean_inc(v_currentTimeout_4580_);
lean_inc(v_keepAliveTimeout_4579_);
lean_inc_ref(v_requestStream_4578_);
lean_inc_ref(v_machine_4576_);
lean_dec_ref(v_____s_4574_);
goto v___jp_4591_;
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
lean_dec_ref(v___f_4572_);
lean_dec_ref(v___f_4571_);
lean_dec(v_socket_4570_);
lean_dec_ref(v_inst_4569_);
lean_dec_ref(v___f_4568_);
lean_dec_ref(v_connectionContext_4566_);
lean_dec_ref(v_config_4565_);
lean_dec(v_handler_4564_);
lean_dec_ref(v_responseBodyInstance_4563_);
lean_dec_ref(v_h_4562_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_____s_4574_);
v___x_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
return v___x_4619_;
}
}
}
else
{
lean_inc(v_pendingHead_4587_);
lean_inc(v_expectData_4585_);
lean_inc(v_respStream_4583_);
lean_inc_ref(v_response_4582_);
lean_inc(v_headerTimeout_4581_);
lean_inc(v_currentTimeout_4580_);
lean_inc(v_keepAliveTimeout_4579_);
lean_inc_ref(v_requestStream_4578_);
lean_inc_ref(v_machine_4576_);
lean_dec_ref(v_____s_4574_);
goto v___jp_4591_;
}
}
else
{
lean_inc(v_pendingHead_4587_);
lean_inc(v_expectData_4585_);
lean_inc(v_respStream_4583_);
lean_inc_ref(v_response_4582_);
lean_inc(v_headerTimeout_4581_);
lean_inc(v_currentTimeout_4580_);
lean_inc(v_keepAliveTimeout_4579_);
lean_inc_ref(v_requestStream_4578_);
lean_inc_ref(v_machine_4576_);
lean_dec_ref(v_____s_4574_);
goto v___jp_4591_;
}
v___jp_4591_:
{
lean_object* v___x_4592_; lean_object* v_snd_4593_; lean_object* v_output_4594_; lean_object* v_fst_4595_; lean_object* v_events_4596_; lean_object* v_data_4597_; lean_object* v_size_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___f_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4592_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4590_, v_machine_4576_);
v_snd_4593_ = lean_ctor_get(v___x_4592_, 1);
lean_inc(v_snd_4593_);
v_output_4594_ = lean_ctor_get(v_snd_4593_, 1);
lean_inc_ref(v_output_4594_);
v_fst_4595_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_fst_4595_);
lean_dec_ref(v___x_4592_);
v_events_4596_ = lean_ctor_get(v_snd_4593_, 0);
lean_inc_ref_n(v_events_4596_, 2);
lean_dec(v_snd_4593_);
v_data_4597_ = lean_ctor_get(v_output_4594_, 0);
lean_inc_ref(v_data_4597_);
v_size_4598_ = lean_ctor_get(v_output_4594_, 1);
lean_inc(v_size_4598_);
lean_dec_ref(v_output_4594_);
v___x_4599_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4599_, 0, v_fst_4595_);
lean_ctor_set(v___x_4599_, 1, v_requestStream_4578_);
lean_ctor_set(v___x_4599_, 2, v_keepAliveTimeout_4579_);
lean_ctor_set(v___x_4599_, 3, v_currentTimeout_4580_);
lean_ctor_set(v___x_4599_, 4, v_headerTimeout_4581_);
lean_ctor_set(v___x_4599_, 5, v_response_4582_);
lean_ctor_set(v___x_4599_, 6, v_respStream_4583_);
lean_ctor_set(v___x_4599_, 7, v_expectData_4585_);
lean_ctor_set(v___x_4599_, 8, v_pendingHead_4587_);
lean_ctor_set_uint8(v___x_4599_, sizeof(void*)*9, v_requiresData_4584_);
lean_ctor_set_uint8(v___x_4599_, sizeof(void*)*9 + 1, v_handlerDispatched_4586_);
v___x_4600_ = lean_box(v___x_4567_);
lean_inc_ref(v___f_4568_);
lean_inc_ref(v___x_4599_);
lean_inc_ref(v_connectionContext_4566_);
lean_inc_ref(v_config_4565_);
lean_inc(v_handler_4564_);
lean_inc_ref(v_responseBodyInstance_4563_);
lean_inc_ref(v_h_4562_);
v___f_4601_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4601_, 0, v_h_4562_);
lean_closure_set(v___f_4601_, 1, v_responseBodyInstance_4563_);
lean_closure_set(v___f_4601_, 2, v_handler_4564_);
lean_closure_set(v___f_4601_, 3, v_config_4565_);
lean_closure_set(v___f_4601_, 4, v_connectionContext_4566_);
lean_closure_set(v___f_4601_, 5, v_events_4596_);
lean_closure_set(v___f_4601_, 6, v___x_4599_);
lean_closure_set(v___f_4601_, 7, v___x_4600_);
lean_closure_set(v___f_4601_, 8, v___f_4568_);
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = lean_nat_dec_lt(v___x_4602_, v_size_4598_);
lean_dec(v_size_4598_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
lean_dec_ref(v___f_4601_);
lean_dec_ref(v_data_4597_);
lean_dec_ref(v___f_4572_);
lean_dec_ref(v___f_4571_);
lean_dec(v_socket_4570_);
lean_dec_ref(v_inst_4569_);
v___x_4604_ = lean_box(0);
v___x_4605_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4562_, v_responseBodyInstance_4563_, v_handler_4564_, v_config_4565_, v_connectionContext_4566_, v_events_4596_, v___x_4599_, v___x_4567_, v___f_4568_, v___x_4604_);
return v___x_4605_;
}
else
{
lean_object* v_sendAll_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___f_4610_; lean_object* v___x_4611_; 
lean_dec_ref(v_events_4596_);
lean_dec_ref(v___f_4568_);
lean_dec_ref(v_connectionContext_4566_);
lean_dec_ref(v_config_4565_);
lean_dec(v_handler_4564_);
lean_dec_ref(v_responseBodyInstance_4563_);
lean_dec_ref(v_h_4562_);
v_sendAll_4606_ = lean_ctor_get(v_inst_4569_, 1);
lean_inc_ref(v_sendAll_4606_);
lean_dec_ref(v_inst_4569_);
v___x_4607_ = lean_apply_3(v_sendAll_4606_, v_socket_4570_, v_data_4597_, lean_box(0));
v___x_4608_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4602_, v___x_4567_, v___x_4607_, v___f_4571_);
v___x_4609_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4602_, v___x_4567_, v___x_4608_, v___f_4572_);
v___f_4610_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4610_, 0, v___x_4599_);
lean_closure_set(v___f_4610_, 1, v___f_4601_);
v___x_4611_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4602_, v___x_4567_, v___x_4609_, v___f_4610_);
return v___x_4611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4620_, lean_object* v_responseBodyInstance_4621_, lean_object* v_handler_4622_, lean_object* v_config_4623_, lean_object* v_connectionContext_4624_, lean_object* v___x_4625_, lean_object* v___f_4626_, lean_object* v_inst_4627_, lean_object* v_socket_4628_, lean_object* v___f_4629_, lean_object* v___f_4630_, lean_object* v_x_4631_, lean_object* v_____s_4632_, lean_object* v___y_4633_){
_start:
{
uint8_t v___x_5957__boxed_4634_; lean_object* v_res_4635_; 
v___x_5957__boxed_4634_ = lean_unbox(v___x_4625_);
v_res_4635_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4620_, v_responseBodyInstance_4621_, v_handler_4622_, v_config_4623_, v_connectionContext_4624_, v___x_5957__boxed_4634_, v___f_4626_, v_inst_4627_, v_socket_4628_, v___f_4629_, v___f_4630_, v_x_4631_, v_____s_4632_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4636_, lean_object* v_x_4637_){
_start:
{
if (lean_obj_tag(v_x_4637_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4647_; 
v_a_4639_ = lean_ctor_get(v_x_4637_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_x_4637_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4641_ = v_x_4637_;
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v_x_4637_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
}
}
else
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
lean_dec_ref_known(v_x_4637_, 1);
v___x_4648_ = l_IO_Promise_result_x21___redArg(v_a_4636_);
v___x_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4650_, lean_object* v_x_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4650_, v_x_4651_);
lean_dec(v_a_4650_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4654_, lean_object* v___x_4655_, lean_object* v___x_4656_, uint8_t v___x_4657_, lean_object* v_x_4658_){
_start:
{
if (lean_obj_tag(v_x_4658_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4668_; 
lean_dec_ref(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec_ref(v___f_4654_);
v_a_4660_ = lean_ctor_get(v_x_4658_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v_x_4658_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4662_ = v_x_4658_;
v_isShared_4663_ = v_isSharedCheck_4668_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v_x_4658_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4668_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
return v___x_4666_;
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4680_; 
v_a_4669_ = lean_ctor_get(v_x_4658_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_x_4658_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4671_ = v_x_4658_;
v_isShared_4672_ = v_isSharedCheck_4680_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v_x_4658_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4680_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___f_4674_; lean_object* v___x_4676_; 
lean_inc(v_a_4669_);
lean_inc(v___x_4655_);
v___x_4673_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4654_, v___x_4655_, v_a_4669_, v___x_4656_);
v___f_4674_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4674_, 0, v_a_4669_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v___x_4673_);
v___x_4676_ = v___x_4671_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4673_);
v___x_4676_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
v___x_4678_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4655_, v___x_4657_, v___x_4677_, v___f_4674_);
return v___x_4678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4681_, lean_object* v___x_4682_, lean_object* v___x_4683_, lean_object* v___x_4684_, lean_object* v_x_4685_, lean_object* v___y_4686_){
_start:
{
uint8_t v___x_6060__boxed_4687_; lean_object* v_res_4688_; 
v___x_6060__boxed_4687_ = lean_unbox(v___x_4684_);
v_res_4688_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4681_, v___x_4682_, v___x_4683_, v___x_6060__boxed_4687_, v_x_4685_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4689_, lean_object* v_machine_4690_, lean_object* v_a_4691_, lean_object* v___x_4692_, lean_object* v_socket_4693_, lean_object* v_connectionContext_4694_, lean_object* v_h_4695_, lean_object* v_responseBodyInstance_4696_, lean_object* v_handler_4697_, lean_object* v___f_4698_, lean_object* v_inst_4699_, lean_object* v_extensions_4700_, lean_object* v___f_4701_, lean_object* v___f_4702_, lean_object* v___f_4703_, lean_object* v_x_4704_){
_start:
{
if (lean_obj_tag(v_x_4704_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4714_; 
lean_dec_ref(v___f_4703_);
lean_dec_ref(v___f_4702_);
lean_dec_ref(v___f_4701_);
lean_dec(v_extensions_4700_);
lean_dec_ref(v_inst_4699_);
lean_dec_ref(v___f_4698_);
lean_dec(v_handler_4697_);
lean_dec_ref(v_responseBodyInstance_4696_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_connectionContext_4694_);
lean_dec(v_socket_4693_);
lean_dec(v___x_4692_);
lean_dec_ref(v_a_4691_);
lean_dec_ref(v_machine_4690_);
lean_dec_ref(v_config_4689_);
v_a_4706_ = lean_ctor_get(v_x_4704_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v_x_4704_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4708_ = v_x_4704_;
v_isShared_4709_ = v_isSharedCheck_4714_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v_x_4704_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4714_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
return v___x_4712_;
}
}
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4740_; 
v_a_4715_ = lean_ctor_get(v_x_4704_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_x_4704_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4717_ = v_x_4704_;
v_isShared_4718_ = v_isSharedCheck_4740_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v_x_4704_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4740_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v_keepAliveTimeout_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___f_4726_; lean_object* v___x_4727_; lean_object* v___f_4728_; lean_object* v___x_4729_; lean_object* v___f_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___f_4733_; lean_object* v___x_4735_; 
v_keepAliveTimeout_4719_ = lean_ctor_get(v_config_4689_, 5);
lean_inc_n(v_keepAliveTimeout_4719_, 2);
v___x_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4720_, 0, v_keepAliveTimeout_4719_);
v___x_4721_ = lean_box(0);
v___x_4722_ = 0;
v___x_4723_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4723_, 0, v_machine_4690_);
lean_ctor_set(v___x_4723_, 1, v_a_4691_);
lean_ctor_set(v___x_4723_, 2, v___x_4720_);
lean_ctor_set(v___x_4723_, 3, v_keepAliveTimeout_4719_);
lean_ctor_set(v___x_4723_, 4, v___x_4721_);
lean_ctor_set(v___x_4723_, 5, v_a_4715_);
lean_ctor_set(v___x_4723_, 6, v___x_4721_);
lean_ctor_set(v___x_4723_, 7, v___x_4692_);
lean_ctor_set(v___x_4723_, 8, v___x_4721_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*9, v___x_4722_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*9 + 1, v___x_4722_);
v___x_4724_ = lean_io_promise_new();
v___x_4725_ = lean_box(v___x_4722_);
lean_inc_ref(v_inst_4699_);
lean_inc_ref(v_config_4689_);
lean_inc_n(v_handler_4697_, 2);
lean_inc_ref(v_responseBodyInstance_4696_);
lean_inc_ref_n(v_h_4695_, 2);
lean_inc_ref_n(v_connectionContext_4694_, 2);
lean_inc(v_socket_4693_);
v___f_4726_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4726_, 0, v___x_4725_);
lean_closure_set(v___f_4726_, 1, v_socket_4693_);
lean_closure_set(v___f_4726_, 2, v_connectionContext_4694_);
lean_closure_set(v___f_4726_, 3, v_h_4695_);
lean_closure_set(v___f_4726_, 4, v_responseBodyInstance_4696_);
lean_closure_set(v___f_4726_, 5, v_handler_4697_);
lean_closure_set(v___f_4726_, 6, v_config_4689_);
lean_closure_set(v___f_4726_, 7, v___f_4698_);
lean_closure_set(v___f_4726_, 8, v_inst_4699_);
v___x_4727_ = lean_box(v___x_4722_);
v___f_4728_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4728_, 0, v_h_4695_);
lean_closure_set(v___f_4728_, 1, v_handler_4697_);
lean_closure_set(v___f_4728_, 2, v_extensions_4700_);
lean_closure_set(v___f_4728_, 3, v_connectionContext_4694_);
lean_closure_set(v___f_4728_, 4, v___x_4727_);
lean_closure_set(v___f_4728_, 5, v___f_4726_);
v___x_4729_ = lean_box(v___x_4722_);
v___f_4730_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4730_, 0, v_h_4695_);
lean_closure_set(v___f_4730_, 1, v_responseBodyInstance_4696_);
lean_closure_set(v___f_4730_, 2, v_handler_4697_);
lean_closure_set(v___f_4730_, 3, v_config_4689_);
lean_closure_set(v___f_4730_, 4, v_connectionContext_4694_);
lean_closure_set(v___f_4730_, 5, v___x_4729_);
lean_closure_set(v___f_4730_, 6, v___f_4728_);
lean_closure_set(v___f_4730_, 7, v_inst_4699_);
lean_closure_set(v___f_4730_, 8, v_socket_4693_);
lean_closure_set(v___f_4730_, 9, v___f_4701_);
lean_closure_set(v___f_4730_, 10, v___f_4702_);
v___x_4731_ = lean_unsigned_to_nat(0u);
v___x_4732_ = lean_box(v___x_4722_);
v___f_4733_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4733_, 0, v___f_4730_);
lean_closure_set(v___f_4733_, 1, v___x_4731_);
lean_closure_set(v___f_4733_, 2, v___x_4723_);
lean_closure_set(v___f_4733_, 3, v___x_4732_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 0, v___x_4724_);
v___x_4735_ = v___x_4717_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4724_);
v___x_4735_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
v___x_4737_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4731_, v___x_4722_, v___x_4736_, v___f_4733_);
v___x_4738_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4731_, v___x_4722_, v___x_4737_, v___f_4703_);
return v___x_4738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4741_ = _args[0];
lean_object* v_machine_4742_ = _args[1];
lean_object* v_a_4743_ = _args[2];
lean_object* v___x_4744_ = _args[3];
lean_object* v_socket_4745_ = _args[4];
lean_object* v_connectionContext_4746_ = _args[5];
lean_object* v_h_4747_ = _args[6];
lean_object* v_responseBodyInstance_4748_ = _args[7];
lean_object* v_handler_4749_ = _args[8];
lean_object* v___f_4750_ = _args[9];
lean_object* v_inst_4751_ = _args[10];
lean_object* v_extensions_4752_ = _args[11];
lean_object* v___f_4753_ = _args[12];
lean_object* v___f_4754_ = _args[13];
lean_object* v___f_4755_ = _args[14];
lean_object* v_x_4756_ = _args[15];
lean_object* v___y_4757_ = _args[16];
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4741_, v_machine_4742_, v_a_4743_, v___x_4744_, v_socket_4745_, v_connectionContext_4746_, v_h_4747_, v_responseBodyInstance_4748_, v_handler_4749_, v___f_4750_, v_inst_4751_, v_extensions_4752_, v___f_4753_, v___f_4754_, v___f_4755_, v_x_4756_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4759_, lean_object* v_machine_4760_, lean_object* v_socket_4761_, lean_object* v_connectionContext_4762_, lean_object* v_h_4763_, lean_object* v_responseBodyInstance_4764_, lean_object* v_handler_4765_, lean_object* v___f_4766_, lean_object* v_inst_4767_, lean_object* v_extensions_4768_, lean_object* v___f_4769_, lean_object* v___f_4770_, lean_object* v___f_4771_, lean_object* v_x_4772_){
_start:
{
if (lean_obj_tag(v_x_4772_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4782_; 
lean_dec_ref(v___f_4771_);
lean_dec_ref(v___f_4770_);
lean_dec_ref(v___f_4769_);
lean_dec(v_extensions_4768_);
lean_dec_ref(v_inst_4767_);
lean_dec_ref(v___f_4766_);
lean_dec(v_handler_4765_);
lean_dec_ref(v_responseBodyInstance_4764_);
lean_dec_ref(v_h_4763_);
lean_dec_ref(v_connectionContext_4762_);
lean_dec(v_socket_4761_);
lean_dec_ref(v_machine_4760_);
lean_dec_ref(v_config_4759_);
v_a_4774_ = lean_ctor_get(v_x_4772_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_x_4772_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4776_ = v_x_4772_;
v_isShared_4777_ = v_isSharedCheck_4782_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v_x_4772_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4782_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4797_; 
v_a_4783_ = lean_ctor_get(v_x_4772_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_x_4772_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4785_ = v_x_4772_;
v_isShared_4786_ = v_isSharedCheck_4797_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v_x_4772_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4797_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___f_4789_; lean_object* v___x_4791_; 
v___x_4787_ = lean_box(0);
v___x_4788_ = l_Std_CloseableChannel_new___redArg(v___x_4787_);
v___f_4789_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4789_, 0, v_config_4759_);
lean_closure_set(v___f_4789_, 1, v_machine_4760_);
lean_closure_set(v___f_4789_, 2, v_a_4783_);
lean_closure_set(v___f_4789_, 3, v___x_4787_);
lean_closure_set(v___f_4789_, 4, v_socket_4761_);
lean_closure_set(v___f_4789_, 5, v_connectionContext_4762_);
lean_closure_set(v___f_4789_, 6, v_h_4763_);
lean_closure_set(v___f_4789_, 7, v_responseBodyInstance_4764_);
lean_closure_set(v___f_4789_, 8, v_handler_4765_);
lean_closure_set(v___f_4789_, 9, v___f_4766_);
lean_closure_set(v___f_4789_, 10, v_inst_4767_);
lean_closure_set(v___f_4789_, 11, v_extensions_4768_);
lean_closure_set(v___f_4789_, 12, v___f_4769_);
lean_closure_set(v___f_4789_, 13, v___f_4770_);
lean_closure_set(v___f_4789_, 14, v___f_4771_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4788_);
v___x_4791_ = v___x_4785_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v___x_4788_);
v___x_4791_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; lean_object* v___x_4795_; 
v___x_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
v___x_4793_ = lean_unsigned_to_nat(0u);
v___x_4794_ = 0;
v___x_4795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4793_, v___x_4794_, v___x_4792_, v___f_4789_);
return v___x_4795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4798_, lean_object* v_machine_4799_, lean_object* v_socket_4800_, lean_object* v_connectionContext_4801_, lean_object* v_h_4802_, lean_object* v_responseBodyInstance_4803_, lean_object* v_handler_4804_, lean_object* v___f_4805_, lean_object* v_inst_4806_, lean_object* v_extensions_4807_, lean_object* v___f_4808_, lean_object* v___f_4809_, lean_object* v___f_4810_, lean_object* v_x_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4798_, v_machine_4799_, v_socket_4800_, v_connectionContext_4801_, v_h_4802_, v_responseBodyInstance_4803_, v_handler_4804_, v___f_4805_, v_inst_4806_, v_extensions_4807_, v___f_4808_, v___f_4809_, v___f_4810_, v_x_4811_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4817_, lean_object* v_h_4818_, lean_object* v_connection_4819_, lean_object* v_config_4820_, lean_object* v_connectionContext_4821_, lean_object* v_handler_4822_){
_start:
{
lean_object* v_responseBodyInstance_4824_; lean_object* v_onFailure_4825_; lean_object* v___x_4826_; lean_object* v_socket_4827_; lean_object* v_machine_4828_; lean_object* v_extensions_4829_; lean_object* v___f_4830_; lean_object* v___f_4831_; lean_object* v___f_4832_; lean_object* v___f_4833_; lean_object* v___f_4834_; lean_object* v___f_4835_; lean_object* v___f_4836_; lean_object* v___f_4837_; lean_object* v___f_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; lean_object* v___x_4841_; 
v_responseBodyInstance_4824_ = lean_ctor_get(v_h_4818_, 0);
lean_inc_ref_n(v_responseBodyInstance_4824_, 2);
v_onFailure_4825_ = lean_ctor_get(v_h_4818_, 2);
v___x_4826_ = l_Std_Http_Body_mkStream();
v_socket_4827_ = lean_ctor_get(v_connection_4819_, 0);
lean_inc_n(v_socket_4827_, 2);
v_machine_4828_ = lean_ctor_get(v_connection_4819_, 1);
lean_inc_ref(v_machine_4828_);
v_extensions_4829_ = lean_ctor_get(v_connection_4819_, 2);
lean_inc(v_extensions_4829_);
lean_dec_ref(v_connection_4819_);
v___f_4830_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4831_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4832_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4833_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4822_);
lean_inc_ref(v_onFailure_4825_);
v___f_4834_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4834_, 0, v_onFailure_4825_);
lean_closure_set(v___f_4834_, 1, v_handler_4822_);
lean_closure_set(v___f_4834_, 2, v___f_4833_);
lean_inc_ref(v_inst_4817_);
v___f_4835_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4835_, 0, v_inst_4817_);
lean_closure_set(v___f_4835_, 1, v_socket_4827_);
lean_inc_ref(v___f_4835_);
v___f_4836_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4836_, 0, v___f_4835_);
v___f_4837_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4837_, 0, v___f_4830_);
lean_closure_set(v___f_4837_, 1, v_responseBodyInstance_4824_);
lean_closure_set(v___f_4837_, 2, v___f_4836_);
lean_closure_set(v___f_4837_, 3, v___f_4835_);
v___f_4838_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4838_, 0, v_config_4820_);
lean_closure_set(v___f_4838_, 1, v_machine_4828_);
lean_closure_set(v___f_4838_, 2, v_socket_4827_);
lean_closure_set(v___f_4838_, 3, v_connectionContext_4821_);
lean_closure_set(v___f_4838_, 4, v_h_4818_);
lean_closure_set(v___f_4838_, 5, v_responseBodyInstance_4824_);
lean_closure_set(v___f_4838_, 6, v_handler_4822_);
lean_closure_set(v___f_4838_, 7, v___f_4831_);
lean_closure_set(v___f_4838_, 8, v_inst_4817_);
lean_closure_set(v___f_4838_, 9, v_extensions_4829_);
lean_closure_set(v___f_4838_, 10, v___f_4832_);
lean_closure_set(v___f_4838_, 11, v___f_4834_);
lean_closure_set(v___f_4838_, 12, v___f_4837_);
v___x_4839_ = lean_unsigned_to_nat(0u);
v___x_4840_ = 0;
v___x_4841_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4839_, v___x_4840_, v___x_4826_, v___f_4838_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4842_, lean_object* v_h_4843_, lean_object* v_connection_4844_, lean_object* v_config_4845_, lean_object* v_connectionContext_4846_, lean_object* v_handler_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4842_, v_h_4843_, v_connection_4844_, v_config_4845_, v_connectionContext_4846_, v_handler_4847_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4850_, lean_object* v_00_u03c3_4851_, lean_object* v_inst_4852_, lean_object* v_h_4853_, lean_object* v_connection_4854_, lean_object* v_config_4855_, lean_object* v_connectionContext_4856_, lean_object* v_handler_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4852_, v_h_4853_, v_connection_4854_, v_config_4855_, v_connectionContext_4856_, v_handler_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4860_, lean_object* v_00_u03c3_4861_, lean_object* v_inst_4862_, lean_object* v_h_4863_, lean_object* v_connection_4864_, lean_object* v_config_4865_, lean_object* v_connectionContext_4866_, lean_object* v_handler_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4860_, v_00_u03c3_4861_, v_inst_4862_, v_h_4863_, v_connection_4864_, v_config_4865_, v_connectionContext_4866_, v_handler_4867_);
return v_res_4869_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4870_; lean_object* v___x_4871_; 
v___x_4870_ = 0;
v___x_4871_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4870_);
return v___x_4871_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = lean_unsigned_to_nat(4096u);
v___x_4873_ = lean_mk_empty_byte_array(v___x_4872_);
return v___x_4873_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4874_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4875_ = l_ByteArray_mkIterator(v___x_4874_);
return v___x_4875_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4876_ = 0;
v___x_4877_ = lean_unsigned_to_nat(0u);
v___x_4878_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4879_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4880_ = lean_box(0);
v___x_4881_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
lean_ctor_set(v___x_4881_, 1, v___x_4879_);
lean_ctor_set(v___x_4881_, 2, v___x_4878_);
lean_ctor_set(v___x_4881_, 3, v___x_4877_);
lean_ctor_set(v___x_4881_, 4, v___x_4877_);
lean_ctor_set(v___x_4881_, 5, v___x_4877_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*6, v___x_4876_);
return v___x_4881_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = 1;
v___x_4890_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4889_);
return v___x_4890_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4891_; uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4891_ = lean_unsigned_to_nat(0u);
v___x_4892_ = 0;
v___x_4893_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4894_ = lean_box(0);
v___x_4895_ = lean_box(0);
v___x_4896_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4897_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4898_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
lean_ctor_set(v___x_4898_, 1, v___x_4896_);
lean_ctor_set(v___x_4898_, 2, v___x_4895_);
lean_ctor_set(v___x_4898_, 3, v___x_4894_);
lean_ctor_set(v___x_4898_, 4, v___x_4893_);
lean_ctor_set(v___x_4898_, 5, v___x_4891_);
lean_ctor_set_uint8(v___x_4898_, sizeof(void*)*6, v___x_4892_);
lean_ctor_set_uint8(v___x_4898_, sizeof(void*)*6 + 1, v___x_4892_);
lean_ctor_set_uint8(v___x_4898_, sizeof(void*)*6 + 2, v___x_4892_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4899_, lean_object* v_client_4900_, lean_object* v_extensions_4901_, lean_object* v_inst_4902_, lean_object* v_inst_4903_, lean_object* v_handler_4904_, lean_object* v_x_4905_){
_start:
{
if (lean_obj_tag(v_x_4905_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4915_; 
lean_dec(v_handler_4904_);
lean_dec_ref(v_inst_4903_);
lean_dec_ref(v_inst_4902_);
lean_dec(v_extensions_4901_);
lean_dec(v_client_4900_);
lean_dec_ref(v_config_4899_);
v_a_4907_ = lean_ctor_get(v_x_4905_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_x_4905_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4909_ = v_x_4905_;
v_isShared_4910_ = v_isSharedCheck_4915_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v_x_4905_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4915_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; 
v___x_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
return v___x_4913_;
}
}
}
else
{
lean_object* v_a_4916_; uint8_t v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; uint8_t v_enableKeepAlive_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
v_a_4916_ = lean_ctor_get(v_x_4905_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v_x_4905_, 1);
v___x_4917_ = 0;
v___x_4918_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4919_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4920_ = lean_box(0);
v___x_4921_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4922_ = l_Std_Http_Config_toH1Config(v_config_4899_);
v_enableKeepAlive_4923_ = lean_ctor_get_uint8(v___x_4922_, sizeof(void*)*18);
v___x_4924_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4924_, 0, v___x_4918_);
lean_ctor_set(v___x_4924_, 1, v___x_4921_);
lean_ctor_set(v___x_4924_, 2, v___x_4922_);
lean_ctor_set(v___x_4924_, 3, v___x_4919_);
lean_ctor_set(v___x_4924_, 4, v___x_4920_);
lean_ctor_set(v___x_4924_, 5, v___x_4920_);
lean_ctor_set_uint8(v___x_4924_, sizeof(void*)*6, v_enableKeepAlive_4923_);
lean_ctor_set_uint8(v___x_4924_, sizeof(void*)*6 + 1, v___x_4917_);
lean_ctor_set_uint8(v___x_4924_, sizeof(void*)*6 + 2, v___x_4917_);
v___x_4925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4925_, 0, v_client_4900_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
lean_ctor_set(v___x_4925_, 2, v_extensions_4901_);
v___x_4926_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4902_, v_inst_4903_, v___x_4925_, v_config_4899_, v_a_4916_, v_handler_4904_);
return v___x_4926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4927_, lean_object* v_client_4928_, lean_object* v_extensions_4929_, lean_object* v_inst_4930_, lean_object* v_inst_4931_, lean_object* v_handler_4932_, lean_object* v_x_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4927_, v_client_4928_, v_extensions_4929_, v_inst_4930_, v_inst_4931_, v_handler_4932_, v_x_4933_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4936_, lean_object* v_inst_4937_, lean_object* v_client_4938_, lean_object* v_handler_4939_, lean_object* v_config_4940_, lean_object* v_extensions_4941_, lean_object* v_a_4942_){
_start:
{
lean_object* v___f_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; uint8_t v___x_4948_; lean_object* v___x_4949_; 
v___f_4944_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4944_, 0, v_config_4940_);
lean_closure_set(v___f_4944_, 1, v_client_4938_);
lean_closure_set(v___f_4944_, 2, v_extensions_4941_);
lean_closure_set(v___f_4944_, 3, v_inst_4936_);
lean_closure_set(v___f_4944_, 4, v_inst_4937_);
lean_closure_set(v___f_4944_, 5, v_handler_4939_);
lean_inc_ref(v_a_4942_);
v___x_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4945_, 0, v_a_4942_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
v___x_4947_ = lean_unsigned_to_nat(0u);
v___x_4948_ = 0;
v___x_4949_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4947_, v___x_4948_, v___x_4946_, v___f_4944_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4950_, lean_object* v_inst_4951_, lean_object* v_client_4952_, lean_object* v_handler_4953_, lean_object* v_config_4954_, lean_object* v_extensions_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4950_, v_inst_4951_, v_client_4952_, v_handler_4953_, v_config_4954_, v_extensions_4955_, v_a_4956_);
lean_dec_ref(v_a_4956_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4959_, lean_object* v_00_u03c3_4960_, lean_object* v_inst_4961_, lean_object* v_inst_4962_, lean_object* v_client_4963_, lean_object* v_handler_4964_, lean_object* v_config_4965_, lean_object* v_extensions_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v___x_4969_; 
v___x_4969_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4961_, v_inst_4962_, v_client_4963_, v_handler_4964_, v_config_4965_, v_extensions_4966_, v_a_4967_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4970_, lean_object* v_00_u03c3_4971_, lean_object* v_inst_4972_, lean_object* v_inst_4973_, lean_object* v_client_4974_, lean_object* v_handler_4975_, lean_object* v_config_4976_, lean_object* v_extensions_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Std_Http_Server_serveConnection(v_t_4970_, v_00_u03c3_4971_, v_inst_4972_, v_inst_4973_, v_client_4974_, v_handler_4975_, v_config_4976_, v_extensions_4977_, v_a_4978_);
lean_dec_ref(v_a_4978_);
return v_res_4980_;
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
