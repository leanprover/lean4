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
uint8_t lean_bool_not(uint8_t);
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
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13;
static const lean_array_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
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
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_machine_507_);
v_a_510_ = lean_ctor_get(v_x_508_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v_x_508_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v_x_508_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_538_; 
v_a_519_ = lean_ctor_get(v_x_508_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_538_ == 0)
{
v___x_521_ = v_x_508_;
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v_x_508_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___y_524_; uint8_t v___x_535_; 
v___x_535_ = lean_unbox(v_a_519_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(40);
v___y_524_ = v___x_536_;
goto v___jp_523_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
v___y_524_ = v___x_537_;
goto v___jp_523_;
}
v___jp_523_:
{
uint8_t v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_525_ = 0;
lean_inc(v___y_524_);
v___x_526_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_525_, v_machine_507_, v___y_524_);
v___x_527_ = lean_unbox(v_a_519_);
lean_dec(v_a_519_);
v___x_528_ = lean_bool_not(v___x_527_);
v___x_529_ = lean_box(v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_526_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_534_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_539_, lean_object* v_x_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_539_, v_x_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_box(v___y_543_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___y_1391__boxed_550_; lean_object* v_res_551_; 
v___y_1391__boxed_550_ = lean_unbox(v___y_548_);
v_res_551_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1391__boxed_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v_x_552_, 1);
v___x_554_ = lean_task_pure(v_a_553_);
return v___x_554_;
}
else
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v_x_552_, 0);
lean_inc_ref(v_a_555_);
lean_dec_ref_known(v_x_552_, 1);
return v_a_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref_known(v_x_557_, 1);
v___x_559_ = 0;
v___x_560_ = lean_box(v___x_559_);
v___x_561_ = l_Std_Channel_send___redArg(v_a_556_, v___x_560_);
lean_dec_ref(v___x_561_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_a_563_ = lean_ctor_get(v_x_557_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v_x_557_, 1);
v___x_564_ = l_Std_Channel_send___redArg(v_a_556_, v_a_563_);
lean_dec_ref(v___x_564_);
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_566_, lean_object* v_x_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_566_, v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_box(v___x_570_);
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_576_, lean_object* v_x_577_, lean_object* v___y_578_){
_start:
{
uint8_t v___x_1435__boxed_579_; lean_object* v_res_580_; 
v___x_1435__boxed_579_ = lean_unbox(v___x_576_);
v_res_580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1435__boxed_579_, v_x_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_581_, uint8_t v___x_582_, lean_object* v_a_583_, lean_object* v___f_584_, lean_object* v___f_585_, lean_object* v___x_586_, uint8_t v___x_587_, lean_object* v___f_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v___f_588_);
lean_dec(v___x_586_);
lean_dec_ref(v___f_585_);
lean_dec_ref(v___f_584_);
lean_dec_ref(v_a_583_);
lean_dec_ref(v_connectionContext_581_);
v_a_591_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_x_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v_x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v_token_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_a_600_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v_x_589_, 1);
v_token_601_ = lean_ctor_get(v_connectionContext_581_, 1);
lean_inc_ref(v_token_601_);
lean_dec_ref(v_connectionContext_581_);
v___x_602_ = lean_box(v___x_582_);
v___x_603_ = l_Std_Channel_recvSelector___redArg(v___x_602_, v_a_583_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___f_584_);
v___x_605_ = l_Std_CancellationToken_selector(v_token_601_);
lean_inc_ref(v___f_585_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___f_585_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v_a_600_);
lean_ctor_set(v___x_607_, 1, v___f_585_);
v___x_608_ = lean_unsigned_to_nat(3u);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_608_);
v___x_610_ = lean_array_push(v___x_609_, v___x_604_);
v___x_611_ = lean_array_push(v___x_610_, v___x_606_);
v___x_612_ = lean_array_push(v___x_611_, v___x_607_);
v___x_613_ = l_Std_Async_Selectable_one___redArg(v___x_612_);
v___x_614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_586_, v___x_587_, v___x_613_, v___f_588_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_615_, lean_object* v___x_616_, lean_object* v_a_617_, lean_object* v___f_618_, lean_object* v___f_619_, lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v___f_622_, lean_object* v_x_623_, lean_object* v___y_624_){
_start:
{
uint8_t v___x_1450__boxed_625_; uint8_t v___x_1455__boxed_626_; lean_object* v_res_627_; 
v___x_1450__boxed_625_ = lean_unbox(v___x_616_);
v___x_1455__boxed_626_ = lean_unbox(v___x_621_);
v_res_627_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_615_, v___x_1450__boxed_625_, v_a_617_, v___f_618_, v___f_619_, v___x_620_, v___x_1455__boxed_626_, v___f_622_, v_x_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_628_, lean_object* v___x_629_, uint8_t v___x_630_, lean_object* v___f_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v___f_631_);
lean_dec(v___x_629_);
v_a_634_ = lean_ctor_get(v_x_632_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_642_ == 0)
{
v___x_636_ = v_x_632_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v_x_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
}
else
{
lean_object* v_lingeringTimeout_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec_ref_known(v_x_632_, 1);
v_lingeringTimeout_643_ = lean_ctor_get(v_config_628_, 4);
v___x_644_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_643_);
v___x_645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_629_, v___x_630_, v___x_644_, v___f_631_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_646_, lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v___f_649_, lean_object* v_x_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___x_1524__boxed_652_; lean_object* v_res_653_; 
v___x_1524__boxed_652_ = lean_unbox(v___x_648_);
v_res_653_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_646_, v___x_647_, v___x_1524__boxed_652_, v___f_649_, v_x_650_);
lean_dec_ref(v_config_646_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v___f_657_, lean_object* v___x_658_, lean_object* v_connectionContext_659_, uint8_t v___x_660_, lean_object* v_a_661_, lean_object* v___f_662_, lean_object* v___f_663_, lean_object* v_config_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_config_664_);
lean_dec_ref(v___f_663_);
lean_dec_ref(v___f_662_);
lean_dec_ref(v_a_661_);
lean_dec_ref(v_connectionContext_659_);
lean_dec(v___x_658_);
lean_dec_ref(v___f_657_);
v_a_667_ = lean_ctor_get(v_x_665_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v_x_665_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v_x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_674_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; 
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_693_; 
v_a_676_ = lean_ctor_get(v_x_665_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_693_ == 0)
{
v___x_678_ = v_x_665_;
v_isShared_679_ = v_isSharedCheck_693_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v_x_665_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_693_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___f_687_; lean_object* v___x_689_; 
v___x_680_ = 0;
lean_inc_n(v___x_658_, 3);
v___x_681_ = l_BaseIO_chainTask___redArg(v_a_676_, v___f_657_, v___x_658_, v___x_680_);
v___f_682_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_683_ = lean_box(v___x_660_);
v___x_684_ = lean_box(v___x_680_);
v___f_685_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_685_, 0, v_connectionContext_659_);
lean_closure_set(v___f_685_, 1, v___x_683_);
lean_closure_set(v___f_685_, 2, v_a_661_);
lean_closure_set(v___f_685_, 3, v___f_662_);
lean_closure_set(v___f_685_, 4, v___f_682_);
lean_closure_set(v___f_685_, 5, v___x_658_);
lean_closure_set(v___f_685_, 6, v___x_684_);
lean_closure_set(v___f_685_, 7, v___f_663_);
v___x_686_ = lean_box(v___x_680_);
v___f_687_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_687_, 0, v_config_664_);
lean_closure_set(v___f_687_, 1, v___x_658_);
lean_closure_set(v___f_687_, 2, v___x_686_);
lean_closure_set(v___f_687_, 3, v___f_685_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_689_ = v___x_678_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_681_);
v___x_689_ = v_reuseFailAlloc_692_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___x_691_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_658_, v___x_680_, v___x_690_, v___f_687_);
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v___f_694_, lean_object* v___x_695_, lean_object* v_connectionContext_696_, lean_object* v___x_697_, lean_object* v_a_698_, lean_object* v___f_699_, lean_object* v___f_700_, lean_object* v_config_701_, lean_object* v_x_702_, lean_object* v___y_703_){
_start:
{
uint8_t v___x_1566__boxed_704_; lean_object* v_res_705_; 
v___x_1566__boxed_704_ = lean_unbox(v___x_697_);
v_res_705_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v___f_694_, v___x_695_, v_connectionContext_696_, v___x_1566__boxed_704_, v_a_698_, v___f_699_, v___f_700_, v_config_701_, v_x_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_706_, lean_object* v_handler_707_, lean_object* v_head_708_, lean_object* v_connectionContext_709_, uint8_t v___x_710_, lean_object* v___f_711_, lean_object* v___f_712_, lean_object* v_config_713_, lean_object* v___f_714_, lean_object* v_x_715_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___f_714_);
lean_dec_ref(v_config_713_);
lean_dec_ref(v___f_712_);
lean_dec_ref(v___f_711_);
lean_dec_ref(v_connectionContext_709_);
lean_dec_ref(v_head_708_);
lean_dec(v_handler_707_);
lean_dec_ref(v_inst_706_);
v_a_717_ = lean_ctor_get(v_x_715_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_725_ == 0)
{
v___x_719_ = v_x_715_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v_x_715_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_724_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_746_; 
v_a_726_ = lean_ctor_get(v_x_715_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_746_ == 0)
{
v___x_728_ = v_x_715_;
v_isShared_729_ = v_isSharedCheck_746_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v_x_715_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_746_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_onContinue_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___f_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v_onContinue_730_ = lean_ctor_get(v_inst_706_, 3);
lean_inc_ref(v_onContinue_730_);
lean_dec_ref(v_inst_706_);
v___x_731_ = lean_apply_2(v_onContinue_730_, v_handler_707_, v_head_708_);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_733_, 0, lean_box(0));
lean_closure_set(v___x_733_, 1, v___x_731_);
v___x_734_ = lean_io_as_task(v___x_733_, v___x_732_);
lean_inc(v_a_726_);
v___f_735_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_735_, 0, v_a_726_);
v___x_736_ = lean_box(v___x_710_);
v___f_737_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_737_, 0, v___f_735_);
lean_closure_set(v___f_737_, 1, v___x_732_);
lean_closure_set(v___f_737_, 2, v_connectionContext_709_);
lean_closure_set(v___f_737_, 3, v___x_736_);
lean_closure_set(v___f_737_, 4, v_a_726_);
lean_closure_set(v___f_737_, 5, v___f_711_);
lean_closure_set(v___f_737_, 6, v___f_712_);
lean_closure_set(v___f_737_, 7, v_config_713_);
v___x_738_ = 1;
v___x_739_ = lean_task_bind(v___x_734_, v___f_714_, v___x_732_, v___x_738_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_739_);
v___x_741_ = v___x_728_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
v___x_743_ = 0;
v___x_744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_732_, v___x_743_, v___x_742_, v___f_737_);
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_747_, lean_object* v_handler_748_, lean_object* v_head_749_, lean_object* v_connectionContext_750_, lean_object* v___x_751_, lean_object* v___f_752_, lean_object* v___f_753_, lean_object* v_config_754_, lean_object* v___f_755_, lean_object* v_x_756_, lean_object* v___y_757_){
_start:
{
uint8_t v___x_1647__boxed_758_; lean_object* v_res_759_; 
v___x_1647__boxed_758_ = lean_unbox(v___x_751_);
v_res_759_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_747_, v_handler_748_, v_head_749_, v_connectionContext_750_, v___x_1647__boxed_758_, v___f_752_, v___f_753_, v_config_754_, v___f_755_, v_x_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_762_, lean_object* v_handler_763_, lean_object* v_machine_764_, lean_object* v_head_765_, lean_object* v_config_766_, lean_object* v_connectionContext_767_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_769_ = lean_box(0);
v___x_770_ = l_Std_CloseableChannel_new___redArg(v___x_769_);
v___f_771_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_771_, 0, v_machine_764_);
v___f_772_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_773_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_774_ = 0;
v___x_775_ = lean_box(v___x_774_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_776_, 0, v_inst_762_);
lean_closure_set(v___f_776_, 1, v_handler_763_);
lean_closure_set(v___f_776_, 2, v_head_765_);
lean_closure_set(v___f_776_, 3, v_connectionContext_767_);
lean_closure_set(v___f_776_, 4, v___x_775_);
lean_closure_set(v___f_776_, 5, v___f_772_);
lean_closure_set(v___f_776_, 6, v___f_771_);
lean_closure_set(v___f_776_, 7, v_config_766_);
lean_closure_set(v___f_776_, 8, v___f_773_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_770_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_779_, v___x_774_, v___x_778_, v___f_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_781_, lean_object* v_handler_782_, lean_object* v_machine_783_, lean_object* v_head_784_, lean_object* v_config_785_, lean_object* v_connectionContext_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_781_, v_handler_782_, v_machine_783_, v_head_784_, v_config_785_, v_connectionContext_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_789_, lean_object* v_inst_790_, lean_object* v_handler_791_, lean_object* v_machine_792_, lean_object* v_head_793_, lean_object* v_config_794_, lean_object* v_connectionContext_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_790_, v_handler_791_, v_machine_792_, v_head_793_, v_config_794_, v_connectionContext_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_798_, lean_object* v_inst_799_, lean_object* v_handler_800_, lean_object* v_machine_801_, lean_object* v_head_802_, lean_object* v_config_803_, lean_object* v_connectionContext_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_798_, v_inst_799_, v_handler_800_, v_machine_801_, v_head_802_, v_config_803_, v_connectionContext_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_x_807_, lean_object* v_x_808_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(lean_object* v_i_835_, lean_object* v_source_836_, lean_object* v_target_837_){
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
v_target_843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_target_837_, v_es_840_);
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
v___x_854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v___x_851_, v_data_847_, v___x_853_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_961_, lean_object* v_indexes_962_, lean_object* v_status_963_, uint8_t v_version_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
lean_dec(v_status_963_);
lean_dec_ref(v_indexes_962_);
lean_dec_ref(v_entries_961_);
v_a_967_ = lean_ctor_get(v_x_965_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v_x_965_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v_x_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_993_; 
v_a_976_ = lean_ctor_get(v_x_965_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_993_ == 0)
{
v___x_978_ = v_x_965_;
v_isShared_979_ = v_isSharedCheck_993_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v_x_965_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_993_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_i_983_; lean_object* v___x_984_; lean_object* v_entries_985_; lean_object* v_indexes_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_980_ = l_Std_Http_Header_Name_date;
v___x_981_ = l_Std_Time_DateTime_toRFC822String(v_a_976_);
v___x_982_ = l_Std_Http_Header_Value_ofString_x21(v___x_981_);
v_i_983_ = lean_array_get_size(v_entries_961_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_980_);
lean_ctor_set(v___x_984_, 1, v___x_982_);
v_entries_985_ = lean_array_push(v_entries_961_, v___x_984_);
v_indexes_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_983_, v_indexes_962_, v___x_980_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_entries_985_);
lean_ctor_set(v___x_987_, 1, v_indexes_986_);
v___x_988_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_988_, 0, v_status_963_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*2, v_version_964_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_988_);
v___x_990_ = v___x_978_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_994_, lean_object* v_indexes_995_, lean_object* v_status_996_, lean_object* v_version_997_, lean_object* v_x_998_, lean_object* v___y_999_){
_start:
{
uint8_t v_version_boxed_1000_; lean_object* v_res_1001_; 
v_version_boxed_1000_ = lean_unbox(v_version_997_);
v_res_1001_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_994_, v_indexes_995_, v_status_996_, v_version_boxed_1000_, v_x_998_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1004_, lean_object* v_a_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v_offset_1007_; lean_object* v_second_1008_; lean_object* v_nano_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_offset_1007_ = lean_ctor_get(v_tz_1004_, 0);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1019_, lean_object* v_a_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1019_, v_a_1020_, v_x_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_tz_1019_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1046_, lean_object* v_head_1047_){
_start:
{
uint8_t v_generateDate_1052_; 
v_generateDate_1052_ = lean_ctor_get_uint8(v_config_1046_, sizeof(void*)*24 + 1);
if (v_generateDate_1052_ == 0)
{
goto v___jp_1049_;
}
else
{
lean_object* v_headers_1053_; lean_object* v_status_1054_; uint8_t v_version_1055_; lean_object* v_entries_1056_; lean_object* v_indexes_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_headers_1053_ = lean_ctor_get(v_head_1047_, 1);
v_status_1054_ = lean_ctor_get(v_head_1047_, 0);
v_version_1055_ = lean_ctor_get_uint8(v_head_1047_, sizeof(void*)*2);
v_entries_1056_ = lean_ctor_get(v_headers_1053_, 0);
v_indexes_1057_ = lean_ctor_get(v_headers_1053_, 1);
v___x_1058_ = l_Std_Http_Header_Name_date;
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_indexes_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v_val_1063_; lean_object* v_a_1068_; lean_object* v___x_1070_; 
lean_inc_ref(v_indexes_1057_);
lean_inc_ref(v_entries_1056_);
lean_inc(v_status_1054_);
lean_dec_ref(v_head_1047_);
v___x_1060_ = lean_box(v_version_1055_);
v___f_1061_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1061_, 0, v_entries_1056_);
lean_closure_set(v___f_1061_, 1, v_indexes_1057_);
lean_closure_set(v___f_1061_, 2, v_status_1054_);
lean_closure_set(v___f_1061_, 3, v___x_1060_);
v___x_1070_ = lean_get_current_time();
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1073_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1085_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_tz_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_inc(v_a_1074_);
v_tz_1078_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1074_, v_a_1071_);
lean_inc(v_a_1071_);
lean_inc_ref(v_tz_1078_);
v___f_1079_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1079_, 0, v_tz_1078_);
lean_closure_set(v___f_1079_, 1, v_a_1071_);
v___x_1080_ = lean_mk_thunk(v___f_1079_);
v___x_1081_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_a_1071_);
lean_ctor_set(v___x_1081_, 2, v_a_1074_);
lean_ctor_set(v___x_1081_, 3, v_tz_1078_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1081_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
v_val_1063_ = v___x_1083_;
goto v___jp_1062_;
}
}
}
else
{
lean_object* v_a_1086_; 
lean_dec(v_a_1071_);
v_a_1086_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1073_, 1);
v_a_1068_ = v_a_1086_;
goto v___jp_1067_;
}
}
else
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1070_, 1);
v_a_1068_ = v_a_1087_;
goto v___jp_1067_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_val_1063_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1065_, v___x_1059_, v___x_1064_, v___f_1061_);
return v___x_1066_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_a_1068_);
v_val_1063_ = v___x_1069_;
goto v___jp_1062_;
}
}
else
{
goto v___jp_1049_;
}
}
v___jp_1049_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_head_1047_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1088_, lean_object* v_head_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1088_, v_head_1089_);
lean_dec_ref(v_config_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1_spec__4(lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_nat_to_int(v_a_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_nat_to_int(v_a_1094_);
v___x_1096_ = l_Rat_ofInt(v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_00_u03b2_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___redArg(v_m_1098_, v_a_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2___boxed(lean_object* v_00_u03b2_1101_, lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_res_1104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(v_00_u03b2_1101_, v_m_1102_, v_a_1103_);
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_m_1102_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1106_, lean_object* v_a_1107_, lean_object* v_x_1108_){
_start:
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1110_, v_a_1111_, v_x_1112_);
lean_dec(v_x_1112_);
lean_dec_ref(v_a_1111_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1115_, lean_object* v_data_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1118_, lean_object* v_i_1119_, lean_object* v_source_1120_, lean_object* v_target_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v_i_1119_, v_source_1120_, v_target_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1124_, v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1127_, lean_object* v_____r_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___y_1127_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1134_, lean_object* v_____r_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1134_, v_____r_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v___f_1138_);
v_a_1141_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v_x_1139_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v_x_1139_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v_x_1139_, 1);
v___x_1151_ = lean_apply_2(v___f_1138_, v_a_1150_, lean_box(0));
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1152_, v_x_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1156_, lean_object* v_body_1157_, lean_object* v___f_1158_, lean_object* v___f_1159_, lean_object* v_x_1160_){
_start:
{
if (lean_obj_tag(v_x_1160_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___f_1159_);
lean_dec_ref(v___f_1158_);
lean_dec(v_body_1157_);
lean_dec_ref(v_close_1156_);
v_a_1162_ = lean_ctor_get(v_x_1160_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_x_1160_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1164_ = v_x_1160_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v_x_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1171_; uint8_t v___x_1172_; 
v_a_1171_ = lean_ctor_get(v_x_1160_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v_x_1160_, 1);
v___x_1172_ = lean_unbox(v_a_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v___f_1159_);
v___x_1173_ = lean_apply_2(v_close_1156_, v_body_1157_, lean_box(0));
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_unbox(v_a_1171_);
lean_dec(v_a_1171_);
v___x_1176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1174_, v___x_1175_, v___x_1173_, v___f_1158_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_a_1171_);
lean_dec_ref(v___f_1158_);
lean_dec(v_body_1157_);
lean_dec_ref(v_close_1156_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_apply_2(v___f_1159_, v___x_1177_, lean_box(0));
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1179_, lean_object* v_body_1180_, lean_object* v___f_1181_, lean_object* v___f_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1179_, v_body_1180_, v___f_1181_, v___f_1182_, v_x_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___f_1186_, lean_object* v___f_1187_, lean_object* v_x1_1188_, lean_object* v_x2_1189_){
_start:
{
lean_object* v_fst_1190_; lean_object* v_entries_1191_; lean_object* v_indexes_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1203_; 
v_fst_1190_ = lean_ctor_get(v_x2_1189_, 0);
lean_inc(v_fst_1190_);
v_entries_1191_ = lean_ctor_get(v_x1_1188_, 0);
v_indexes_1192_ = lean_ctor_get(v_x1_1188_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x1_1188_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1194_ = v_x1_1188_;
v_isShared_1195_ = v_isSharedCheck_1203_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_indexes_1192_);
lean_inc(v_entries_1191_);
lean_dec(v_x1_1188_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1203_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_i_1196_; lean_object* v_f_1197_; lean_object* v_entries_1198_; lean_object* v_indexes_1199_; lean_object* v___x_1201_; 
v_i_1196_ = lean_array_get_size(v_entries_1191_);
v_f_1197_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1197_, 0, v_i_1196_);
v_entries_1198_ = lean_array_push(v_entries_1191_, v_x2_1189_);
v_indexes_1199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1186_, v___f_1187_, v_indexes_1192_, v_fst_1190_, v_f_1197_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_indexes_1199_);
lean_ctor_set(v___x_1194_, 0, v_entries_1198_);
v___x_1201_ = v___x_1194_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_entries_1198_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_indexes_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v___x_1204_, lean_object* v_x1_1205_, lean_object* v_x2_1206_){
_start:
{
lean_object* v_fst_1207_; uint8_t v___x_1208_; uint8_t v___x_1209_; 
v_fst_1207_ = lean_ctor_get(v_x2_1206_, 0);
v___x_1208_ = lean_string_dec_eq(v_fst_1207_, v___x_1204_);
v___x_1209_ = lean_bool_not(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_dec_ref(v_x2_1206_);
return v_x1_1205_;
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_array_push(v_x1_1205_, v_x2_1206_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v___x_1211_, lean_object* v_x1_1212_, lean_object* v_x2_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v___x_1211_, v_x1_1212_, v_x2_1213_);
lean_dec_ref(v___x_1211_);
return v_res_1214_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13(void){
_start:
{
lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; 
v___f_1239_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11));
v___f_1240_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___x_1241_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1240_, v___f_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___f_1245_; 
v___x_1244_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1245_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1245_, 0, v___x_1244_);
return v___f_1245_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16(void){
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
lean_object* v___y_1255_; uint8_t v_omitBody_1256_; lean_object* v___y_1269_; uint8_t v___y_1304_; lean_object* v___y_1305_; 
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
lean_object* v_writer_1318_; lean_object* v_a_1319_; lean_object* v_reader_1320_; lean_object* v_config_1321_; lean_object* v_events_1322_; lean_object* v_error_1323_; lean_object* v_instant_1324_; uint8_t v_keepAlive_1325_; uint8_t v_forcedFlush_1326_; uint8_t v_pullBodyStalled_1327_; lean_object* v_userData_1328_; lean_object* v_outputData_1329_; lean_object* v_state_1330_; lean_object* v_knownSize_1331_; lean_object* v_messageHead_1332_; uint8_t v_sentMessage_1333_; uint8_t v_userClosedBody_1334_; uint8_t v_omitBody_1335_; lean_object* v_userDataBytes_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1472_; 
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
v_isSharedCheck_1472_ = !lean_is_exclusive(v_writer_1318_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1338_ = v_writer_1318_;
v_isShared_1339_ = v_isSharedCheck_1472_;
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
v_isShared_1339_ = v_isSharedCheck_1472_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; lean_object* v___y_1394_; uint8_t v___x_1428_; uint8_t v___y_1430_; uint8_t v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1433_; uint8_t v___y_1434_; uint8_t v___y_1441_; uint8_t v___y_1442_; uint8_t v___y_1443_; uint8_t v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1460_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1428_ = 0;
v___x_1469_ = lean_box(1);
v___x_1470_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1330_, v___x_1469_);
if (v___x_1470_ == 0)
{
v___y_1460_ = v___x_1470_;
goto v___jp_1459_;
}
else
{
if (v_sentMessage_1333_ == 0)
{
v___y_1460_ = v___x_1470_;
goto v___jp_1459_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = 0;
v___y_1460_ = v___x_1471_;
goto v___jp_1459_;
}
}
v___jp_1340_:
{
lean_object* v_message_1343_; lean_object* v___x_2574__overap_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_message_1343_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1341_, v_a_1319_, v___y_1342_);
v___x_2574__overap_1344_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1341_);
v___x_1345_ = lean_apply_2(v___x_2574__overap_1344_, v_outputData_1329_, v_message_1343_);
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
v___x_1358_ = lean_nat_dec_lt(v___y_1353_, v___x_1356_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v___y_1355_);
lean_inc_ref(v___y_1352_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___y_1352_;
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
lean_inc_ref(v___y_1352_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___y_1352_;
goto v___jp_1340_;
}
else
{
size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = lean_usize_of_nat(v___x_1356_);
lean_inc_ref(v___y_1352_);
lean_inc_ref(v___y_1351_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1357_, v___y_1351_, v___y_1355_, v___x_1360_, v___x_1361_, v___y_1352_);
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
lean_inc_ref(v___y_1352_);
lean_inc_ref(v___y_1351_);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1357_, v___y_1351_, v___y_1355_, v___x_1363_, v___x_1364_, v___y_1352_);
v___y_1341_ = v___y_1354_;
v___y_1342_ = v___x_1365_;
goto v___jp_1340_;
}
}
}
v___jp_1366_:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___f_1371_; uint8_t v___x_1372_; 
v___x_1369_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1370_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___f_1371_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11));
v___x_1372_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1370_, v___f_1371_, v___x_1369_, v___y_1368_);
if (v___x_1372_ == 0)
{
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1368_;
goto v___jp_1340_;
}
else
{
lean_object* v_entries_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_entries_1373_ = lean_ctor_get(v___y_1368_, 0);
lean_inc_ref(v_entries_1373_);
lean_dec_ref(v___y_1368_);
v___f_1374_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1375_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_entries_1373_);
v___x_1378_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1379_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1380_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1380_ == 0)
{
lean_dec_ref(v_entries_1373_);
v___y_1351_ = v___f_1374_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1367_;
v___y_1355_ = v___x_1378_;
goto v___jp_1350_;
}
else
{
lean_object* v___f_1381_; uint8_t v___x_1382_; 
v___f_1381_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15);
v___x_1382_ = lean_nat_dec_le(v___x_1377_, v___x_1377_);
if (v___x_1382_ == 0)
{
if (v___x_1380_ == 0)
{
lean_dec_ref(v_entries_1373_);
v___y_1351_ = v___f_1374_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1367_;
v___y_1355_ = v___x_1378_;
goto v___jp_1350_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = lean_usize_of_nat(v___x_1377_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1379_, v___f_1381_, v_entries_1373_, v___x_1383_, v___x_1384_, v___x_1378_);
v___y_1351_ = v___f_1374_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1367_;
v___y_1355_ = v___x_1385_;
goto v___jp_1350_;
}
}
else
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = lean_usize_of_nat(v___x_1377_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1379_, v___f_1381_, v_entries_1373_, v___x_1386_, v___x_1387_, v___x_1378_);
v___y_1351_ = v___f_1374_;
v___y_1352_ = v___x_1375_;
v___y_1353_ = v___x_1376_;
v___y_1354_ = v___y_1367_;
v___y_1355_ = v___x_1388_;
goto v___jp_1350_;
}
}
}
}
v___jp_1389_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = lean_array_get_size(v___y_1394_);
v___x_1396_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1397_ = lean_nat_dec_lt(v___y_1391_, v___x_1395_);
if (v___x_1397_ == 0)
{
lean_dec_ref(v___y_1394_);
lean_inc_ref(v___y_1392_);
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1392_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_nat_dec_le(v___x_1395_, v___x_1395_);
if (v___x_1398_ == 0)
{
if (v___x_1397_ == 0)
{
lean_dec_ref(v___y_1394_);
lean_inc_ref(v___y_1392_);
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1392_;
goto v___jp_1366_;
}
else
{
size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = lean_usize_of_nat(v___x_1395_);
lean_inc_ref(v___y_1392_);
lean_inc_ref(v___y_1390_);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1396_, v___y_1390_, v___y_1394_, v___x_1399_, v___x_1400_, v___y_1392_);
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___x_1401_;
goto v___jp_1366_;
}
}
else
{
size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = lean_usize_of_nat(v___x_1395_);
lean_inc_ref(v___y_1392_);
lean_inc_ref(v___y_1390_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1396_, v___y_1390_, v___y_1394_, v___x_1402_, v___x_1403_, v___y_1392_);
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___x_1404_;
goto v___jp_1366_;
}
}
}
v___jp_1405_:
{
uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v___f_1410_; uint8_t v___x_1411_; 
v___x_1406_ = 1;
v___x_1407_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1406_, v_a_1319_);
v___x_1408_ = l_Std_Http_Header_Name_contentLength;
v___f_1409_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___f_1410_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11));
v___x_1411_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1409_, v___f_1410_, v___x_1408_, v___x_1407_);
if (v___x_1411_ == 0)
{
v___y_1367_ = v___x_1406_;
v___y_1368_ = v___x_1407_;
goto v___jp_1366_;
}
else
{
lean_object* v_entries_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_entries_1412_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_entries_1412_);
lean_dec_ref(v___x_1407_);
v___f_1413_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1414_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_entries_1412_);
v___x_1417_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14));
v___x_1418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1419_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1419_ == 0)
{
lean_dec_ref(v_entries_1412_);
v___y_1390_ = v___f_1413_;
v___y_1391_ = v___x_1415_;
v___y_1392_ = v___x_1414_;
v___y_1393_ = v___x_1406_;
v___y_1394_ = v___x_1417_;
goto v___jp_1389_;
}
else
{
lean_object* v___f_1420_; uint8_t v___x_1421_; 
v___f_1420_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16);
v___x_1421_ = lean_nat_dec_le(v___x_1416_, v___x_1416_);
if (v___x_1421_ == 0)
{
if (v___x_1419_ == 0)
{
lean_dec_ref(v_entries_1412_);
v___y_1390_ = v___f_1413_;
v___y_1391_ = v___x_1415_;
v___y_1392_ = v___x_1414_;
v___y_1393_ = v___x_1406_;
v___y_1394_ = v___x_1417_;
goto v___jp_1389_;
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1416_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1418_, v___f_1420_, v_entries_1412_, v___x_1422_, v___x_1423_, v___x_1417_);
v___y_1390_ = v___f_1413_;
v___y_1391_ = v___x_1415_;
v___y_1392_ = v___x_1414_;
v___y_1393_ = v___x_1406_;
v___y_1394_ = v___x_1424_;
goto v___jp_1389_;
}
}
else
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = lean_usize_of_nat(v___x_1416_);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1418_, v___f_1420_, v_entries_1412_, v___x_1425_, v___x_1426_, v___x_1417_);
v___y_1390_ = v___f_1413_;
v___y_1391_ = v___x_1415_;
v___y_1392_ = v___x_1414_;
v___y_1393_ = v___x_1406_;
v___y_1394_ = v___x_1427_;
goto v___jp_1389_;
}
}
}
}
v___jp_1429_:
{
lean_object* v_headerSize_1435_; lean_object* v_machine_1436_; lean_object* v_machine_1437_; lean_object* v_reader_1438_; lean_object* v_state_1439_; 
v_headerSize_1435_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1431_, v_a_1319_, v___y_1430_);
v_machine_1436_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1428_, v___y_1433_, v_headerSize_1435_, v___y_1434_);
v_machine_1437_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1428_, v_machine_1436_, v_a_1319_);
lean_dec(v_a_1319_);
v_reader_1438_ = lean_ctor_get(v_machine_1437_, 0);
lean_inc_ref(v_reader_1438_);
v_state_1439_ = lean_ctor_get(v_reader_1438_, 0);
lean_inc(v_state_1439_);
lean_dec_ref(v_reader_1438_);
if (lean_obj_tag(v_state_1439_) == 7)
{
lean_dec_ref_known(v_state_1439_, 1);
v___y_1304_ = v___y_1432_;
v___y_1305_ = v_machine_1437_;
goto v___jp_1303_;
}
else
{
lean_dec(v_state_1439_);
if (v___y_1430_ == 0)
{
v___y_1269_ = v_machine_1437_;
goto v___jp_1268_;
}
else
{
v___y_1304_ = v___y_1432_;
v___y_1305_ = v_machine_1437_;
goto v___jp_1303_;
}
}
}
v___jp_1440_:
{
uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v_indexes_1446_; lean_object* v___x_1447_; lean_object* v_machine_1448_; lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; uint8_t v___x_1452_; 
v___x_1444_ = 1;
v___x_1445_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1444_, v_a_1319_);
v_indexes_1446_ = lean_ctor_get(v___x_1445_, 1);
lean_inc_ref(v_indexes_1446_);
lean_dec_ref(v___x_1445_);
lean_inc(v_a_1319_);
v___x_1447_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1447_, 0, v_userData_1328_);
lean_ctor_set(v___x_1447_, 1, v_outputData_1329_);
lean_ctor_set(v___x_1447_, 2, v_state_1330_);
lean_ctor_set(v___x_1447_, 3, v_knownSize_1331_);
lean_ctor_set(v___x_1447_, 4, v_a_1319_);
lean_ctor_set(v___x_1447_, 5, v_userDataBytes_1336_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*6, v___y_1442_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*6 + 1, v_userClosedBody_1334_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*6 + 2, v_omitBody_1335_);
v_machine_1448_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1448_, 0, v_reader_1320_);
lean_ctor_set(v_machine_1448_, 1, v___x_1447_);
lean_ctor_set(v_machine_1448_, 2, v_config_1321_);
lean_ctor_set(v_machine_1448_, 3, v_events_1322_);
lean_ctor_set(v_machine_1448_, 4, v_error_1323_);
lean_ctor_set(v_machine_1448_, 5, v_instant_1324_);
lean_ctor_set_uint8(v_machine_1448_, sizeof(void*)*6, v_keepAlive_1325_);
lean_ctor_set_uint8(v_machine_1448_, sizeof(void*)*6 + 1, v_forcedFlush_1326_);
lean_ctor_set_uint8(v_machine_1448_, sizeof(void*)*6 + 2, v_pullBodyStalled_1327_);
v___x_1449_ = l_Std_Http_Header_Name_contentLength;
v___f_1450_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10));
v___f_1451_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11));
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1450_, v___f_1451_, v_indexes_1446_, v___x_1449_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1450_, v___f_1451_, v_indexes_1446_, v___x_1453_);
lean_dec_ref(v_indexes_1446_);
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___x_1444_;
v___y_1432_ = v___y_1443_;
v___y_1433_ = v_machine_1448_;
v___y_1434_ = v___x_1454_;
goto v___jp_1429_;
}
else
{
lean_dec_ref(v_indexes_1446_);
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___x_1444_;
v___y_1432_ = v___y_1443_;
v___y_1433_ = v_machine_1448_;
v___y_1434_ = v___x_1452_;
goto v___jp_1429_;
}
}
v___jp_1455_:
{
if (v___y_1457_ == 0)
{
lean_object* v_state_1458_; 
lean_del_object(v___x_1338_);
lean_dec(v_messageHead_1332_);
v_state_1458_ = lean_ctor_get(v_reader_1320_, 0);
if (lean_obj_tag(v_state_1458_) == 7)
{
v___y_1441_ = v___y_1457_;
v___y_1442_ = v___y_1456_;
v___y_1443_ = v___y_1456_;
goto v___jp_1440_;
}
else
{
v___y_1441_ = v___y_1457_;
v___y_1442_ = v___y_1456_;
v___y_1443_ = v___y_1457_;
goto v___jp_1440_;
}
}
else
{
goto v___jp_1405_;
}
}
v___jp_1459_:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_bool_not(v___y_1460_);
if (v___x_1461_ == 0)
{
lean_object* v_status_1462_; uint8_t v___x_1463_; uint16_t v___x_1464_; uint16_t v___x_1465_; uint8_t v___x_1466_; 
lean_inc(v_instant_1324_);
lean_inc(v_error_1323_);
lean_inc_ref(v_events_1322_);
lean_inc_ref(v_config_1321_);
lean_inc_ref(v_reader_1320_);
lean_dec_ref(v___y_1248_);
v_status_1462_ = lean_ctor_get(v_a_1319_, 0);
v___x_1463_ = 1;
v___x_1464_ = 100;
v___x_1465_ = l_Std_Http_Status_toCode(v_status_1462_);
v___x_1466_ = lean_uint16_dec_le(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
v___y_1456_ = v___x_1463_;
v___y_1457_ = v___x_1461_;
goto v___jp_1455_;
}
else
{
uint16_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = 200;
v___x_1468_ = lean_uint16_dec_lt(v___x_1465_, v___x_1467_);
if (v___x_1468_ == 0)
{
v___y_1456_ = v___x_1463_;
v___y_1457_ = v___x_1461_;
goto v___jp_1455_;
}
else
{
goto v___jp_1405_;
}
}
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
uint8_t v___x_1306_; 
v___x_1306_ = lean_bool_not(v___y_1304_);
if (v___x_1306_ == 0)
{
v___y_1269_ = v___y_1305_;
goto v___jp_1268_;
}
else
{
lean_object* v_writer_1307_; uint8_t v_omitBody_1308_; 
v_writer_1307_ = lean_ctor_get(v___y_1305_, 1);
v_omitBody_1308_ = lean_ctor_get_uint8(v_writer_1307_, sizeof(void*)*6 + 2);
v___y_1255_ = v___y_1305_;
v_omitBody_1256_ = v_omitBody_1308_;
goto v___jp_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1473_, lean_object* v_body_1474_, lean_object* v_isClosed_1475_, lean_object* v_close_1476_, lean_object* v_x_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1473_, v_body_1474_, v_isClosed_1475_, v_close_1476_, v_x_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v_config_1480_, lean_object* v_line_1481_, lean_object* v_body_1482_, lean_object* v_isClosed_1483_, lean_object* v_close_1484_, lean_object* v_machine_1485_, lean_object* v_x_1486_){
_start:
{
lean_object* v___y_1489_; 
if (lean_obj_tag(v_x_1486_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v_machine_1485_);
lean_dec_ref(v_close_1484_);
lean_dec_ref(v_isClosed_1483_);
lean_dec(v_body_1482_);
lean_dec_ref(v_line_1481_);
v_a_1495_ = lean_ctor_get(v_x_1486_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_x_1486_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1497_ = v_x_1486_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v_x_1486_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v_x_1486_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v_x_1486_, 1);
if (lean_obj_tag(v_a_1504_) == 1)
{
lean_object* v_writer_1505_; lean_object* v_reader_1506_; lean_object* v_config_1507_; lean_object* v_events_1508_; lean_object* v_error_1509_; lean_object* v_instant_1510_; uint8_t v_keepAlive_1511_; uint8_t v_forcedFlush_1512_; uint8_t v_pullBodyStalled_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1536_; 
v_writer_1505_ = lean_ctor_get(v_machine_1485_, 1);
v_reader_1506_ = lean_ctor_get(v_machine_1485_, 0);
v_config_1507_ = lean_ctor_get(v_machine_1485_, 2);
v_events_1508_ = lean_ctor_get(v_machine_1485_, 3);
v_error_1509_ = lean_ctor_get(v_machine_1485_, 4);
v_instant_1510_ = lean_ctor_get(v_machine_1485_, 5);
v_keepAlive_1511_ = lean_ctor_get_uint8(v_machine_1485_, sizeof(void*)*6);
v_forcedFlush_1512_ = lean_ctor_get_uint8(v_machine_1485_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1513_ = lean_ctor_get_uint8(v_machine_1485_, sizeof(void*)*6 + 2);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_machine_1485_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1515_ = v_machine_1485_;
v_isShared_1516_ = v_isSharedCheck_1536_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_instant_1510_);
lean_inc(v_error_1509_);
lean_inc(v_events_1508_);
lean_inc(v_config_1507_);
lean_inc(v_writer_1505_);
lean_inc(v_reader_1506_);
lean_dec(v_machine_1485_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1536_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_userData_1517_; lean_object* v_outputData_1518_; lean_object* v_state_1519_; lean_object* v_messageHead_1520_; uint8_t v_sentMessage_1521_; uint8_t v_userClosedBody_1522_; uint8_t v_omitBody_1523_; lean_object* v_userDataBytes_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1534_; 
v_userData_1517_ = lean_ctor_get(v_writer_1505_, 0);
v_outputData_1518_ = lean_ctor_get(v_writer_1505_, 1);
v_state_1519_ = lean_ctor_get(v_writer_1505_, 2);
v_messageHead_1520_ = lean_ctor_get(v_writer_1505_, 4);
v_sentMessage_1521_ = lean_ctor_get_uint8(v_writer_1505_, sizeof(void*)*6);
v_userClosedBody_1522_ = lean_ctor_get_uint8(v_writer_1505_, sizeof(void*)*6 + 1);
v_omitBody_1523_ = lean_ctor_get_uint8(v_writer_1505_, sizeof(void*)*6 + 2);
v_userDataBytes_1524_ = lean_ctor_get(v_writer_1505_, 5);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_writer_1505_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_writer_1505_, 3);
lean_dec(v_unused_1535_);
v___x_1526_ = v_writer_1505_;
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_userDataBytes_1524_);
lean_inc(v_messageHead_1520_);
lean_inc(v_state_1519_);
lean_inc(v_outputData_1518_);
lean_inc(v_userData_1517_);
lean_dec(v_writer_1505_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 3, v_a_1504_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_userData_1517_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_outputData_1518_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_state_1519_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_messageHead_1520_);
lean_ctor_set(v_reuseFailAlloc_1533_, 5, v_userDataBytes_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1533_, sizeof(void*)*6, v_sentMessage_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1533_, sizeof(void*)*6 + 1, v_userClosedBody_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1533_, sizeof(void*)*6 + 2, v_omitBody_1523_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1529_);
v___x_1531_ = v___x_1515_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_reader_1506_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_config_1507_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_events_1508_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_error_1509_);
lean_ctor_set(v_reuseFailAlloc_1532_, 5, v_instant_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1532_, sizeof(void*)*6, v_keepAlive_1511_);
lean_ctor_set_uint8(v_reuseFailAlloc_1532_, sizeof(void*)*6 + 1, v_forcedFlush_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1532_, sizeof(void*)*6 + 2, v_pullBodyStalled_1513_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
v___y_1489_ = v___x_1531_;
goto v___jp_1488_;
}
}
}
}
}
else
{
lean_dec(v_a_1504_);
v___y_1489_ = v_machine_1485_;
goto v___jp_1488_;
}
}
v___jp_1488_:
{
lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1490_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1480_, v_line_1481_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1491_, 0, v___y_1489_);
lean_closure_set(v___f_1491_, 1, v_body_1482_);
lean_closure_set(v___f_1491_, 2, v_isClosed_1483_);
lean_closure_set(v___f_1491_, 3, v_close_1484_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = 0;
v___x_1494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1492_, v___x_1493_, v___x_1490_, v___f_1491_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object* v_config_1537_, lean_object* v_line_1538_, lean_object* v_body_1539_, lean_object* v_isClosed_1540_, lean_object* v_close_1541_, lean_object* v_machine_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(v_config_1537_, v_line_1538_, v_body_1539_, v_isClosed_1540_, v_close_1541_, v_machine_1542_, v_x_1543_);
lean_dec_ref(v_config_1537_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1546_, lean_object* v_config_1547_, lean_object* v_machine_1548_, lean_object* v_res_1549_){
_start:
{
lean_object* v_close_1551_; lean_object* v_isClosed_1552_; lean_object* v_getKnownSize_1553_; lean_object* v_line_1554_; lean_object* v_body_1555_; lean_object* v___x_1556_; lean_object* v___f_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v_close_1551_ = lean_ctor_get(v_inst_1546_, 1);
lean_inc_ref(v_close_1551_);
v_isClosed_1552_ = lean_ctor_get(v_inst_1546_, 2);
lean_inc_ref(v_isClosed_1552_);
v_getKnownSize_1553_ = lean_ctor_get(v_inst_1546_, 5);
lean_inc_ref(v_getKnownSize_1553_);
lean_dec_ref(v_inst_1546_);
v_line_1554_ = lean_ctor_get(v_res_1549_, 0);
lean_inc_ref(v_line_1554_);
v_body_1555_ = lean_ctor_get(v_res_1549_, 1);
lean_inc_n(v_body_1555_, 2);
lean_dec_ref(v_res_1549_);
v___x_1556_ = lean_apply_2(v_getKnownSize_1553_, v_body_1555_, lean_box(0));
v___f_1557_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_1557_, 0, v_config_1547_);
lean_closure_set(v___f_1557_, 1, v_line_1554_);
lean_closure_set(v___f_1557_, 2, v_body_1555_);
lean_closure_set(v___f_1557_, 3, v_isClosed_1552_);
lean_closure_set(v___f_1557_, 4, v_close_1551_);
lean_closure_set(v___f_1557_, 5, v_machine_1548_);
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = 0;
v___x_1560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1558_, v___x_1559_, v___x_1556_, v___f_1557_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1561_, lean_object* v_config_1562_, lean_object* v_machine_1563_, lean_object* v_res_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1561_, v_config_1562_, v_machine_1563_, v_res_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1567_, lean_object* v_inst_1568_, lean_object* v_config_1569_, lean_object* v_machine_1570_, lean_object* v_res_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1568_, v_config_1569_, v_machine_1570_, v_res_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1574_, lean_object* v_inst_1575_, lean_object* v_config_1576_, lean_object* v_machine_1577_, lean_object* v_res_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1574_, v_inst_1575_, v_config_1576_, v_machine_1577_, v_res_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v_closed_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_closed_1584_ = lean_ctor_get_uint8(v_____do__lift_1581_, sizeof(void*)*5);
v___x_1585_ = lean_box(v_closed_1584_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v_____do__lift_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v_pendingProducer_1600_; lean_object* v_pendingConsumer_1601_; lean_object* v_interestWaiter_1602_; uint8_t v_closed_1603_; lean_object* v_pendingIncompleteChunk_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1613_; 
v___x_1599_ = lean_st_ref_take(v___y_1597_);
v_pendingProducer_1600_ = lean_ctor_get(v___x_1599_, 0);
v_pendingConsumer_1601_ = lean_ctor_get(v___x_1599_, 1);
v_interestWaiter_1602_ = lean_ctor_get(v___x_1599_, 2);
v_closed_1603_ = lean_ctor_get_uint8(v___x_1599_, sizeof(void*)*5);
v_pendingIncompleteChunk_1604_ = lean_ctor_get(v___x_1599_, 4);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1599_, 3);
lean_dec(v_unused_1614_);
v___x_1606_ = v___x_1599_;
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1604_);
lean_inc(v_interestWaiter_1602_);
lean_inc(v_pendingConsumer_1601_);
lean_inc(v_pendingProducer_1600_);
lean_dec(v___x_1599_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 3, v___x_1596_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_pendingProducer_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_pendingConsumer_1601_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_interestWaiter_1602_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_pendingIncompleteChunk_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1612_, sizeof(void*)*5, v_closed_1603_);
v___x_1609_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_st_ref_set(v___y_1597_, v___x_1609_);
v___x_1611_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1615_, v___y_1616_);
lean_dec(v___y_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1619_, lean_object* v_x_1620_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v___x_1619_);
v_a_1622_ = lean_ctor_get(v_x_1620_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_x_1620_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1624_ = v_x_1620_;
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v_x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
}
else
{
lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1639_; 
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1620_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v_x_1620_, 0);
lean_dec(v_unused_1640_);
v___x_1632_ = v_x_1620_;
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v_x_1620_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1619_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1634_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1641_, lean_object* v_x_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1641_, v_x_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1645_, lean_object* v_requestStream_1646_, lean_object* v_keepAliveTimeout_1647_, lean_object* v_currentTimeout_1648_, lean_object* v_headerTimeout_1649_, lean_object* v_response_1650_, lean_object* v_respStream_1651_, lean_object* v_expectData_1652_, uint8_t v_handlerDispatched_1653_, lean_object* v_____r_1654_){
_start:
{
uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1656_ = 0;
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1658_, 0, v_machine_1645_);
lean_ctor_set(v___x_1658_, 1, v_requestStream_1646_);
lean_ctor_set(v___x_1658_, 2, v_keepAliveTimeout_1647_);
lean_ctor_set(v___x_1658_, 3, v_currentTimeout_1648_);
lean_ctor_set(v___x_1658_, 4, v_headerTimeout_1649_);
lean_ctor_set(v___x_1658_, 5, v_response_1650_);
lean_ctor_set(v___x_1658_, 6, v_respStream_1651_);
lean_ctor_set(v___x_1658_, 7, v_expectData_1652_);
lean_ctor_set(v___x_1658_, 8, v___x_1657_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*9, v___x_1656_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*9 + 1, v_handlerDispatched_1653_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1662_, lean_object* v_requestStream_1663_, lean_object* v_keepAliveTimeout_1664_, lean_object* v_currentTimeout_1665_, lean_object* v_headerTimeout_1666_, lean_object* v_response_1667_, lean_object* v_respStream_1668_, lean_object* v_expectData_1669_, lean_object* v_handlerDispatched_1670_, lean_object* v_____r_1671_, lean_object* v___y_1672_){
_start:
{
uint8_t v_handlerDispatched_boxed_1673_; lean_object* v_res_1674_; 
v_handlerDispatched_boxed_1673_ = lean_unbox(v_handlerDispatched_1670_);
v_res_1674_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1662_, v_requestStream_1663_, v_keepAliveTimeout_1664_, v_currentTimeout_1665_, v_headerTimeout_1666_, v_response_1667_, v_respStream_1668_, v_expectData_1669_, v_handlerDispatched_boxed_1673_, v_____r_1671_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1675_, lean_object* v_x_1676_){
_start:
{
if (lean_obj_tag(v_x_1676_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v___f_1675_);
v_a_1678_ = lean_ctor_get(v_x_1676_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_x_1676_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v_x_1676_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v_x_1676_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1688_; 
v_a_1687_ = lean_ctor_get(v_x_1676_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v_x_1676_, 1);
v___x_1688_ = lean_apply_2(v___f_1675_, v_a_1687_, lean_box(0));
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1689_, lean_object* v_x_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1689_, v_x_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1693_, lean_object* v___f_1694_, lean_object* v___f_1695_, lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v___f_1695_);
lean_dec_ref(v___f_1694_);
lean_dec_ref(v_requestStream_1693_);
v_a_1698_ = lean_ctor_get(v_x_1696_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v_x_1696_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v_x_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; uint8_t v___x_1708_; 
v_a_1707_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v_x_1696_, 1);
v___x_1708_ = lean_unbox(v_a_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; 
lean_dec_ref(v___f_1695_);
v___x_1709_ = l_Std_Http_Body_Stream_close(v_requestStream_1693_);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1712_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1710_, v___x_1711_, v___x_1709_, v___f_1694_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_a_1707_);
lean_dec_ref(v___f_1694_);
lean_dec_ref(v_requestStream_1693_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_apply_2(v___f_1695_, v___x_1713_, lean_box(0));
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1715_, lean_object* v___f_1716_, lean_object* v___f_1717_, lean_object* v_x_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1715_, v___f_1716_, v___f_1717_, v_x_1718_);
return v_res_1720_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1721_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1722_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___f_1729_; lean_object* v___f_1730_; 
v___x_1728_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1729_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1730_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1730_, 0, v___f_1729_);
lean_closure_set(v___f_1730_, 1, v___x_1728_);
return v___f_1730_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; 
v___x_1739_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1740_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1741_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1741_, 0, v___f_1740_);
lean_closure_set(v___f_1741_, 1, v___x_1739_);
return v___f_1741_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1742_; lean_object* v___x_1743_; 
v___f_1742_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1743_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1743_, 0, lean_box(0));
lean_closure_set(v___x_1743_, 1, lean_box(0));
lean_closure_set(v___x_1743_, 2, lean_box(0));
lean_closure_set(v___x_1743_, 3, v___f_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1744_, lean_object* v___f_1745_, lean_object* v_x_1746_){
_start:
{
if (lean_obj_tag(v_x_1746_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1756_; 
lean_dec_ref(v___f_1745_);
lean_dec_ref(v___y_1744_);
v_a_1748_ = lean_ctor_get(v_x_1746_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_x_1746_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1750_ = v_x_1746_;
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v_x_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
else
{
lean_object* v_machine_1757_; lean_object* v_requestStream_1758_; lean_object* v_keepAliveTimeout_1759_; lean_object* v_currentTimeout_1760_; lean_object* v_headerTimeout_1761_; lean_object* v_response_1762_; lean_object* v_respStream_1763_; lean_object* v_expectData_1764_; uint8_t v_handlerDispatched_1765_; lean_object* v___x_1766_; lean_object* v___f_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_4928__overap_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___f_1774_; lean_object* v___f_1775_; lean_object* v___f_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; 
lean_dec_ref_known(v_x_1746_, 1);
v_machine_1757_ = lean_ctor_get(v___y_1744_, 0);
lean_inc_ref(v_machine_1757_);
v_requestStream_1758_ = lean_ctor_get(v___y_1744_, 1);
lean_inc_ref_n(v_requestStream_1758_, 3);
v_keepAliveTimeout_1759_ = lean_ctor_get(v___y_1744_, 2);
lean_inc(v_keepAliveTimeout_1759_);
v_currentTimeout_1760_ = lean_ctor_get(v___y_1744_, 3);
lean_inc(v_currentTimeout_1760_);
v_headerTimeout_1761_ = lean_ctor_get(v___y_1744_, 4);
lean_inc(v_headerTimeout_1761_);
v_response_1762_ = lean_ctor_get(v___y_1744_, 5);
lean_inc_ref(v_response_1762_);
v_respStream_1763_ = lean_ctor_get(v___y_1744_, 6);
lean_inc(v_respStream_1763_);
v_expectData_1764_ = lean_ctor_get(v___y_1744_, 7);
lean_inc(v_expectData_1764_);
v_handlerDispatched_1765_ = lean_ctor_get_uint8(v___y_1744_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1744_);
v___x_1766_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1767_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1768_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1769_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1770_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1770_, 0, lean_box(0));
lean_closure_set(v___x_1770_, 1, lean_box(0));
lean_closure_set(v___x_1770_, 2, v___x_1766_);
lean_closure_set(v___x_1770_, 3, lean_box(0));
lean_closure_set(v___x_1770_, 4, lean_box(0));
lean_closure_set(v___x_1770_, 5, v___x_1769_);
lean_closure_set(v___x_1770_, 6, v___f_1745_);
v___x_4928__overap_1771_ = l_Std_Mutex_atomically___redArg(v___x_1766_, v___f_1767_, v___f_1768_, v_requestStream_1758_, v___x_1770_);
v___x_1772_ = lean_apply_1(v___x_4928__overap_1771_, lean_box(0));
v___x_1773_ = lean_box(v_handlerDispatched_1765_);
v___f_1774_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1774_, 0, v_machine_1757_);
lean_closure_set(v___f_1774_, 1, v_requestStream_1758_);
lean_closure_set(v___f_1774_, 2, v_keepAliveTimeout_1759_);
lean_closure_set(v___f_1774_, 3, v_currentTimeout_1760_);
lean_closure_set(v___f_1774_, 4, v_headerTimeout_1761_);
lean_closure_set(v___f_1774_, 5, v_response_1762_);
lean_closure_set(v___f_1774_, 6, v_respStream_1763_);
lean_closure_set(v___f_1774_, 7, v_expectData_1764_);
lean_closure_set(v___f_1774_, 8, v___x_1773_);
lean_inc_ref(v___f_1774_);
v___f_1775_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1775_, 0, v___f_1774_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1776_, 0, v_requestStream_1758_);
lean_closure_set(v___f_1776_, 1, v___f_1775_);
lean_closure_set(v___f_1776_, 2, v___f_1774_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = 0;
v___x_1779_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1777_, v___x_1778_, v___x_1772_, v___f_1776_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1780_, lean_object* v___f_1781_, lean_object* v_x_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1780_, v___f_1781_, v_x_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1785_, lean_object* v_x_1786_){
_start:
{
if (lean_obj_tag(v_x_1786_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v___y_1785_);
v_a_1788_ = lean_ctor_get(v_x_1786_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1786_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1790_ = v_x_1786_;
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v_x_1786_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
}
else
{
lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1805_; 
v_isSharedCheck_1805_ = !lean_is_exclusive(v_x_1786_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v_x_1786_, 0);
lean_dec(v_unused_1806_);
v___x_1798_ = v_x_1786_;
v_isShared_1799_ = v_isSharedCheck_1805_;
goto v_resetjp_1797_;
}
else
{
lean_dec(v_x_1786_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1805_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___y_1785_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1802_ = v___x_1798_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1800_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1807_, lean_object* v_x_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1807_, v_x_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1811_, lean_object* v___f_1812_, lean_object* v___y_1813_, lean_object* v_x_1814_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v___y_1813_);
lean_dec_ref(v___f_1812_);
lean_dec_ref(v_requestStream_1811_);
v_a_1816_ = lean_ctor_get(v_x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1818_ = v_x_1814_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v_x_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1839_; 
v_a_1825_ = lean_ctor_get(v_x_1814_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_x_1814_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1827_ = v_x_1814_;
v_isShared_1828_ = v_isSharedCheck_1839_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v_x_1814_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1839_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_unbox(v_a_1825_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; 
lean_del_object(v___x_1827_);
lean_dec_ref(v___y_1813_);
v___x_1830_ = l_Std_Http_Body_Stream_close(v_requestStream_1811_);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_unbox(v_a_1825_);
lean_dec(v_a_1825_);
v___x_1833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1831_, v___x_1832_, v___x_1830_, v___f_1812_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec(v_a_1825_);
lean_dec_ref(v___f_1812_);
lean_dec_ref(v_requestStream_1811_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___y_1813_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1834_);
v___x_1836_ = v___x_1827_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1834_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1840_, lean_object* v___f_1841_, lean_object* v___y_1842_, lean_object* v_x_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1840_, v___f_1841_, v___y_1842_, v_x_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1846_, lean_object* v_machine_1847_, lean_object* v_a_1848_, uint8_t v_requiresData_1849_, lean_object* v_expectData_1850_, lean_object* v_pendingHead_1851_, lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1852_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_pendingHead_1851_);
lean_dec(v_expectData_1850_);
lean_dec_ref(v_a_1848_);
lean_dec_ref(v_machine_1847_);
v_a_1854_ = lean_ctor_get(v_x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1856_ = v_x_1852_;
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v_x_1852_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1877_; 
v_a_1863_ = lean_ctor_get(v_x_1852_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1852_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1865_ = v_x_1852_;
v_isShared_1866_ = v_isSharedCheck_1877_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v_x_1852_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1877_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_keepAliveTimeout_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v_keepAliveTimeout_1867_ = lean_ctor_get(v_config_1846_, 5);
lean_inc_n(v_keepAliveTimeout_1867_, 2);
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_keepAliveTimeout_1867_);
v___x_1869_ = lean_box(0);
v___x_1870_ = 0;
v___x_1871_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1871_, 0, v_machine_1847_);
lean_ctor_set(v___x_1871_, 1, v_a_1848_);
lean_ctor_set(v___x_1871_, 2, v___x_1868_);
lean_ctor_set(v___x_1871_, 3, v_keepAliveTimeout_1867_);
lean_ctor_set(v___x_1871_, 4, v___x_1869_);
lean_ctor_set(v___x_1871_, 5, v_a_1863_);
lean_ctor_set(v___x_1871_, 6, v___x_1869_);
lean_ctor_set(v___x_1871_, 7, v_expectData_1850_);
lean_ctor_set(v___x_1871_, 8, v_pendingHead_1851_);
lean_ctor_set_uint8(v___x_1871_, sizeof(void*)*9, v_requiresData_1849_);
lean_ctor_set_uint8(v___x_1871_, sizeof(void*)*9 + 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1872_);
v___x_1874_ = v___x_1865_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1872_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1878_, lean_object* v_machine_1879_, lean_object* v_a_1880_, lean_object* v_requiresData_1881_, lean_object* v_expectData_1882_, lean_object* v_pendingHead_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_){
_start:
{
uint8_t v_requiresData_boxed_1886_; lean_object* v_res_1887_; 
v_requiresData_boxed_1886_ = lean_unbox(v_requiresData_1881_);
v_res_1887_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1878_, v_machine_1879_, v_a_1880_, v_requiresData_boxed_1886_, v_expectData_1882_, v_pendingHead_1883_, v_x_1884_);
lean_dec_ref(v_config_1878_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1888_, lean_object* v_machine_1889_, uint8_t v_requiresData_1890_, lean_object* v_expectData_1891_, lean_object* v_pendingHead_1892_, lean_object* v_x_1893_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_pendingHead_1892_);
lean_dec(v_expectData_1891_);
lean_dec_ref(v_machine_1889_);
lean_dec_ref(v_config_1888_);
v_a_1895_ = lean_ctor_get(v_x_1893_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_x_1893_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v_x_1893_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v_x_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1919_; 
v_a_1904_ = lean_ctor_get(v_x_1893_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_x_1893_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1906_ = v_x_1893_;
v_isShared_1907_ = v_isSharedCheck_1919_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v_x_1893_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1919_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_1913_; 
v___x_1908_ = lean_box(0);
v___x_1909_ = l_Std_CloseableChannel_new___redArg(v___x_1908_);
v___x_1910_ = lean_box(v_requiresData_1890_);
v___f_1911_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1911_, 0, v_config_1888_);
lean_closure_set(v___f_1911_, 1, v_machine_1889_);
lean_closure_set(v___f_1911_, 2, v_a_1904_);
lean_closure_set(v___f_1911_, 3, v___x_1910_);
lean_closure_set(v___f_1911_, 4, v_expectData_1891_);
lean_closure_set(v___f_1911_, 5, v_pendingHead_1892_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1909_);
v___x_1913_ = v___x_1906_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1909_);
v___x_1913_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = 0;
v___x_1917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1915_, v___x_1916_, v___x_1914_, v___f_1911_);
return v___x_1917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1920_, lean_object* v_machine_1921_, lean_object* v_requiresData_1922_, lean_object* v_expectData_1923_, lean_object* v_pendingHead_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_requiresData_boxed_1927_; lean_object* v_res_1928_; 
v_requiresData_boxed_1927_ = lean_unbox(v_requiresData_1922_);
v_res_1928_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1920_, v_machine_1921_, v_requiresData_boxed_1927_, v_expectData_1923_, v_pendingHead_1924_, v_x_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1929_, lean_object* v_____r_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1932_ = l_Std_Http_Body_mkStream();
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = 0;
v___x_1935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1933_, v___x_1934_, v___x_1932_, v___f_1929_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1936_, lean_object* v_____r_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1936_, v_____r_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1940_, lean_object* v_val_1941_, lean_object* v___f_1942_, lean_object* v___f_1943_, lean_object* v_x_1944_){
_start:
{
if (lean_obj_tag(v_x_1944_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v___f_1943_);
lean_dec_ref(v___f_1942_);
lean_dec(v_val_1941_);
lean_dec_ref(v_close_1940_);
v_a_1946_ = lean_ctor_get(v_x_1944_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_x_1944_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1948_ = v_x_1944_;
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v_x_1944_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1955_; uint8_t v___x_1956_; 
v_a_1955_ = lean_ctor_get(v_x_1944_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v_x_1944_, 1);
v___x_1956_ = lean_unbox(v_a_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v___f_1943_);
v___x_1957_ = lean_apply_2(v_close_1940_, v_val_1941_, lean_box(0));
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
v___x_1960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1958_, v___x_1959_, v___x_1957_, v___f_1942_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_a_1955_);
lean_dec_ref(v___f_1942_);
lean_dec(v_val_1941_);
lean_dec_ref(v_close_1940_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_apply_2(v___f_1943_, v___x_1961_, lean_box(0));
return v___x_1962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1963_, lean_object* v_val_1964_, lean_object* v___f_1965_, lean_object* v___f_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1963_, v_val_1964_, v___f_1965_, v___f_1966_, v_x_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1970_, lean_object* v_inst_1971_, lean_object* v___f_1972_, lean_object* v___f_1973_, lean_object* v_____r_1974_){
_start:
{
if (lean_obj_tag(v_respStream_1970_) == 1)
{
lean_object* v_val_1976_; lean_object* v_close_1977_; lean_object* v_isClosed_1978_; lean_object* v___x_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
v_val_1976_ = lean_ctor_get(v_respStream_1970_, 0);
lean_inc_n(v_val_1976_, 2);
lean_dec_ref_known(v_respStream_1970_, 1);
v_close_1977_ = lean_ctor_get(v_inst_1971_, 1);
lean_inc_ref(v_close_1977_);
v_isClosed_1978_ = lean_ctor_get(v_inst_1971_, 2);
lean_inc_ref(v_isClosed_1978_);
lean_dec_ref(v_inst_1971_);
v___x_1979_ = lean_apply_2(v_isClosed_1978_, v_val_1976_, lean_box(0));
v___f_1980_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1980_, 0, v_close_1977_);
lean_closure_set(v___f_1980_, 1, v_val_1976_);
lean_closure_set(v___f_1980_, 2, v___f_1972_);
lean_closure_set(v___f_1980_, 3, v___f_1973_);
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = 0;
v___x_1983_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1981_, v___x_1982_, v___x_1979_, v___f_1980_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v___f_1972_);
lean_dec_ref(v_inst_1971_);
lean_dec(v_respStream_1970_);
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_apply_2(v___f_1973_, v___x_1984_, lean_box(0));
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1986_, lean_object* v_inst_1987_, lean_object* v___f_1988_, lean_object* v___f_1989_, lean_object* v_____r_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1986_, v_inst_1987_, v___f_1988_, v___f_1989_, v_____r_1990_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1993_, lean_object* v_keepAliveTimeout_1994_, lean_object* v_currentTimeout_1995_, lean_object* v_headerTimeout_1996_, lean_object* v_response_1997_, lean_object* v_respStream_1998_, uint8_t v_requiresData_1999_, lean_object* v_expectData_2000_, uint8_t v_handlerDispatched_2001_, lean_object* v_pendingHead_2002_, lean_object* v_x_2003_){
_start:
{
if (lean_obj_tag(v_x_2003_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_pendingHead_2002_);
lean_dec(v_expectData_2000_);
lean_dec(v_respStream_1998_);
lean_dec_ref(v_response_1997_);
lean_dec(v_headerTimeout_1996_);
lean_dec(v_currentTimeout_1995_);
lean_dec(v_keepAliveTimeout_1994_);
lean_dec_ref(v_requestStream_1993_);
v_a_2005_ = lean_ctor_get(v_x_2003_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_x_2003_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2007_ = v_x_2003_;
v_isShared_2008_ = v_isSharedCheck_2013_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v_x_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2013_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2035_; 
v_a_2014_ = lean_ctor_get(v_x_2003_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_x_2003_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2016_ = v_x_2003_;
v_isShared_2017_ = v_isSharedCheck_2035_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v_x_2003_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2035_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v_snd_2018_; uint8_t v___x_2019_; 
v_snd_2018_ = lean_ctor_get(v_a_2014_, 1);
v___x_2019_ = lean_unbox(v_snd_2018_);
if (v___x_2019_ == 0)
{
lean_object* v_fst_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v_fst_2020_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_fst_2020_);
lean_dec(v_a_2014_);
v___x_2021_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2021_, 0, v_fst_2020_);
lean_ctor_set(v___x_2021_, 1, v_requestStream_1993_);
lean_ctor_set(v___x_2021_, 2, v_keepAliveTimeout_1994_);
lean_ctor_set(v___x_2021_, 3, v_currentTimeout_1995_);
lean_ctor_set(v___x_2021_, 4, v_headerTimeout_1996_);
lean_ctor_set(v___x_2021_, 5, v_response_1997_);
lean_ctor_set(v___x_2021_, 6, v_respStream_1998_);
lean_ctor_set(v___x_2021_, 7, v_expectData_2000_);
lean_ctor_set(v___x_2021_, 8, v_pendingHead_2002_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*9, v_requiresData_1999_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*9 + 1, v_handlerDispatched_2001_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2022_);
v___x_2024_ = v___x_2016_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2022_);
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
else
{
lean_object* v_fst_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec(v_pendingHead_2002_);
v_fst_2027_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_fst_2027_);
lean_dec(v_a_2014_);
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2029_, 0, v_fst_2027_);
lean_ctor_set(v___x_2029_, 1, v_requestStream_1993_);
lean_ctor_set(v___x_2029_, 2, v_keepAliveTimeout_1994_);
lean_ctor_set(v___x_2029_, 3, v_currentTimeout_1995_);
lean_ctor_set(v___x_2029_, 4, v_headerTimeout_1996_);
lean_ctor_set(v___x_2029_, 5, v_response_1997_);
lean_ctor_set(v___x_2029_, 6, v_respStream_1998_);
lean_ctor_set(v___x_2029_, 7, v_expectData_2000_);
lean_ctor_set(v___x_2029_, 8, v___x_2028_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*9, v_requiresData_1999_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*9 + 1, v_handlerDispatched_2001_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2030_);
v___x_2032_ = v___x_2016_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2036_, lean_object* v_keepAliveTimeout_2037_, lean_object* v_currentTimeout_2038_, lean_object* v_headerTimeout_2039_, lean_object* v_response_2040_, lean_object* v_respStream_2041_, lean_object* v_requiresData_2042_, lean_object* v_expectData_2043_, lean_object* v_handlerDispatched_2044_, lean_object* v_pendingHead_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_requiresData_boxed_2048_; uint8_t v_handlerDispatched_boxed_2049_; lean_object* v_res_2050_; 
v_requiresData_boxed_2048_ = lean_unbox(v_requiresData_2042_);
v_handlerDispatched_boxed_2049_ = lean_unbox(v_handlerDispatched_2044_);
v_res_2050_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2036_, v_keepAliveTimeout_2037_, v_currentTimeout_2038_, v_headerTimeout_2039_, v_response_2040_, v_respStream_2041_, v_requiresData_boxed_2048_, v_expectData_2043_, v_handlerDispatched_boxed_2049_, v_pendingHead_2045_, v_x_2046_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2063_, lean_object* v_inst_2064_, lean_object* v___f_2065_, lean_object* v_handler_2066_, lean_object* v___f_2067_, lean_object* v___f_2068_, lean_object* v_inst_2069_, lean_object* v_connectionContext_2070_, lean_object* v_a_2071_, lean_object* v_x_2072_, lean_object* v___y_2073_){
_start:
{
switch(lean_obj_tag(v_a_2071_))
{
case 0:
{
lean_object* v_head_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_connectionContext_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v___f_2068_);
lean_dec_ref(v___f_2067_);
lean_dec(v_handler_2066_);
lean_dec_ref(v___f_2065_);
lean_dec_ref(v_inst_2064_);
v_head_2075_ = lean_ctor_get(v_a_2071_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_a_2071_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2077_ = v_a_2071_;
v_isShared_2078_ = v_isSharedCheck_2118_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_head_2075_);
lean_dec(v_a_2071_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2118_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_machine_2079_; lean_object* v_requestStream_2080_; lean_object* v_response_2081_; lean_object* v_respStream_2082_; uint8_t v_requiresData_2083_; lean_object* v_expectData_2084_; uint8_t v_handlerDispatched_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2113_; 
v_machine_2079_ = lean_ctor_get(v___y_2073_, 0);
v_requestStream_2080_ = lean_ctor_get(v___y_2073_, 1);
v_response_2081_ = lean_ctor_get(v___y_2073_, 5);
v_respStream_2082_ = lean_ctor_get(v___y_2073_, 6);
v_requiresData_2083_ = lean_ctor_get_uint8(v___y_2073_, sizeof(void*)*9);
v_expectData_2084_ = lean_ctor_get(v___y_2073_, 7);
v_handlerDispatched_2085_ = lean_ctor_get_uint8(v___y_2073_, sizeof(void*)*9 + 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___y_2073_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; 
v_unused_2114_ = lean_ctor_get(v___y_2073_, 8);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v___y_2073_, 4);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v___y_2073_, 3);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v___y_2073_, 2);
lean_dec(v_unused_2117_);
v___x_2087_ = v___y_2073_;
v_isShared_2088_ = v_isSharedCheck_2113_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_expectData_2084_);
lean_inc(v_respStream_2082_);
lean_inc(v_response_2081_);
lean_inc(v_requestStream_2080_);
lean_inc(v_machine_2079_);
lean_dec(v___y_2073_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2113_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_lingeringTimeout_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v_lingeringTimeout_2089_ = lean_ctor_get(v_config_2063_, 4);
lean_inc(v_lingeringTimeout_2089_);
lean_dec_ref(v_config_2063_);
v___x_2090_ = lean_box(0);
lean_inc(v_head_2075_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 1);
v___x_2092_ = v___x_2077_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_head_2075_);
v___x_2092_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
lean_inc_ref(v_requestStream_2080_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 8, v___x_2092_);
lean_ctor_set(v___x_2087_, 4, v___x_2090_);
lean_ctor_set(v___x_2087_, 3, v_lingeringTimeout_2089_);
lean_ctor_set(v___x_2087_, 2, v___x_2090_);
v___x_2094_ = v___x_2087_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_machine_2079_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_requestStream_2080_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_lingeringTimeout_2089_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2111_, 5, v_response_2081_);
lean_ctor_set(v_reuseFailAlloc_2111_, 6, v_respStream_2082_);
lean_ctor_set(v_reuseFailAlloc_2111_, 7, v_expectData_2084_);
lean_ctor_set(v_reuseFailAlloc_2111_, 8, v___x_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*9, v_requiresData_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*9 + 1, v_handlerDispatched_2085_);
v___x_2094_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
uint8_t v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = 0;
v___x_2096_ = 1;
v___x_2097_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2095_, v_head_2075_, v___x_2096_);
lean_dec(v_head_2075_);
if (lean_obj_tag(v___x_2097_) == 1)
{
lean_object* v___f_2098_; lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___f_2101_; lean_object* v___x_5121__overap_2102_; lean_object* v___x_2103_; lean_object* v___f_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; 
v___f_2098_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2098_, 0, v___x_2097_);
v___x_2099_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2100_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2101_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5121__overap_2102_ = l_Std_Mutex_atomically___redArg(v___x_2099_, v___f_2100_, v___f_2101_, v_requestStream_2080_, v___f_2098_);
v___x_2103_ = lean_apply_1(v___x_5121__overap_2102_, lean_box(0));
v___f_2104_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2104_, 0, v___x_2094_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = 0;
v___x_2107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2105_, v___x_2106_, v___x_2103_, v___f_2104_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v___x_2097_);
lean_dec_ref(v_requestStream_2080_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2094_);
v___x_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
return v___x_2110_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_connectionContext_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v___f_2068_);
lean_dec_ref(v___f_2067_);
lean_dec(v_handler_2066_);
lean_dec_ref(v___f_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec_ref(v_config_2063_);
v_size_2119_ = lean_ctor_get(v_a_2071_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2071_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2121_ = v_a_2071_;
v_isShared_2122_ = v_isSharedCheck_2146_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_size_2119_);
lean_dec(v_a_2071_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2146_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_machine_2123_; lean_object* v_requestStream_2124_; lean_object* v_keepAliveTimeout_2125_; lean_object* v_currentTimeout_2126_; lean_object* v_headerTimeout_2127_; lean_object* v_response_2128_; lean_object* v_respStream_2129_; uint8_t v_handlerDispatched_2130_; lean_object* v_pendingHead_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2144_; 
v_machine_2123_ = lean_ctor_get(v___y_2073_, 0);
v_requestStream_2124_ = lean_ctor_get(v___y_2073_, 1);
v_keepAliveTimeout_2125_ = lean_ctor_get(v___y_2073_, 2);
v_currentTimeout_2126_ = lean_ctor_get(v___y_2073_, 3);
v_headerTimeout_2127_ = lean_ctor_get(v___y_2073_, 4);
v_response_2128_ = lean_ctor_get(v___y_2073_, 5);
v_respStream_2129_ = lean_ctor_get(v___y_2073_, 6);
v_handlerDispatched_2130_ = lean_ctor_get_uint8(v___y_2073_, sizeof(void*)*9 + 1);
v_pendingHead_2131_ = lean_ctor_get(v___y_2073_, 8);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___y_2073_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___y_2073_, 7);
lean_dec(v_unused_2145_);
v___x_2133_ = v___y_2073_;
v_isShared_2134_ = v_isSharedCheck_2144_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_pendingHead_2131_);
lean_inc(v_respStream_2129_);
lean_inc(v_response_2128_);
lean_inc(v_headerTimeout_2127_);
lean_inc(v_currentTimeout_2126_);
lean_inc(v_keepAliveTimeout_2125_);
lean_inc(v_requestStream_2124_);
lean_inc(v_machine_2123_);
lean_dec(v___y_2073_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2144_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
uint8_t v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = 1;
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 7, v_size_2119_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_machine_2123_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_requestStream_2124_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_keepAliveTimeout_2125_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_currentTimeout_2126_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_headerTimeout_2127_);
lean_ctor_set(v_reuseFailAlloc_2143_, 5, v_response_2128_);
lean_ctor_set(v_reuseFailAlloc_2143_, 6, v_respStream_2129_);
lean_ctor_set(v_reuseFailAlloc_2143_, 7, v_size_2119_);
lean_ctor_set(v_reuseFailAlloc_2143_, 8, v_pendingHead_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*9 + 1, v_handlerDispatched_2130_);
v___x_2137_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*9, v___x_2135_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2137_);
v___x_2139_ = v___x_2121_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
return v___x_2141_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2147_; lean_object* v_onFailure_2148_; lean_object* v___f_2149_; lean_object* v___y_2151_; 
lean_dec_ref(v_connectionContext_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v___f_2068_);
lean_dec_ref(v___f_2067_);
lean_dec_ref(v_config_2063_);
v_err_2147_ = lean_ctor_get(v_a_2071_, 0);
lean_inc(v_err_2147_);
lean_dec_ref_known(v_a_2071_, 1);
v_onFailure_2148_ = lean_ctor_get(v_inst_2064_, 2);
lean_inc_ref(v_onFailure_2148_);
lean_dec_ref(v_inst_2064_);
v___f_2149_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2149_, 0, v___y_2073_);
lean_closure_set(v___f_2149_, 1, v___f_2065_);
switch(lean_obj_tag(v_err_2147_))
{
case 0:
{
lean_object* v___x_2157_; 
v___x_2157_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2151_ = v___x_2157_;
goto v___jp_2150_;
}
case 1:
{
lean_object* v___x_2158_; 
v___x_2158_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2151_ = v___x_2158_;
goto v___jp_2150_;
}
case 2:
{
lean_object* v___x_2159_; 
v___x_2159_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2151_ = v___x_2159_;
goto v___jp_2150_;
}
case 3:
{
lean_object* v___x_2160_; 
v___x_2160_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2151_ = v___x_2160_;
goto v___jp_2150_;
}
case 4:
{
lean_object* v___x_2161_; 
v___x_2161_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2151_ = v___x_2161_;
goto v___jp_2150_;
}
case 5:
{
lean_object* v___x_2162_; 
v___x_2162_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2151_ = v___x_2162_;
goto v___jp_2150_;
}
case 6:
{
lean_object* v___x_2163_; 
v___x_2163_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2151_ = v___x_2163_;
goto v___jp_2150_;
}
case 7:
{
lean_object* v___x_2164_; 
v___x_2164_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2151_ = v___x_2164_;
goto v___jp_2150_;
}
case 8:
{
lean_object* v___x_2165_; 
v___x_2165_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2151_ = v___x_2165_;
goto v___jp_2150_;
}
case 9:
{
lean_object* v___x_2166_; 
v___x_2166_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2151_ = v___x_2166_;
goto v___jp_2150_;
}
case 10:
{
lean_object* v___x_2167_; 
v___x_2167_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2151_ = v___x_2167_;
goto v___jp_2150_;
}
default: 
{
lean_object* v_message_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_message_2168_ = lean_ctor_get(v_err_2147_, 0);
lean_inc_ref(v_message_2168_);
lean_dec_ref_known(v_err_2147_, 1);
v___x_2169_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2170_ = lean_string_append(v___x_2169_, v_message_2168_);
lean_dec_ref(v_message_2168_);
v___y_2151_ = v___x_2170_;
goto v___jp_2150_;
}
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; 
v___x_2152_ = lean_mk_io_user_error(v___y_2151_);
v___x_2153_ = lean_apply_3(v_onFailure_2148_, v_handler_2066_, v___x_2152_, lean_box(0));
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = 0;
v___x_2156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2154_, v___x_2155_, v___x_2153_, v___f_2149_);
return v___x_2156_;
}
}
case 4:
{
lean_object* v_requestStream_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_5177__overap_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v_connectionContext_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v___f_2068_);
lean_dec(v_handler_2066_);
lean_dec_ref(v___f_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec_ref(v_config_2063_);
v_requestStream_2171_ = lean_ctor_get(v___y_2073_, 1);
lean_inc_ref_n(v_requestStream_2171_, 2);
v___x_2172_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2173_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2174_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2175_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2176_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2176_, 0, lean_box(0));
lean_closure_set(v___x_2176_, 1, lean_box(0));
lean_closure_set(v___x_2176_, 2, v___x_2172_);
lean_closure_set(v___x_2176_, 3, lean_box(0));
lean_closure_set(v___x_2176_, 4, lean_box(0));
lean_closure_set(v___x_2176_, 5, v___x_2175_);
lean_closure_set(v___x_2176_, 6, v___f_2067_);
v___x_5177__overap_2177_ = l_Std_Mutex_atomically___redArg(v___x_2172_, v___f_2173_, v___f_2174_, v_requestStream_2171_, v___x_2176_);
v___x_2178_ = lean_apply_1(v___x_5177__overap_2177_, lean_box(0));
lean_inc_ref(v___y_2073_);
v___f_2179_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2179_, 0, v___y_2073_);
v___f_2180_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2180_, 0, v_requestStream_2171_);
lean_closure_set(v___f_2180_, 1, v___f_2179_);
lean_closure_set(v___f_2180_, 2, v___y_2073_);
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = 0;
v___x_2183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2181_, v___x_2182_, v___x_2178_, v___f_2180_);
return v___x_2183_;
}
case 6:
{
lean_object* v_machine_2184_; lean_object* v_requestStream_2185_; lean_object* v_respStream_2186_; uint8_t v_requiresData_2187_; lean_object* v_expectData_2188_; lean_object* v_pendingHead_2189_; lean_object* v___x_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_5198__overap_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___f_2199_; lean_object* v___f_2200_; lean_object* v___f_2201_; lean_object* v___f_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_connectionContext_2070_);
lean_dec_ref(v___f_2067_);
lean_dec(v_handler_2066_);
lean_dec_ref(v___f_2065_);
lean_dec_ref(v_inst_2064_);
v_machine_2184_ = lean_ctor_get(v___y_2073_, 0);
lean_inc_ref(v_machine_2184_);
v_requestStream_2185_ = lean_ctor_get(v___y_2073_, 1);
lean_inc_ref_n(v_requestStream_2185_, 2);
v_respStream_2186_ = lean_ctor_get(v___y_2073_, 6);
lean_inc(v_respStream_2186_);
v_requiresData_2187_ = lean_ctor_get_uint8(v___y_2073_, sizeof(void*)*9);
v_expectData_2188_ = lean_ctor_get(v___y_2073_, 7);
lean_inc(v_expectData_2188_);
v_pendingHead_2189_ = lean_ctor_get(v___y_2073_, 8);
lean_inc(v_pendingHead_2189_);
lean_dec_ref(v___y_2073_);
v___x_2190_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2191_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2192_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2193_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2194_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2194_, 0, lean_box(0));
lean_closure_set(v___x_2194_, 1, lean_box(0));
lean_closure_set(v___x_2194_, 2, v___x_2190_);
lean_closure_set(v___x_2194_, 3, lean_box(0));
lean_closure_set(v___x_2194_, 4, lean_box(0));
lean_closure_set(v___x_2194_, 5, v___x_2193_);
lean_closure_set(v___x_2194_, 6, v___f_2068_);
v___x_5198__overap_2195_ = l_Std_Mutex_atomically___redArg(v___x_2190_, v___f_2191_, v___f_2192_, v_requestStream_2185_, v___x_2194_);
v___x_2196_ = lean_apply_1(v___x_5198__overap_2195_, lean_box(0));
v___x_2197_ = lean_box(v_requiresData_2187_);
v___f_2198_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2198_, 0, v_config_2063_);
lean_closure_set(v___f_2198_, 1, v_machine_2184_);
lean_closure_set(v___f_2198_, 2, v___x_2197_);
lean_closure_set(v___f_2198_, 3, v_expectData_2188_);
lean_closure_set(v___f_2198_, 4, v_pendingHead_2189_);
v___f_2199_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2199_, 0, v___f_2198_);
lean_inc_ref(v___f_2199_);
v___f_2200_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2200_, 0, v___f_2199_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2201_, 0, v_respStream_2186_);
lean_closure_set(v___f_2201_, 1, v_inst_2069_);
lean_closure_set(v___f_2201_, 2, v___f_2200_);
lean_closure_set(v___f_2201_, 3, v___f_2199_);
lean_inc_ref(v___f_2201_);
v___f_2202_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2202_, 0, v___f_2201_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2203_, 0, v_requestStream_2185_);
lean_closure_set(v___f_2203_, 1, v___f_2202_);
lean_closure_set(v___f_2203_, 2, v___f_2201_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = 0;
v___x_2206_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2204_, v___x_2205_, v___x_2196_, v___f_2203_);
return v___x_2206_;
}
case 7:
{
lean_object* v_pendingHead_2207_; 
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v___f_2068_);
lean_dec_ref(v___f_2067_);
lean_dec_ref(v___f_2065_);
v_pendingHead_2207_ = lean_ctor_get(v___y_2073_, 8);
if (lean_obj_tag(v_pendingHead_2207_) == 1)
{
lean_object* v_machine_2208_; lean_object* v_requestStream_2209_; lean_object* v_keepAliveTimeout_2210_; lean_object* v_currentTimeout_2211_; lean_object* v_headerTimeout_2212_; lean_object* v_response_2213_; lean_object* v_respStream_2214_; uint8_t v_requiresData_2215_; lean_object* v_expectData_2216_; uint8_t v_handlerDispatched_2217_; lean_object* v_val_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
lean_inc_ref(v_pendingHead_2207_);
v_machine_2208_ = lean_ctor_get(v___y_2073_, 0);
lean_inc_ref(v_machine_2208_);
v_requestStream_2209_ = lean_ctor_get(v___y_2073_, 1);
lean_inc_ref(v_requestStream_2209_);
v_keepAliveTimeout_2210_ = lean_ctor_get(v___y_2073_, 2);
lean_inc(v_keepAliveTimeout_2210_);
v_currentTimeout_2211_ = lean_ctor_get(v___y_2073_, 3);
lean_inc(v_currentTimeout_2211_);
v_headerTimeout_2212_ = lean_ctor_get(v___y_2073_, 4);
lean_inc(v_headerTimeout_2212_);
v_response_2213_ = lean_ctor_get(v___y_2073_, 5);
lean_inc_ref(v_response_2213_);
v_respStream_2214_ = lean_ctor_get(v___y_2073_, 6);
lean_inc(v_respStream_2214_);
v_requiresData_2215_ = lean_ctor_get_uint8(v___y_2073_, sizeof(void*)*9);
v_expectData_2216_ = lean_ctor_get(v___y_2073_, 7);
lean_inc(v_expectData_2216_);
v_handlerDispatched_2217_ = lean_ctor_get_uint8(v___y_2073_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2073_);
v_val_2218_ = lean_ctor_get(v_pendingHead_2207_, 0);
lean_inc(v_val_2218_);
v___x_2219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2064_, v_handler_2066_, v_machine_2208_, v_val_2218_, v_config_2063_, v_connectionContext_2070_);
v___x_2220_ = lean_box(v_requiresData_2215_);
v___x_2221_ = lean_box(v_handlerDispatched_2217_);
v___f_2222_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2222_, 0, v_requestStream_2209_);
lean_closure_set(v___f_2222_, 1, v_keepAliveTimeout_2210_);
lean_closure_set(v___f_2222_, 2, v_currentTimeout_2211_);
lean_closure_set(v___f_2222_, 3, v_headerTimeout_2212_);
lean_closure_set(v___f_2222_, 4, v_response_2213_);
lean_closure_set(v___f_2222_, 5, v_respStream_2214_);
lean_closure_set(v___f_2222_, 6, v___x_2220_);
lean_closure_set(v___f_2222_, 7, v_expectData_2216_);
lean_closure_set(v___f_2222_, 8, v___x_2221_);
lean_closure_set(v___f_2222_, 9, v_pendingHead_2207_);
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = 0;
v___x_2225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2223_, v___x_2224_, v___x_2219_, v___f_2222_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_connectionContext_2070_);
lean_dec(v_handler_2066_);
lean_dec_ref(v_inst_2064_);
lean_dec_ref(v_config_2063_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___y_2073_);
v___x_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
default: 
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_a_2071_);
lean_dec_ref(v_connectionContext_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v___f_2068_);
lean_dec_ref(v___f_2067_);
lean_dec(v_handler_2066_);
lean_dec_ref(v___f_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec_ref(v_config_2063_);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___y_2073_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2232_, lean_object* v_inst_2233_, lean_object* v___f_2234_, lean_object* v_handler_2235_, lean_object* v___f_2236_, lean_object* v___f_2237_, lean_object* v_inst_2238_, lean_object* v_connectionContext_2239_, lean_object* v_a_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2232_, v_inst_2233_, v___f_2234_, v_handler_2235_, v___f_2236_, v___f_2237_, v_inst_2238_, v_connectionContext_2239_, v_a_2240_, v_x_2241_, v___y_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_x_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_handler_2255_, lean_object* v_config_2256_, lean_object* v_connectionContext_2257_, lean_object* v_events_2258_, lean_object* v_state_2259_){
_start:
{
lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___x_2263_; size_t v_sz_2264_; size_t v___x_2265_; lean_object* v___x_4110__overap_2266_; lean_object* v___x_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; 
v___f_2261_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2262_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2262_, 0, v_config_2256_);
lean_closure_set(v___f_2262_, 1, v_inst_2253_);
lean_closure_set(v___f_2262_, 2, v___f_2261_);
lean_closure_set(v___f_2262_, 3, v_handler_2255_);
lean_closure_set(v___f_2262_, 4, v___f_2261_);
lean_closure_set(v___f_2262_, 5, v___f_2261_);
lean_closure_set(v___f_2262_, 6, v_inst_2254_);
lean_closure_set(v___f_2262_, 7, v_connectionContext_2257_);
v___x_2263_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2264_ = lean_array_size(v_events_2258_);
v___x_2265_ = ((size_t)0ULL);
v___x_4110__overap_2266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2263_, v_events_2258_, v___f_2262_, v_sz_2264_, v___x_2265_, v_state_2259_);
v___x_2267_ = lean_apply_1(v___x_4110__overap_2266_, lean_box(0));
v___f_2268_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = 0;
v___x_2271_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2269_, v___x_2270_, v___x_2267_, v___f_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_handler_2274_, lean_object* v_config_2275_, lean_object* v_connectionContext_2276_, lean_object* v_events_2277_, lean_object* v_state_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2272_, v_inst_2273_, v_handler_2274_, v_config_2275_, v_connectionContext_2276_, v_events_2277_, v_state_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2281_, lean_object* v_00_u03b2_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_handler_2285_, lean_object* v_config_2286_, lean_object* v_connectionContext_2287_, lean_object* v_events_2288_, lean_object* v_state_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2283_, v_inst_2284_, v_handler_2285_, v_config_2286_, v_connectionContext_2287_, v_events_2288_, v_state_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2292_, lean_object* v_00_u03b2_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_handler_2296_, lean_object* v_config_2297_, lean_object* v_connectionContext_2298_, lean_object* v_events_2299_, lean_object* v_state_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2292_, v_00_u03b2_2293_, v_inst_2294_, v_inst_2295_, v_handler_2296_, v_config_2297_, v_connectionContext_2298_, v_events_2299_, v_state_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2303_){
_start:
{
if (lean_obj_tag(v_x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v_x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v_x_2303_, 1);
v___x_2305_ = lean_task_pure(v_a_2304_);
return v___x_2305_;
}
else
{
lean_object* v_a_2306_; 
v_a_2306_ = lean_ctor_get(v_x_2303_, 0);
lean_inc_ref(v_a_2306_);
lean_dec_ref_known(v_x_2303_, 1);
return v_a_2306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2307_, lean_object* v_requestStream_2308_, lean_object* v_keepAliveTimeout_2309_, lean_object* v_currentTimeout_2310_, lean_object* v_headerTimeout_2311_, lean_object* v_response_2312_, lean_object* v_respStream_2313_, uint8_t v_requiresData_2314_, lean_object* v_expectData_2315_, lean_object* v_x_2316_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_expectData_2315_);
lean_dec(v_respStream_2313_);
lean_dec_ref(v_response_2312_);
lean_dec(v_headerTimeout_2311_);
lean_dec(v_currentTimeout_2310_);
lean_dec(v_keepAliveTimeout_2309_);
lean_dec_ref(v_requestStream_2308_);
lean_dec_ref(v_machine_2307_);
v_a_2318_ = lean_ctor_get(v_x_2316_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_x_2316_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v_x_2316_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v_x_2316_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
}
else
{
lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2316_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v_x_2316_, 0);
lean_dec(v_unused_2338_);
v___x_2328_ = v_x_2316_;
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_x_2316_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2330_ = 1;
v___x_2331_ = lean_box(0);
v___x_2332_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2332_, 0, v_machine_2307_);
lean_ctor_set(v___x_2332_, 1, v_requestStream_2308_);
lean_ctor_set(v___x_2332_, 2, v_keepAliveTimeout_2309_);
lean_ctor_set(v___x_2332_, 3, v_currentTimeout_2310_);
lean_ctor_set(v___x_2332_, 4, v_headerTimeout_2311_);
lean_ctor_set(v___x_2332_, 5, v_response_2312_);
lean_ctor_set(v___x_2332_, 6, v_respStream_2313_);
lean_ctor_set(v___x_2332_, 7, v_expectData_2315_);
lean_ctor_set(v___x_2332_, 8, v___x_2331_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*9, v_requiresData_2314_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*9 + 1, v___x_2330_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2334_ = v___x_2328_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2332_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2339_, lean_object* v_requestStream_2340_, lean_object* v_keepAliveTimeout_2341_, lean_object* v_currentTimeout_2342_, lean_object* v_headerTimeout_2343_, lean_object* v_response_2344_, lean_object* v_respStream_2345_, lean_object* v_requiresData_2346_, lean_object* v_expectData_2347_, lean_object* v_x_2348_, lean_object* v___y_2349_){
_start:
{
uint8_t v_requiresData_boxed_2350_; lean_object* v_res_2351_; 
v_requiresData_boxed_2350_ = lean_unbox(v_requiresData_2346_);
v_res_2351_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2339_, v_requestStream_2340_, v_keepAliveTimeout_2341_, v_currentTimeout_2342_, v_headerTimeout_2343_, v_response_2344_, v_respStream_2345_, v_requiresData_boxed_2350_, v_expectData_2347_, v_x_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2352_, lean_object* v_response_2353_, lean_object* v___x_2354_, lean_object* v___f_2355_, lean_object* v_x_2356_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___f_2355_);
lean_dec(v___x_2354_);
lean_dec_ref(v_response_2353_);
lean_dec_ref(v_toFunctor_2352_);
v_a_2358_ = lean_ctor_get(v_x_2356_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_x_2356_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2360_ = v_x_2356_;
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v_x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2381_; 
v_a_2367_ = lean_ctor_get(v_x_2356_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_x_2356_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2369_ = v_x_2356_;
v_isShared_2370_ = v_isSharedCheck_2381_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v_x_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2381_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2371_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2371_, 0, lean_box(0));
lean_closure_set(v___x_2371_, 1, lean_box(0));
lean_closure_set(v___x_2371_, 2, v_toFunctor_2352_);
v___x_2372_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2372_, 0, lean_box(0));
lean_closure_set(v___x_2372_, 1, v_response_2353_);
v___x_2373_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2373_, 0, lean_box(0));
lean_closure_set(v___x_2373_, 1, lean_box(0));
lean_closure_set(v___x_2373_, 2, lean_box(0));
lean_closure_set(v___x_2373_, 3, v___x_2371_);
lean_closure_set(v___x_2373_, 4, v___x_2372_);
v___x_2374_ = 0;
lean_inc(v___x_2354_);
v___x_2375_ = l_BaseIO_chainTask___redArg(v_a_2367_, v___x_2373_, v___x_2354_, v___x_2374_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2375_);
v___x_2377_ = v___x_2369_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___x_2379_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2354_, v___x_2374_, v___x_2378_, v___f_2355_);
return v___x_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2382_, lean_object* v_response_2383_, lean_object* v___x_2384_, lean_object* v___f_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2382_, v_response_2383_, v___x_2384_, v___f_2385_, v_x_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2390_, lean_object* v_handler_2391_, lean_object* v_extensions_2392_, lean_object* v_connectionContext_2393_, lean_object* v_state_2394_){
_start:
{
lean_object* v___x_2396_; lean_object* v_toApplicative_2397_; lean_object* v_pendingHead_2398_; 
v___x_2396_ = l_instMonadBaseIO;
v_toApplicative_2397_ = lean_ctor_get(v___x_2396_, 0);
v_pendingHead_2398_ = lean_ctor_get(v_state_2394_, 8);
lean_inc(v_pendingHead_2398_);
if (lean_obj_tag(v_pendingHead_2398_) == 1)
{
lean_object* v_toFunctor_2399_; lean_object* v_machine_2400_; lean_object* v_requestStream_2401_; lean_object* v_keepAliveTimeout_2402_; lean_object* v_currentTimeout_2403_; lean_object* v_headerTimeout_2404_; lean_object* v_response_2405_; lean_object* v_respStream_2406_; uint8_t v_requiresData_2407_; lean_object* v_expectData_2408_; lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2431_; 
v_toFunctor_2399_ = lean_ctor_get(v_toApplicative_2397_, 0);
v_machine_2400_ = lean_ctor_get(v_state_2394_, 0);
lean_inc_ref(v_machine_2400_);
v_requestStream_2401_ = lean_ctor_get(v_state_2394_, 1);
lean_inc_ref(v_requestStream_2401_);
v_keepAliveTimeout_2402_ = lean_ctor_get(v_state_2394_, 2);
lean_inc(v_keepAliveTimeout_2402_);
v_currentTimeout_2403_ = lean_ctor_get(v_state_2394_, 3);
lean_inc(v_currentTimeout_2403_);
v_headerTimeout_2404_ = lean_ctor_get(v_state_2394_, 4);
lean_inc(v_headerTimeout_2404_);
v_response_2405_ = lean_ctor_get(v_state_2394_, 5);
lean_inc_ref(v_response_2405_);
v_respStream_2406_ = lean_ctor_get(v_state_2394_, 6);
lean_inc(v_respStream_2406_);
v_requiresData_2407_ = lean_ctor_get_uint8(v_state_2394_, sizeof(void*)*9);
v_expectData_2408_ = lean_ctor_get(v_state_2394_, 7);
lean_inc(v_expectData_2408_);
lean_dec_ref(v_state_2394_);
v_val_2409_ = lean_ctor_get(v_pendingHead_2398_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_pendingHead_2398_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2411_ = v_pendingHead_2398_;
v_isShared_2412_ = v_isSharedCheck_2431_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v_pendingHead_2398_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2431_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_onRequest_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___f_2419_; lean_object* v___x_2420_; lean_object* v___f_2421_; lean_object* v___f_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v_onRequest_2413_ = lean_ctor_get(v_inst_2390_, 1);
lean_inc_ref(v_onRequest_2413_);
lean_dec_ref(v_inst_2390_);
lean_inc_ref(v_requestStream_2401_);
v___x_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2414_, 0, v_val_2409_);
lean_ctor_set(v___x_2414_, 1, v_requestStream_2401_);
lean_ctor_set(v___x_2414_, 2, v_extensions_2392_);
v___x_2415_ = lean_apply_3(v_onRequest_2413_, v_handler_2391_, v___x_2414_, v_connectionContext_2393_);
v___x_2416_ = lean_unsigned_to_nat(0u);
v___x_2417_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2417_, 0, lean_box(0));
lean_closure_set(v___x_2417_, 1, v___x_2415_);
v___x_2418_ = lean_io_as_task(v___x_2417_, v___x_2416_);
v___f_2419_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2420_ = lean_box(v_requiresData_2407_);
lean_inc_ref(v_response_2405_);
v___f_2421_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2421_, 0, v_machine_2400_);
lean_closure_set(v___f_2421_, 1, v_requestStream_2401_);
lean_closure_set(v___f_2421_, 2, v_keepAliveTimeout_2402_);
lean_closure_set(v___f_2421_, 3, v_currentTimeout_2403_);
lean_closure_set(v___f_2421_, 4, v_headerTimeout_2404_);
lean_closure_set(v___f_2421_, 5, v_response_2405_);
lean_closure_set(v___f_2421_, 6, v_respStream_2406_);
lean_closure_set(v___f_2421_, 7, v___x_2420_);
lean_closure_set(v___f_2421_, 8, v_expectData_2408_);
lean_inc_ref(v_toFunctor_2399_);
v___f_2422_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2422_, 0, v_toFunctor_2399_);
lean_closure_set(v___f_2422_, 1, v_response_2405_);
lean_closure_set(v___f_2422_, 2, v___x_2416_);
lean_closure_set(v___f_2422_, 3, v___f_2421_);
v___x_2423_ = 1;
v___x_2424_ = lean_task_bind(v___x_2418_, v___f_2419_, v___x_2416_, v___x_2423_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2424_);
v___x_2426_ = v___x_2411_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
v___x_2428_ = 0;
v___x_2429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2416_, v___x_2428_, v___x_2427_, v___f_2422_);
return v___x_2429_;
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec(v_pendingHead_2398_);
lean_dec_ref(v_connectionContext_2393_);
lean_dec(v_extensions_2392_);
lean_dec(v_handler_2391_);
lean_dec_ref(v_inst_2390_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_state_2394_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2434_, lean_object* v_handler_2435_, lean_object* v_extensions_2436_, lean_object* v_connectionContext_2437_, lean_object* v_state_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2434_, v_handler_2435_, v_extensions_2436_, v_connectionContext_2437_, v_state_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2441_, lean_object* v_inst_2442_, lean_object* v_handler_2443_, lean_object* v_extensions_2444_, lean_object* v_connectionContext_2445_, lean_object* v_state_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2442_, v_handler_2443_, v_extensions_2444_, v_connectionContext_2445_, v_state_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2449_, lean_object* v_inst_2450_, lean_object* v_handler_2451_, lean_object* v_extensions_2452_, lean_object* v_connectionContext_2453_, lean_object* v_state_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2449_, v_inst_2450_, v_handler_2451_, v_extensions_2452_, v_connectionContext_2453_, v_state_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2457_, lean_object* v_____r_2458_){
_start:
{
lean_object* v_writer_2460_; lean_object* v_reader_2461_; lean_object* v_config_2462_; lean_object* v_events_2463_; lean_object* v_error_2464_; lean_object* v_instant_2465_; uint8_t v_keepAlive_2466_; uint8_t v_forcedFlush_2467_; uint8_t v_pullBodyStalled_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2495_; 
v_writer_2460_ = lean_ctor_get(v_machine_2457_, 1);
v_reader_2461_ = lean_ctor_get(v_machine_2457_, 0);
v_config_2462_ = lean_ctor_get(v_machine_2457_, 2);
v_events_2463_ = lean_ctor_get(v_machine_2457_, 3);
v_error_2464_ = lean_ctor_get(v_machine_2457_, 4);
v_instant_2465_ = lean_ctor_get(v_machine_2457_, 5);
v_keepAlive_2466_ = lean_ctor_get_uint8(v_machine_2457_, sizeof(void*)*6);
v_forcedFlush_2467_ = lean_ctor_get_uint8(v_machine_2457_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2468_ = lean_ctor_get_uint8(v_machine_2457_, sizeof(void*)*6 + 2);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_machine_2457_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2470_ = v_machine_2457_;
v_isShared_2471_ = v_isSharedCheck_2495_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_instant_2465_);
lean_inc(v_error_2464_);
lean_inc(v_events_2463_);
lean_inc(v_config_2462_);
lean_inc(v_writer_2460_);
lean_inc(v_reader_2461_);
lean_dec(v_machine_2457_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2495_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_userData_2472_; lean_object* v_outputData_2473_; lean_object* v_state_2474_; lean_object* v_knownSize_2475_; lean_object* v_messageHead_2476_; uint8_t v_sentMessage_2477_; uint8_t v_omitBody_2478_; lean_object* v_userDataBytes_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2494_; 
v_userData_2472_ = lean_ctor_get(v_writer_2460_, 0);
v_outputData_2473_ = lean_ctor_get(v_writer_2460_, 1);
v_state_2474_ = lean_ctor_get(v_writer_2460_, 2);
v_knownSize_2475_ = lean_ctor_get(v_writer_2460_, 3);
v_messageHead_2476_ = lean_ctor_get(v_writer_2460_, 4);
v_sentMessage_2477_ = lean_ctor_get_uint8(v_writer_2460_, sizeof(void*)*6);
v_omitBody_2478_ = lean_ctor_get_uint8(v_writer_2460_, sizeof(void*)*6 + 2);
v_userDataBytes_2479_ = lean_ctor_get(v_writer_2460_, 5);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_writer_2460_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2481_ = v_writer_2460_;
v_isShared_2482_ = v_isSharedCheck_2494_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_userDataBytes_2479_);
lean_inc(v_messageHead_2476_);
lean_inc(v_knownSize_2475_);
lean_inc(v_state_2474_);
lean_inc(v_outputData_2473_);
lean_inc(v_userData_2472_);
lean_dec(v_writer_2460_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2494_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
uint8_t v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = 1;
if (v_isShared_2482_ == 0)
{
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_userData_2472_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_outputData_2473_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_state_2474_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_knownSize_2475_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_messageHead_2476_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_userDataBytes_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*6, v_sentMessage_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*6 + 2, v_omitBody_2478_);
v___x_2485_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*6 + 1, v___x_2483_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2485_);
v___x_2487_ = v___x_2470_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_reader_2461_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_config_2462_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_events_2463_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_error_2464_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_instant_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2492_, sizeof(void*)*6, v_keepAlive_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2492_, sizeof(void*)*6 + 1, v_forcedFlush_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2492_, sizeof(void*)*6 + 2, v_pullBodyStalled_2468_);
v___x_2487_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2496_, lean_object* v_____r_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2496_, v_____r_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__2(lean_object* v___f_2500_, lean_object* v_close_2501_, lean_object* v_body_2502_, lean_object* v___f_2503_, lean_object* v_x_2504_){
_start:
{
if (lean_obj_tag(v_x_2504_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2514_; 
lean_dec_ref(v___f_2503_);
lean_dec(v_body_2502_);
lean_dec_ref(v_close_2501_);
lean_dec_ref(v___f_2500_);
v_a_2506_ = lean_ctor_get(v_x_2504_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_x_2504_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2508_ = v_x_2504_;
v_isShared_2509_ = v_isSharedCheck_2514_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v_x_2504_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2514_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
}
else
{
lean_object* v_a_2515_; uint8_t v___x_2516_; uint8_t v___x_2517_; 
v_a_2515_ = lean_ctor_get(v_x_2504_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v_x_2504_, 1);
v___x_2516_ = lean_unbox(v_a_2515_);
lean_dec(v_a_2515_);
v___x_2517_ = lean_bool_not(v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref(v___f_2503_);
lean_dec(v_body_2502_);
lean_dec_ref(v_close_2501_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_apply_2(v___f_2500_, v___x_2518_, lean_box(0));
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref(v___f_2500_);
v___x_2520_ = lean_apply_2(v_close_2501_, v_body_2502_, lean_box(0));
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = 0;
v___x_2523_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2521_, v___x_2522_, v___x_2520_, v___f_2503_);
return v___x_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__2___boxed(lean_object* v___f_2524_, lean_object* v_close_2525_, lean_object* v_body_2526_, lean_object* v___f_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__2(v___f_2524_, v_close_2525_, v_body_2526_, v___f_2527_, v_x_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_x1_2531_, lean_object* v_x2_2532_){
_start:
{
lean_object* v_data_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_data_2533_ = lean_ctor_get(v_x2_2532_, 0);
v___x_2534_ = lean_byte_array_size(v_data_2533_);
v___x_2535_ = lean_nat_add(v_x1_2531_, v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_x1_2536_, lean_object* v_x2_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_x1_2536_, v_x2_2537_);
lean_dec_ref(v_x2_2537_);
lean_dec(v_x1_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_body_2539_, lean_object* v_machine_2540_, lean_object* v_isClosed_2541_, lean_object* v___f_2542_, lean_object* v___f_2543_, lean_object* v_x_2544_){
_start:
{
lean_object* v___y_2547_; 
if (lean_obj_tag(v_x_2544_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v___f_2543_);
lean_dec_ref(v___f_2542_);
lean_dec_ref(v_isClosed_2541_);
lean_dec_ref(v_machine_2540_);
lean_dec(v_body_2539_);
v_a_2552_ = lean_ctor_get(v_x_2544_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_x_2544_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2554_ = v_x_2544_;
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v_x_2544_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2628_; 
v_a_2561_ = lean_ctor_get(v_x_2544_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_x_2544_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2563_ = v_x_2544_;
v_isShared_2564_ = v_isSharedCheck_2628_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v_x_2544_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2628_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
if (lean_obj_tag(v_a_2561_) == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_dec_ref(v___f_2543_);
lean_dec_ref(v___f_2542_);
lean_dec_ref(v_isClosed_2541_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_body_2539_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_machine_2540_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2566_);
v___x_2568_ = v___x_2563_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
return v___x_2569_;
}
}
else
{
lean_object* v_val_2571_; 
lean_del_object(v___x_2563_);
v_val_2571_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_val_2571_);
lean_dec_ref_known(v_a_2561_, 1);
if (lean_obj_tag(v_val_2571_) == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref(v___f_2543_);
lean_dec_ref(v_machine_2540_);
v___x_2572_ = lean_apply_2(v_isClosed_2541_, v_body_2539_, lean_box(0));
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = 0;
v___x_2575_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2573_, v___x_2574_, v___x_2572_, v___f_2542_);
return v___x_2575_;
}
else
{
lean_object* v_val_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
lean_dec_ref(v___f_2542_);
lean_dec_ref(v_isClosed_2541_);
v_val_2576_ = lean_ctor_get(v_val_2571_, 0);
lean_inc(v_val_2576_);
lean_dec_ref_known(v_val_2571_, 1);
v___x_2577_ = lean_unsigned_to_nat(1u);
v___x_2578_ = lean_mk_empty_array_with_capacity(v___x_2577_);
v___x_2579_ = lean_array_push(v___x_2578_, v_val_2576_);
v___x_2580_ = lean_array_get_size(v___x_2579_);
v___x_2581_ = lean_unsigned_to_nat(0u);
v___x_2582_ = lean_nat_dec_eq(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v_reader_2583_; lean_object* v_writer_2584_; lean_object* v_config_2585_; lean_object* v_events_2586_; lean_object* v_error_2587_; lean_object* v_instant_2588_; uint8_t v_keepAlive_2589_; uint8_t v_forcedFlush_2590_; uint8_t v_pullBodyStalled_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2627_; 
v_reader_2583_ = lean_ctor_get(v_machine_2540_, 0);
v_writer_2584_ = lean_ctor_get(v_machine_2540_, 1);
v_config_2585_ = lean_ctor_get(v_machine_2540_, 2);
v_events_2586_ = lean_ctor_get(v_machine_2540_, 3);
v_error_2587_ = lean_ctor_get(v_machine_2540_, 4);
v_instant_2588_ = lean_ctor_get(v_machine_2540_, 5);
v_keepAlive_2589_ = lean_ctor_get_uint8(v_machine_2540_, sizeof(void*)*6);
v_forcedFlush_2590_ = lean_ctor_get_uint8(v_machine_2540_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2591_ = lean_ctor_get_uint8(v_machine_2540_, sizeof(void*)*6 + 2);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_machine_2540_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2593_ = v_machine_2540_;
v_isShared_2594_ = v_isSharedCheck_2627_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_instant_2588_);
lean_inc(v_error_2587_);
lean_inc(v_events_2586_);
lean_inc(v_config_2585_);
lean_inc(v_writer_2584_);
lean_inc(v_reader_2583_);
lean_dec(v_machine_2540_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2627_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___y_2596_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2619_ = lean_nat_dec_lt(v___x_2581_, v___x_2580_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v___f_2543_);
v___y_2596_ = v___x_2581_;
goto v___jp_2595_;
}
else
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_nat_dec_le(v___x_2580_, v___x_2580_);
if (v___x_2620_ == 0)
{
if (v___x_2619_ == 0)
{
lean_dec_ref(v___f_2543_);
v___y_2596_ = v___x_2581_;
goto v___jp_2595_;
}
else
{
size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = lean_usize_of_nat(v___x_2580_);
lean_inc_ref(v___x_2579_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2618_, v___f_2543_, v___x_2579_, v___x_2621_, v___x_2622_, v___x_2581_);
v___y_2596_ = v___x_2623_;
goto v___jp_2595_;
}
}
else
{
size_t v___x_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = lean_usize_of_nat(v___x_2580_);
lean_inc_ref(v___x_2579_);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2618_, v___f_2543_, v___x_2579_, v___x_2624_, v___x_2625_, v___x_2581_);
v___y_2596_ = v___x_2626_;
goto v___jp_2595_;
}
}
v___jp_2595_:
{
lean_object* v_userData_2597_; lean_object* v_outputData_2598_; lean_object* v_state_2599_; lean_object* v_knownSize_2600_; lean_object* v_messageHead_2601_; uint8_t v_sentMessage_2602_; uint8_t v_userClosedBody_2603_; uint8_t v_omitBody_2604_; lean_object* v_userDataBytes_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2617_; 
v_userData_2597_ = lean_ctor_get(v_writer_2584_, 0);
v_outputData_2598_ = lean_ctor_get(v_writer_2584_, 1);
v_state_2599_ = lean_ctor_get(v_writer_2584_, 2);
v_knownSize_2600_ = lean_ctor_get(v_writer_2584_, 3);
v_messageHead_2601_ = lean_ctor_get(v_writer_2584_, 4);
v_sentMessage_2602_ = lean_ctor_get_uint8(v_writer_2584_, sizeof(void*)*6);
v_userClosedBody_2603_ = lean_ctor_get_uint8(v_writer_2584_, sizeof(void*)*6 + 1);
v_omitBody_2604_ = lean_ctor_get_uint8(v_writer_2584_, sizeof(void*)*6 + 2);
v_userDataBytes_2605_ = lean_ctor_get(v_writer_2584_, 5);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_writer_2584_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2607_ = v_writer_2584_;
v_isShared_2608_ = v_isSharedCheck_2617_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_userDataBytes_2605_);
lean_inc(v_messageHead_2601_);
lean_inc(v_knownSize_2600_);
lean_inc(v_state_2599_);
lean_inc(v_outputData_2598_);
lean_inc(v_userData_2597_);
lean_dec(v_writer_2584_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2617_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2609_ = l_Array_append___redArg(v_userData_2597_, v___x_2579_);
lean_dec_ref(v___x_2579_);
v___x_2610_ = lean_nat_add(v_userDataBytes_2605_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec(v_userDataBytes_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 5, v___x_2610_);
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2612_ = v___x_2607_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_outputData_2598_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_state_2599_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_knownSize_2600_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_messageHead_2601_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v___x_2610_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*6, v_sentMessage_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*6 + 1, v_userClosedBody_2603_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*6 + 2, v_omitBody_2604_);
v___x_2612_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2612_);
v___x_2614_ = v___x_2593_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_reader_2583_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_config_2585_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_events_2586_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_error_2587_);
lean_ctor_set(v_reuseFailAlloc_2615_, 5, v_instant_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*6, v_keepAlive_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*6 + 1, v_forcedFlush_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*6 + 2, v_pullBodyStalled_2591_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
v___y_2547_ = v___x_2614_;
goto v___jp_2546_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2579_);
lean_dec_ref(v___f_2543_);
v___y_2547_ = v_machine_2540_;
goto v___jp_2546_;
}
}
}
}
}
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_body_2539_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___y_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_body_2629_, lean_object* v_machine_2630_, lean_object* v_isClosed_2631_, lean_object* v___f_2632_, lean_object* v___f_2633_, lean_object* v_x_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_body_2629_, v_machine_2630_, v_isClosed_2631_, v___f_2632_, v___f_2633_, v_x_2634_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2638_, lean_object* v_machine_2639_, lean_object* v_body_2640_){
_start:
{
lean_object* v_close_2642_; lean_object* v_isClosed_2643_; lean_object* v_tryRecv_2644_; lean_object* v___x_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; lean_object* v___x_2653_; 
v_close_2642_ = lean_ctor_get(v_inst_2638_, 1);
lean_inc_ref(v_close_2642_);
v_isClosed_2643_ = lean_ctor_get(v_inst_2638_, 2);
lean_inc_ref(v_isClosed_2643_);
v_tryRecv_2644_ = lean_ctor_get(v_inst_2638_, 4);
lean_inc_ref(v_tryRecv_2644_);
lean_dec_ref(v_inst_2638_);
lean_inc_n(v_body_2640_, 2);
v___x_2645_ = lean_apply_2(v_tryRecv_2644_, v_body_2640_, lean_box(0));
lean_inc_ref(v_machine_2639_);
v___f_2646_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2646_, 0, v_machine_2639_);
lean_inc_ref(v___f_2646_);
v___f_2647_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2647_, 0, v___f_2646_);
v___f_2648_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2648_, 0, v___f_2646_);
lean_closure_set(v___f_2648_, 1, v_close_2642_);
lean_closure_set(v___f_2648_, 2, v_body_2640_);
lean_closure_set(v___f_2648_, 3, v___f_2647_);
v___f_2649_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2650_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2650_, 0, v_body_2640_);
lean_closure_set(v___f_2650_, 1, v_machine_2639_);
lean_closure_set(v___f_2650_, 2, v_isClosed_2643_);
lean_closure_set(v___f_2650_, 3, v___f_2648_);
lean_closure_set(v___f_2650_, 4, v___f_2649_);
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = 0;
v___x_2653_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2651_, v___x_2652_, v___x_2645_, v___f_2650_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2654_, lean_object* v_machine_2655_, lean_object* v_body_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2654_, v_machine_2655_, v_body_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2659_, lean_object* v_inst_2660_, lean_object* v_machine_2661_, lean_object* v_body_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2660_, v_machine_2661_, v_body_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2665_, lean_object* v_inst_2666_, lean_object* v_machine_2667_, lean_object* v_body_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2665_, v_inst_2666_, v_machine_2667_, v_body_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2677_, lean_object* v_____r_2678_, lean_object* v_st_2679_){
_start:
{
lean_object* v_machine_2681_; lean_object* v_requestStream_2682_; lean_object* v_keepAliveTimeout_2683_; lean_object* v_currentTimeout_2684_; lean_object* v_headerTimeout_2685_; lean_object* v_response_2686_; lean_object* v_respStream_2687_; uint8_t v_requiresData_2688_; lean_object* v_expectData_2689_; uint8_t v_handlerDispatched_2690_; lean_object* v_pendingHead_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2773_; 
v_machine_2681_ = lean_ctor_get(v_st_2679_, 0);
v_requestStream_2682_ = lean_ctor_get(v_st_2679_, 1);
v_keepAliveTimeout_2683_ = lean_ctor_get(v_st_2679_, 2);
v_currentTimeout_2684_ = lean_ctor_get(v_st_2679_, 3);
v_headerTimeout_2685_ = lean_ctor_get(v_st_2679_, 4);
v_response_2686_ = lean_ctor_get(v_st_2679_, 5);
v_respStream_2687_ = lean_ctor_get(v_st_2679_, 6);
v_requiresData_2688_ = lean_ctor_get_uint8(v_st_2679_, sizeof(void*)*9);
v_expectData_2689_ = lean_ctor_get(v_st_2679_, 7);
v_handlerDispatched_2690_ = lean_ctor_get_uint8(v_st_2679_, sizeof(void*)*9 + 1);
v_pendingHead_2691_ = lean_ctor_get(v_st_2679_, 8);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_st_2679_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2693_ = v_st_2679_;
v_isShared_2694_ = v_isSharedCheck_2773_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_pendingHead_2691_);
lean_inc(v_expectData_2689_);
lean_inc(v_respStream_2687_);
lean_inc(v_response_2686_);
lean_inc(v_headerTimeout_2685_);
lean_inc(v_currentTimeout_2684_);
lean_inc(v_keepAliveTimeout_2683_);
lean_inc(v_requestStream_2682_);
lean_inc(v_machine_2681_);
lean_dec(v_st_2679_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2773_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___y_2696_; lean_object* v_reader_2705_; lean_object* v_state_2706_; 
v_reader_2705_ = lean_ctor_get(v_machine_2681_, 0);
lean_inc_ref(v_reader_2705_);
v_state_2706_ = lean_ctor_get(v_reader_2705_, 0);
lean_inc(v_state_2706_);
if (lean_obj_tag(v_state_2706_) == 6)
{
lean_dec_ref(v_reader_2705_);
lean_dec_ref(v_val_2677_);
v___y_2696_ = v_machine_2681_;
goto v___jp_2695_;
}
else
{
if (lean_obj_tag(v_state_2706_) == 7)
{
lean_dec_ref_known(v_state_2706_, 1);
lean_dec_ref(v_reader_2705_);
lean_dec_ref(v_val_2677_);
v___y_2696_ = v_machine_2681_;
goto v___jp_2695_;
}
else
{
lean_object* v_input_2707_; lean_object* v_writer_2708_; lean_object* v_config_2709_; lean_object* v_events_2710_; lean_object* v_error_2711_; lean_object* v_instant_2712_; uint8_t v_keepAlive_2713_; uint8_t v_forcedFlush_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2771_; 
v_input_2707_ = lean_ctor_get(v_reader_2705_, 1);
lean_inc_ref(v_input_2707_);
v_writer_2708_ = lean_ctor_get(v_machine_2681_, 1);
v_config_2709_ = lean_ctor_get(v_machine_2681_, 2);
v_events_2710_ = lean_ctor_get(v_machine_2681_, 3);
v_error_2711_ = lean_ctor_get(v_machine_2681_, 4);
v_instant_2712_ = lean_ctor_get(v_machine_2681_, 5);
v_keepAlive_2713_ = lean_ctor_get_uint8(v_machine_2681_, sizeof(void*)*6);
v_forcedFlush_2714_ = lean_ctor_get_uint8(v_machine_2681_, sizeof(void*)*6 + 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_machine_2681_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v_machine_2681_, 0);
lean_dec(v_unused_2772_);
v___x_2716_ = v_machine_2681_;
v_isShared_2717_ = v_isSharedCheck_2771_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_instant_2712_);
lean_inc(v_error_2711_);
lean_inc(v_events_2710_);
lean_inc(v_config_2709_);
lean_inc(v_writer_2708_);
lean_dec(v_machine_2681_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2771_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_messageHead_2718_; lean_object* v_messageCount_2719_; lean_object* v_bodyBytesRead_2720_; lean_object* v_headerBytesRead_2721_; uint8_t v_noMoreInput_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2768_; 
v_messageHead_2718_ = lean_ctor_get(v_reader_2705_, 2);
v_messageCount_2719_ = lean_ctor_get(v_reader_2705_, 3);
v_bodyBytesRead_2720_ = lean_ctor_get(v_reader_2705_, 4);
v_headerBytesRead_2721_ = lean_ctor_get(v_reader_2705_, 5);
v_noMoreInput_2722_ = lean_ctor_get_uint8(v_reader_2705_, sizeof(void*)*6);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_reader_2705_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; lean_object* v_unused_2770_; 
v_unused_2769_ = lean_ctor_get(v_reader_2705_, 1);
lean_dec(v_unused_2769_);
v_unused_2770_ = lean_ctor_get(v_reader_2705_, 0);
lean_dec(v_unused_2770_);
v___x_2724_ = v_reader_2705_;
v_isShared_2725_ = v_isSharedCheck_2768_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_headerBytesRead_2721_);
lean_inc(v_bodyBytesRead_2720_);
lean_inc(v_messageCount_2719_);
lean_inc(v_messageHead_2718_);
lean_dec(v_reader_2705_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2768_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_array_2726_; lean_object* v_idx_2727_; uint8_t v___x_2728_; lean_object* v___y_2730_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_array_2726_ = lean_ctor_get(v_input_2707_, 0);
lean_inc_ref(v_array_2726_);
v_idx_2727_ = lean_ctor_get(v_input_2707_, 1);
lean_inc(v_idx_2727_);
lean_dec_ref(v_input_2707_);
v___x_2728_ = 0;
v___x_2759_ = lean_byte_array_size(v_array_2726_);
v___x_2760_ = lean_nat_dec_le(v___x_2759_, v_idx_2727_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2761_ = l_ByteArray_extract(v_array_2726_, v_idx_2727_, v___x_2759_);
lean_dec_ref(v_array_2726_);
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = lean_byte_array_size(v___x_2761_);
v___x_2764_ = lean_byte_array_size(v_val_2677_);
v___x_2765_ = lean_byte_array_copy_slice(v_val_2677_, v___x_2762_, v___x_2761_, v___x_2763_, v___x_2764_, v___x_2760_);
lean_dec_ref(v_val_2677_);
v___x_2766_ = l_ByteArray_mkIterator(v___x_2765_);
v___y_2730_ = v___x_2766_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2767_; 
lean_dec(v_idx_2727_);
lean_dec_ref(v_array_2726_);
v___x_2767_ = l_ByteArray_mkIterator(v_val_2677_);
v___y_2730_ = v___x_2767_;
goto v___jp_2729_;
}
v___jp_2729_:
{
lean_object* v_maxHeaderBytes_2731_; lean_object* v_maxStartLineLength_2732_; lean_object* v_maxChunkLineLength_2733_; lean_object* v_maxBodySize_2734_; lean_object* v_array_2735_; lean_object* v_idx_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_maxHeaderBytes_2731_ = lean_ctor_get(v_config_2709_, 2);
v_maxStartLineLength_2732_ = lean_ctor_get(v_config_2709_, 5);
v_maxChunkLineLength_2733_ = lean_ctor_get(v_config_2709_, 13);
v_maxBodySize_2734_ = lean_ctor_get(v_config_2709_, 15);
v_array_2735_ = lean_ctor_get(v___y_2730_, 0);
v_idx_2736_ = lean_ctor_get(v___y_2730_, 1);
v___x_2737_ = lean_nat_add(v_maxBodySize_2734_, v_maxHeaderBytes_2731_);
v___x_2738_ = lean_nat_add(v___x_2737_, v_maxStartLineLength_2732_);
lean_dec(v___x_2737_);
v___x_2739_ = lean_nat_add(v___x_2738_, v_maxChunkLineLength_2733_);
lean_dec(v___x_2738_);
v___x_2740_ = lean_byte_array_size(v_array_2735_);
v___x_2741_ = lean_nat_sub(v___x_2740_, v_idx_2736_);
v___x_2742_ = lean_nat_dec_lt(v___x_2739_, v___x_2741_);
lean_dec(v___x_2741_);
lean_dec(v___x_2739_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2744_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v___y_2730_);
v___x_2744_ = v___x_2724_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_state_2706_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v___y_2730_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_messageHead_2718_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_messageCount_2719_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_bodyBytesRead_2720_);
lean_ctor_set(v_reuseFailAlloc_2748_, 5, v_headerBytesRead_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*6, v_noMoreInput_2722_);
v___x_2744_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v_machine_2746_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2744_);
v_machine_2746_ = v___x_2716_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_writer_2708_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_config_2709_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_events_2710_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_error_2711_);
lean_ctor_set(v_reuseFailAlloc_2747_, 5, v_instant_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6, v_keepAlive_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2747_, sizeof(void*)*6 + 1, v_forcedFlush_2714_);
v_machine_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_ctor_set_uint8(v_machine_2746_, sizeof(void*)*6 + 2, v___x_2728_);
v___y_2696_ = v_machine_2746_;
goto v___jp_2695_;
}
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
lean_dec(v_error_2711_);
lean_dec(v_state_2706_);
v___x_2749_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2750_ = lean_array_push(v_events_2710_, v___x_2749_);
v___x_2751_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v___y_2730_);
lean_ctor_set(v___x_2724_, 0, v___x_2751_);
v___x_2753_ = v___x_2724_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___y_2730_);
lean_ctor_set(v_reuseFailAlloc_2758_, 2, v_messageHead_2718_);
lean_ctor_set(v_reuseFailAlloc_2758_, 3, v_messageCount_2719_);
lean_ctor_set(v_reuseFailAlloc_2758_, 4, v_bodyBytesRead_2720_);
lean_ctor_set(v_reuseFailAlloc_2758_, 5, v_headerBytesRead_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2758_, sizeof(void*)*6, v_noMoreInput_2722_);
v___x_2753_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2754_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 4, v___x_2754_);
lean_ctor_set(v___x_2716_, 3, v___x_2750_);
lean_ctor_set(v___x_2716_, 0, v___x_2753_);
v___x_2756_ = v___x_2716_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_writer_2708_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_config_2709_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2757_, 5, v_instant_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*6, v_keepAlive_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*6 + 1, v_forcedFlush_2714_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_ctor_set_uint8(v___x_2756_, sizeof(void*)*6 + 2, v___x_2728_);
v___y_2696_ = v___x_2756_;
goto v___jp_2695_;
}
}
}
}
}
}
}
}
v___jp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___y_2696_);
v___x_2698_ = v___x_2693_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___y_2696_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_requestStream_2682_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_keepAliveTimeout_2683_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_currentTimeout_2684_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v_headerTimeout_2685_);
lean_ctor_set(v_reuseFailAlloc_2704_, 5, v_response_2686_);
lean_ctor_set(v_reuseFailAlloc_2704_, 6, v_respStream_2687_);
lean_ctor_set(v_reuseFailAlloc_2704_, 7, v_expectData_2689_);
lean_ctor_set(v_reuseFailAlloc_2704_, 8, v_pendingHead_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, sizeof(void*)*9, v_requiresData_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, sizeof(void*)*9 + 1, v_handlerDispatched_2690_);
v___x_2698_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2699_ = 0;
v___x_2700_ = lean_box(v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2698_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2774_, lean_object* v_____r_2775_, lean_object* v_st_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2774_, v_____r_2775_, v_st_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2779_, lean_object* v_machine_2780_, lean_object* v_requestStream_2781_, lean_object* v_currentTimeout_2782_, lean_object* v_response_2783_, lean_object* v_respStream_2784_, uint8_t v_requiresData_2785_, lean_object* v_expectData_2786_, uint8_t v_handlerDispatched_2787_, lean_object* v_pendingHead_2788_, lean_object* v___f_2789_, lean_object* v_x_2790_){
_start:
{
if (lean_obj_tag(v_x_2790_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2800_; 
lean_dec_ref(v___f_2789_);
lean_dec(v_pendingHead_2788_);
lean_dec(v_expectData_2786_);
lean_dec(v_respStream_2784_);
lean_dec_ref(v_response_2783_);
lean_dec(v_currentTimeout_2782_);
lean_dec_ref(v_requestStream_2781_);
lean_dec_ref(v_machine_2780_);
v_a_2792_ = lean_ctor_get(v_x_2790_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_x_2790_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2794_ = v_x_2790_;
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v_x_2790_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
return v___x_2798_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v_headerTimeout_2802_; lean_object* v_second_2803_; lean_object* v_nano_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v_second_2808_; lean_object* v_nano_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_a_2801_ = lean_ctor_get(v_x_2790_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v_x_2790_, 1);
v_headerTimeout_2802_ = lean_ctor_get(v_config_2779_, 6);
v_second_2803_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_second_2803_);
v_nano_2804_ = lean_ctor_get(v_a_2801_, 1);
lean_inc(v_nano_2804_);
lean_dec(v_a_2801_);
v___x_2805_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_2806_ = lean_int_mul(v_headerTimeout_2802_, v___x_2805_);
v___x_2807_ = l_Std_Time_Duration_ofNanoseconds(v___x_2806_);
lean_dec(v___x_2806_);
v_second_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_second_2808_);
v_nano_2809_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_nano_2809_);
lean_dec_ref(v___x_2807_);
v___x_2810_ = lean_box(0);
v___x_2811_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_2812_ = lean_int_mul(v_second_2803_, v___x_2811_);
lean_dec(v_second_2803_);
v___x_2813_ = lean_int_add(v___x_2812_, v_nano_2804_);
lean_dec(v_nano_2804_);
lean_dec(v___x_2812_);
v___x_2814_ = lean_int_mul(v_second_2808_, v___x_2811_);
lean_dec(v_second_2808_);
v___x_2815_ = lean_int_add(v___x_2814_, v_nano_2809_);
lean_dec(v_nano_2809_);
lean_dec(v___x_2814_);
v___x_2816_ = lean_int_add(v___x_2813_, v___x_2815_);
lean_dec(v___x_2815_);
lean_dec(v___x_2813_);
v___x_2817_ = l_Std_Time_Duration_ofNanoseconds(v___x_2816_);
lean_dec(v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2819_, 0, v_machine_2780_);
lean_ctor_set(v___x_2819_, 1, v_requestStream_2781_);
lean_ctor_set(v___x_2819_, 2, v___x_2810_);
lean_ctor_set(v___x_2819_, 3, v_currentTimeout_2782_);
lean_ctor_set(v___x_2819_, 4, v___x_2818_);
lean_ctor_set(v___x_2819_, 5, v_response_2783_);
lean_ctor_set(v___x_2819_, 6, v_respStream_2784_);
lean_ctor_set(v___x_2819_, 7, v_expectData_2786_);
lean_ctor_set(v___x_2819_, 8, v_pendingHead_2788_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*9, v_requiresData_2785_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*9 + 1, v_handlerDispatched_2787_);
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_apply_3(v___f_2789_, v___x_2820_, v___x_2819_, lean_box(0));
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2822_, lean_object* v_machine_2823_, lean_object* v_requestStream_2824_, lean_object* v_currentTimeout_2825_, lean_object* v_response_2826_, lean_object* v_respStream_2827_, lean_object* v_requiresData_2828_, lean_object* v_expectData_2829_, lean_object* v_handlerDispatched_2830_, lean_object* v_pendingHead_2831_, lean_object* v___f_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_){
_start:
{
uint8_t v_requiresData_boxed_2835_; uint8_t v_handlerDispatched_boxed_2836_; lean_object* v_res_2837_; 
v_requiresData_boxed_2835_ = lean_unbox(v_requiresData_2828_);
v_handlerDispatched_boxed_2836_ = lean_unbox(v_handlerDispatched_2830_);
v_res_2837_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2822_, v_machine_2823_, v_requestStream_2824_, v_currentTimeout_2825_, v_response_2826_, v_respStream_2827_, v_requiresData_boxed_2835_, v_expectData_2829_, v_handlerDispatched_boxed_2836_, v_pendingHead_2831_, v___f_2832_, v_x_2833_);
lean_dec_ref(v_config_2822_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2838_, lean_object* v_requestStream_2839_, lean_object* v_keepAliveTimeout_2840_, lean_object* v_currentTimeout_2841_, lean_object* v_headerTimeout_2842_, lean_object* v_response_2843_, uint8_t v_requiresData_2844_, lean_object* v_expectData_2845_, uint8_t v_handlerDispatched_2846_, lean_object* v_pendingHead_2847_, lean_object* v_____r_2848_){
_start:
{
lean_object* v_writer_2850_; lean_object* v_reader_2851_; lean_object* v_config_2852_; lean_object* v_events_2853_; lean_object* v_error_2854_; lean_object* v_instant_2855_; uint8_t v_keepAlive_2856_; uint8_t v_forcedFlush_2857_; uint8_t v_pullBodyStalled_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2888_; 
v_writer_2850_ = lean_ctor_get(v_machine_2838_, 1);
v_reader_2851_ = lean_ctor_get(v_machine_2838_, 0);
v_config_2852_ = lean_ctor_get(v_machine_2838_, 2);
v_events_2853_ = lean_ctor_get(v_machine_2838_, 3);
v_error_2854_ = lean_ctor_get(v_machine_2838_, 4);
v_instant_2855_ = lean_ctor_get(v_machine_2838_, 5);
v_keepAlive_2856_ = lean_ctor_get_uint8(v_machine_2838_, sizeof(void*)*6);
v_forcedFlush_2857_ = lean_ctor_get_uint8(v_machine_2838_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2858_ = lean_ctor_get_uint8(v_machine_2838_, sizeof(void*)*6 + 2);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_machine_2838_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2860_ = v_machine_2838_;
v_isShared_2861_ = v_isSharedCheck_2888_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_instant_2855_);
lean_inc(v_error_2854_);
lean_inc(v_events_2853_);
lean_inc(v_config_2852_);
lean_inc(v_writer_2850_);
lean_inc(v_reader_2851_);
lean_dec(v_machine_2838_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2888_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_userData_2862_; lean_object* v_outputData_2863_; lean_object* v_state_2864_; lean_object* v_knownSize_2865_; lean_object* v_messageHead_2866_; uint8_t v_sentMessage_2867_; uint8_t v_omitBody_2868_; lean_object* v_userDataBytes_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2887_; 
v_userData_2862_ = lean_ctor_get(v_writer_2850_, 0);
v_outputData_2863_ = lean_ctor_get(v_writer_2850_, 1);
v_state_2864_ = lean_ctor_get(v_writer_2850_, 2);
v_knownSize_2865_ = lean_ctor_get(v_writer_2850_, 3);
v_messageHead_2866_ = lean_ctor_get(v_writer_2850_, 4);
v_sentMessage_2867_ = lean_ctor_get_uint8(v_writer_2850_, sizeof(void*)*6);
v_omitBody_2868_ = lean_ctor_get_uint8(v_writer_2850_, sizeof(void*)*6 + 2);
v_userDataBytes_2869_ = lean_ctor_get(v_writer_2850_, 5);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_writer_2850_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2871_ = v_writer_2850_;
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_userDataBytes_2869_);
lean_inc(v_messageHead_2866_);
lean_inc(v_knownSize_2865_);
lean_inc(v_state_2864_);
lean_inc(v_outputData_2863_);
lean_inc(v_userData_2862_);
lean_dec(v_writer_2850_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
uint8_t v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = 1;
if (v_isShared_2872_ == 0)
{
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_userData_2862_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_outputData_2863_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_state_2864_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_knownSize_2865_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_messageHead_2866_);
lean_ctor_set(v_reuseFailAlloc_2886_, 5, v_userDataBytes_2869_);
lean_ctor_set_uint8(v_reuseFailAlloc_2886_, sizeof(void*)*6, v_sentMessage_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2886_, sizeof(void*)*6 + 2, v_omitBody_2868_);
v___x_2875_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2877_; 
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*6 + 1, v___x_2873_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2875_);
v___x_2877_ = v___x_2860_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_reader_2851_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_config_2852_);
lean_ctor_set(v_reuseFailAlloc_2885_, 3, v_events_2853_);
lean_ctor_set(v_reuseFailAlloc_2885_, 4, v_error_2854_);
lean_ctor_set(v_reuseFailAlloc_2885_, 5, v_instant_2855_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*6, v_keepAlive_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*6 + 1, v_forcedFlush_2857_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*6 + 2, v_pullBodyStalled_2858_);
v___x_2877_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v_requestStream_2839_);
lean_ctor_set(v___x_2879_, 2, v_keepAliveTimeout_2840_);
lean_ctor_set(v___x_2879_, 3, v_currentTimeout_2841_);
lean_ctor_set(v___x_2879_, 4, v_headerTimeout_2842_);
lean_ctor_set(v___x_2879_, 5, v_response_2843_);
lean_ctor_set(v___x_2879_, 6, v___x_2878_);
lean_ctor_set(v___x_2879_, 7, v_expectData_2845_);
lean_ctor_set(v___x_2879_, 8, v_pendingHead_2847_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*9, v_requiresData_2844_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*9 + 1, v_handlerDispatched_2846_);
v___x_2880_ = 0;
v___x_2881_ = lean_box(v___x_2880_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2879_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2889_, lean_object* v_requestStream_2890_, lean_object* v_keepAliveTimeout_2891_, lean_object* v_currentTimeout_2892_, lean_object* v_headerTimeout_2893_, lean_object* v_response_2894_, lean_object* v_requiresData_2895_, lean_object* v_expectData_2896_, lean_object* v_handlerDispatched_2897_, lean_object* v_pendingHead_2898_, lean_object* v_____r_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v_requiresData_boxed_2901_; uint8_t v_handlerDispatched_boxed_2902_; lean_object* v_res_2903_; 
v_requiresData_boxed_2901_ = lean_unbox(v_requiresData_2895_);
v_handlerDispatched_boxed_2902_ = lean_unbox(v_handlerDispatched_2897_);
v_res_2903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2889_, v_requestStream_2890_, v_keepAliveTimeout_2891_, v_currentTimeout_2892_, v_headerTimeout_2893_, v_response_2894_, v_requiresData_boxed_2901_, v_expectData_2896_, v_handlerDispatched_boxed_2902_, v_pendingHead_2898_, v_____r_2899_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2904_, lean_object* v_x_2905_){
_start:
{
if (lean_obj_tag(v_x_2905_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v___f_2904_);
v_a_2907_ = lean_ctor_get(v_x_2905_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_x_2905_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2909_ = v_x_2905_;
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v_x_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2917_; 
v_a_2916_ = lean_ctor_get(v_x_2905_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v_x_2905_, 1);
v___x_2917_ = lean_apply_2(v___f_2904_, v_a_2916_, lean_box(0));
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2918_, lean_object* v_x_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2918_, v_x_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2922_, lean_object* v_val_2923_, lean_object* v___f_2924_, lean_object* v___f_2925_, lean_object* v_x_2926_){
_start:
{
if (lean_obj_tag(v_x_2926_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v___f_2925_);
lean_dec_ref(v___f_2924_);
lean_dec(v_val_2923_);
lean_dec_ref(v_close_2922_);
v_a_2928_ = lean_ctor_get(v_x_2926_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_x_2926_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2930_ = v_x_2926_;
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v_x_2926_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
}
else
{
lean_object* v_a_2937_; uint8_t v___x_2938_; 
v_a_2937_ = lean_ctor_get(v_x_2926_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v_x_2926_, 1);
v___x_2938_ = lean_unbox(v_a_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v___f_2925_);
v___x_2939_ = lean_apply_2(v_close_2922_, v_val_2923_, lean_box(0));
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_unbox(v_a_2937_);
lean_dec(v_a_2937_);
v___x_2942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2940_, v___x_2941_, v___x_2939_, v___f_2924_);
return v___x_2942_;
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v_a_2937_);
lean_dec_ref(v___f_2924_);
lean_dec(v_val_2923_);
lean_dec_ref(v_close_2922_);
v___x_2943_ = lean_box(0);
v___x_2944_ = lean_apply_2(v___f_2925_, v___x_2943_, lean_box(0));
return v___x_2944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2945_, lean_object* v_val_2946_, lean_object* v___f_2947_, lean_object* v___f_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2945_, v_val_2946_, v___f_2947_, v___f_2948_, v_x_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_2952_, lean_object* v_handler_2953_, lean_object* v_x_2954_){
_start:
{
if (lean_obj_tag(v_x_2954_) == 0)
{
lean_object* v_a_2956_; lean_object* v_onFailure_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v_x_2954_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v_x_2954_, 1);
v_onFailure_2957_ = lean_ctor_get(v_inst_2952_, 2);
lean_inc_ref(v_onFailure_2957_);
lean_dec_ref(v_inst_2952_);
v___x_2958_ = lean_apply_3(v_onFailure_2957_, v_handler_2953_, v_a_2956_, lean_box(0));
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; 
lean_dec(v_handler_2953_);
lean_dec_ref(v_inst_2952_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v_x_2954_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_2960_, lean_object* v_handler_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_2960_, v_handler_2961_, v_x_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_2965_, lean_object* v_____r_2966_){
_start:
{
uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2968_ = 0;
v___x_2969_ = lean_box(v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_st_2965_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_2973_, lean_object* v_____r_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_2973_, v_____r_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2977_, lean_object* v___f_2978_, lean_object* v___f_2979_, lean_object* v_x_2980_){
_start:
{
if (lean_obj_tag(v_x_2980_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v___f_2979_);
lean_dec_ref(v___f_2978_);
lean_dec_ref(v_requestStream_2977_);
v_a_2982_ = lean_ctor_get(v_x_2980_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_x_2980_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2984_ = v_x_2980_;
v_isShared_2985_ = v_isSharedCheck_2990_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v_x_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2990_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
}
}
else
{
lean_object* v_a_2991_; uint8_t v___x_2992_; 
v_a_2991_ = lean_ctor_get(v_x_2980_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v_x_2980_, 1);
v___x_2992_ = lean_unbox(v_a_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; 
lean_dec_ref(v___f_2979_);
v___x_2993_ = l_Std_Http_Body_Stream_close(v_requestStream_2977_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_unbox(v_a_2991_);
lean_dec(v_a_2991_);
v___x_2996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2994_, v___x_2995_, v___x_2993_, v___f_2978_);
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_a_2991_);
lean_dec_ref(v___f_2978_);
lean_dec_ref(v_requestStream_2977_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_apply_2(v___f_2979_, v___x_2997_, lean_box(0));
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2999_, lean_object* v___f_3000_, lean_object* v___f_3001_, lean_object* v_x_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2999_, v___f_3000_, v___f_3001_, v_x_3002_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(uint8_t v_final_3005_, lean_object* v___f_3006_, lean_object* v___f_3007_, lean_object* v_requestStream_3008_, lean_object* v___f_3009_, lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3010_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v___f_3009_);
lean_dec_ref(v_requestStream_3008_);
lean_dec_ref(v___f_3007_);
lean_dec_ref(v___f_3006_);
v_a_3012_ = lean_ctor_get(v_x_3010_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_x_3010_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3014_ = v_x_3010_;
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v_x_3010_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
return v___x_3018_;
}
}
}
else
{
lean_dec_ref_known(v_x_3010_, 1);
if (v_final_3005_ == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref(v___f_3009_);
lean_dec_ref(v_requestStream_3008_);
lean_dec_ref(v___f_3007_);
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_apply_2(v___f_3006_, v___x_3021_, lean_box(0));
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; lean_object* v___f_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_7002__overap_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; 
lean_dec_ref(v___f_3006_);
v___x_3023_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3024_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3025_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3026_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3027_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3027_, 0, lean_box(0));
lean_closure_set(v___x_3027_, 1, lean_box(0));
lean_closure_set(v___x_3027_, 2, v___x_3023_);
lean_closure_set(v___x_3027_, 3, lean_box(0));
lean_closure_set(v___x_3027_, 4, lean_box(0));
lean_closure_set(v___x_3027_, 5, v___x_3026_);
lean_closure_set(v___x_3027_, 6, v___f_3007_);
v___x_7002__overap_3028_ = l_Std_Mutex_atomically___redArg(v___x_3023_, v___f_3024_, v___f_3025_, v_requestStream_3008_, v___x_3027_);
v___x_3029_ = lean_apply_1(v___x_7002__overap_3028_, lean_box(0));
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = 0;
v___x_3032_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3030_, v___x_3031_, v___x_3029_, v___f_3009_);
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_final_3033_, lean_object* v___f_3034_, lean_object* v___f_3035_, lean_object* v_requestStream_3036_, lean_object* v___f_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_){
_start:
{
uint8_t v_final_boxed_3040_; lean_object* v_res_3041_; 
v_final_boxed_3040_ = lean_unbox(v_final_3033_);
v_res_3041_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_final_boxed_3040_, v___f_3034_, v___f_3035_, v_requestStream_3036_, v___f_3037_, v_x_3038_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3042_, lean_object* v_x_3043_){
_start:
{
if (lean_obj_tag(v_x_3043_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref(v_state_3042_);
v_a_3045_ = lean_ctor_get(v_x_3043_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_x_3043_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3047_ = v_x_3043_;
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v_x_3043_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
return v___x_3051_;
}
}
}
else
{
lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3083_; 
v_isSharedCheck_3083_ = !lean_is_exclusive(v_x_3043_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v_x_3043_, 0);
lean_dec(v_unused_3084_);
v___x_3055_ = v_x_3043_;
v_isShared_3056_ = v_isSharedCheck_3083_;
goto v_resetjp_3054_;
}
else
{
lean_dec(v_x_3043_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3083_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_machine_3057_; lean_object* v_requestStream_3058_; lean_object* v_keepAliveTimeout_3059_; lean_object* v_currentTimeout_3060_; lean_object* v_headerTimeout_3061_; lean_object* v_response_3062_; lean_object* v_respStream_3063_; uint8_t v_requiresData_3064_; lean_object* v_expectData_3065_; lean_object* v_pendingHead_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3082_; 
v_machine_3057_ = lean_ctor_get(v_state_3042_, 0);
v_requestStream_3058_ = lean_ctor_get(v_state_3042_, 1);
v_keepAliveTimeout_3059_ = lean_ctor_get(v_state_3042_, 2);
v_currentTimeout_3060_ = lean_ctor_get(v_state_3042_, 3);
v_headerTimeout_3061_ = lean_ctor_get(v_state_3042_, 4);
v_response_3062_ = lean_ctor_get(v_state_3042_, 5);
v_respStream_3063_ = lean_ctor_get(v_state_3042_, 6);
v_requiresData_3064_ = lean_ctor_get_uint8(v_state_3042_, sizeof(void*)*9);
v_expectData_3065_ = lean_ctor_get(v_state_3042_, 7);
v_pendingHead_3066_ = lean_ctor_get(v_state_3042_, 8);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_state_3042_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3068_ = v_state_3042_;
v_isShared_3069_ = v_isSharedCheck_3082_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_pendingHead_3066_);
lean_inc(v_expectData_3065_);
lean_inc(v_respStream_3063_);
lean_inc(v_response_3062_);
lean_inc(v_headerTimeout_3061_);
lean_inc(v_currentTimeout_3060_);
lean_inc(v_keepAliveTimeout_3059_);
lean_inc(v_requestStream_3058_);
lean_inc(v_machine_3057_);
lean_dec(v_state_3042_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3082_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3074_; 
v___x_3070_ = lean_box(52);
v___x_3071_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3057_, v___x_3070_);
v___x_3072_ = 0;
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3071_);
v___x_3074_ = v___x_3068_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_requestStream_3058_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_keepAliveTimeout_3059_);
lean_ctor_set(v_reuseFailAlloc_3081_, 3, v_currentTimeout_3060_);
lean_ctor_set(v_reuseFailAlloc_3081_, 4, v_headerTimeout_3061_);
lean_ctor_set(v_reuseFailAlloc_3081_, 5, v_response_3062_);
lean_ctor_set(v_reuseFailAlloc_3081_, 6, v_respStream_3063_);
lean_ctor_set(v_reuseFailAlloc_3081_, 7, v_expectData_3065_);
lean_ctor_set(v_reuseFailAlloc_3081_, 8, v_pendingHead_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*9, v_requiresData_3064_);
v___x_3074_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_ctor_set_uint8(v___x_3074_, sizeof(void*)*9 + 1, v___x_3072_);
v___x_3075_ = lean_box(v___x_3072_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3076_);
v___x_3078_ = v___x_3055_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3085_, v_x_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3089_, lean_object* v_requestStream_3090_, lean_object* v_keepAliveTimeout_3091_, lean_object* v_currentTimeout_3092_, lean_object* v_headerTimeout_3093_, lean_object* v_response_3094_, lean_object* v_respStream_3095_, uint8_t v_requiresData_3096_, lean_object* v_expectData_3097_, lean_object* v_pendingHead_3098_, lean_object* v_____r_3099_){
_start:
{
uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3101_ = 0;
v___x_3102_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3102_, 0, v_machine_3089_);
lean_ctor_set(v___x_3102_, 1, v_requestStream_3090_);
lean_ctor_set(v___x_3102_, 2, v_keepAliveTimeout_3091_);
lean_ctor_set(v___x_3102_, 3, v_currentTimeout_3092_);
lean_ctor_set(v___x_3102_, 4, v_headerTimeout_3093_);
lean_ctor_set(v___x_3102_, 5, v_response_3094_);
lean_ctor_set(v___x_3102_, 6, v_respStream_3095_);
lean_ctor_set(v___x_3102_, 7, v_expectData_3097_);
lean_ctor_set(v___x_3102_, 8, v_pendingHead_3098_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*9, v_requiresData_3096_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*9 + 1, v___x_3101_);
v___x_3103_ = lean_box(v___x_3101_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3107_, lean_object* v_requestStream_3108_, lean_object* v_keepAliveTimeout_3109_, lean_object* v_currentTimeout_3110_, lean_object* v_headerTimeout_3111_, lean_object* v_response_3112_, lean_object* v_respStream_3113_, lean_object* v_requiresData_3114_, lean_object* v_expectData_3115_, lean_object* v_pendingHead_3116_, lean_object* v_____r_3117_, lean_object* v___y_3118_){
_start:
{
uint8_t v_requiresData_boxed_3119_; lean_object* v_res_3120_; 
v_requiresData_boxed_3119_ = lean_unbox(v_requiresData_3114_);
v_res_3120_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3107_, v_requestStream_3108_, v_keepAliveTimeout_3109_, v_currentTimeout_3110_, v_headerTimeout_3111_, v_response_3112_, v_respStream_3113_, v_requiresData_boxed_3119_, v_expectData_3115_, v_pendingHead_3116_, v_____r_3117_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3121_, lean_object* v_body_3122_, lean_object* v___f_3123_, lean_object* v___f_3124_, lean_object* v_x_3125_){
_start:
{
if (lean_obj_tag(v_x_3125_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v___f_3124_);
lean_dec_ref(v___f_3123_);
lean_dec(v_body_3122_);
lean_dec_ref(v_close_3121_);
v_a_3127_ = lean_ctor_get(v_x_3125_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_x_3125_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3129_ = v_x_3125_;
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v_x_3125_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
}
}
else
{
lean_object* v_a_3136_; uint8_t v___x_3137_; 
v_a_3136_ = lean_ctor_get(v_x_3125_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v_x_3125_, 1);
v___x_3137_ = lean_unbox(v_a_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; 
lean_dec_ref(v___f_3124_);
v___x_3138_ = lean_apply_2(v_close_3121_, v_body_3122_, lean_box(0));
v___x_3139_ = lean_unsigned_to_nat(0u);
v___x_3140_ = lean_unbox(v_a_3136_);
lean_dec(v_a_3136_);
v___x_3141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3139_, v___x_3140_, v___x_3138_, v___f_3123_);
return v___x_3141_;
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec(v_a_3136_);
lean_dec_ref(v___f_3123_);
lean_dec(v_body_3122_);
lean_dec_ref(v_close_3121_);
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_apply_2(v___f_3124_, v___x_3142_, lean_box(0));
return v___x_3143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3144_, lean_object* v_body_3145_, lean_object* v___f_3146_, lean_object* v___f_3147_, lean_object* v_x_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3144_, v_body_3145_, v___f_3146_, v___f_3147_, v_x_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3151_, lean_object* v_keepAliveTimeout_3152_, lean_object* v_currentTimeout_3153_, lean_object* v_headerTimeout_3154_, lean_object* v_response_3155_, uint8_t v_requiresData_3156_, lean_object* v_expectData_3157_, uint8_t v___x_3158_, lean_object* v_pendingHead_3159_, lean_object* v_____x_3160_){
_start:
{
lean_object* v_fst_3162_; lean_object* v_snd_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3174_; 
v_fst_3162_ = lean_ctor_get(v_____x_3160_, 0);
v_snd_3163_ = lean_ctor_get(v_____x_3160_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_____x_3160_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3165_ = v_____x_3160_;
v_isShared_3166_ = v_isSharedCheck_3174_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_snd_3163_);
lean_inc(v_fst_3162_);
lean_dec(v_____x_3160_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3174_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3167_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3167_, 0, v_fst_3162_);
lean_ctor_set(v___x_3167_, 1, v_requestStream_3151_);
lean_ctor_set(v___x_3167_, 2, v_keepAliveTimeout_3152_);
lean_ctor_set(v___x_3167_, 3, v_currentTimeout_3153_);
lean_ctor_set(v___x_3167_, 4, v_headerTimeout_3154_);
lean_ctor_set(v___x_3167_, 5, v_response_3155_);
lean_ctor_set(v___x_3167_, 6, v_snd_3163_);
lean_ctor_set(v___x_3167_, 7, v_expectData_3157_);
lean_ctor_set(v___x_3167_, 8, v_pendingHead_3159_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*9, v_requiresData_3156_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*9 + 1, v___x_3158_);
v___x_3168_ = lean_box(v___x_3158_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 1, v___x_3168_);
lean_ctor_set(v___x_3165_, 0, v___x_3167_);
v___x_3170_ = v___x_3165_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3175_, lean_object* v_keepAliveTimeout_3176_, lean_object* v_currentTimeout_3177_, lean_object* v_headerTimeout_3178_, lean_object* v_response_3179_, lean_object* v_requiresData_3180_, lean_object* v_expectData_3181_, lean_object* v___x_3182_, lean_object* v_pendingHead_3183_, lean_object* v_____x_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_requiresData_boxed_3186_; uint8_t v___x_7758__boxed_3187_; lean_object* v_res_3188_; 
v_requiresData_boxed_3186_ = lean_unbox(v_requiresData_3180_);
v___x_7758__boxed_3187_ = lean_unbox(v___x_3182_);
v_res_3188_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3175_, v_keepAliveTimeout_3176_, v_currentTimeout_3177_, v_headerTimeout_3178_, v_response_3179_, v_requiresData_boxed_3186_, v_expectData_3181_, v___x_7758__boxed_3187_, v_pendingHead_3183_, v_____x_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v___f_3189_);
v_a_3192_ = lean_ctor_get(v_x_3190_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_x_3190_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3194_ = v_x_3190_;
v_isShared_3195_ = v_isSharedCheck_3200_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v_x_3190_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3200_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
return v___x_3198_;
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3202_; 
v_a_3201_ = lean_ctor_get(v_x_3190_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v_x_3190_, 1);
v___x_3202_ = lean_apply_2(v___f_3189_, v_a_3201_, lean_box(0));
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3203_, lean_object* v_x_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3203_, v_x_3204_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3207_, lean_object* v___f_3208_, lean_object* v_inst_3209_, lean_object* v___f_3210_, lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3211_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___f_3210_);
lean_dec_ref(v_inst_3209_);
lean_dec_ref(v___f_3208_);
v_a_3213_ = lean_ctor_get(v_x_3211_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_x_3211_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3215_ = v_x_3211_;
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v_x_3211_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v_snd_3223_; 
v_a_3222_ = lean_ctor_get(v_x_3211_, 0);
v_snd_3223_ = lean_ctor_get(v_a_3222_, 1);
if (lean_obj_tag(v_snd_3223_) == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec_ref(v___f_3210_);
lean_dec_ref(v_inst_3209_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_x_3211_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3225_, v___x_3207_, v___x_3224_, v___f_3208_);
return v___x_3226_;
}
else
{
lean_object* v_fst_3227_; lean_object* v_val_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_inc_ref(v_snd_3223_);
lean_inc(v_a_3222_);
lean_dec_ref_known(v_x_3211_, 1);
lean_dec_ref(v___f_3208_);
v_fst_3227_ = lean_ctor_get(v_a_3222_, 0);
lean_inc(v_fst_3227_);
lean_dec(v_a_3222_);
v_val_3228_ = lean_ctor_get(v_snd_3223_, 0);
lean_inc(v_val_3228_);
lean_dec_ref_known(v_snd_3223_, 1);
v___x_3229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3209_, v_fst_3227_, v_val_3228_);
v___x_3230_ = lean_unsigned_to_nat(0u);
v___x_3231_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3230_, v___x_3207_, v___x_3229_, v___f_3210_);
return v___x_3231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3232_, lean_object* v___f_3233_, lean_object* v_inst_3234_, lean_object* v___f_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v___x_7824__boxed_3238_; lean_object* v_res_3239_; 
v___x_7824__boxed_3238_ = lean_unbox(v___x_3232_);
v_res_3239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7824__boxed_3238_, v___f_3233_, v_inst_3234_, v___f_3235_, v_x_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_state_3240_, lean_object* v_x_3241_){
_start:
{
if (lean_obj_tag(v_x_3241_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v_state_3240_);
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
lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3281_; 
v_isSharedCheck_3281_ = !lean_is_exclusive(v_x_3241_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_x_3241_, 0);
lean_dec(v_unused_3282_);
v___x_3253_ = v_x_3241_;
v_isShared_3254_ = v_isSharedCheck_3281_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v_x_3241_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3281_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_machine_3255_; lean_object* v_requestStream_3256_; lean_object* v_keepAliveTimeout_3257_; lean_object* v_currentTimeout_3258_; lean_object* v_headerTimeout_3259_; lean_object* v_response_3260_; lean_object* v_respStream_3261_; uint8_t v_requiresData_3262_; lean_object* v_expectData_3263_; lean_object* v_pendingHead_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3280_; 
v_machine_3255_ = lean_ctor_get(v_state_3240_, 0);
v_requestStream_3256_ = lean_ctor_get(v_state_3240_, 1);
v_keepAliveTimeout_3257_ = lean_ctor_get(v_state_3240_, 2);
v_currentTimeout_3258_ = lean_ctor_get(v_state_3240_, 3);
v_headerTimeout_3259_ = lean_ctor_get(v_state_3240_, 4);
v_response_3260_ = lean_ctor_get(v_state_3240_, 5);
v_respStream_3261_ = lean_ctor_get(v_state_3240_, 6);
v_requiresData_3262_ = lean_ctor_get_uint8(v_state_3240_, sizeof(void*)*9);
v_expectData_3263_ = lean_ctor_get(v_state_3240_, 7);
v_pendingHead_3264_ = lean_ctor_get(v_state_3240_, 8);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_state_3240_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3266_ = v_state_3240_;
v_isShared_3267_ = v_isSharedCheck_3280_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_pendingHead_3264_);
lean_inc(v_expectData_3263_);
lean_inc(v_respStream_3261_);
lean_inc(v_response_3260_);
lean_inc(v_headerTimeout_3259_);
lean_inc(v_currentTimeout_3258_);
lean_inc(v_keepAliveTimeout_3257_);
lean_inc(v_requestStream_3256_);
lean_inc(v_machine_3255_);
lean_dec(v_state_3240_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3280_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; lean_object* v___x_3272_; 
v___x_3268_ = lean_box(31);
v___x_3269_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3255_, v___x_3268_);
v___x_3270_ = 0;
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3269_);
v___x_3272_ = v___x_3266_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_requestStream_3256_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_keepAliveTimeout_3257_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_currentTimeout_3258_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v_headerTimeout_3259_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v_response_3260_);
lean_ctor_set(v_reuseFailAlloc_3279_, 6, v_respStream_3261_);
lean_ctor_set(v_reuseFailAlloc_3279_, 7, v_expectData_3263_);
lean_ctor_set(v_reuseFailAlloc_3279_, 8, v_pendingHead_3264_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*9, v_requiresData_3262_);
v___x_3272_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*9 + 1, v___x_3270_);
v___x_3273_ = lean_box(v___x_3270_);
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3274_);
v___x_3276_ = v___x_3253_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_state_3283_, lean_object* v_x_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_state_3283_, v_x_3284_);
return v_res_3286_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3289_ = lean_mk_io_user_error(v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3290_, lean_object* v_inst_3291_, lean_object* v_handler_3292_, lean_object* v_config_3293_, lean_object* v_event_3294_, lean_object* v_state_3295_){
_start:
{
switch(lean_obj_tag(v_event_3294_))
{
case 0:
{
lean_object* v_x_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_handler_3292_);
lean_dec_ref(v_inst_3291_);
lean_dec_ref(v_inst_3290_);
v_x_3297_ = lean_ctor_get(v_event_3294_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_event_3294_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3299_ = v_event_3294_;
v_isShared_3300_ = v_isSharedCheck_3404_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_x_3297_);
lean_dec(v_event_3294_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3404_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
if (lean_obj_tag(v_x_3297_) == 0)
{
lean_object* v_machine_3301_; lean_object* v_reader_3302_; lean_object* v_requestStream_3303_; lean_object* v_keepAliveTimeout_3304_; lean_object* v_currentTimeout_3305_; lean_object* v_headerTimeout_3306_; lean_object* v_response_3307_; lean_object* v_respStream_3308_; uint8_t v_requiresData_3309_; lean_object* v_expectData_3310_; uint8_t v_handlerDispatched_3311_; lean_object* v_pendingHead_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v_config_3293_);
v_machine_3301_ = lean_ctor_get(v_state_3295_, 0);
lean_inc_ref(v_machine_3301_);
v_reader_3302_ = lean_ctor_get(v_machine_3301_, 0);
lean_inc_ref(v_reader_3302_);
v_requestStream_3303_ = lean_ctor_get(v_state_3295_, 1);
v_keepAliveTimeout_3304_ = lean_ctor_get(v_state_3295_, 2);
v_currentTimeout_3305_ = lean_ctor_get(v_state_3295_, 3);
v_headerTimeout_3306_ = lean_ctor_get(v_state_3295_, 4);
v_response_3307_ = lean_ctor_get(v_state_3295_, 5);
v_respStream_3308_ = lean_ctor_get(v_state_3295_, 6);
v_requiresData_3309_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3310_ = lean_ctor_get(v_state_3295_, 7);
v_handlerDispatched_3311_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9 + 1);
v_pendingHead_3312_ = lean_ctor_get(v_state_3295_, 8);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_state_3295_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; 
v_unused_3356_ = lean_ctor_get(v_state_3295_, 0);
lean_dec(v_unused_3356_);
v___x_3314_ = v_state_3295_;
v_isShared_3315_ = v_isSharedCheck_3355_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_pendingHead_3312_);
lean_inc(v_expectData_3310_);
lean_inc(v_respStream_3308_);
lean_inc(v_response_3307_);
lean_inc(v_headerTimeout_3306_);
lean_inc(v_currentTimeout_3305_);
lean_inc(v_keepAliveTimeout_3304_);
lean_inc(v_requestStream_3303_);
lean_dec(v_state_3295_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3355_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_writer_3316_; lean_object* v_config_3317_; lean_object* v_events_3318_; lean_object* v_error_3319_; lean_object* v_instant_3320_; uint8_t v_keepAlive_3321_; uint8_t v_forcedFlush_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3353_; 
v_writer_3316_ = lean_ctor_get(v_machine_3301_, 1);
v_config_3317_ = lean_ctor_get(v_machine_3301_, 2);
v_events_3318_ = lean_ctor_get(v_machine_3301_, 3);
v_error_3319_ = lean_ctor_get(v_machine_3301_, 4);
v_instant_3320_ = lean_ctor_get(v_machine_3301_, 5);
v_keepAlive_3321_ = lean_ctor_get_uint8(v_machine_3301_, sizeof(void*)*6);
v_forcedFlush_3322_ = lean_ctor_get_uint8(v_machine_3301_, sizeof(void*)*6 + 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_machine_3301_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; 
v_unused_3354_ = lean_ctor_get(v_machine_3301_, 0);
lean_dec(v_unused_3354_);
v___x_3324_ = v_machine_3301_;
v_isShared_3325_ = v_isSharedCheck_3353_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_instant_3320_);
lean_inc(v_error_3319_);
lean_inc(v_events_3318_);
lean_inc(v_config_3317_);
lean_inc(v_writer_3316_);
lean_dec(v_machine_3301_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3353_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_state_3326_; lean_object* v_input_3327_; lean_object* v_messageHead_3328_; lean_object* v_messageCount_3329_; lean_object* v_bodyBytesRead_3330_; lean_object* v_headerBytesRead_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3352_; 
v_state_3326_ = lean_ctor_get(v_reader_3302_, 0);
v_input_3327_ = lean_ctor_get(v_reader_3302_, 1);
v_messageHead_3328_ = lean_ctor_get(v_reader_3302_, 2);
v_messageCount_3329_ = lean_ctor_get(v_reader_3302_, 3);
v_bodyBytesRead_3330_ = lean_ctor_get(v_reader_3302_, 4);
v_headerBytesRead_3331_ = lean_ctor_get(v_reader_3302_, 5);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_reader_3302_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3333_ = v_reader_3302_;
v_isShared_3334_ = v_isSharedCheck_3352_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_headerBytesRead_3331_);
lean_inc(v_bodyBytesRead_3330_);
lean_inc(v_messageCount_3329_);
lean_inc(v_messageHead_3328_);
lean_inc(v_input_3327_);
lean_inc(v_state_3326_);
lean_dec(v_reader_3302_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3352_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
uint8_t v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = 1;
if (v_isShared_3334_ == 0)
{
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_state_3326_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_input_3327_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_messageHead_3328_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_messageCount_3329_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_bodyBytesRead_3330_);
lean_ctor_set(v_reuseFailAlloc_3351_, 5, v_headerBytesRead_3331_);
v___x_3337_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
uint8_t v___x_3338_; lean_object* v___x_3340_; 
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*6, v___x_3335_);
v___x_3338_ = 0;
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3337_);
v___x_3340_ = v___x_3324_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_writer_3316_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_config_3317_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_events_3318_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_error_3319_);
lean_ctor_set(v_reuseFailAlloc_3350_, 5, v_instant_3320_);
lean_ctor_set_uint8(v_reuseFailAlloc_3350_, sizeof(void*)*6, v_keepAlive_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3350_, sizeof(void*)*6 + 1, v_forcedFlush_3322_);
v___x_3340_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3342_; 
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*6 + 2, v___x_3338_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3340_);
v___x_3342_ = v___x_3314_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_requestStream_3303_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_keepAliveTimeout_3304_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_currentTimeout_3305_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_headerTimeout_3306_);
lean_ctor_set(v_reuseFailAlloc_3349_, 5, v_response_3307_);
lean_ctor_set(v_reuseFailAlloc_3349_, 6, v_respStream_3308_);
lean_ctor_set(v_reuseFailAlloc_3349_, 7, v_expectData_3310_);
lean_ctor_set(v_reuseFailAlloc_3349_, 8, v_pendingHead_3312_);
lean_ctor_set_uint8(v_reuseFailAlloc_3349_, sizeof(void*)*9, v_requiresData_3309_);
lean_ctor_set_uint8(v_reuseFailAlloc_3349_, sizeof(void*)*9 + 1, v_handlerDispatched_3311_);
v___x_3342_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3343_ = lean_box(v___x_3338_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set_tag(v___x_3299_, 1);
lean_ctor_set(v___x_3299_, 0, v___x_3344_);
v___x_3346_ = v___x_3299_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
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
lean_object* v_val_3357_; lean_object* v_machine_3358_; lean_object* v_requestStream_3359_; lean_object* v_keepAliveTimeout_3360_; lean_object* v_currentTimeout_3361_; lean_object* v_response_3362_; lean_object* v_respStream_3363_; uint8_t v_requiresData_3364_; lean_object* v_expectData_3365_; uint8_t v_handlerDispatched_3366_; lean_object* v_pendingHead_3367_; lean_object* v___f_3368_; 
lean_del_object(v___x_3299_);
v_val_3357_ = lean_ctor_get(v_x_3297_, 0);
lean_inc_n(v_val_3357_, 2);
lean_dec_ref_known(v_x_3297_, 1);
v_machine_3358_ = lean_ctor_get(v_state_3295_, 0);
v_requestStream_3359_ = lean_ctor_get(v_state_3295_, 1);
v_keepAliveTimeout_3360_ = lean_ctor_get(v_state_3295_, 2);
lean_inc(v_keepAliveTimeout_3360_);
v_currentTimeout_3361_ = lean_ctor_get(v_state_3295_, 3);
v_response_3362_ = lean_ctor_get(v_state_3295_, 5);
v_respStream_3363_ = lean_ctor_get(v_state_3295_, 6);
v_requiresData_3364_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3365_ = lean_ctor_get(v_state_3295_, 7);
v_handlerDispatched_3366_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9 + 1);
v_pendingHead_3367_ = lean_ctor_get(v_state_3295_, 8);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3368_, 0, v_val_3357_);
if (lean_obj_tag(v_keepAliveTimeout_3360_) == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec_ref(v___f_3368_);
lean_dec_ref(v_config_3293_);
v___x_3369_ = lean_box(0);
v___x_3370_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3357_, v___x_3369_, v_state_3295_);
return v___x_3370_;
}
else
{
lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3402_; 
lean_inc(v_pendingHead_3367_);
lean_inc(v_expectData_3365_);
lean_inc(v_respStream_3363_);
lean_inc_ref(v_response_3362_);
lean_inc(v_currentTimeout_3361_);
lean_inc_ref(v_requestStream_3359_);
lean_inc_ref(v_machine_3358_);
lean_dec(v_val_3357_);
lean_dec_ref(v_state_3295_);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_keepAliveTimeout_3360_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_keepAliveTimeout_3360_, 0);
lean_dec(v_unused_3403_);
v___x_3372_ = v_keepAliveTimeout_3360_;
v_isShared_3373_ = v_isSharedCheck_3402_;
goto v_resetjp_3371_;
}
else
{
lean_dec(v_keepAliveTimeout_3360_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3402_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; lean_object* v_val_3378_; lean_object* v___x_3385_; 
v___x_3374_ = lean_box(v_requiresData_3364_);
v___x_3375_ = lean_box(v_handlerDispatched_3366_);
v___f_3376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3376_, 0, v_config_3293_);
lean_closure_set(v___f_3376_, 1, v_machine_3358_);
lean_closure_set(v___f_3376_, 2, v_requestStream_3359_);
lean_closure_set(v___f_3376_, 3, v_currentTimeout_3361_);
lean_closure_set(v___f_3376_, 4, v_response_3362_);
lean_closure_set(v___f_3376_, 5, v_respStream_3363_);
lean_closure_set(v___f_3376_, 6, v___x_3374_);
lean_closure_set(v___f_3376_, 7, v_expectData_3365_);
lean_closure_set(v___f_3376_, 8, v___x_3375_);
lean_closure_set(v___f_3376_, 9, v_pendingHead_3367_);
lean_closure_set(v___f_3376_, 10, v___f_3368_);
v___x_3385_ = lean_get_current_time();
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 1);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v_val_3378_ = v___x_3391_;
goto v___jp_3377_;
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
v_a_3394_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3385_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3385_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 0);
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
v_val_3378_ = v___x_3399_;
goto v___jp_3377_;
}
}
}
v___jp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set_tag(v___x_3372_, 0);
lean_ctor_set(v___x_3372_, 0, v_val_3378_);
v___x_3380_ = v___x_3372_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_val_3378_);
v___x_3380_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = 0;
v___x_3383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3381_, v___x_3382_, v___x_3380_, v___f_3376_);
return v___x_3383_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_config_3293_);
lean_dec(v_handler_3292_);
lean_dec_ref(v_inst_3290_);
v_x_3405_ = lean_ctor_get(v_event_3294_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_event_3294_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3407_ = v_event_3294_;
v_isShared_3408_ = v_isSharedCheck_3520_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_x_3405_);
lean_dec(v_event_3294_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3520_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
lean_object* v_machine_3409_; lean_object* v_requestStream_3410_; lean_object* v_keepAliveTimeout_3411_; lean_object* v_currentTimeout_3412_; lean_object* v_headerTimeout_3413_; lean_object* v_response_3414_; lean_object* v_respStream_3415_; uint8_t v_requiresData_3416_; lean_object* v_expectData_3417_; uint8_t v_handlerDispatched_3418_; lean_object* v_pendingHead_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___f_3422_; 
lean_del_object(v___x_3407_);
v_machine_3409_ = lean_ctor_get(v_state_3295_, 0);
lean_inc_ref_n(v_machine_3409_, 2);
v_requestStream_3410_ = lean_ctor_get(v_state_3295_, 1);
lean_inc_ref_n(v_requestStream_3410_, 2);
v_keepAliveTimeout_3411_ = lean_ctor_get(v_state_3295_, 2);
lean_inc_n(v_keepAliveTimeout_3411_, 2);
v_currentTimeout_3412_ = lean_ctor_get(v_state_3295_, 3);
lean_inc_n(v_currentTimeout_3412_, 2);
v_headerTimeout_3413_ = lean_ctor_get(v_state_3295_, 4);
lean_inc_n(v_headerTimeout_3413_, 2);
v_response_3414_ = lean_ctor_get(v_state_3295_, 5);
lean_inc_ref_n(v_response_3414_, 2);
v_respStream_3415_ = lean_ctor_get(v_state_3295_, 6);
lean_inc(v_respStream_3415_);
v_requiresData_3416_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3417_ = lean_ctor_get(v_state_3295_, 7);
lean_inc_n(v_expectData_3417_, 2);
v_handlerDispatched_3418_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9 + 1);
v_pendingHead_3419_ = lean_ctor_get(v_state_3295_, 8);
lean_inc_n(v_pendingHead_3419_, 2);
lean_dec_ref(v_state_3295_);
v___x_3420_ = lean_box(v_requiresData_3416_);
v___x_3421_ = lean_box(v_handlerDispatched_3418_);
v___f_3422_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3422_, 0, v_machine_3409_);
lean_closure_set(v___f_3422_, 1, v_requestStream_3410_);
lean_closure_set(v___f_3422_, 2, v_keepAliveTimeout_3411_);
lean_closure_set(v___f_3422_, 3, v_currentTimeout_3412_);
lean_closure_set(v___f_3422_, 4, v_headerTimeout_3413_);
lean_closure_set(v___f_3422_, 5, v_response_3414_);
lean_closure_set(v___f_3422_, 6, v___x_3420_);
lean_closure_set(v___f_3422_, 7, v_expectData_3417_);
lean_closure_set(v___f_3422_, 8, v___x_3421_);
lean_closure_set(v___f_3422_, 9, v_pendingHead_3419_);
if (lean_obj_tag(v_respStream_3415_) == 1)
{
lean_object* v_val_3423_; lean_object* v_close_3424_; lean_object* v_isClosed_3425_; lean_object* v___x_3426_; lean_object* v___f_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v_pendingHead_3419_);
lean_dec(v_expectData_3417_);
lean_dec_ref(v_response_3414_);
lean_dec(v_headerTimeout_3413_);
lean_dec(v_currentTimeout_3412_);
lean_dec(v_keepAliveTimeout_3411_);
lean_dec_ref(v_requestStream_3410_);
lean_dec_ref(v_machine_3409_);
v_val_3423_ = lean_ctor_get(v_respStream_3415_, 0);
lean_inc_n(v_val_3423_, 2);
lean_dec_ref_known(v_respStream_3415_, 1);
v_close_3424_ = lean_ctor_get(v_inst_3291_, 1);
lean_inc_ref(v_close_3424_);
v_isClosed_3425_ = lean_ctor_get(v_inst_3291_, 2);
lean_inc_ref(v_isClosed_3425_);
lean_dec_ref(v_inst_3291_);
v___x_3426_ = lean_apply_2(v_isClosed_3425_, v_val_3423_, lean_box(0));
lean_inc_ref(v___f_3422_);
v___f_3427_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3427_, 0, v___f_3422_);
v___f_3428_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3428_, 0, v_close_3424_);
lean_closure_set(v___f_3428_, 1, v_val_3423_);
lean_closure_set(v___f_3428_, 2, v___f_3427_);
lean_closure_set(v___f_3428_, 3, v___f_3422_);
v___x_3429_ = lean_unsigned_to_nat(0u);
v___x_3430_ = 0;
v___x_3431_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3429_, v___x_3430_, v___x_3426_, v___f_3428_);
return v___x_3431_;
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v___f_3422_);
lean_dec(v_respStream_3415_);
lean_dec_ref(v_inst_3291_);
v___x_3432_ = lean_box(0);
v___x_3433_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3409_, v_requestStream_3410_, v_keepAliveTimeout_3411_, v_currentTimeout_3412_, v_headerTimeout_3413_, v_response_3414_, v_requiresData_3416_, v_expectData_3417_, v_handlerDispatched_3418_, v_pendingHead_3419_, v___x_3432_);
return v___x_3433_;
}
}
else
{
lean_object* v_val_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_inst_3291_);
v_val_3434_ = lean_ctor_get(v_x_3405_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_x_3405_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3436_ = v_x_3405_;
v_isShared_3437_ = v_isSharedCheck_3519_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_val_3434_);
lean_dec(v_x_3405_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3519_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_machine_3438_; lean_object* v_requestStream_3439_; lean_object* v_keepAliveTimeout_3440_; lean_object* v_currentTimeout_3441_; lean_object* v_headerTimeout_3442_; lean_object* v_response_3443_; lean_object* v_respStream_3444_; uint8_t v_requiresData_3445_; lean_object* v_expectData_3446_; uint8_t v_handlerDispatched_3447_; lean_object* v_pendingHead_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3518_; 
v_machine_3438_ = lean_ctor_get(v_state_3295_, 0);
v_requestStream_3439_ = lean_ctor_get(v_state_3295_, 1);
v_keepAliveTimeout_3440_ = lean_ctor_get(v_state_3295_, 2);
v_currentTimeout_3441_ = lean_ctor_get(v_state_3295_, 3);
v_headerTimeout_3442_ = lean_ctor_get(v_state_3295_, 4);
v_response_3443_ = lean_ctor_get(v_state_3295_, 5);
v_respStream_3444_ = lean_ctor_get(v_state_3295_, 6);
v_requiresData_3445_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3446_ = lean_ctor_get(v_state_3295_, 7);
v_handlerDispatched_3447_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9 + 1);
v_pendingHead_3448_ = lean_ctor_get(v_state_3295_, 8);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_state_3295_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3450_ = v_state_3295_;
v_isShared_3451_ = v_isSharedCheck_3518_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_pendingHead_3448_);
lean_inc(v_expectData_3446_);
lean_inc(v_respStream_3444_);
lean_inc(v_response_3443_);
lean_inc(v_headerTimeout_3442_);
lean_inc(v_currentTimeout_3441_);
lean_inc(v_keepAliveTimeout_3440_);
lean_inc(v_requestStream_3439_);
lean_inc(v_machine_3438_);
lean_dec(v_state_3295_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3518_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___y_3453_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_mk_empty_array_with_capacity(v___x_3466_);
v___x_3468_ = lean_array_push(v___x_3467_, v_val_3434_);
v___x_3469_ = lean_array_get_size(v___x_3468_);
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = lean_nat_dec_eq(v___x_3469_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_object* v_reader_3472_; lean_object* v_writer_3473_; lean_object* v_config_3474_; lean_object* v_events_3475_; lean_object* v_error_3476_; lean_object* v_instant_3477_; uint8_t v_keepAlive_3478_; uint8_t v_forcedFlush_3479_; uint8_t v_pullBodyStalled_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3517_; 
v_reader_3472_ = lean_ctor_get(v_machine_3438_, 0);
v_writer_3473_ = lean_ctor_get(v_machine_3438_, 1);
v_config_3474_ = lean_ctor_get(v_machine_3438_, 2);
v_events_3475_ = lean_ctor_get(v_machine_3438_, 3);
v_error_3476_ = lean_ctor_get(v_machine_3438_, 4);
v_instant_3477_ = lean_ctor_get(v_machine_3438_, 5);
v_keepAlive_3478_ = lean_ctor_get_uint8(v_machine_3438_, sizeof(void*)*6);
v_forcedFlush_3479_ = lean_ctor_get_uint8(v_machine_3438_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3480_ = lean_ctor_get_uint8(v_machine_3438_, sizeof(void*)*6 + 2);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_machine_3438_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3482_ = v_machine_3438_;
v_isShared_3483_ = v_isSharedCheck_3517_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_instant_3477_);
lean_inc(v_error_3476_);
lean_inc(v_events_3475_);
lean_inc(v_config_3474_);
lean_inc(v_writer_3473_);
lean_inc(v_reader_3472_);
lean_dec(v_machine_3438_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3517_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___y_3485_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3508_ = lean_nat_dec_lt(v___x_3470_, v___x_3469_);
if (v___x_3508_ == 0)
{
v___y_3485_ = v___x_3470_;
goto v___jp_3484_;
}
else
{
lean_object* v___f_3509_; uint8_t v___x_3510_; 
v___f_3509_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3510_ = lean_nat_dec_le(v___x_3469_, v___x_3469_);
if (v___x_3510_ == 0)
{
if (v___x_3508_ == 0)
{
v___y_3485_ = v___x_3470_;
goto v___jp_3484_;
}
else
{
size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((size_t)0ULL);
v___x_3512_ = lean_usize_of_nat(v___x_3469_);
lean_inc_ref(v___x_3468_);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3507_, v___f_3509_, v___x_3468_, v___x_3511_, v___x_3512_, v___x_3470_);
v___y_3485_ = v___x_3513_;
goto v___jp_3484_;
}
}
else
{
size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = lean_usize_of_nat(v___x_3469_);
lean_inc_ref(v___x_3468_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3507_, v___f_3509_, v___x_3468_, v___x_3514_, v___x_3515_, v___x_3470_);
v___y_3485_ = v___x_3516_;
goto v___jp_3484_;
}
}
v___jp_3484_:
{
lean_object* v_userData_3486_; lean_object* v_outputData_3487_; lean_object* v_state_3488_; lean_object* v_knownSize_3489_; lean_object* v_messageHead_3490_; uint8_t v_sentMessage_3491_; uint8_t v_userClosedBody_3492_; uint8_t v_omitBody_3493_; lean_object* v_userDataBytes_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3506_; 
v_userData_3486_ = lean_ctor_get(v_writer_3473_, 0);
v_outputData_3487_ = lean_ctor_get(v_writer_3473_, 1);
v_state_3488_ = lean_ctor_get(v_writer_3473_, 2);
v_knownSize_3489_ = lean_ctor_get(v_writer_3473_, 3);
v_messageHead_3490_ = lean_ctor_get(v_writer_3473_, 4);
v_sentMessage_3491_ = lean_ctor_get_uint8(v_writer_3473_, sizeof(void*)*6);
v_userClosedBody_3492_ = lean_ctor_get_uint8(v_writer_3473_, sizeof(void*)*6 + 1);
v_omitBody_3493_ = lean_ctor_get_uint8(v_writer_3473_, sizeof(void*)*6 + 2);
v_userDataBytes_3494_ = lean_ctor_get(v_writer_3473_, 5);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_writer_3473_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3496_ = v_writer_3473_;
v_isShared_3497_ = v_isSharedCheck_3506_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_userDataBytes_3494_);
lean_inc(v_messageHead_3490_);
lean_inc(v_knownSize_3489_);
lean_inc(v_state_3488_);
lean_inc(v_outputData_3487_);
lean_inc(v_userData_3486_);
lean_dec(v_writer_3473_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3506_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3498_ = l_Array_append___redArg(v_userData_3486_, v___x_3468_);
lean_dec_ref(v___x_3468_);
v___x_3499_ = lean_nat_add(v_userDataBytes_3494_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec(v_userDataBytes_3494_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 5, v___x_3499_);
lean_ctor_set(v___x_3496_, 0, v___x_3498_);
v___x_3501_ = v___x_3496_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_outputData_3487_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_state_3488_);
lean_ctor_set(v_reuseFailAlloc_3505_, 3, v_knownSize_3489_);
lean_ctor_set(v_reuseFailAlloc_3505_, 4, v_messageHead_3490_);
lean_ctor_set(v_reuseFailAlloc_3505_, 5, v___x_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3505_, sizeof(void*)*6, v_sentMessage_3491_);
lean_ctor_set_uint8(v_reuseFailAlloc_3505_, sizeof(void*)*6 + 1, v_userClosedBody_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3505_, sizeof(void*)*6 + 2, v_omitBody_3493_);
v___x_3501_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3503_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3501_);
v___x_3503_ = v___x_3482_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_reader_3472_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3504_, 2, v_config_3474_);
lean_ctor_set(v_reuseFailAlloc_3504_, 3, v_events_3475_);
lean_ctor_set(v_reuseFailAlloc_3504_, 4, v_error_3476_);
lean_ctor_set(v_reuseFailAlloc_3504_, 5, v_instant_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3504_, sizeof(void*)*6, v_keepAlive_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3504_, sizeof(void*)*6 + 1, v_forcedFlush_3479_);
lean_ctor_set_uint8(v_reuseFailAlloc_3504_, sizeof(void*)*6 + 2, v_pullBodyStalled_3480_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
v___y_3453_ = v___x_3503_;
goto v___jp_3452_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3468_);
v___y_3453_ = v_machine_3438_;
goto v___jp_3452_;
}
v___jp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___y_3453_);
v___x_3455_ = v___x_3450_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___y_3453_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_requestStream_3439_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_keepAliveTimeout_3440_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_currentTimeout_3441_);
lean_ctor_set(v_reuseFailAlloc_3465_, 4, v_headerTimeout_3442_);
lean_ctor_set(v_reuseFailAlloc_3465_, 5, v_response_3443_);
lean_ctor_set(v_reuseFailAlloc_3465_, 6, v_respStream_3444_);
lean_ctor_set(v_reuseFailAlloc_3465_, 7, v_expectData_3446_);
lean_ctor_set(v_reuseFailAlloc_3465_, 8, v_pendingHead_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3465_, sizeof(void*)*9, v_requiresData_3445_);
lean_ctor_set_uint8(v_reuseFailAlloc_3465_, sizeof(void*)*9 + 1, v_handlerDispatched_3447_);
v___x_3455_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
uint8_t v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3456_ = 0;
v___x_3457_ = lean_box(v___x_3456_);
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3455_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3458_);
v___x_3460_ = v___x_3436_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set_tag(v___x_3407_, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3460_);
v___x_3462_ = v___x_3407_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
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
uint8_t v_x_3521_; 
lean_dec_ref(v_config_3293_);
lean_dec_ref(v_inst_3291_);
v_x_3521_ = lean_ctor_get_uint8(v_event_3294_, 0);
lean_dec_ref_known(v_event_3294_, 0);
if (v_x_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec(v_handler_3292_);
lean_dec_ref(v_inst_3290_);
v___x_3522_ = lean_box(v_x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v_state_3295_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
return v___x_3525_;
}
else
{
lean_object* v_machine_3526_; lean_object* v_requestStream_3527_; lean_object* v_keepAliveTimeout_3528_; lean_object* v_currentTimeout_3529_; lean_object* v_headerTimeout_3530_; lean_object* v_response_3531_; lean_object* v_respStream_3532_; uint8_t v_requiresData_3533_; lean_object* v_expectData_3534_; uint8_t v_handlerDispatched_3535_; lean_object* v_pendingHead_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3587_; 
v_machine_3526_ = lean_ctor_get(v_state_3295_, 0);
v_requestStream_3527_ = lean_ctor_get(v_state_3295_, 1);
v_keepAliveTimeout_3528_ = lean_ctor_get(v_state_3295_, 2);
v_currentTimeout_3529_ = lean_ctor_get(v_state_3295_, 3);
v_headerTimeout_3530_ = lean_ctor_get(v_state_3295_, 4);
v_response_3531_ = lean_ctor_get(v_state_3295_, 5);
v_respStream_3532_ = lean_ctor_get(v_state_3295_, 6);
v_requiresData_3533_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3534_ = lean_ctor_get(v_state_3295_, 7);
v_handlerDispatched_3535_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9 + 1);
v_pendingHead_3536_ = lean_ctor_get(v_state_3295_, 8);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_state_3295_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3538_ = v_state_3295_;
v_isShared_3539_ = v_isSharedCheck_3587_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_pendingHead_3536_);
lean_inc(v_expectData_3534_);
lean_inc(v_respStream_3532_);
lean_inc(v_response_3531_);
lean_inc(v_headerTimeout_3530_);
lean_inc(v_currentTimeout_3529_);
lean_inc(v_keepAliveTimeout_3528_);
lean_inc(v_requestStream_3527_);
lean_inc(v_machine_3526_);
lean_dec(v_state_3295_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3587_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
uint8_t v___x_3540_; lean_object* v___x_3541_; lean_object* v_fst_3542_; lean_object* v_snd_3543_; lean_object* v_reader_3544_; lean_object* v_writer_3545_; lean_object* v_config_3546_; lean_object* v_events_3547_; lean_object* v_error_3548_; lean_object* v_instant_3549_; uint8_t v_keepAlive_3550_; uint8_t v_forcedFlush_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3586_; 
v___x_3540_ = 0;
v___x_3541_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3540_, v_machine_3526_);
v_fst_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_fst_3542_);
v_snd_3543_ = lean_ctor_get(v___x_3541_, 1);
lean_inc(v_snd_3543_);
lean_dec_ref(v___x_3541_);
v_reader_3544_ = lean_ctor_get(v_fst_3542_, 0);
v_writer_3545_ = lean_ctor_get(v_fst_3542_, 1);
v_config_3546_ = lean_ctor_get(v_fst_3542_, 2);
v_events_3547_ = lean_ctor_get(v_fst_3542_, 3);
v_error_3548_ = lean_ctor_get(v_fst_3542_, 4);
v_instant_3549_ = lean_ctor_get(v_fst_3542_, 5);
v_keepAlive_3550_ = lean_ctor_get_uint8(v_fst_3542_, sizeof(void*)*6);
v_forcedFlush_3551_ = lean_ctor_get_uint8(v_fst_3542_, sizeof(void*)*6 + 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_fst_3542_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3553_ = v_fst_3542_;
v_isShared_3554_ = v_isSharedCheck_3586_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_instant_3549_);
lean_inc(v_error_3548_);
lean_inc(v_events_3547_);
lean_inc(v_config_3546_);
lean_inc(v_writer_3545_);
lean_inc(v_reader_3544_);
lean_dec(v_fst_3542_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3586_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___f_3555_; lean_object* v___f_3556_; uint8_t v___y_3558_; 
v___f_3555_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3555_, 0, v_inst_3290_);
lean_closure_set(v___f_3555_, 1, v_handler_3292_);
v___f_3556_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3543_) == 0)
{
uint8_t v_sentMessage_3581_; uint8_t v___x_3582_; 
v_sentMessage_3581_ = lean_ctor_get_uint8(v_writer_3545_, sizeof(void*)*6);
v___x_3582_ = lean_bool_not(v_sentMessage_3581_);
if (v___x_3582_ == 0)
{
v___y_3558_ = v___x_3582_;
goto v___jp_3557_;
}
else
{
lean_object* v_state_3583_; 
v_state_3583_ = lean_ctor_get(v_reader_3544_, 0);
if (lean_obj_tag(v_state_3583_) == 2)
{
v___y_3558_ = v___x_3582_;
goto v___jp_3557_;
}
else
{
uint8_t v___x_3584_; 
v___x_3584_ = 0;
v___y_3558_ = v___x_3584_;
goto v___jp_3557_;
}
}
}
else
{
uint8_t v___x_3585_; 
v___x_3585_ = 0;
v___y_3558_ = v___x_3585_;
goto v___jp_3557_;
}
v___jp_3557_:
{
lean_object* v___x_3560_; 
if (v_isShared_3554_ == 0)
{
v___x_3560_ = v___x_3553_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_reader_3544_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_writer_3545_);
lean_ctor_set(v_reuseFailAlloc_3580_, 2, v_config_3546_);
lean_ctor_set(v_reuseFailAlloc_3580_, 3, v_events_3547_);
lean_ctor_set(v_reuseFailAlloc_3580_, 4, v_error_3548_);
lean_ctor_set(v_reuseFailAlloc_3580_, 5, v_instant_3549_);
lean_ctor_set_uint8(v_reuseFailAlloc_3580_, sizeof(void*)*6, v_keepAlive_3550_);
lean_ctor_set_uint8(v_reuseFailAlloc_3580_, sizeof(void*)*6 + 1, v_forcedFlush_3551_);
v___x_3560_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v_st_3562_; 
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*6 + 2, v___y_3558_);
lean_inc_ref(v_requestStream_3527_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3560_);
v_st_3562_ = v___x_3538_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_requestStream_3527_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_keepAliveTimeout_3528_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_currentTimeout_3529_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_headerTimeout_3530_);
lean_ctor_set(v_reuseFailAlloc_3579_, 5, v_response_3531_);
lean_ctor_set(v_reuseFailAlloc_3579_, 6, v_respStream_3532_);
lean_ctor_set(v_reuseFailAlloc_3579_, 7, v_expectData_3534_);
lean_ctor_set(v_reuseFailAlloc_3579_, 8, v_pendingHead_3536_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*9, v_requiresData_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*9 + 1, v_handlerDispatched_3535_);
v_st_3562_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___f_3563_; 
lean_inc_ref(v_st_3562_);
v___f_3563_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3563_, 0, v_st_3562_);
if (lean_obj_tag(v_snd_3543_) == 1)
{
lean_object* v_val_3564_; uint8_t v_final_3565_; uint8_t v_incomplete_3566_; lean_object* v_chunk_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; lean_object* v___f_3573_; lean_object* v___x_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; 
lean_dec_ref(v_st_3562_);
v_val_3564_ = lean_ctor_get(v_snd_3543_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v_snd_3543_, 1);
v_final_3565_ = lean_ctor_get_uint8(v_val_3564_, sizeof(void*)*1);
v_incomplete_3566_ = lean_ctor_get_uint8(v_val_3564_, sizeof(void*)*1 + 1);
v_chunk_3567_ = lean_ctor_get(v_val_3564_, 0);
lean_inc_ref(v_chunk_3567_);
lean_dec(v_val_3564_);
lean_inc_ref_n(v_requestStream_3527_, 2);
v___x_3568_ = l_Std_Http_Body_Stream_send(v_requestStream_3527_, v_chunk_3567_, v_incomplete_3566_);
v___x_3569_ = lean_unsigned_to_nat(0u);
v___x_3570_ = 0;
v___x_3571_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3569_, v___x_3570_, v___x_3568_, v___f_3555_);
lean_inc_ref_n(v___f_3563_, 2);
v___f_3572_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3572_, 0, v___f_3563_);
v___f_3573_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3573_, 0, v_requestStream_3527_);
lean_closure_set(v___f_3573_, 1, v___f_3572_);
lean_closure_set(v___f_3573_, 2, v___f_3563_);
v___x_3574_ = lean_box(v_final_3565_);
v___f_3575_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3575_, 0, v___x_3574_);
lean_closure_set(v___f_3575_, 1, v___f_3563_);
lean_closure_set(v___f_3575_, 2, v___f_3556_);
lean_closure_set(v___f_3575_, 3, v_requestStream_3527_);
lean_closure_set(v___f_3575_, 4, v___f_3573_);
v___x_3576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3569_, v___x_3570_, v___x_3571_, v___f_3575_);
return v___x_3576_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v___f_3563_);
lean_dec_ref(v___f_3555_);
lean_dec(v_snd_3543_);
lean_dec_ref(v_requestStream_3527_);
v___x_3577_ = lean_box(0);
v___x_3578_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3562_, v___x_3577_);
return v___x_3578_;
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
lean_object* v_x_3588_; 
v_x_3588_ = lean_ctor_get(v_event_3294_, 0);
lean_inc_ref(v_x_3588_);
lean_dec_ref_known(v_event_3294_, 1);
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v_onFailure_3590_; lean_object* v___x_3591_; lean_object* v___f_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; 
lean_dec_ref(v_config_3293_);
lean_dec_ref(v_inst_3291_);
v_a_3589_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v_x_3588_, 1);
v_onFailure_3590_ = lean_ctor_get(v_inst_3290_, 2);
lean_inc_ref(v_onFailure_3590_);
lean_dec_ref(v_inst_3290_);
v___x_3591_ = lean_apply_3(v_onFailure_3590_, v_handler_3292_, v_a_3589_, lean_box(0));
v___f_3592_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3592_, 0, v_state_3295_);
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = 0;
v___x_3595_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3593_, v___x_3594_, v___x_3591_, v___f_3592_);
return v___x_3595_;
}
else
{
lean_object* v_machine_3596_; lean_object* v_reader_3597_; lean_object* v_state_3598_; 
lean_dec(v_handler_3292_);
lean_dec_ref(v_inst_3290_);
v_machine_3596_ = lean_ctor_get(v_state_3295_, 0);
lean_inc_ref(v_machine_3596_);
v_reader_3597_ = lean_ctor_get(v_machine_3596_, 0);
v_state_3598_ = lean_ctor_get(v_reader_3597_, 0);
if (lean_obj_tag(v_state_3598_) == 7)
{
lean_object* v_a_3599_; lean_object* v_requestStream_3600_; lean_object* v_keepAliveTimeout_3601_; lean_object* v_currentTimeout_3602_; lean_object* v_headerTimeout_3603_; lean_object* v_response_3604_; lean_object* v_respStream_3605_; uint8_t v_requiresData_3606_; lean_object* v_expectData_3607_; lean_object* v_pendingHead_3608_; lean_object* v_close_3609_; lean_object* v_isClosed_3610_; lean_object* v_body_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; lean_object* v___x_3619_; 
lean_dec_ref(v_config_3293_);
v_a_3599_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v_x_3588_, 1);
v_requestStream_3600_ = lean_ctor_get(v_state_3295_, 1);
lean_inc_ref(v_requestStream_3600_);
v_keepAliveTimeout_3601_ = lean_ctor_get(v_state_3295_, 2);
lean_inc(v_keepAliveTimeout_3601_);
v_currentTimeout_3602_ = lean_ctor_get(v_state_3295_, 3);
lean_inc(v_currentTimeout_3602_);
v_headerTimeout_3603_ = lean_ctor_get(v_state_3295_, 4);
lean_inc(v_headerTimeout_3603_);
v_response_3604_ = lean_ctor_get(v_state_3295_, 5);
lean_inc_ref(v_response_3604_);
v_respStream_3605_ = lean_ctor_get(v_state_3295_, 6);
lean_inc(v_respStream_3605_);
v_requiresData_3606_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3607_ = lean_ctor_get(v_state_3295_, 7);
lean_inc(v_expectData_3607_);
v_pendingHead_3608_ = lean_ctor_get(v_state_3295_, 8);
lean_inc(v_pendingHead_3608_);
lean_dec_ref(v_state_3295_);
v_close_3609_ = lean_ctor_get(v_inst_3291_, 1);
lean_inc_ref(v_close_3609_);
v_isClosed_3610_ = lean_ctor_get(v_inst_3291_, 2);
lean_inc_ref(v_isClosed_3610_);
lean_dec_ref(v_inst_3291_);
v_body_3611_ = lean_ctor_get(v_a_3599_, 1);
lean_inc_n(v_body_3611_, 2);
lean_dec(v_a_3599_);
v___x_3612_ = lean_apply_2(v_isClosed_3610_, v_body_3611_, lean_box(0));
v___x_3613_ = lean_box(v_requiresData_3606_);
v___f_3614_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3614_, 0, v_machine_3596_);
lean_closure_set(v___f_3614_, 1, v_requestStream_3600_);
lean_closure_set(v___f_3614_, 2, v_keepAliveTimeout_3601_);
lean_closure_set(v___f_3614_, 3, v_currentTimeout_3602_);
lean_closure_set(v___f_3614_, 4, v_headerTimeout_3603_);
lean_closure_set(v___f_3614_, 5, v_response_3604_);
lean_closure_set(v___f_3614_, 6, v_respStream_3605_);
lean_closure_set(v___f_3614_, 7, v___x_3613_);
lean_closure_set(v___f_3614_, 8, v_expectData_3607_);
lean_closure_set(v___f_3614_, 9, v_pendingHead_3608_);
lean_inc_ref(v___f_3614_);
v___f_3615_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3615_, 0, v___f_3614_);
v___f_3616_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3616_, 0, v_close_3609_);
lean_closure_set(v___f_3616_, 1, v_body_3611_);
lean_closure_set(v___f_3616_, 2, v___f_3615_);
lean_closure_set(v___f_3616_, 3, v___f_3614_);
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3618_ = 0;
v___x_3619_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3617_, v___x_3618_, v___x_3612_, v___f_3616_);
return v___x_3619_;
}
else
{
lean_object* v_a_3620_; lean_object* v_requestStream_3621_; lean_object* v_keepAliveTimeout_3622_; lean_object* v_currentTimeout_3623_; lean_object* v_headerTimeout_3624_; lean_object* v_response_3625_; uint8_t v_requiresData_3626_; lean_object* v_expectData_3627_; lean_object* v_pendingHead_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___f_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_a_3620_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v_x_3588_, 1);
v_requestStream_3621_ = lean_ctor_get(v_state_3295_, 1);
lean_inc_ref(v_requestStream_3621_);
v_keepAliveTimeout_3622_ = lean_ctor_get(v_state_3295_, 2);
lean_inc(v_keepAliveTimeout_3622_);
v_currentTimeout_3623_ = lean_ctor_get(v_state_3295_, 3);
lean_inc(v_currentTimeout_3623_);
v_headerTimeout_3624_ = lean_ctor_get(v_state_3295_, 4);
lean_inc(v_headerTimeout_3624_);
v_response_3625_ = lean_ctor_get(v_state_3295_, 5);
lean_inc_ref(v_response_3625_);
v_requiresData_3626_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3627_ = lean_ctor_get(v_state_3295_, 7);
lean_inc(v_expectData_3627_);
v_pendingHead_3628_ = lean_ctor_get(v_state_3295_, 8);
lean_inc(v_pendingHead_3628_);
lean_dec_ref(v_state_3295_);
lean_inc_ref(v_inst_3291_);
v___x_3629_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3291_, v_config_3293_, v_machine_3596_, v_a_3620_);
v___x_3630_ = 0;
v___x_3631_ = lean_box(v_requiresData_3626_);
v___x_3632_ = lean_box(v___x_3630_);
v___f_3633_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3633_, 0, v_requestStream_3621_);
lean_closure_set(v___f_3633_, 1, v_keepAliveTimeout_3622_);
lean_closure_set(v___f_3633_, 2, v_currentTimeout_3623_);
lean_closure_set(v___f_3633_, 3, v_headerTimeout_3624_);
lean_closure_set(v___f_3633_, 4, v_response_3625_);
lean_closure_set(v___f_3633_, 5, v___x_3631_);
lean_closure_set(v___f_3633_, 6, v_expectData_3627_);
lean_closure_set(v___f_3633_, 7, v___x_3632_);
lean_closure_set(v___f_3633_, 8, v_pendingHead_3628_);
v___f_3634_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3634_, 0, v___f_3633_);
v___x_3635_ = lean_box(v___x_3630_);
lean_inc_ref(v___f_3634_);
v___f_3636_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 6, 4);
lean_closure_set(v___f_3636_, 0, v___x_3635_);
lean_closure_set(v___f_3636_, 1, v___f_3634_);
lean_closure_set(v___f_3636_, 2, v_inst_3291_);
lean_closure_set(v___f_3636_, 3, v___f_3634_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3637_, v___x_3630_, v___x_3629_, v___f_3636_);
return v___x_3638_;
}
}
}
case 4:
{
lean_object* v_onFailure_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; lean_object* v___x_3645_; 
lean_dec_ref(v_config_3293_);
lean_dec_ref(v_inst_3291_);
v_onFailure_3639_ = lean_ctor_get(v_inst_3290_, 2);
lean_inc_ref(v_onFailure_3639_);
lean_dec_ref(v_inst_3290_);
v___x_3640_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_3641_ = lean_apply_3(v_onFailure_3639_, v_handler_3292_, v___x_3640_, lean_box(0));
v___f_3642_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 3, 1);
lean_closure_set(v___f_3642_, 0, v_state_3295_);
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = 0;
v___x_3645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3643_, v___x_3644_, v___x_3641_, v___f_3642_);
return v___x_3645_;
}
case 5:
{
lean_object* v_machine_3646_; lean_object* v_requestStream_3647_; lean_object* v_keepAliveTimeout_3648_; lean_object* v_currentTimeout_3649_; lean_object* v_headerTimeout_3650_; lean_object* v_response_3651_; lean_object* v_respStream_3652_; uint8_t v_requiresData_3653_; lean_object* v_expectData_3654_; lean_object* v_pendingHead_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref(v_config_3293_);
lean_dec(v_handler_3292_);
lean_dec_ref(v_inst_3291_);
lean_dec_ref(v_inst_3290_);
v_machine_3646_ = lean_ctor_get(v_state_3295_, 0);
v_requestStream_3647_ = lean_ctor_get(v_state_3295_, 1);
v_keepAliveTimeout_3648_ = lean_ctor_get(v_state_3295_, 2);
v_currentTimeout_3649_ = lean_ctor_get(v_state_3295_, 3);
v_headerTimeout_3650_ = lean_ctor_get(v_state_3295_, 4);
v_response_3651_ = lean_ctor_get(v_state_3295_, 5);
v_respStream_3652_ = lean_ctor_get(v_state_3295_, 6);
v_requiresData_3653_ = lean_ctor_get_uint8(v_state_3295_, sizeof(void*)*9);
v_expectData_3654_ = lean_ctor_get(v_state_3295_, 7);
v_pendingHead_3655_ = lean_ctor_get(v_state_3295_, 8);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_state_3295_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3657_ = v_state_3295_;
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_pendingHead_3655_);
lean_inc(v_expectData_3654_);
lean_inc(v_respStream_3652_);
lean_inc(v_response_3651_);
lean_inc(v_headerTimeout_3650_);
lean_inc(v_currentTimeout_3649_);
lean_inc(v_keepAliveTimeout_3648_);
lean_inc(v_requestStream_3647_);
lean_inc(v_machine_3646_);
lean_dec(v_state_3295_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3663_; 
v___x_3659_ = lean_box(55);
v___x_3660_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3646_, v___x_3659_);
v___x_3661_ = 0;
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3660_);
v___x_3663_ = v___x_3657_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_requestStream_3647_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_keepAliveTimeout_3648_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_currentTimeout_3649_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_headerTimeout_3650_);
lean_ctor_set(v_reuseFailAlloc_3668_, 5, v_response_3651_);
lean_ctor_set(v_reuseFailAlloc_3668_, 6, v_respStream_3652_);
lean_ctor_set(v_reuseFailAlloc_3668_, 7, v_expectData_3654_);
lean_ctor_set(v_reuseFailAlloc_3668_, 8, v_pendingHead_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*9, v_requiresData_3653_);
v___x_3663_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*9 + 1, v___x_3661_);
v___x_3664_ = lean_box(v___x_3661_);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
}
}
default: 
{
uint8_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_dec_ref(v_config_3293_);
lean_dec(v_handler_3292_);
lean_dec_ref(v_inst_3291_);
lean_dec_ref(v_inst_3290_);
v___x_3670_ = 1;
v___x_3671_ = lean_box(v___x_3670_);
v___x_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3672_, 0, v_state_3295_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
return v___x_3674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3675_, lean_object* v_inst_3676_, lean_object* v_handler_3677_, lean_object* v_config_3678_, lean_object* v_event_3679_, lean_object* v_state_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3675_, v_inst_3676_, v_handler_3677_, v_config_3678_, v_event_3679_, v_state_3680_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3683_, lean_object* v_00_u03b2_3684_, lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_handler_3687_, lean_object* v_config_3688_, lean_object* v_event_3689_, lean_object* v_state_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3685_, v_inst_3686_, v_handler_3687_, v_config_3688_, v_event_3689_, v_state_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3693_, lean_object* v_00_u03b2_3694_, lean_object* v_inst_3695_, lean_object* v_inst_3696_, lean_object* v_handler_3697_, lean_object* v_config_3698_, lean_object* v_event_3699_, lean_object* v_state_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3693_, v_00_u03b2_3694_, v_inst_3695_, v_inst_3696_, v_handler_3697_, v_config_3698_, v_event_3699_, v_state_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3703_, uint8_t v_handlerDispatched_3704_, lean_object* v_respStream_3705_, lean_object* v_currentTimeout_3706_, lean_object* v_expectData_3707_, lean_object* v_headerTimeout_3708_, lean_object* v_keepAliveTimeout_3709_, lean_object* v_response_3710_, lean_object* v_socket_3711_, uint8_t v_requiresData_3712_, uint8_t v_sentMessage_3713_, uint8_t v_requestBodyInterested_3714_, lean_object* v_reader_3715_, lean_object* v_requestBody_3716_){
_start:
{
lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3730_; uint8_t v___y_3738_; 
if (v_requiresData_3712_ == 0)
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_bool_not(v_handlerDispatched_3704_);
if (v___x_3739_ == 0)
{
if (lean_obj_tag(v_respStream_3705_) == 0)
{
if (v___x_3739_ == 0)
{
if (v_sentMessage_3713_ == 0)
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_bool_not(v_sentMessage_3713_);
if (v___x_3740_ == 0)
{
v___y_3738_ = v___x_3740_;
goto v___jp_3737_;
}
else
{
lean_object* v_state_3741_; 
v_state_3741_ = lean_ctor_get(v_reader_3715_, 0);
if (lean_obj_tag(v_state_3741_) == 2)
{
v___y_3738_ = v___x_3740_;
goto v___jp_3737_;
}
else
{
lean_dec(v_socket_3711_);
goto v___jp_3735_;
}
}
}
else
{
goto v___jp_3733_;
}
}
else
{
goto v___jp_3733_;
}
}
else
{
goto v___jp_3733_;
}
}
else
{
goto v___jp_3733_;
}
}
else
{
goto v___jp_3733_;
}
v___jp_3718_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3726_, 0, v___y_3719_);
lean_ctor_set(v___x_3726_, 1, v___y_3722_);
lean_ctor_set(v___x_3726_, 2, v___y_3725_);
lean_ctor_set(v___x_3726_, 3, v___y_3720_);
lean_ctor_set(v___x_3726_, 4, v_requestBody_3716_);
lean_ctor_set(v___x_3726_, 5, v___y_3721_);
lean_ctor_set(v___x_3726_, 6, v___y_3724_);
lean_ctor_set(v___x_3726_, 7, v___y_3723_);
lean_ctor_set(v___x_3726_, 8, v_connectionContext_3703_);
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
v___jp_3729_:
{
if (v_handlerDispatched_3704_ == 0)
{
lean_object* v___x_3731_; 
lean_dec_ref(v_response_3710_);
v___x_3731_ = lean_box(0);
v___y_3719_ = v___y_3730_;
v___y_3720_ = v_respStream_3705_;
v___y_3721_ = v_currentTimeout_3706_;
v___y_3722_ = v_expectData_3707_;
v___y_3723_ = v_headerTimeout_3708_;
v___y_3724_ = v_keepAliveTimeout_3709_;
v___y_3725_ = v___x_3731_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3732_, 0, v_response_3710_);
v___y_3719_ = v___y_3730_;
v___y_3720_ = v_respStream_3705_;
v___y_3721_ = v_currentTimeout_3706_;
v___y_3722_ = v_expectData_3707_;
v___y_3723_ = v_headerTimeout_3708_;
v___y_3724_ = v_keepAliveTimeout_3709_;
v___y_3725_ = v___x_3732_;
goto v___jp_3718_;
}
}
v___jp_3733_:
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v_socket_3711_);
v___y_3730_ = v___x_3734_;
goto v___jp_3729_;
}
v___jp_3735_:
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_box(0);
v___y_3730_ = v___x_3736_;
goto v___jp_3729_;
}
v___jp_3737_:
{
if (v___y_3738_ == 0)
{
lean_dec(v_socket_3711_);
goto v___jp_3735_;
}
else
{
if (v_requestBodyInterested_3714_ == 0)
{
lean_dec(v_socket_3711_);
goto v___jp_3735_;
}
else
{
goto v___jp_3733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3742_, lean_object* v_handlerDispatched_3743_, lean_object* v_respStream_3744_, lean_object* v_currentTimeout_3745_, lean_object* v_expectData_3746_, lean_object* v_headerTimeout_3747_, lean_object* v_keepAliveTimeout_3748_, lean_object* v_response_3749_, lean_object* v_socket_3750_, lean_object* v_requiresData_3751_, lean_object* v_sentMessage_3752_, lean_object* v_requestBodyInterested_3753_, lean_object* v_reader_3754_, lean_object* v_requestBody_3755_, lean_object* v___y_3756_){
_start:
{
uint8_t v_handlerDispatched_boxed_3757_; uint8_t v_requiresData_boxed_3758_; uint8_t v_sentMessage_boxed_3759_; uint8_t v_requestBodyInterested_boxed_3760_; lean_object* v_res_3761_; 
v_handlerDispatched_boxed_3757_ = lean_unbox(v_handlerDispatched_3743_);
v_requiresData_boxed_3758_ = lean_unbox(v_requiresData_3751_);
v_sentMessage_boxed_3759_ = lean_unbox(v_sentMessage_3752_);
v_requestBodyInterested_boxed_3760_ = lean_unbox(v_requestBodyInterested_3753_);
v_res_3761_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3742_, v_handlerDispatched_boxed_3757_, v_respStream_3744_, v_currentTimeout_3745_, v_expectData_3746_, v_headerTimeout_3747_, v_keepAliveTimeout_3748_, v_response_3749_, v_socket_3750_, v_requiresData_boxed_3758_, v_sentMessage_boxed_3759_, v_requestBodyInterested_boxed_3760_, v_reader_3754_, v_requestBody_3755_);
lean_dec_ref(v_reader_3754_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3762_, lean_object* v_x_3763_){
_start:
{
if (lean_obj_tag(v_x_3763_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v___f_3762_);
v_a_3765_ = lean_ctor_get(v_x_3763_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_x_3763_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3767_ = v_x_3763_;
v_isShared_3768_ = v_isSharedCheck_3773_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v_x_3763_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3773_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
return v___x_3771_;
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3775_; 
v_a_3774_ = lean_ctor_get(v_x_3763_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v_x_3763_, 1);
v___x_3775_ = lean_apply_2(v___f_3762_, v_a_3774_, lean_box(0));
return v___x_3775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3776_, lean_object* v_x_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3776_, v_x_3777_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3784_, uint8_t v_handlerDispatched_3785_, lean_object* v_respStream_3786_, lean_object* v_currentTimeout_3787_, lean_object* v_expectData_3788_, lean_object* v_headerTimeout_3789_, lean_object* v_keepAliveTimeout_3790_, lean_object* v_response_3791_, lean_object* v_socket_3792_, uint8_t v_requiresData_3793_, uint8_t v_sentMessage_3794_, lean_object* v_reader_3795_, uint8_t v_pullBodyStalled_3796_, uint8_t v_requestBodyOpen_3797_, lean_object* v_requestStream_3798_, uint8_t v_requestBodyInterested_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___f_3805_; lean_object* v___f_3806_; uint8_t v___y_3813_; uint8_t v___x_3821_; 
v___x_3801_ = lean_box(v_handlerDispatched_3785_);
v___x_3802_ = lean_box(v_requiresData_3793_);
v___x_3803_ = lean_box(v_sentMessage_3794_);
v___x_3804_ = lean_box(v_requestBodyInterested_3799_);
lean_inc_ref(v_reader_3795_);
v___f_3805_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3805_, 0, v_connectionContext_3784_);
lean_closure_set(v___f_3805_, 1, v___x_3801_);
lean_closure_set(v___f_3805_, 2, v_respStream_3786_);
lean_closure_set(v___f_3805_, 3, v_currentTimeout_3787_);
lean_closure_set(v___f_3805_, 4, v_expectData_3788_);
lean_closure_set(v___f_3805_, 5, v_headerTimeout_3789_);
lean_closure_set(v___f_3805_, 6, v_keepAliveTimeout_3790_);
lean_closure_set(v___f_3805_, 7, v_response_3791_);
lean_closure_set(v___f_3805_, 8, v_socket_3792_);
lean_closure_set(v___f_3805_, 9, v___x_3802_);
lean_closure_set(v___f_3805_, 10, v___x_3803_);
lean_closure_set(v___f_3805_, 11, v___x_3804_);
lean_closure_set(v___f_3805_, 12, v_reader_3795_);
v___f_3806_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3806_, 0, v___f_3805_);
v___x_3821_ = lean_bool_not(v_sentMessage_3794_);
if (v___x_3821_ == 0)
{
lean_dec_ref(v_reader_3795_);
v___y_3813_ = v___x_3821_;
goto v___jp_3812_;
}
else
{
lean_object* v_state_3822_; 
v_state_3822_ = lean_ctor_get(v_reader_3795_, 0);
lean_inc(v_state_3822_);
lean_dec_ref(v_reader_3795_);
if (lean_obj_tag(v_state_3822_) == 2)
{
lean_dec_ref_known(v_state_3822_, 1);
v___y_3813_ = v___x_3821_;
goto v___jp_3812_;
}
else
{
lean_dec(v_state_3822_);
lean_dec_ref(v_requestStream_3798_);
goto v___jp_3807_;
}
}
v___jp_3807_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; lean_object* v___x_3811_; 
v___x_3808_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = 0;
v___x_3811_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3809_, v___x_3810_, v___x_3808_, v___f_3806_);
return v___x_3811_;
}
v___jp_3812_:
{
if (v___y_3813_ == 0)
{
lean_dec_ref(v_requestStream_3798_);
goto v___jp_3807_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_bool_not(v_pullBodyStalled_3796_);
if (v___x_3814_ == 0)
{
lean_dec_ref(v_requestStream_3798_);
goto v___jp_3807_;
}
else
{
if (v_requestBodyOpen_3797_ == 0)
{
lean_dec_ref(v_requestStream_3798_);
goto v___jp_3807_;
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_requestStream_3798_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = 0;
v___x_3820_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3818_, v___x_3819_, v___x_3817_, v___f_3806_);
return v___x_3820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3823_ = _args[0];
lean_object* v_handlerDispatched_3824_ = _args[1];
lean_object* v_respStream_3825_ = _args[2];
lean_object* v_currentTimeout_3826_ = _args[3];
lean_object* v_expectData_3827_ = _args[4];
lean_object* v_headerTimeout_3828_ = _args[5];
lean_object* v_keepAliveTimeout_3829_ = _args[6];
lean_object* v_response_3830_ = _args[7];
lean_object* v_socket_3831_ = _args[8];
lean_object* v_requiresData_3832_ = _args[9];
lean_object* v_sentMessage_3833_ = _args[10];
lean_object* v_reader_3834_ = _args[11];
lean_object* v_pullBodyStalled_3835_ = _args[12];
lean_object* v_requestBodyOpen_3836_ = _args[13];
lean_object* v_requestStream_3837_ = _args[14];
lean_object* v_requestBodyInterested_3838_ = _args[15];
lean_object* v___y_3839_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3840_; uint8_t v_requiresData_boxed_3841_; uint8_t v_sentMessage_boxed_3842_; uint8_t v_pullBodyStalled_boxed_3843_; uint8_t v_requestBodyOpen_boxed_3844_; uint8_t v_requestBodyInterested_boxed_3845_; lean_object* v_res_3846_; 
v_handlerDispatched_boxed_3840_ = lean_unbox(v_handlerDispatched_3824_);
v_requiresData_boxed_3841_ = lean_unbox(v_requiresData_3832_);
v_sentMessage_boxed_3842_ = lean_unbox(v_sentMessage_3833_);
v_pullBodyStalled_boxed_3843_ = lean_unbox(v_pullBodyStalled_3835_);
v_requestBodyOpen_boxed_3844_ = lean_unbox(v_requestBodyOpen_3836_);
v_requestBodyInterested_boxed_3845_ = lean_unbox(v_requestBodyInterested_3838_);
v_res_3846_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3823_, v_handlerDispatched_boxed_3840_, v_respStream_3825_, v_currentTimeout_3826_, v_expectData_3827_, v_headerTimeout_3828_, v_keepAliveTimeout_3829_, v_response_3830_, v_socket_3831_, v_requiresData_boxed_3841_, v_sentMessage_boxed_3842_, v_reader_3834_, v_pullBodyStalled_boxed_3843_, v_requestBodyOpen_boxed_3844_, v_requestStream_3837_, v_requestBodyInterested_boxed_3845_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3847_, lean_object* v_x_3848_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v___f_3847_);
v_a_3850_ = lean_ctor_get(v_x_3848_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_x_3848_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3852_ = v_x_3848_;
v_isShared_3853_ = v_isSharedCheck_3858_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v_x_3848_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3858_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
return v___x_3856_;
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3860_; 
v_a_3859_ = lean_ctor_get(v_x_3848_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v_x_3848_, 1);
v___x_3860_ = lean_apply_2(v___f_3847_, v_a_3859_, lean_box(0));
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3861_, lean_object* v_x_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3861_, v_x_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3870_, uint8_t v_handlerDispatched_3871_, lean_object* v_respStream_3872_, lean_object* v_currentTimeout_3873_, lean_object* v_expectData_3874_, lean_object* v_headerTimeout_3875_, lean_object* v_keepAliveTimeout_3876_, lean_object* v_response_3877_, lean_object* v_socket_3878_, uint8_t v_requiresData_3879_, uint8_t v_sentMessage_3880_, lean_object* v_reader_3881_, uint8_t v_pullBodyStalled_3882_, lean_object* v_requestStream_3883_, uint8_t v_requestBodyOpen_3884_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___f_3891_; lean_object* v___f_3892_; uint8_t v___y_3899_; uint8_t v___x_3904_; 
v___x_3886_ = lean_box(v_handlerDispatched_3871_);
v___x_3887_ = lean_box(v_requiresData_3879_);
v___x_3888_ = lean_box(v_sentMessage_3880_);
v___x_3889_ = lean_box(v_pullBodyStalled_3882_);
v___x_3890_ = lean_box(v_requestBodyOpen_3884_);
lean_inc_ref(v_requestStream_3883_);
lean_inc_ref(v_reader_3881_);
v___f_3891_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3891_, 0, v_connectionContext_3870_);
lean_closure_set(v___f_3891_, 1, v___x_3886_);
lean_closure_set(v___f_3891_, 2, v_respStream_3872_);
lean_closure_set(v___f_3891_, 3, v_currentTimeout_3873_);
lean_closure_set(v___f_3891_, 4, v_expectData_3874_);
lean_closure_set(v___f_3891_, 5, v_headerTimeout_3875_);
lean_closure_set(v___f_3891_, 6, v_keepAliveTimeout_3876_);
lean_closure_set(v___f_3891_, 7, v_response_3877_);
lean_closure_set(v___f_3891_, 8, v_socket_3878_);
lean_closure_set(v___f_3891_, 9, v___x_3887_);
lean_closure_set(v___f_3891_, 10, v___x_3888_);
lean_closure_set(v___f_3891_, 11, v_reader_3881_);
lean_closure_set(v___f_3891_, 12, v___x_3889_);
lean_closure_set(v___f_3891_, 13, v___x_3890_);
lean_closure_set(v___f_3891_, 14, v_requestStream_3883_);
v___f_3892_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3892_, 0, v___f_3891_);
v___x_3904_ = lean_bool_not(v_sentMessage_3880_);
if (v___x_3904_ == 0)
{
lean_dec_ref(v_reader_3881_);
v___y_3899_ = v___x_3904_;
goto v___jp_3898_;
}
else
{
lean_object* v_state_3905_; 
v_state_3905_ = lean_ctor_get(v_reader_3881_, 0);
lean_inc(v_state_3905_);
lean_dec_ref(v_reader_3881_);
if (lean_obj_tag(v_state_3905_) == 2)
{
lean_dec_ref_known(v_state_3905_, 1);
v___y_3899_ = v___x_3904_;
goto v___jp_3898_;
}
else
{
lean_dec(v_state_3905_);
lean_dec_ref(v_requestStream_3883_);
goto v___jp_3893_;
}
}
v___jp_3893_:
{
uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3894_ = 0;
v___x_3895_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___closed__1));
v___x_3896_ = lean_unsigned_to_nat(0u);
v___x_3897_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3896_, v___x_3894_, v___x_3895_, v___f_3892_);
return v___x_3897_;
}
v___jp_3898_:
{
if (v___y_3899_ == 0)
{
lean_dec_ref(v_requestStream_3883_);
goto v___jp_3893_;
}
else
{
if (v_requestBodyOpen_3884_ == 0)
{
lean_dec_ref(v_requestStream_3883_);
goto v___jp_3893_;
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3900_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3883_);
v___x_3901_ = lean_unsigned_to_nat(0u);
v___x_3902_ = 0;
v___x_3903_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3901_, v___x_3902_, v___x_3900_, v___f_3892_);
return v___x_3903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3906_, lean_object* v_handlerDispatched_3907_, lean_object* v_respStream_3908_, lean_object* v_currentTimeout_3909_, lean_object* v_expectData_3910_, lean_object* v_headerTimeout_3911_, lean_object* v_keepAliveTimeout_3912_, lean_object* v_response_3913_, lean_object* v_socket_3914_, lean_object* v_requiresData_3915_, lean_object* v_sentMessage_3916_, lean_object* v_reader_3917_, lean_object* v_pullBodyStalled_3918_, lean_object* v_requestStream_3919_, lean_object* v_requestBodyOpen_3920_, lean_object* v___y_3921_){
_start:
{
uint8_t v_handlerDispatched_boxed_3922_; uint8_t v_requiresData_boxed_3923_; uint8_t v_sentMessage_boxed_3924_; uint8_t v_pullBodyStalled_boxed_3925_; uint8_t v_requestBodyOpen_boxed_3926_; lean_object* v_res_3927_; 
v_handlerDispatched_boxed_3922_ = lean_unbox(v_handlerDispatched_3907_);
v_requiresData_boxed_3923_ = lean_unbox(v_requiresData_3915_);
v_sentMessage_boxed_3924_ = lean_unbox(v_sentMessage_3916_);
v_pullBodyStalled_boxed_3925_ = lean_unbox(v_pullBodyStalled_3918_);
v_requestBodyOpen_boxed_3926_ = lean_unbox(v_requestBodyOpen_3920_);
v_res_3927_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3906_, v_handlerDispatched_boxed_3922_, v_respStream_3908_, v_currentTimeout_3909_, v_expectData_3910_, v_headerTimeout_3911_, v_keepAliveTimeout_3912_, v_response_3913_, v_socket_3914_, v_requiresData_boxed_3923_, v_sentMessage_boxed_3924_, v_reader_3917_, v_pullBodyStalled_boxed_3925_, v_requestStream_3919_, v_requestBodyOpen_boxed_3926_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(lean_object* v___f_3928_, lean_object* v_x_3929_){
_start:
{
if (lean_obj_tag(v_x_3929_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v___f_3928_);
v_a_3931_ = lean_ctor_get(v_x_3929_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_x_3929_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3933_ = v_x_3929_;
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v_x_3929_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3954_; 
v_a_3940_ = lean_ctor_get(v_x_3929_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_x_3929_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3942_ = v_x_3929_;
v_isShared_3943_ = v_isSharedCheck_3954_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v_x_3929_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3954_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
uint8_t v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3944_ = lean_unbox(v_a_3940_);
lean_dec(v_a_3940_);
v___x_3945_ = lean_bool_not(v___x_3944_);
v___x_3946_ = lean_box(v___x_3945_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3946_);
v___x_3948_ = v___x_3942_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; lean_object* v___x_3952_; 
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
v___x_3950_ = lean_unsigned_to_nat(0u);
v___x_3951_ = 0;
v___x_3952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3950_, v___x_3951_, v___x_3949_, v___f_3928_);
return v___x_3952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v___f_3955_, lean_object* v_x_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v___f_3955_, v_x_3956_);
return v_res_3958_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___f_3959_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3960_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3961_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3962_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3962_, 0, lean_box(0));
lean_closure_set(v___x_3962_, 1, lean_box(0));
lean_closure_set(v___x_3962_, 2, v___x_3961_);
lean_closure_set(v___x_3962_, 3, lean_box(0));
lean_closure_set(v___x_3962_, 4, lean_box(0));
lean_closure_set(v___x_3962_, 5, v___x_3960_);
lean_closure_set(v___x_3962_, 6, v___f_3959_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3963_, lean_object* v_connectionContext_3964_, lean_object* v_state_3965_){
_start:
{
lean_object* v_machine_3967_; lean_object* v_writer_3968_; lean_object* v_requestStream_3969_; lean_object* v_keepAliveTimeout_3970_; lean_object* v_currentTimeout_3971_; lean_object* v_headerTimeout_3972_; lean_object* v_response_3973_; lean_object* v_respStream_3974_; uint8_t v_requiresData_3975_; lean_object* v_expectData_3976_; uint8_t v_handlerDispatched_3977_; lean_object* v_reader_3978_; uint8_t v_pullBodyStalled_3979_; uint8_t v_sentMessage_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___f_3985_; lean_object* v___f_3986_; uint8_t v___y_3988_; lean_object* v___f_3994_; uint8_t v___y_3996_; uint8_t v___x_4006_; 
v_machine_3967_ = lean_ctor_get(v_state_3965_, 0);
lean_inc_ref(v_machine_3967_);
v_writer_3968_ = lean_ctor_get(v_machine_3967_, 1);
lean_inc_ref(v_writer_3968_);
v_requestStream_3969_ = lean_ctor_get(v_state_3965_, 1);
lean_inc_ref_n(v_requestStream_3969_, 2);
v_keepAliveTimeout_3970_ = lean_ctor_get(v_state_3965_, 2);
lean_inc(v_keepAliveTimeout_3970_);
v_currentTimeout_3971_ = lean_ctor_get(v_state_3965_, 3);
lean_inc(v_currentTimeout_3971_);
v_headerTimeout_3972_ = lean_ctor_get(v_state_3965_, 4);
lean_inc(v_headerTimeout_3972_);
v_response_3973_ = lean_ctor_get(v_state_3965_, 5);
lean_inc_ref(v_response_3973_);
v_respStream_3974_ = lean_ctor_get(v_state_3965_, 6);
lean_inc(v_respStream_3974_);
v_requiresData_3975_ = lean_ctor_get_uint8(v_state_3965_, sizeof(void*)*9);
v_expectData_3976_ = lean_ctor_get(v_state_3965_, 7);
lean_inc(v_expectData_3976_);
v_handlerDispatched_3977_ = lean_ctor_get_uint8(v_state_3965_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3965_);
v_reader_3978_ = lean_ctor_get(v_machine_3967_, 0);
lean_inc_ref_n(v_reader_3978_, 2);
v_pullBodyStalled_3979_ = lean_ctor_get_uint8(v_machine_3967_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3967_);
v_sentMessage_3980_ = lean_ctor_get_uint8(v_writer_3968_, sizeof(void*)*6);
lean_dec_ref(v_writer_3968_);
v___x_3981_ = lean_box(v_handlerDispatched_3977_);
v___x_3982_ = lean_box(v_requiresData_3975_);
v___x_3983_ = lean_box(v_sentMessage_3980_);
v___x_3984_ = lean_box(v_pullBodyStalled_3979_);
v___f_3985_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3985_, 0, v_connectionContext_3964_);
lean_closure_set(v___f_3985_, 1, v___x_3981_);
lean_closure_set(v___f_3985_, 2, v_respStream_3974_);
lean_closure_set(v___f_3985_, 3, v_currentTimeout_3971_);
lean_closure_set(v___f_3985_, 4, v_expectData_3976_);
lean_closure_set(v___f_3985_, 5, v_headerTimeout_3972_);
lean_closure_set(v___f_3985_, 6, v_keepAliveTimeout_3970_);
lean_closure_set(v___f_3985_, 7, v_response_3973_);
lean_closure_set(v___f_3985_, 8, v_socket_3963_);
lean_closure_set(v___f_3985_, 9, v___x_3982_);
lean_closure_set(v___f_3985_, 10, v___x_3983_);
lean_closure_set(v___f_3985_, 11, v_reader_3978_);
lean_closure_set(v___f_3985_, 12, v___x_3984_);
lean_closure_set(v___f_3985_, 13, v_requestStream_3969_);
v___f_3986_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3986_, 0, v___f_3985_);
lean_inc_ref(v___f_3986_);
v___f_3994_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_3994_, 0, v___f_3986_);
v___x_4006_ = lean_bool_not(v_sentMessage_3980_);
if (v___x_4006_ == 0)
{
lean_dec_ref(v_reader_3978_);
v___y_3996_ = v___x_4006_;
goto v___jp_3995_;
}
else
{
lean_object* v_state_4007_; 
v_state_4007_ = lean_ctor_get(v_reader_3978_, 0);
lean_inc(v_state_4007_);
lean_dec_ref(v_reader_3978_);
if (lean_obj_tag(v_state_4007_) == 2)
{
lean_dec_ref_known(v_state_4007_, 1);
v___y_3996_ = v___x_4006_;
goto v___jp_3995_;
}
else
{
uint8_t v___x_4008_; 
lean_dec(v_state_4007_);
lean_dec_ref(v___f_3994_);
lean_dec_ref(v_requestStream_3969_);
v___x_4008_ = 0;
v___y_3988_ = v___x_4008_;
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
v___x_3993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3992_, v___y_3988_, v___x_3991_, v___f_3986_);
return v___x_3993_;
}
v___jp_3995_:
{
if (v___y_3996_ == 0)
{
lean_dec_ref(v___f_3994_);
lean_dec_ref(v_requestStream_3969_);
v___y_3988_ = v___y_3996_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_3997_; lean_object* v___f_3998_; lean_object* v___f_3999_; lean_object* v___x_4000_; lean_object* v___x_3032__overap_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; lean_object* v___x_4005_; 
lean_dec_ref(v___f_3986_);
v___x_3997_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3998_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3999_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4000_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_3032__overap_4001_ = l_Std_Mutex_atomically___redArg(v___x_3997_, v___f_3998_, v___f_3999_, v_requestStream_3969_, v___x_4000_);
v___x_4002_ = lean_apply_1(v___x_3032__overap_4001_, lean_box(0));
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = 0;
v___x_4005_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4003_, v___x_4004_, v___x_4002_, v___f_3994_);
return v___x_4005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4009_, lean_object* v_connectionContext_4010_, lean_object* v_state_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4009_, v_connectionContext_4010_, v_state_4011_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4014_, lean_object* v_00_u03b2_4015_, lean_object* v_inst_4016_, lean_object* v_socket_4017_, lean_object* v_connectionContext_4018_, lean_object* v_state_4019_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4017_, v_connectionContext_4018_, v_state_4019_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4022_, lean_object* v_00_u03b2_4023_, lean_object* v_inst_4024_, lean_object* v_socket_4025_, lean_object* v_connectionContext_4026_, lean_object* v_state_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4022_, v_00_u03b2_4023_, v_inst_4024_, v_socket_4025_, v_connectionContext_4026_, v_state_4027_);
lean_dec_ref(v_inst_4024_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4030_){
_start:
{
if (lean_obj_tag(v_x_4030_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4040_; 
v_a_4032_ = lean_ctor_get(v_x_4030_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_x_4030_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4034_ = v_x_4030_;
v_isShared_4035_ = v_isSharedCheck_4040_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v_x_4030_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4040_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4059_; 
v_a_4041_ = lean_ctor_get(v_x_4030_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_x_4030_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4043_ = v_x_4030_;
v_isShared_4044_ = v_isSharedCheck_4059_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v_x_4030_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4059_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v_snd_4045_; uint8_t v___x_4046_; 
v_snd_4045_ = lean_ctor_get(v_a_4041_, 1);
v___x_4046_ = lean_unbox(v_snd_4045_);
if (v___x_4046_ == 0)
{
lean_object* v_fst_4047_; lean_object* v___x_4048_; lean_object* v___x_4050_; 
v_fst_4047_ = lean_ctor_get(v_a_4041_, 0);
lean_inc(v_fst_4047_);
lean_dec(v_a_4041_);
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v_fst_4047_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4048_);
v___x_4050_ = v___x_4043_;
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
else
{
lean_object* v_fst_4053_; lean_object* v___x_4054_; lean_object* v___x_4056_; 
v_fst_4053_ = lean_ctor_get(v_a_4041_, 0);
lean_inc(v_fst_4053_);
lean_dec(v_a_4041_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_fst_4053_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4054_);
v___x_4056_ = v___x_4043_;
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4063_){
_start:
{
if (lean_obj_tag(v_x_4063_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4073_; 
v_a_4065_ = lean_ctor_get(v_x_4063_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_x_4063_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4067_ = v_x_4063_;
v_isShared_4068_ = v_isSharedCheck_4073_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v_x_4063_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4073_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
return v___x_4071_;
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4083_; 
v_a_4074_ = lean_ctor_get(v_x_4063_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_x_4063_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4076_ = v_x_4063_;
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v_x_4063_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_a_4074_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4078_);
v___x_4080_ = v___x_4076_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4078_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4084_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
v_a_4093_ = lean_ctor_get(v_x_4091_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_x_4091_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4095_ = v_x_4091_;
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v_x_4091_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
}
else
{
lean_object* v___x_4102_; 
lean_dec_ref_known(v_x_4091_, 1);
v___x_4102_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___closed__1));
return v___x_4102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4103_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_onFailure_4106_, lean_object* v_handler_4107_, lean_object* v___f_4108_, lean_object* v_x_4109_){
_start:
{
if (lean_obj_tag(v_x_4109_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; 
v_a_4111_ = lean_ctor_get(v_x_4109_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v_x_4109_, 1);
v___x_4112_ = lean_apply_3(v_onFailure_4106_, v_handler_4107_, v_a_4111_, lean_box(0));
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = 0;
v___x_4115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4113_, v___x_4114_, v___x_4112_, v___f_4108_);
return v___x_4115_;
}
else
{
lean_object* v___x_4116_; 
lean_dec_ref(v___f_4108_);
lean_dec(v_handler_4107_);
lean_dec_ref(v_onFailure_4106_);
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_x_4109_);
return v___x_4116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_onFailure_4117_, lean_object* v_handler_4118_, lean_object* v___f_4119_, lean_object* v_x_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_onFailure_4117_, v_handler_4118_, v___f_4119_, v_x_4120_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4123_, lean_object* v_socket_4124_, lean_object* v_____r_4125_){
_start:
{
lean_object* v_val_4128_; lean_object* v_close_4130_; lean_object* v___x_4131_; 
v_close_4130_ = lean_ctor_get(v_inst_4123_, 3);
lean_inc_ref(v_close_4130_);
lean_dec_ref(v_inst_4123_);
v___x_4131_ = lean_apply_2(v_close_4130_, v_socket_4124_, lean_box(0));
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4131_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 1);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
v_val_4128_ = v___x_4137_;
goto v___jp_4127_;
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
v_a_4140_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4131_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4131_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
lean_ctor_set_tag(v___x_4142_, 0);
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
v_val_4128_ = v___x_4145_;
goto v___jp_4127_;
}
}
}
v___jp_4127_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_val_4128_);
return v___x_4129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4148_, lean_object* v_socket_4149_, lean_object* v_____r_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4148_, v_socket_4149_, v_____r_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4153_, lean_object* v_x_4154_){
_start:
{
if (lean_obj_tag(v_x_4154_) == 0)
{
lean_object* v___x_4156_; 
lean_dec_ref(v___f_4153_);
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v_x_4154_);
return v___x_4156_;
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4158_; 
v_a_4157_ = lean_ctor_get(v_x_4154_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v_x_4154_, 1);
v___x_4158_ = lean_apply_2(v___f_4153_, v_a_4157_, lean_box(0));
return v___x_4158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4159_, lean_object* v_x_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4159_, v_x_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4163_, lean_object* v_val_4164_, lean_object* v___f_4165_, lean_object* v___f_4166_, lean_object* v_x_4167_){
_start:
{
if (lean_obj_tag(v_x_4167_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v___f_4166_);
lean_dec_ref(v___f_4165_);
lean_dec(v_val_4164_);
lean_dec_ref(v_close_4163_);
v_a_4169_ = lean_ctor_get(v_x_4167_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_x_4167_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4171_ = v_x_4167_;
v_isShared_4172_ = v_isSharedCheck_4177_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v_x_4167_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4177_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4169_);
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
}
else
{
lean_object* v_a_4178_; uint8_t v___x_4179_; 
v_a_4178_ = lean_ctor_get(v_x_4167_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v_x_4167_, 1);
v___x_4179_ = lean_unbox(v_a_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v___f_4166_);
v___x_4180_ = lean_apply_2(v_close_4163_, v_val_4164_, lean_box(0));
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = lean_unbox(v_a_4178_);
lean_dec(v_a_4178_);
v___x_4183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4181_, v___x_4182_, v___x_4180_, v___f_4165_);
return v___x_4183_;
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec(v_a_4178_);
lean_dec_ref(v___f_4165_);
lean_dec(v_val_4164_);
lean_dec_ref(v_close_4163_);
v___x_4184_ = lean_box(0);
v___x_4185_ = lean_apply_2(v___f_4166_, v___x_4184_, lean_box(0));
return v___x_4185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4186_, lean_object* v_val_4187_, lean_object* v___f_4188_, lean_object* v___f_4189_, lean_object* v_x_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4186_, v_val_4187_, v___f_4188_, v___f_4189_, v_x_4190_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4193_, lean_object* v_responseBodyInstance_4194_, lean_object* v___f_4195_, lean_object* v___f_4196_, lean_object* v_____r_4197_){
_start:
{
if (lean_obj_tag(v_respStream_4193_) == 1)
{
lean_object* v_val_4199_; lean_object* v_close_4200_; lean_object* v_isClosed_4201_; lean_object* v___x_4202_; lean_object* v___f_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; 
v_val_4199_ = lean_ctor_get(v_respStream_4193_, 0);
lean_inc_n(v_val_4199_, 2);
lean_dec_ref_known(v_respStream_4193_, 1);
v_close_4200_ = lean_ctor_get(v_responseBodyInstance_4194_, 1);
lean_inc_ref(v_close_4200_);
v_isClosed_4201_ = lean_ctor_get(v_responseBodyInstance_4194_, 2);
lean_inc_ref(v_isClosed_4201_);
lean_dec_ref(v_responseBodyInstance_4194_);
v___x_4202_ = lean_apply_2(v_isClosed_4201_, v_val_4199_, lean_box(0));
v___f_4203_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4203_, 0, v_close_4200_);
lean_closure_set(v___f_4203_, 1, v_val_4199_);
lean_closure_set(v___f_4203_, 2, v___f_4195_);
lean_closure_set(v___f_4203_, 3, v___f_4196_);
v___x_4204_ = lean_unsigned_to_nat(0u);
v___x_4205_ = 0;
v___x_4206_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4204_, v___x_4205_, v___x_4202_, v___f_4203_);
return v___x_4206_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec_ref(v___f_4195_);
lean_dec_ref(v_responseBodyInstance_4194_);
lean_dec(v_respStream_4193_);
v___x_4207_ = lean_box(0);
v___x_4208_ = lean_apply_2(v___f_4196_, v___x_4207_, lean_box(0));
return v___x_4208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4209_, lean_object* v_responseBodyInstance_4210_, lean_object* v___f_4211_, lean_object* v___f_4212_, lean_object* v_____r_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4209_, v_responseBodyInstance_4210_, v___f_4211_, v___f_4212_, v_____r_4213_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4216_, lean_object* v___f_4217_, lean_object* v___f_4218_, lean_object* v_x_4219_){
_start:
{
if (lean_obj_tag(v_x_4219_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref(v___f_4218_);
lean_dec_ref(v___f_4217_);
lean_dec_ref(v_requestStream_4216_);
v_a_4221_ = lean_ctor_get(v_x_4219_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v_x_4219_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4223_ = v_x_4219_;
v_isShared_4224_ = v_isSharedCheck_4229_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v_x_4219_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4229_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
return v___x_4227_;
}
}
}
else
{
lean_object* v_a_4230_; uint8_t v___x_4231_; 
v_a_4230_ = lean_ctor_get(v_x_4219_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v_x_4219_, 1);
v___x_4231_ = lean_unbox(v_a_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; 
lean_dec_ref(v___f_4218_);
v___x_4232_ = l_Std_Http_Body_Stream_close(v_requestStream_4216_);
v___x_4233_ = lean_unsigned_to_nat(0u);
v___x_4234_ = lean_unbox(v_a_4230_);
lean_dec(v_a_4230_);
v___x_4235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4233_, v___x_4234_, v___x_4232_, v___f_4217_);
return v___x_4235_;
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_dec(v_a_4230_);
lean_dec_ref(v___f_4217_);
lean_dec_ref(v_requestStream_4216_);
v___x_4236_ = lean_box(0);
v___x_4237_ = lean_apply_2(v___f_4218_, v___x_4236_, lean_box(0));
return v___x_4237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4238_, lean_object* v___f_4239_, lean_object* v___f_4240_, lean_object* v_x_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4238_, v___f_4239_, v___f_4240_, v_x_4241_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4244_, lean_object* v_responseBodyInstance_4245_, lean_object* v___f_4246_, lean_object* v___f_4247_, lean_object* v_x_4248_){
_start:
{
if (lean_obj_tag(v_x_4248_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4258_; 
lean_dec_ref(v___f_4247_);
lean_dec_ref(v___f_4246_);
lean_dec_ref(v_responseBodyInstance_4245_);
lean_dec_ref(v___f_4244_);
v_a_4250_ = lean_ctor_get(v_x_4248_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v_x_4248_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4252_ = v_x_4248_;
v_isShared_4253_ = v_isSharedCheck_4258_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v_x_4248_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4258_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4256_; 
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v_requestStream_4260_; lean_object* v_respStream_4261_; lean_object* v___x_4262_; lean_object* v___f_4263_; lean_object* v___f_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_5029__overap_4267_; lean_object* v___x_4268_; lean_object* v___f_4269_; lean_object* v___f_4270_; lean_object* v___f_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; lean_object* v___x_4274_; 
v_a_4259_ = lean_ctor_get(v_x_4248_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v_x_4248_, 1);
v_requestStream_4260_ = lean_ctor_get(v_a_4259_, 1);
lean_inc_ref_n(v_requestStream_4260_, 2);
v_respStream_4261_ = lean_ctor_get(v_a_4259_, 6);
lean_inc(v_respStream_4261_);
lean_dec(v_a_4259_);
v___x_4262_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4263_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4264_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4265_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4266_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4266_, 0, lean_box(0));
lean_closure_set(v___x_4266_, 1, lean_box(0));
lean_closure_set(v___x_4266_, 2, v___x_4262_);
lean_closure_set(v___x_4266_, 3, lean_box(0));
lean_closure_set(v___x_4266_, 4, lean_box(0));
lean_closure_set(v___x_4266_, 5, v___x_4265_);
lean_closure_set(v___x_4266_, 6, v___f_4244_);
v___x_5029__overap_4267_ = l_Std_Mutex_atomically___redArg(v___x_4262_, v___f_4263_, v___f_4264_, v_requestStream_4260_, v___x_4266_);
v___x_4268_ = lean_apply_1(v___x_5029__overap_4267_, lean_box(0));
v___f_4269_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4269_, 0, v_respStream_4261_);
lean_closure_set(v___f_4269_, 1, v_responseBodyInstance_4245_);
lean_closure_set(v___f_4269_, 2, v___f_4246_);
lean_closure_set(v___f_4269_, 3, v___f_4247_);
lean_inc_ref(v___f_4269_);
v___f_4270_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4270_, 0, v___f_4269_);
v___f_4271_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4271_, 0, v_requestStream_4260_);
lean_closure_set(v___f_4271_, 1, v___f_4270_);
lean_closure_set(v___f_4271_, 2, v___f_4269_);
v___x_4272_ = lean_unsigned_to_nat(0u);
v___x_4273_ = 0;
v___x_4274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4272_, v___x_4273_, v___x_4268_, v___f_4271_);
return v___x_4274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4275_, lean_object* v_responseBodyInstance_4276_, lean_object* v___f_4277_, lean_object* v___f_4278_, lean_object* v_x_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4275_, v_responseBodyInstance_4276_, v___f_4277_, v___f_4278_, v_x_4279_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4282_, lean_object* v_responseBodyInstance_4283_, lean_object* v_handler_4284_, lean_object* v_config_4285_, lean_object* v___x_4286_, uint8_t v___x_4287_, lean_object* v___f_4288_, lean_object* v_x_4289_){
_start:
{
if (lean_obj_tag(v_x_4289_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v___f_4288_);
lean_dec_ref(v___x_4286_);
lean_dec_ref(v_config_4285_);
lean_dec(v_handler_4284_);
lean_dec_ref(v_responseBodyInstance_4283_);
lean_dec_ref(v_h_4282_);
v_a_4291_ = lean_ctor_get(v_x_4289_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_x_4289_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4293_ = v_x_4289_;
v_isShared_4294_ = v_isSharedCheck_4299_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v_x_4289_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4299_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4296_);
return v___x_4297_;
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v_a_4300_ = lean_ctor_get(v_x_4289_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v_x_4289_, 1);
v___x_4301_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4282_, v_responseBodyInstance_4283_, v_handler_4284_, v_config_4285_, v_a_4300_, v___x_4286_);
v___x_4302_ = lean_unsigned_to_nat(0u);
v___x_4303_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4302_, v___x_4287_, v___x_4301_, v___f_4288_);
return v___x_4303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4304_, lean_object* v_responseBodyInstance_4305_, lean_object* v_handler_4306_, lean_object* v_config_4307_, lean_object* v___x_4308_, lean_object* v___x_4309_, lean_object* v___f_4310_, lean_object* v_x_4311_, lean_object* v___y_4312_){
_start:
{
uint8_t v___x_5703__boxed_4313_; lean_object* v_res_4314_; 
v___x_5703__boxed_4313_ = lean_unbox(v___x_4309_);
v_res_4314_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4304_, v_responseBodyInstance_4305_, v_handler_4306_, v_config_4307_, v___x_4308_, v___x_5703__boxed_4313_, v___f_4310_, v_x_4311_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4315_, lean_object* v_h_4316_, lean_object* v_responseBodyInstance_4317_, lean_object* v_config_4318_, lean_object* v_handler_4319_, uint8_t v___x_4320_, lean_object* v___f_4321_, lean_object* v_x_4322_){
_start:
{
if (lean_obj_tag(v_x_4322_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v___f_4321_);
lean_dec(v_handler_4319_);
lean_dec_ref(v_config_4318_);
lean_dec_ref(v_responseBodyInstance_4317_);
lean_dec_ref(v_h_4316_);
lean_dec_ref(v_inst_4315_);
v_a_4324_ = lean_ctor_get(v_x_4322_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v_x_4322_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4326_ = v_x_4322_;
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v_x_4322_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
return v___x_4330_;
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v_a_4333_ = lean_ctor_get(v_x_4322_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v_x_4322_, 1);
v___x_4334_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4315_, v_h_4316_, v_responseBodyInstance_4317_, v_config_4318_, v_handler_4319_, v_a_4333_);
v___x_4335_ = lean_unsigned_to_nat(0u);
v___x_4336_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4335_, v___x_4320_, v___x_4334_, v___f_4321_);
return v___x_4336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4337_, lean_object* v_h_4338_, lean_object* v_responseBodyInstance_4339_, lean_object* v_config_4340_, lean_object* v_handler_4341_, lean_object* v___x_4342_, lean_object* v___f_4343_, lean_object* v_x_4344_, lean_object* v___y_4345_){
_start:
{
uint8_t v___x_5744__boxed_4346_; lean_object* v_res_4347_; 
v___x_5744__boxed_4346_ = lean_unbox(v___x_4342_);
v_res_4347_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4337_, v_h_4338_, v_responseBodyInstance_4339_, v_config_4340_, v_handler_4341_, v___x_5744__boxed_4346_, v___f_4343_, v_x_4344_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4348_, lean_object* v_socket_4349_, lean_object* v_connectionContext_4350_, lean_object* v_h_4351_, lean_object* v_responseBodyInstance_4352_, lean_object* v_handler_4353_, lean_object* v_config_4354_, lean_object* v___f_4355_, lean_object* v_inst_4356_, lean_object* v_x_4357_){
_start:
{
if (lean_obj_tag(v_x_4357_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4367_; 
lean_dec_ref(v_inst_4356_);
lean_dec_ref(v___f_4355_);
lean_dec_ref(v_config_4354_);
lean_dec(v_handler_4353_);
lean_dec_ref(v_responseBodyInstance_4352_);
lean_dec_ref(v_h_4351_);
lean_dec_ref(v_connectionContext_4350_);
lean_dec(v_socket_4349_);
v_a_4359_ = lean_ctor_get(v_x_4357_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v_x_4357_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4361_ = v_x_4357_;
v_isShared_4362_ = v_isSharedCheck_4367_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v_x_4357_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4367_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
lean_object* v___x_4365_; 
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
return v___x_4365_;
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4405_; 
v_a_4368_ = lean_ctor_get(v_x_4357_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_x_4357_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4370_ = v_x_4357_;
v_isShared_4371_ = v_isSharedCheck_4405_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v_x_4357_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4405_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_machine_4378_; lean_object* v_requestStream_4379_; lean_object* v_keepAliveTimeout_4380_; lean_object* v_currentTimeout_4381_; lean_object* v_headerTimeout_4382_; lean_object* v_response_4383_; lean_object* v_respStream_4384_; uint8_t v_requiresData_4385_; lean_object* v_expectData_4386_; uint8_t v_handlerDispatched_4387_; lean_object* v_pendingHead_4388_; uint8_t v___y_4399_; 
v_machine_4378_ = lean_ctor_get(v_a_4368_, 0);
v_requestStream_4379_ = lean_ctor_get(v_a_4368_, 1);
v_keepAliveTimeout_4380_ = lean_ctor_get(v_a_4368_, 2);
v_currentTimeout_4381_ = lean_ctor_get(v_a_4368_, 3);
v_headerTimeout_4382_ = lean_ctor_get(v_a_4368_, 4);
v_response_4383_ = lean_ctor_get(v_a_4368_, 5);
v_respStream_4384_ = lean_ctor_get(v_a_4368_, 6);
v_requiresData_4385_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*9);
v_expectData_4386_ = lean_ctor_get(v_a_4368_, 7);
v_handlerDispatched_4387_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*9 + 1);
v_pendingHead_4388_ = lean_ctor_get(v_a_4368_, 8);
if (v_requiresData_4385_ == 0)
{
if (v_handlerDispatched_4387_ == 0)
{
if (lean_obj_tag(v_respStream_4384_) == 0)
{
lean_object* v_writer_4400_; lean_object* v_reader_4401_; uint8_t v_sentMessage_4402_; uint8_t v___x_4403_; 
v_writer_4400_ = lean_ctor_get(v_machine_4378_, 1);
v_reader_4401_ = lean_ctor_get(v_machine_4378_, 0);
v_sentMessage_4402_ = lean_ctor_get_uint8(v_writer_4400_, sizeof(void*)*6);
v___x_4403_ = lean_bool_not(v_sentMessage_4402_);
if (v___x_4403_ == 0)
{
v___y_4399_ = v___x_4403_;
goto v___jp_4398_;
}
else
{
lean_object* v_state_4404_; 
v_state_4404_ = lean_ctor_get(v_reader_4401_, 0);
if (lean_obj_tag(v_state_4404_) == 2)
{
v___y_4399_ = v___x_4403_;
goto v___jp_4398_;
}
else
{
lean_dec_ref(v_inst_4356_);
lean_dec_ref(v___f_4355_);
lean_dec_ref(v_config_4354_);
lean_dec(v_handler_4353_);
lean_dec_ref(v_responseBodyInstance_4352_);
lean_dec_ref(v_h_4351_);
lean_dec_ref(v_connectionContext_4350_);
lean_dec(v_socket_4349_);
goto v___jp_4372_;
}
}
}
else
{
lean_inc_ref(v_respStream_4384_);
lean_inc(v_pendingHead_4388_);
lean_inc(v_expectData_4386_);
lean_inc_ref(v_response_4383_);
lean_inc(v_headerTimeout_4382_);
lean_inc(v_currentTimeout_4381_);
lean_inc(v_keepAliveTimeout_4380_);
lean_inc_ref(v_requestStream_4379_);
lean_inc_ref(v_machine_4378_);
lean_del_object(v___x_4370_);
lean_dec(v_a_4368_);
goto v___jp_4389_;
}
}
else
{
lean_inc(v_pendingHead_4388_);
lean_inc(v_expectData_4386_);
lean_inc(v_respStream_4384_);
lean_inc_ref(v_response_4383_);
lean_inc(v_headerTimeout_4382_);
lean_inc(v_currentTimeout_4381_);
lean_inc(v_keepAliveTimeout_4380_);
lean_inc_ref(v_requestStream_4379_);
lean_inc_ref(v_machine_4378_);
lean_del_object(v___x_4370_);
lean_dec(v_a_4368_);
goto v___jp_4389_;
}
}
else
{
lean_inc(v_pendingHead_4388_);
lean_inc(v_expectData_4386_);
lean_inc(v_respStream_4384_);
lean_inc_ref(v_response_4383_);
lean_inc(v_headerTimeout_4382_);
lean_inc(v_currentTimeout_4381_);
lean_inc(v_keepAliveTimeout_4380_);
lean_inc_ref(v_requestStream_4379_);
lean_inc_ref(v_machine_4378_);
lean_del_object(v___x_4370_);
lean_dec(v_a_4368_);
goto v___jp_4389_;
}
v___jp_4372_:
{
lean_object* v___x_4373_; lean_object* v___x_4375_; 
v___x_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4373_, 0, v_a_4368_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4373_);
v___x_4375_ = v___x_4370_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
lean_object* v___x_4376_; 
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
v___jp_4389_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___f_4393_; lean_object* v___x_4394_; lean_object* v___f_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4390_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4390_, 0, v_machine_4378_);
lean_ctor_set(v___x_4390_, 1, v_requestStream_4379_);
lean_ctor_set(v___x_4390_, 2, v_keepAliveTimeout_4380_);
lean_ctor_set(v___x_4390_, 3, v_currentTimeout_4381_);
lean_ctor_set(v___x_4390_, 4, v_headerTimeout_4382_);
lean_ctor_set(v___x_4390_, 5, v_response_4383_);
lean_ctor_set(v___x_4390_, 6, v_respStream_4384_);
lean_ctor_set(v___x_4390_, 7, v_expectData_4386_);
lean_ctor_set(v___x_4390_, 8, v_pendingHead_4388_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*9, v___x_4348_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*9 + 1, v_handlerDispatched_4387_);
lean_inc_ref(v___x_4390_);
v___x_4391_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4349_, v_connectionContext_4350_, v___x_4390_);
v___x_4392_ = lean_box(v___x_4348_);
lean_inc_ref(v_config_4354_);
lean_inc(v_handler_4353_);
lean_inc_ref(v_responseBodyInstance_4352_);
lean_inc_ref(v_h_4351_);
v___f_4393_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4393_, 0, v_h_4351_);
lean_closure_set(v___f_4393_, 1, v_responseBodyInstance_4352_);
lean_closure_set(v___f_4393_, 2, v_handler_4353_);
lean_closure_set(v___f_4393_, 3, v_config_4354_);
lean_closure_set(v___f_4393_, 4, v___x_4390_);
lean_closure_set(v___f_4393_, 5, v___x_4392_);
lean_closure_set(v___f_4393_, 6, v___f_4355_);
v___x_4394_ = lean_box(v___x_4348_);
v___f_4395_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4395_, 0, v_inst_4356_);
lean_closure_set(v___f_4395_, 1, v_h_4351_);
lean_closure_set(v___f_4395_, 2, v_responseBodyInstance_4352_);
lean_closure_set(v___f_4395_, 3, v_config_4354_);
lean_closure_set(v___f_4395_, 4, v_handler_4353_);
lean_closure_set(v___f_4395_, 5, v___x_4394_);
lean_closure_set(v___f_4395_, 6, v___f_4393_);
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4396_, v___x_4348_, v___x_4391_, v___f_4395_);
return v___x_4397_;
}
v___jp_4398_:
{
if (v___y_4399_ == 0)
{
lean_dec_ref(v_inst_4356_);
lean_dec_ref(v___f_4355_);
lean_dec_ref(v_config_4354_);
lean_dec(v_handler_4353_);
lean_dec_ref(v_responseBodyInstance_4352_);
lean_dec_ref(v_h_4351_);
lean_dec_ref(v_connectionContext_4350_);
lean_dec(v_socket_4349_);
goto v___jp_4372_;
}
else
{
lean_inc(v_pendingHead_4388_);
lean_inc(v_expectData_4386_);
lean_inc(v_respStream_4384_);
lean_inc_ref(v_response_4383_);
lean_inc(v_headerTimeout_4382_);
lean_inc(v_currentTimeout_4381_);
lean_inc(v_keepAliveTimeout_4380_);
lean_inc_ref(v_requestStream_4379_);
lean_inc_ref(v_machine_4378_);
lean_del_object(v___x_4370_);
lean_dec(v_a_4368_);
goto v___jp_4389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4406_, lean_object* v_socket_4407_, lean_object* v_connectionContext_4408_, lean_object* v_h_4409_, lean_object* v_responseBodyInstance_4410_, lean_object* v_handler_4411_, lean_object* v_config_4412_, lean_object* v___f_4413_, lean_object* v_inst_4414_, lean_object* v_x_4415_, lean_object* v___y_4416_){
_start:
{
uint8_t v___x_5784__boxed_4417_; lean_object* v_res_4418_; 
v___x_5784__boxed_4417_ = lean_unbox(v___x_4406_);
v_res_4418_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5784__boxed_4417_, v_socket_4407_, v_connectionContext_4408_, v_h_4409_, v_responseBodyInstance_4410_, v_handler_4411_, v_config_4412_, v___f_4413_, v_inst_4414_, v_x_4415_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4419_, lean_object* v_handler_4420_, lean_object* v_extensions_4421_, lean_object* v_connectionContext_4422_, uint8_t v___x_4423_, lean_object* v___f_4424_, lean_object* v_x_4425_){
_start:
{
if (lean_obj_tag(v_x_4425_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref(v___f_4424_);
lean_dec_ref(v_connectionContext_4422_);
lean_dec(v_extensions_4421_);
lean_dec(v_handler_4420_);
lean_dec_ref(v_h_4419_);
v_a_4427_ = lean_ctor_get(v_x_4425_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v_x_4425_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4429_ = v_x_4425_;
v_isShared_4430_ = v_isSharedCheck_4435_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v_x_4425_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4435_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
return v___x_4433_;
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_a_4436_ = lean_ctor_get(v_x_4425_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v_x_4425_, 1);
v___x_4437_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4419_, v_handler_4420_, v_extensions_4421_, v_connectionContext_4422_, v_a_4436_);
v___x_4438_ = lean_unsigned_to_nat(0u);
v___x_4439_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4438_, v___x_4423_, v___x_4437_, v___f_4424_);
return v___x_4439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4440_, lean_object* v_handler_4441_, lean_object* v_extensions_4442_, lean_object* v_connectionContext_4443_, lean_object* v___x_4444_, lean_object* v___f_4445_, lean_object* v_x_4446_, lean_object* v___y_4447_){
_start:
{
uint8_t v___x_5865__boxed_4448_; lean_object* v_res_4449_; 
v___x_5865__boxed_4448_ = lean_unbox(v___x_4444_);
v_res_4449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4440_, v_handler_4441_, v_extensions_4442_, v_connectionContext_4443_, v___x_5865__boxed_4448_, v___f_4445_, v_x_4446_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4450_, lean_object* v_responseBodyInstance_4451_, lean_object* v_handler_4452_, lean_object* v_config_4453_, lean_object* v_connectionContext_4454_, lean_object* v_events_4455_, lean_object* v___x_4456_, uint8_t v___x_4457_, lean_object* v___f_4458_, lean_object* v_____r_4459_){
_start:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4461_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4450_, v_responseBodyInstance_4451_, v_handler_4452_, v_config_4453_, v_connectionContext_4454_, v_events_4455_, v___x_4456_);
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4462_, v___x_4457_, v___x_4461_, v___f_4458_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4464_, lean_object* v_responseBodyInstance_4465_, lean_object* v_handler_4466_, lean_object* v_config_4467_, lean_object* v_connectionContext_4468_, lean_object* v_events_4469_, lean_object* v___x_4470_, lean_object* v___x_4471_, lean_object* v___f_4472_, lean_object* v_____r_4473_, lean_object* v___y_4474_){
_start:
{
uint8_t v___x_5904__boxed_4475_; lean_object* v_res_4476_; 
v___x_5904__boxed_4475_ = lean_unbox(v___x_4471_);
v_res_4476_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4464_, v_responseBodyInstance_4465_, v_handler_4466_, v_config_4467_, v_connectionContext_4468_, v_events_4469_, v___x_4470_, v___x_5904__boxed_4475_, v___f_4472_, v_____r_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4477_, lean_object* v___f_4478_, lean_object* v_x_4479_){
_start:
{
if (lean_obj_tag(v_x_4479_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref(v___f_4478_);
lean_dec_ref(v___x_4477_);
v_a_4481_ = lean_ctor_get(v_x_4479_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_x_4479_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4483_ = v_x_4479_;
v_isShared_4484_ = v_isSharedCheck_4489_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v_x_4479_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4489_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; 
v___x_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
return v___x_4487_;
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4501_; 
v_a_4490_ = lean_ctor_get(v_x_4479_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_x_4479_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4492_ = v_x_4479_;
v_isShared_4493_ = v_isSharedCheck_4501_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v_x_4479_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4501_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
if (lean_obj_tag(v_a_4490_) == 0)
{
lean_object* v___x_4494_; lean_object* v___x_4496_; 
lean_dec_ref(v___f_4478_);
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4477_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4494_);
v___x_4496_ = v___x_4492_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
else
{
lean_object* v_val_4499_; lean_object* v___x_4500_; 
lean_del_object(v___x_4492_);
lean_dec_ref(v___x_4477_);
v_val_4499_ = lean_ctor_get(v_a_4490_, 0);
lean_inc(v_val_4499_);
lean_dec_ref_known(v_a_4490_, 1);
v___x_4500_ = lean_apply_2(v___f_4478_, v_val_4499_, lean_box(0));
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4502_, lean_object* v___f_4503_, lean_object* v_x_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4502_, v___f_4503_, v_x_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4507_, lean_object* v_responseBodyInstance_4508_, lean_object* v_handler_4509_, lean_object* v_config_4510_, lean_object* v_connectionContext_4511_, uint8_t v___x_4512_, lean_object* v___f_4513_, lean_object* v_inst_4514_, lean_object* v_socket_4515_, lean_object* v___f_4516_, lean_object* v___f_4517_, lean_object* v_x_4518_, lean_object* v_____s_4519_){
_start:
{
lean_object* v_machine_4521_; lean_object* v_reader_4522_; lean_object* v_requestStream_4523_; lean_object* v_keepAliveTimeout_4524_; lean_object* v_currentTimeout_4525_; lean_object* v_headerTimeout_4526_; lean_object* v_response_4527_; lean_object* v_respStream_4528_; uint8_t v_requiresData_4529_; lean_object* v_expectData_4530_; uint8_t v_handlerDispatched_4531_; lean_object* v_pendingHead_4532_; lean_object* v_writer_4533_; lean_object* v_state_4534_; uint8_t v___x_4535_; 
v_machine_4521_ = lean_ctor_get(v_____s_4519_, 0);
v_reader_4522_ = lean_ctor_get(v_machine_4521_, 0);
v_requestStream_4523_ = lean_ctor_get(v_____s_4519_, 1);
v_keepAliveTimeout_4524_ = lean_ctor_get(v_____s_4519_, 2);
v_currentTimeout_4525_ = lean_ctor_get(v_____s_4519_, 3);
v_headerTimeout_4526_ = lean_ctor_get(v_____s_4519_, 4);
v_response_4527_ = lean_ctor_get(v_____s_4519_, 5);
v_respStream_4528_ = lean_ctor_get(v_____s_4519_, 6);
v_requiresData_4529_ = lean_ctor_get_uint8(v_____s_4519_, sizeof(void*)*9);
v_expectData_4530_ = lean_ctor_get(v_____s_4519_, 7);
v_handlerDispatched_4531_ = lean_ctor_get_uint8(v_____s_4519_, sizeof(void*)*9 + 1);
v_pendingHead_4532_ = lean_ctor_get(v_____s_4519_, 8);
v_writer_4533_ = lean_ctor_get(v_machine_4521_, 1);
v_state_4534_ = lean_ctor_get(v_reader_4522_, 0);
v___x_4535_ = 0;
if (lean_obj_tag(v_state_4534_) == 6)
{
lean_object* v_state_4557_; 
v_state_4557_ = lean_ctor_get(v_writer_4533_, 2);
if (lean_obj_tag(v_state_4557_) == 7)
{
lean_object* v_outputData_4558_; lean_object* v_size_4559_; lean_object* v___x_4560_; uint8_t v___x_4561_; 
v_outputData_4558_ = lean_ctor_get(v_writer_4533_, 1);
v_size_4559_ = lean_ctor_get(v_outputData_4558_, 1);
v___x_4560_ = lean_unsigned_to_nat(0u);
v___x_4561_ = lean_nat_dec_eq(v_size_4559_, v___x_4560_);
if (v___x_4561_ == 0)
{
lean_inc(v_pendingHead_4532_);
lean_inc(v_expectData_4530_);
lean_inc(v_respStream_4528_);
lean_inc_ref(v_response_4527_);
lean_inc(v_headerTimeout_4526_);
lean_inc(v_currentTimeout_4525_);
lean_inc(v_keepAliveTimeout_4524_);
lean_inc_ref(v_requestStream_4523_);
lean_inc_ref(v_machine_4521_);
lean_dec_ref(v_____s_4519_);
goto v___jp_4536_;
}
else
{
if (v___x_4561_ == 0)
{
lean_inc(v_pendingHead_4532_);
lean_inc(v_expectData_4530_);
lean_inc(v_respStream_4528_);
lean_inc_ref(v_response_4527_);
lean_inc(v_headerTimeout_4526_);
lean_inc(v_currentTimeout_4525_);
lean_inc(v_keepAliveTimeout_4524_);
lean_inc_ref(v_requestStream_4523_);
lean_inc_ref(v_machine_4521_);
lean_dec_ref(v_____s_4519_);
goto v___jp_4536_;
}
else
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
lean_dec_ref(v___f_4517_);
lean_dec_ref(v___f_4516_);
lean_dec(v_socket_4515_);
lean_dec_ref(v_inst_4514_);
lean_dec_ref(v___f_4513_);
lean_dec_ref(v_connectionContext_4511_);
lean_dec_ref(v_config_4510_);
lean_dec(v_handler_4509_);
lean_dec_ref(v_responseBodyInstance_4508_);
lean_dec_ref(v_h_4507_);
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v_____s_4519_);
v___x_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
}
}
else
{
lean_inc(v_pendingHead_4532_);
lean_inc(v_expectData_4530_);
lean_inc(v_respStream_4528_);
lean_inc_ref(v_response_4527_);
lean_inc(v_headerTimeout_4526_);
lean_inc(v_currentTimeout_4525_);
lean_inc(v_keepAliveTimeout_4524_);
lean_inc_ref(v_requestStream_4523_);
lean_inc_ref(v_machine_4521_);
lean_dec_ref(v_____s_4519_);
goto v___jp_4536_;
}
}
else
{
lean_inc(v_pendingHead_4532_);
lean_inc(v_expectData_4530_);
lean_inc(v_respStream_4528_);
lean_inc_ref(v_response_4527_);
lean_inc(v_headerTimeout_4526_);
lean_inc(v_currentTimeout_4525_);
lean_inc(v_keepAliveTimeout_4524_);
lean_inc_ref(v_requestStream_4523_);
lean_inc_ref(v_machine_4521_);
lean_dec_ref(v_____s_4519_);
goto v___jp_4536_;
}
v___jp_4536_:
{
lean_object* v___x_4537_; lean_object* v_snd_4538_; lean_object* v_output_4539_; lean_object* v_fst_4540_; lean_object* v_events_4541_; lean_object* v_data_4542_; lean_object* v_size_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___f_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4537_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4535_, v_machine_4521_);
v_snd_4538_ = lean_ctor_get(v___x_4537_, 1);
lean_inc(v_snd_4538_);
v_output_4539_ = lean_ctor_get(v_snd_4538_, 1);
lean_inc_ref(v_output_4539_);
v_fst_4540_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_fst_4540_);
lean_dec_ref(v___x_4537_);
v_events_4541_ = lean_ctor_get(v_snd_4538_, 0);
lean_inc_ref_n(v_events_4541_, 2);
lean_dec(v_snd_4538_);
v_data_4542_ = lean_ctor_get(v_output_4539_, 0);
lean_inc_ref(v_data_4542_);
v_size_4543_ = lean_ctor_get(v_output_4539_, 1);
lean_inc(v_size_4543_);
lean_dec_ref(v_output_4539_);
v___x_4544_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4544_, 0, v_fst_4540_);
lean_ctor_set(v___x_4544_, 1, v_requestStream_4523_);
lean_ctor_set(v___x_4544_, 2, v_keepAliveTimeout_4524_);
lean_ctor_set(v___x_4544_, 3, v_currentTimeout_4525_);
lean_ctor_set(v___x_4544_, 4, v_headerTimeout_4526_);
lean_ctor_set(v___x_4544_, 5, v_response_4527_);
lean_ctor_set(v___x_4544_, 6, v_respStream_4528_);
lean_ctor_set(v___x_4544_, 7, v_expectData_4530_);
lean_ctor_set(v___x_4544_, 8, v_pendingHead_4532_);
lean_ctor_set_uint8(v___x_4544_, sizeof(void*)*9, v_requiresData_4529_);
lean_ctor_set_uint8(v___x_4544_, sizeof(void*)*9 + 1, v_handlerDispatched_4531_);
v___x_4545_ = lean_box(v___x_4512_);
lean_inc_ref(v___f_4513_);
lean_inc_ref(v___x_4544_);
lean_inc_ref(v_connectionContext_4511_);
lean_inc_ref(v_config_4510_);
lean_inc(v_handler_4509_);
lean_inc_ref(v_responseBodyInstance_4508_);
lean_inc_ref(v_h_4507_);
v___f_4546_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4546_, 0, v_h_4507_);
lean_closure_set(v___f_4546_, 1, v_responseBodyInstance_4508_);
lean_closure_set(v___f_4546_, 2, v_handler_4509_);
lean_closure_set(v___f_4546_, 3, v_config_4510_);
lean_closure_set(v___f_4546_, 4, v_connectionContext_4511_);
lean_closure_set(v___f_4546_, 5, v_events_4541_);
lean_closure_set(v___f_4546_, 6, v___x_4544_);
lean_closure_set(v___f_4546_, 7, v___x_4545_);
lean_closure_set(v___f_4546_, 8, v___f_4513_);
v___x_4547_ = lean_unsigned_to_nat(0u);
v___x_4548_ = lean_nat_dec_lt(v___x_4547_, v_size_4543_);
lean_dec(v_size_4543_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
lean_dec_ref(v___f_4546_);
lean_dec_ref(v_data_4542_);
lean_dec_ref(v___f_4517_);
lean_dec_ref(v___f_4516_);
lean_dec(v_socket_4515_);
lean_dec_ref(v_inst_4514_);
v___x_4549_ = lean_box(0);
v___x_4550_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4507_, v_responseBodyInstance_4508_, v_handler_4509_, v_config_4510_, v_connectionContext_4511_, v_events_4541_, v___x_4544_, v___x_4512_, v___f_4513_, v___x_4549_);
return v___x_4550_;
}
else
{
lean_object* v_sendAll_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___f_4555_; lean_object* v___x_4556_; 
lean_dec_ref(v_events_4541_);
lean_dec_ref(v___f_4513_);
lean_dec_ref(v_connectionContext_4511_);
lean_dec_ref(v_config_4510_);
lean_dec(v_handler_4509_);
lean_dec_ref(v_responseBodyInstance_4508_);
lean_dec_ref(v_h_4507_);
v_sendAll_4551_ = lean_ctor_get(v_inst_4514_, 1);
lean_inc_ref(v_sendAll_4551_);
lean_dec_ref(v_inst_4514_);
v___x_4552_ = lean_apply_3(v_sendAll_4551_, v_socket_4515_, v_data_4542_, lean_box(0));
v___x_4553_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4547_, v___x_4512_, v___x_4552_, v___f_4516_);
v___x_4554_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4547_, v___x_4512_, v___x_4553_, v___f_4517_);
v___f_4555_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4555_, 0, v___x_4544_);
lean_closure_set(v___f_4555_, 1, v___f_4546_);
v___x_4556_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4547_, v___x_4512_, v___x_4554_, v___f_4555_);
return v___x_4556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4565_, lean_object* v_responseBodyInstance_4566_, lean_object* v_handler_4567_, lean_object* v_config_4568_, lean_object* v_connectionContext_4569_, lean_object* v___x_4570_, lean_object* v___f_4571_, lean_object* v_inst_4572_, lean_object* v_socket_4573_, lean_object* v___f_4574_, lean_object* v___f_4575_, lean_object* v_x_4576_, lean_object* v_____s_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_5978__boxed_4579_; lean_object* v_res_4580_; 
v___x_5978__boxed_4579_ = lean_unbox(v___x_4570_);
v_res_4580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4565_, v_responseBodyInstance_4566_, v_handler_4567_, v_config_4568_, v_connectionContext_4569_, v___x_5978__boxed_4579_, v___f_4571_, v_inst_4572_, v_socket_4573_, v___f_4574_, v___f_4575_, v_x_4576_, v_____s_4577_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4581_, lean_object* v_x_4582_){
_start:
{
if (lean_obj_tag(v_x_4582_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4592_; 
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
lean_object* v___x_4593_; lean_object* v___x_4594_; 
lean_dec_ref_known(v_x_4582_, 1);
v___x_4593_ = l_IO_Promise_result_x21___redArg(v_a_4581_);
v___x_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4593_);
return v___x_4594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4595_, lean_object* v_x_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4595_, v_x_4596_);
lean_dec(v_a_4595_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4599_, lean_object* v___x_4600_, lean_object* v___x_4601_, uint8_t v___x_4602_, lean_object* v_x_4603_){
_start:
{
if (lean_obj_tag(v_x_4603_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v___x_4601_);
lean_dec(v___x_4600_);
lean_dec_ref(v___f_4599_);
v_a_4605_ = lean_ctor_get(v_x_4603_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_x_4603_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4607_ = v_x_4603_;
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v_x_4603_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4611_; 
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
return v___x_4611_;
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4625_; 
v_a_4614_ = lean_ctor_get(v_x_4603_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v_x_4603_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4616_ = v_x_4603_;
v_isShared_4617_ = v_isSharedCheck_4625_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v_x_4603_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4625_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4618_; lean_object* v___f_4619_; lean_object* v___x_4621_; 
lean_inc(v_a_4614_);
lean_inc(v___x_4600_);
v___x_4618_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4599_, v___x_4600_, v_a_4614_, v___x_4601_);
v___f_4619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4619_, 0, v_a_4614_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4618_);
v___x_4621_ = v___x_4616_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4618_);
v___x_4621_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
v___x_4623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4600_, v___x_4602_, v___x_4622_, v___f_4619_);
return v___x_4623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4626_, lean_object* v___x_4627_, lean_object* v___x_4628_, lean_object* v___x_4629_, lean_object* v_x_4630_, lean_object* v___y_4631_){
_start:
{
uint8_t v___x_6081__boxed_4632_; lean_object* v_res_4633_; 
v___x_6081__boxed_4632_ = lean_unbox(v___x_4629_);
v_res_4633_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4626_, v___x_4627_, v___x_4628_, v___x_6081__boxed_4632_, v_x_4630_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4634_, lean_object* v_machine_4635_, lean_object* v_a_4636_, lean_object* v___x_4637_, lean_object* v_socket_4638_, lean_object* v_connectionContext_4639_, lean_object* v_h_4640_, lean_object* v_responseBodyInstance_4641_, lean_object* v_handler_4642_, lean_object* v___f_4643_, lean_object* v_inst_4644_, lean_object* v_extensions_4645_, lean_object* v___f_4646_, lean_object* v___f_4647_, lean_object* v___f_4648_, lean_object* v_x_4649_){
_start:
{
if (lean_obj_tag(v_x_4649_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4659_; 
lean_dec_ref(v___f_4648_);
lean_dec_ref(v___f_4647_);
lean_dec_ref(v___f_4646_);
lean_dec(v_extensions_4645_);
lean_dec_ref(v_inst_4644_);
lean_dec_ref(v___f_4643_);
lean_dec(v_handler_4642_);
lean_dec_ref(v_responseBodyInstance_4641_);
lean_dec_ref(v_h_4640_);
lean_dec_ref(v_connectionContext_4639_);
lean_dec(v_socket_4638_);
lean_dec(v___x_4637_);
lean_dec_ref(v_a_4636_);
lean_dec_ref(v_machine_4635_);
lean_dec_ref(v_config_4634_);
v_a_4651_ = lean_ctor_get(v_x_4649_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v_x_4649_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4653_ = v_x_4649_;
v_isShared_4654_ = v_isSharedCheck_4659_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v_x_4649_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4659_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4685_; 
v_a_4660_ = lean_ctor_get(v_x_4649_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v_x_4649_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4662_ = v_x_4649_;
v_isShared_4663_ = v_isSharedCheck_4685_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v_x_4649_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4685_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v_keepAliveTimeout_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___f_4671_; lean_object* v___x_4672_; lean_object* v___f_4673_; lean_object* v___x_4674_; lean_object* v___f_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___f_4678_; lean_object* v___x_4680_; 
v_keepAliveTimeout_4664_ = lean_ctor_get(v_config_4634_, 5);
lean_inc_n(v_keepAliveTimeout_4664_, 2);
v___x_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4665_, 0, v_keepAliveTimeout_4664_);
v___x_4666_ = lean_box(0);
v___x_4667_ = 0;
v___x_4668_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4668_, 0, v_machine_4635_);
lean_ctor_set(v___x_4668_, 1, v_a_4636_);
lean_ctor_set(v___x_4668_, 2, v___x_4665_);
lean_ctor_set(v___x_4668_, 3, v_keepAliveTimeout_4664_);
lean_ctor_set(v___x_4668_, 4, v___x_4666_);
lean_ctor_set(v___x_4668_, 5, v_a_4660_);
lean_ctor_set(v___x_4668_, 6, v___x_4666_);
lean_ctor_set(v___x_4668_, 7, v___x_4637_);
lean_ctor_set(v___x_4668_, 8, v___x_4666_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*9, v___x_4667_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*9 + 1, v___x_4667_);
v___x_4669_ = lean_io_promise_new();
v___x_4670_ = lean_box(v___x_4667_);
lean_inc_ref(v_inst_4644_);
lean_inc_ref(v_config_4634_);
lean_inc_n(v_handler_4642_, 2);
lean_inc_ref(v_responseBodyInstance_4641_);
lean_inc_ref_n(v_h_4640_, 2);
lean_inc_ref_n(v_connectionContext_4639_, 2);
lean_inc(v_socket_4638_);
v___f_4671_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4671_, 0, v___x_4670_);
lean_closure_set(v___f_4671_, 1, v_socket_4638_);
lean_closure_set(v___f_4671_, 2, v_connectionContext_4639_);
lean_closure_set(v___f_4671_, 3, v_h_4640_);
lean_closure_set(v___f_4671_, 4, v_responseBodyInstance_4641_);
lean_closure_set(v___f_4671_, 5, v_handler_4642_);
lean_closure_set(v___f_4671_, 6, v_config_4634_);
lean_closure_set(v___f_4671_, 7, v___f_4643_);
lean_closure_set(v___f_4671_, 8, v_inst_4644_);
v___x_4672_ = lean_box(v___x_4667_);
v___f_4673_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4673_, 0, v_h_4640_);
lean_closure_set(v___f_4673_, 1, v_handler_4642_);
lean_closure_set(v___f_4673_, 2, v_extensions_4645_);
lean_closure_set(v___f_4673_, 3, v_connectionContext_4639_);
lean_closure_set(v___f_4673_, 4, v___x_4672_);
lean_closure_set(v___f_4673_, 5, v___f_4671_);
v___x_4674_ = lean_box(v___x_4667_);
v___f_4675_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4675_, 0, v_h_4640_);
lean_closure_set(v___f_4675_, 1, v_responseBodyInstance_4641_);
lean_closure_set(v___f_4675_, 2, v_handler_4642_);
lean_closure_set(v___f_4675_, 3, v_config_4634_);
lean_closure_set(v___f_4675_, 4, v_connectionContext_4639_);
lean_closure_set(v___f_4675_, 5, v___x_4674_);
lean_closure_set(v___f_4675_, 6, v___f_4673_);
lean_closure_set(v___f_4675_, 7, v_inst_4644_);
lean_closure_set(v___f_4675_, 8, v_socket_4638_);
lean_closure_set(v___f_4675_, 9, v___f_4646_);
lean_closure_set(v___f_4675_, 10, v___f_4647_);
v___x_4676_ = lean_unsigned_to_nat(0u);
v___x_4677_ = lean_box(v___x_4667_);
v___f_4678_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4678_, 0, v___f_4675_);
lean_closure_set(v___f_4678_, 1, v___x_4676_);
lean_closure_set(v___f_4678_, 2, v___x_4668_);
lean_closure_set(v___f_4678_, 3, v___x_4677_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4669_);
v___x_4680_ = v___x_4662_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4669_);
v___x_4680_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
v___x_4682_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4676_, v___x_4667_, v___x_4681_, v___f_4678_);
v___x_4683_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4676_, v___x_4667_, v___x_4682_, v___f_4648_);
return v___x_4683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4686_ = _args[0];
lean_object* v_machine_4687_ = _args[1];
lean_object* v_a_4688_ = _args[2];
lean_object* v___x_4689_ = _args[3];
lean_object* v_socket_4690_ = _args[4];
lean_object* v_connectionContext_4691_ = _args[5];
lean_object* v_h_4692_ = _args[6];
lean_object* v_responseBodyInstance_4693_ = _args[7];
lean_object* v_handler_4694_ = _args[8];
lean_object* v___f_4695_ = _args[9];
lean_object* v_inst_4696_ = _args[10];
lean_object* v_extensions_4697_ = _args[11];
lean_object* v___f_4698_ = _args[12];
lean_object* v___f_4699_ = _args[13];
lean_object* v___f_4700_ = _args[14];
lean_object* v_x_4701_ = _args[15];
lean_object* v___y_4702_ = _args[16];
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4686_, v_machine_4687_, v_a_4688_, v___x_4689_, v_socket_4690_, v_connectionContext_4691_, v_h_4692_, v_responseBodyInstance_4693_, v_handler_4694_, v___f_4695_, v_inst_4696_, v_extensions_4697_, v___f_4698_, v___f_4699_, v___f_4700_, v_x_4701_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4704_, lean_object* v_machine_4705_, lean_object* v_socket_4706_, lean_object* v_connectionContext_4707_, lean_object* v_h_4708_, lean_object* v_responseBodyInstance_4709_, lean_object* v_handler_4710_, lean_object* v___f_4711_, lean_object* v_inst_4712_, lean_object* v_extensions_4713_, lean_object* v___f_4714_, lean_object* v___f_4715_, lean_object* v___f_4716_, lean_object* v_x_4717_){
_start:
{
if (lean_obj_tag(v_x_4717_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4727_; 
lean_dec_ref(v___f_4716_);
lean_dec_ref(v___f_4715_);
lean_dec_ref(v___f_4714_);
lean_dec(v_extensions_4713_);
lean_dec_ref(v_inst_4712_);
lean_dec_ref(v___f_4711_);
lean_dec(v_handler_4710_);
lean_dec_ref(v_responseBodyInstance_4709_);
lean_dec_ref(v_h_4708_);
lean_dec_ref(v_connectionContext_4707_);
lean_dec(v_socket_4706_);
lean_dec_ref(v_machine_4705_);
lean_dec_ref(v_config_4704_);
v_a_4719_ = lean_ctor_get(v_x_4717_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_x_4717_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4721_ = v_x_4717_;
v_isShared_4722_ = v_isSharedCheck_4727_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v_x_4717_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4727_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; 
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4724_);
return v___x_4725_;
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4742_; 
v_a_4728_ = lean_ctor_get(v_x_4717_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v_x_4717_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4730_ = v_x_4717_;
v_isShared_4731_ = v_isSharedCheck_4742_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v_x_4717_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4742_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___f_4734_; lean_object* v___x_4736_; 
v___x_4732_ = lean_box(0);
v___x_4733_ = l_Std_CloseableChannel_new___redArg(v___x_4732_);
v___f_4734_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4734_, 0, v_config_4704_);
lean_closure_set(v___f_4734_, 1, v_machine_4705_);
lean_closure_set(v___f_4734_, 2, v_a_4728_);
lean_closure_set(v___f_4734_, 3, v___x_4732_);
lean_closure_set(v___f_4734_, 4, v_socket_4706_);
lean_closure_set(v___f_4734_, 5, v_connectionContext_4707_);
lean_closure_set(v___f_4734_, 6, v_h_4708_);
lean_closure_set(v___f_4734_, 7, v_responseBodyInstance_4709_);
lean_closure_set(v___f_4734_, 8, v_handler_4710_);
lean_closure_set(v___f_4734_, 9, v___f_4711_);
lean_closure_set(v___f_4734_, 10, v_inst_4712_);
lean_closure_set(v___f_4734_, 11, v_extensions_4713_);
lean_closure_set(v___f_4734_, 12, v___f_4714_);
lean_closure_set(v___f_4734_, 13, v___f_4715_);
lean_closure_set(v___f_4734_, 14, v___f_4716_);
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 0, v___x_4733_);
v___x_4736_ = v___x_4730_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4733_);
v___x_4736_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; lean_object* v___x_4740_; 
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
v___x_4738_ = lean_unsigned_to_nat(0u);
v___x_4739_ = 0;
v___x_4740_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4738_, v___x_4739_, v___x_4737_, v___f_4734_);
return v___x_4740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4743_, lean_object* v_machine_4744_, lean_object* v_socket_4745_, lean_object* v_connectionContext_4746_, lean_object* v_h_4747_, lean_object* v_responseBodyInstance_4748_, lean_object* v_handler_4749_, lean_object* v___f_4750_, lean_object* v_inst_4751_, lean_object* v_extensions_4752_, lean_object* v___f_4753_, lean_object* v___f_4754_, lean_object* v___f_4755_, lean_object* v_x_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4743_, v_machine_4744_, v_socket_4745_, v_connectionContext_4746_, v_h_4747_, v_responseBodyInstance_4748_, v_handler_4749_, v___f_4750_, v_inst_4751_, v_extensions_4752_, v___f_4753_, v___f_4754_, v___f_4755_, v_x_4756_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4762_, lean_object* v_h_4763_, lean_object* v_connection_4764_, lean_object* v_config_4765_, lean_object* v_connectionContext_4766_, lean_object* v_handler_4767_){
_start:
{
lean_object* v_responseBodyInstance_4769_; lean_object* v_onFailure_4770_; lean_object* v___x_4771_; lean_object* v_socket_4772_; lean_object* v_machine_4773_; lean_object* v_extensions_4774_; lean_object* v___f_4775_; lean_object* v___f_4776_; lean_object* v___f_4777_; lean_object* v___f_4778_; lean_object* v___f_4779_; lean_object* v___f_4780_; lean_object* v___f_4781_; lean_object* v___f_4782_; lean_object* v___f_4783_; lean_object* v___x_4784_; uint8_t v___x_4785_; lean_object* v___x_4786_; 
v_responseBodyInstance_4769_ = lean_ctor_get(v_h_4763_, 0);
lean_inc_ref_n(v_responseBodyInstance_4769_, 2);
v_onFailure_4770_ = lean_ctor_get(v_h_4763_, 2);
v___x_4771_ = l_Std_Http_Body_mkStream();
v_socket_4772_ = lean_ctor_get(v_connection_4764_, 0);
lean_inc_n(v_socket_4772_, 2);
v_machine_4773_ = lean_ctor_get(v_connection_4764_, 1);
lean_inc_ref(v_machine_4773_);
v_extensions_4774_ = lean_ctor_get(v_connection_4764_, 2);
lean_inc(v_extensions_4774_);
lean_dec_ref(v_connection_4764_);
v___f_4775_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4776_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4777_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4778_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc(v_handler_4767_);
lean_inc_ref(v_onFailure_4770_);
v___f_4779_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4779_, 0, v_onFailure_4770_);
lean_closure_set(v___f_4779_, 1, v_handler_4767_);
lean_closure_set(v___f_4779_, 2, v___f_4778_);
lean_inc_ref(v_inst_4762_);
v___f_4780_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4780_, 0, v_inst_4762_);
lean_closure_set(v___f_4780_, 1, v_socket_4772_);
lean_inc_ref(v___f_4780_);
v___f_4781_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4781_, 0, v___f_4780_);
v___f_4782_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4782_, 0, v___f_4775_);
lean_closure_set(v___f_4782_, 1, v_responseBodyInstance_4769_);
lean_closure_set(v___f_4782_, 2, v___f_4781_);
lean_closure_set(v___f_4782_, 3, v___f_4780_);
v___f_4783_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4783_, 0, v_config_4765_);
lean_closure_set(v___f_4783_, 1, v_machine_4773_);
lean_closure_set(v___f_4783_, 2, v_socket_4772_);
lean_closure_set(v___f_4783_, 3, v_connectionContext_4766_);
lean_closure_set(v___f_4783_, 4, v_h_4763_);
lean_closure_set(v___f_4783_, 5, v_responseBodyInstance_4769_);
lean_closure_set(v___f_4783_, 6, v_handler_4767_);
lean_closure_set(v___f_4783_, 7, v___f_4776_);
lean_closure_set(v___f_4783_, 8, v_inst_4762_);
lean_closure_set(v___f_4783_, 9, v_extensions_4774_);
lean_closure_set(v___f_4783_, 10, v___f_4777_);
lean_closure_set(v___f_4783_, 11, v___f_4779_);
lean_closure_set(v___f_4783_, 12, v___f_4782_);
v___x_4784_ = lean_unsigned_to_nat(0u);
v___x_4785_ = 0;
v___x_4786_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4784_, v___x_4785_, v___x_4771_, v___f_4783_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4787_, lean_object* v_h_4788_, lean_object* v_connection_4789_, lean_object* v_config_4790_, lean_object* v_connectionContext_4791_, lean_object* v_handler_4792_, lean_object* v_a_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4787_, v_h_4788_, v_connection_4789_, v_config_4790_, v_connectionContext_4791_, v_handler_4792_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4795_, lean_object* v_00_u03c3_4796_, lean_object* v_inst_4797_, lean_object* v_h_4798_, lean_object* v_connection_4799_, lean_object* v_config_4800_, lean_object* v_connectionContext_4801_, lean_object* v_handler_4802_){
_start:
{
lean_object* v___x_4804_; 
v___x_4804_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4797_, v_h_4798_, v_connection_4799_, v_config_4800_, v_connectionContext_4801_, v_handler_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4805_, lean_object* v_00_u03c3_4806_, lean_object* v_inst_4807_, lean_object* v_h_4808_, lean_object* v_connection_4809_, lean_object* v_config_4810_, lean_object* v_connectionContext_4811_, lean_object* v_handler_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4805_, v_00_u03c3_4806_, v_inst_4807_, v_h_4808_, v_connection_4809_, v_config_4810_, v_connectionContext_4811_, v_handler_4812_);
return v_res_4814_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4815_; lean_object* v___x_4816_; 
v___x_4815_ = 0;
v___x_4816_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4815_);
return v___x_4816_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4817_ = lean_unsigned_to_nat(4096u);
v___x_4818_ = lean_mk_empty_byte_array(v___x_4817_);
return v___x_4818_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4819_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4820_ = l_ByteArray_mkIterator(v___x_4819_);
return v___x_4820_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4821_ = 0;
v___x_4822_ = lean_unsigned_to_nat(0u);
v___x_4823_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4824_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4825_ = lean_box(0);
v___x_4826_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
lean_ctor_set(v___x_4826_, 1, v___x_4824_);
lean_ctor_set(v___x_4826_, 2, v___x_4823_);
lean_ctor_set(v___x_4826_, 3, v___x_4822_);
lean_ctor_set(v___x_4826_, 4, v___x_4822_);
lean_ctor_set(v___x_4826_, 5, v___x_4822_);
lean_ctor_set_uint8(v___x_4826_, sizeof(void*)*6, v___x_4821_);
return v___x_4826_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = 1;
v___x_4835_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4834_);
return v___x_4835_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4836_; uint8_t v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4836_ = lean_unsigned_to_nat(0u);
v___x_4837_ = 0;
v___x_4838_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4839_ = lean_box(0);
v___x_4840_ = lean_box(0);
v___x_4841_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4842_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4843_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
lean_ctor_set(v___x_4843_, 1, v___x_4841_);
lean_ctor_set(v___x_4843_, 2, v___x_4840_);
lean_ctor_set(v___x_4843_, 3, v___x_4839_);
lean_ctor_set(v___x_4843_, 4, v___x_4838_);
lean_ctor_set(v___x_4843_, 5, v___x_4836_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*6, v___x_4837_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*6 + 1, v___x_4837_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*6 + 2, v___x_4837_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4844_, lean_object* v_client_4845_, lean_object* v_extensions_4846_, lean_object* v_inst_4847_, lean_object* v_inst_4848_, lean_object* v_handler_4849_, lean_object* v_x_4850_){
_start:
{
if (lean_obj_tag(v_x_4850_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v_handler_4849_);
lean_dec_ref(v_inst_4848_);
lean_dec_ref(v_inst_4847_);
lean_dec(v_extensions_4846_);
lean_dec(v_client_4845_);
lean_dec_ref(v_config_4844_);
v_a_4852_ = lean_ctor_get(v_x_4850_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v_x_4850_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4854_ = v_x_4850_;
v_isShared_4855_ = v_isSharedCheck_4860_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v_x_4850_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4860_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
return v___x_4858_;
}
}
}
else
{
lean_object* v_a_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v_enableKeepAlive_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v_a_4861_ = lean_ctor_get(v_x_4850_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v_x_4850_, 1);
v___x_4862_ = 0;
v___x_4863_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4864_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4865_ = lean_box(0);
v___x_4866_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4867_ = l_Std_Http_Config_toH1Config(v_config_4844_);
v_enableKeepAlive_4868_ = lean_ctor_get_uint8(v___x_4867_, sizeof(void*)*18);
v___x_4869_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4869_, 0, v___x_4863_);
lean_ctor_set(v___x_4869_, 1, v___x_4866_);
lean_ctor_set(v___x_4869_, 2, v___x_4867_);
lean_ctor_set(v___x_4869_, 3, v___x_4864_);
lean_ctor_set(v___x_4869_, 4, v___x_4865_);
lean_ctor_set(v___x_4869_, 5, v___x_4865_);
lean_ctor_set_uint8(v___x_4869_, sizeof(void*)*6, v_enableKeepAlive_4868_);
lean_ctor_set_uint8(v___x_4869_, sizeof(void*)*6 + 1, v___x_4862_);
lean_ctor_set_uint8(v___x_4869_, sizeof(void*)*6 + 2, v___x_4862_);
v___x_4870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4870_, 0, v_client_4845_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
lean_ctor_set(v___x_4870_, 2, v_extensions_4846_);
v___x_4871_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4847_, v_inst_4848_, v___x_4870_, v_config_4844_, v_a_4861_, v_handler_4849_);
return v___x_4871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4872_, lean_object* v_client_4873_, lean_object* v_extensions_4874_, lean_object* v_inst_4875_, lean_object* v_inst_4876_, lean_object* v_handler_4877_, lean_object* v_x_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4872_, v_client_4873_, v_extensions_4874_, v_inst_4875_, v_inst_4876_, v_handler_4877_, v_x_4878_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4881_, lean_object* v_inst_4882_, lean_object* v_client_4883_, lean_object* v_handler_4884_, lean_object* v_config_4885_, lean_object* v_extensions_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v___f_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; uint8_t v___x_4893_; lean_object* v___x_4894_; 
v___f_4889_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4889_, 0, v_config_4885_);
lean_closure_set(v___f_4889_, 1, v_client_4883_);
lean_closure_set(v___f_4889_, 2, v_extensions_4886_);
lean_closure_set(v___f_4889_, 3, v_inst_4881_);
lean_closure_set(v___f_4889_, 4, v_inst_4882_);
lean_closure_set(v___f_4889_, 5, v_handler_4884_);
lean_inc_ref(v_a_4887_);
v___x_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4890_, 0, v_a_4887_);
v___x_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = 0;
v___x_4894_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4892_, v___x_4893_, v___x_4891_, v___f_4889_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4895_, lean_object* v_inst_4896_, lean_object* v_client_4897_, lean_object* v_handler_4898_, lean_object* v_config_4899_, lean_object* v_extensions_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4895_, v_inst_4896_, v_client_4897_, v_handler_4898_, v_config_4899_, v_extensions_4900_, v_a_4901_);
lean_dec_ref(v_a_4901_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4904_, lean_object* v_00_u03c3_4905_, lean_object* v_inst_4906_, lean_object* v_inst_4907_, lean_object* v_client_4908_, lean_object* v_handler_4909_, lean_object* v_config_4910_, lean_object* v_extensions_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4906_, v_inst_4907_, v_client_4908_, v_handler_4909_, v_config_4910_, v_extensions_4911_, v_a_4912_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4915_, lean_object* v_00_u03c3_4916_, lean_object* v_inst_4917_, lean_object* v_inst_4918_, lean_object* v_client_4919_, lean_object* v_handler_4920_, lean_object* v_config_4921_, lean_object* v_extensions_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_Std_Http_Server_serveConnection(v_t_4915_, v_00_u03c3_4916_, v_inst_4917_, v_inst_4918_, v_client_4919_, v_handler_4920_, v_config_4921_, v_extensions_4922_, v_a_4923_);
lean_dec_ref(v_a_4923_);
return v_res_4925_;
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
