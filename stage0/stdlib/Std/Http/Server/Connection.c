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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_nbuckets_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_857_ = lean_array_get_size(v_data_856_);
v___x_858_ = lean_unsigned_to_nat(2u);
v_nbuckets_859_ = lean_nat_mul(v___x_857_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_box(0);
v___x_862_ = lean_mk_array(v_nbuckets_859_, v___x_861_);
v___x_863_ = lean_array_propagate_mark(v_data_856_, v___x_862_);
v___x_864_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v___x_860_, v_data_856_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_865_, lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_mk_empty_array_with_capacity(v___x_867_);
v___x_869_ = lean_array_push(v___x_868_, v_i_865_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_val_871_ = lean_ctor_get(v_x_866_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_879_ == 0)
{
v___x_873_ = v_x_866_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_val_871_);
lean_dec(v_x_866_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_array_push(v_val_871_, v_i_865_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_880_, lean_object* v_a_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_val_885_; lean_object* v___x_886_; 
v___x_883_ = lean_box(0);
v___x_884_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_880_, v___x_883_);
v_val_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_val_885_);
lean_dec(v___x_884_);
v___x_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_886_, 0, v_a_881_);
lean_ctor_set(v___x_886_, 1, v_val_885_);
lean_ctor_set(v___x_886_, 2, v_x_882_);
return v___x_886_;
}
else
{
lean_object* v_key_887_; lean_object* v_value_888_; lean_object* v_tail_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_904_; 
v_key_887_ = lean_ctor_get(v_x_882_, 0);
v_value_888_ = lean_ctor_get(v_x_882_, 1);
v_tail_889_ = lean_ctor_get(v_x_882_, 2);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_904_ == 0)
{
v___x_891_ = v_x_882_;
v_isShared_892_ = v_isSharedCheck_904_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_tail_889_);
lean_inc(v_value_888_);
lean_inc(v_key_887_);
lean_dec(v_x_882_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_904_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = lean_string_dec_eq(v_key_887_, v_a_881_);
if (v___x_893_ == 0)
{
lean_object* v_tail_894_; lean_object* v___x_896_; 
v_tail_894_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_880_, v_a_881_, v_tail_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v_tail_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_key_887_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_value_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_tail_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_val_900_; lean_object* v___x_902_; 
lean_dec(v_key_887_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_value_888_);
v___x_899_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_880_, v___x_898_);
v_val_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_val_900_);
lean_dec(v___x_899_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_val_900_);
lean_ctor_set(v___x_891_, 0, v_a_881_);
v___x_902_ = v___x_891_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_881_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_val_900_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_tail_889_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_905_, lean_object* v_x_906_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
uint8_t v___x_907_; 
v___x_907_ = 0;
return v___x_907_;
}
else
{
lean_object* v_key_908_; lean_object* v_tail_909_; uint8_t v___x_910_; 
v_key_908_ = lean_ctor_get(v_x_906_, 0);
v_tail_909_ = lean_ctor_get(v_x_906_, 2);
v___x_910_ = lean_string_dec_eq(v_key_908_, v_a_905_);
if (v___x_910_ == 0)
{
v_x_906_ = v_tail_909_;
goto _start;
}
else
{
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_912_, lean_object* v_x_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_912_, v_x_913_);
lean_dec(v_x_913_);
lean_dec_ref(v_a_912_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_916_, lean_object* v_m_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_size_919_; lean_object* v_buckets_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_970_; 
v_size_919_ = lean_ctor_get(v_m_917_, 0);
v_buckets_920_ = lean_ctor_get(v_m_917_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_m_917_);
if (v_isSharedCheck_970_ == 0)
{
v___x_922_ = v_m_917_;
v_isShared_923_ = v_isSharedCheck_970_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_buckets_920_);
lean_inc(v_size_919_);
lean_dec(v_m_917_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_970_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v_fold_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v___x_935_; size_t v___x_936_; lean_object* v_bkt_937_; uint8_t v___x_938_; 
v___x_924_ = lean_array_get_size(v_buckets_920_);
v___x_925_ = lean_string_hash(v_a_918_);
v___x_926_ = 32ULL;
v___x_927_ = lean_uint64_shift_right(v___x_925_, v___x_926_);
v_fold_928_ = lean_uint64_xor(v___x_925_, v___x_927_);
v___x_929_ = 16ULL;
v___x_930_ = lean_uint64_shift_right(v_fold_928_, v___x_929_);
v___x_931_ = lean_uint64_xor(v_fold_928_, v___x_930_);
v___x_932_ = lean_uint64_to_usize(v___x_931_);
v___x_933_ = lean_usize_of_nat(v___x_924_);
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_sub(v___x_933_, v___x_934_);
v___x_936_ = lean_usize_land(v___x_932_, v___x_935_);
v_bkt_937_ = lean_array_uget_borrowed(v_buckets_920_, v___x_936_);
v___x_938_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_918_, v_bkt_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_size_x27_942_; lean_object* v___x_943_; lean_object* v_buckets_x27_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v_i_916_);
v_size_x27_942_ = lean_nat_add(v_size_919_, v___x_939_);
lean_dec(v_size_919_);
lean_inc(v_bkt_937_);
v___x_943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_943_, 0, v_a_918_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v_bkt_937_);
v_buckets_x27_944_ = lean_array_uset(v_buckets_920_, v___x_936_, v___x_943_);
v___x_945_ = lean_unsigned_to_nat(4u);
v___x_946_ = lean_nat_mul(v_size_x27_942_, v___x_945_);
v___x_947_ = lean_unsigned_to_nat(3u);
v___x_948_ = lean_nat_div(v___x_946_, v___x_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_array_get_size(v_buckets_x27_944_);
v___x_950_ = lean_nat_dec_le(v___x_948_, v___x_949_);
lean_dec(v___x_948_);
if (v___x_950_ == 0)
{
lean_object* v_val_951_; lean_object* v___x_953_; 
v_val_951_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_944_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_val_951_);
lean_ctor_set(v___x_922_, 0, v_size_x27_942_);
v___x_953_ = v___x_922_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_size_x27_942_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_val_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_buckets_x27_944_);
lean_ctor_set(v___x_922_, 0, v_size_x27_942_);
v___x_956_ = v___x_922_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_size_x27_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_buckets_x27_944_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_object* v___x_958_; lean_object* v_buckets_x27_959_; lean_object* v_bkt_x27_960_; lean_object* v___y_962_; uint8_t v___x_967_; 
lean_inc(v_bkt_937_);
v___x_958_ = lean_box(0);
v_buckets_x27_959_ = lean_array_uset(v_buckets_920_, v___x_936_, v___x_958_);
lean_inc_ref(v_a_918_);
v_bkt_x27_960_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_916_, v_a_918_, v_bkt_937_);
v___x_967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_918_, v_bkt_x27_960_);
lean_dec_ref(v_a_918_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_sub(v_size_919_, v___x_968_);
lean_dec(v_size_919_);
v___y_962_ = v___x_969_;
goto v___jp_961_;
}
else
{
v___y_962_ = v_size_919_;
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = lean_array_uset(v_buckets_x27_959_, v___x_936_, v_bkt_x27_960_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_963_);
lean_ctor_set(v___x_922_, 0, v___y_962_);
v___x_965_ = v___x_922_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___y_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_971_, lean_object* v___x_972_, lean_object* v_indexes_973_, lean_object* v_status_974_, uint8_t v_version_975_, lean_object* v_x_976_){
_start:
{
if (lean_obj_tag(v_x_976_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_status_974_);
lean_dec_ref(v_indexes_973_);
lean_dec_ref(v___x_972_);
lean_dec_ref(v_entries_971_);
v_a_978_ = lean_ctor_get(v_x_976_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_976_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v_x_976_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v_x_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1003_; 
v_a_987_ = lean_ctor_get(v_x_976_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_x_976_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_989_ = v_x_976_;
v_isShared_990_ = v_isSharedCheck_1003_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v_x_976_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1003_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_i_993_; lean_object* v___x_994_; lean_object* v_entries_995_; lean_object* v_indexes_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_991_ = l_Std_Time_DateTime_toRFC822String(v_a_987_);
v___x_992_ = l_Std_Http_Header_Value_ofString_x21(v___x_991_);
v_i_993_ = lean_array_get_size(v_entries_971_);
lean_inc_ref(v___x_972_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_972_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
v_entries_995_ = lean_array_push(v_entries_971_, v___x_994_);
v_indexes_996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_993_, v_indexes_973_, v___x_972_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_entries_995_);
lean_ctor_set(v___x_997_, 1, v_indexes_996_);
v___x_998_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_998_, 0, v_status_974_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*2, v_version_975_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_998_);
v___x_1000_ = v___x_989_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_1004_, lean_object* v___x_1005_, lean_object* v_indexes_1006_, lean_object* v_status_1007_, lean_object* v_version_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_version_boxed_1011_; lean_object* v_res_1012_; 
v_version_boxed_1011_ = lean_unbox(v_version_1008_);
v_res_1012_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_1004_, v___x_1005_, v_indexes_1006_, v_status_1007_, v_version_boxed_1011_, v_x_1009_);
return v_res_1012_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_nat_to_int(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1015_, lean_object* v_a_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v_offset_1018_; lean_object* v_second_1019_; lean_object* v_nano_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_offset_1018_ = lean_ctor_get(v_tz_1015_, 0);
v_second_1019_ = lean_ctor_get(v_a_1016_, 0);
v_nano_1020_ = lean_ctor_get(v_a_1016_, 1);
v___x_1021_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_1022_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_1023_ = lean_int_mul(v_second_1019_, v___x_1022_);
v___x_1024_ = lean_int_add(v___x_1023_, v_nano_1020_);
lean_dec(v___x_1023_);
v___x_1025_ = lean_int_mul(v_offset_1018_, v___x_1022_);
v___x_1026_ = lean_int_add(v___x_1025_, v___x_1021_);
lean_dec(v___x_1025_);
v___x_1027_ = lean_int_add(v___x_1024_, v___x_1026_);
lean_dec(v___x_1026_);
lean_dec(v___x_1024_);
v___x_1028_ = l_Std_Time_Duration_ofNanoseconds(v___x_1027_);
lean_dec(v___x_1027_);
v___x_1029_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1030_, lean_object* v_a_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1030_, v_a_1031_, v_x_1032_);
lean_dec_ref(v_a_1031_);
lean_dec_ref(v_tz_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object* v_m_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_buckets_1036_; lean_object* v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v_fold_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_buckets_1036_ = lean_ctor_get(v_m_1034_, 1);
v___x_1037_ = lean_array_get_size(v_buckets_1036_);
v___x_1038_ = lean_string_hash(v_a_1035_);
v___x_1039_ = 32ULL;
v___x_1040_ = lean_uint64_shift_right(v___x_1038_, v___x_1039_);
v_fold_1041_ = lean_uint64_xor(v___x_1038_, v___x_1040_);
v___x_1042_ = 16ULL;
v___x_1043_ = lean_uint64_shift_right(v_fold_1041_, v___x_1042_);
v___x_1044_ = lean_uint64_xor(v_fold_1041_, v___x_1043_);
v___x_1045_ = lean_uint64_to_usize(v___x_1044_);
v___x_1046_ = lean_usize_of_nat(v___x_1037_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_sub(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_usize_land(v___x_1045_, v___x_1048_);
v___x_1050_ = lean_array_uget_borrowed(v_buckets_1036_, v___x_1049_);
v___x_1051_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1035_, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object* v_m_1052_, lean_object* v_a_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1052_, v_a_1053_);
lean_dec_ref(v_a_1053_);
lean_dec_ref(v_m_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1057_, lean_object* v_head_1058_){
_start:
{
lean_object* v_headers_1063_; uint8_t v_generateDate_1064_; lean_object* v_status_1065_; uint8_t v_version_1066_; lean_object* v_entries_1067_; lean_object* v_indexes_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___f_1071_; lean_object* v_val_1073_; lean_object* v_a_1079_; uint8_t v___y_1082_; uint8_t v___x_1101_; 
v_headers_1063_ = lean_ctor_get(v_head_1058_, 1);
v_generateDate_1064_ = lean_ctor_get_uint8(v_config_1057_, sizeof(void*)*24 + 1);
v_status_1065_ = lean_ctor_get(v_head_1058_, 0);
v_version_1066_ = lean_ctor_get_uint8(v_head_1058_, sizeof(void*)*2);
v_entries_1067_ = lean_ctor_get(v_headers_1063_, 0);
v_indexes_1068_ = lean_ctor_get(v_headers_1063_, 1);
v___x_1069_ = l_Std_Http_Header_Name_date;
v___x_1070_ = lean_box(v_version_1066_);
lean_inc(v_status_1065_);
lean_inc_ref(v_indexes_1068_);
lean_inc_ref(v_entries_1067_);
v___f_1071_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1071_, 0, v_entries_1067_);
lean_closure_set(v___f_1071_, 1, v___x_1069_);
lean_closure_set(v___f_1071_, 2, v_indexes_1068_);
lean_closure_set(v___f_1071_, 3, v_status_1065_);
lean_closure_set(v___f_1071_, 4, v___x_1070_);
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_1068_, v___x_1069_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; 
v___x_1102_ = 1;
v___y_1082_ = v___x_1102_;
goto v___jp_1081_;
}
else
{
uint8_t v___x_1103_; 
v___x_1103_ = 0;
v___y_1082_ = v___x_1103_;
goto v___jp_1081_;
}
v___jp_1060_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_head_1058_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_val_1073_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = 0;
v___x_1077_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1075_, v___x_1076_, v___x_1074_, v___f_1071_);
return v___x_1077_;
}
v___jp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_a_1079_);
v_val_1073_ = v___x_1080_;
goto v___jp_1072_;
}
v___jp_1081_:
{
if (v_generateDate_1064_ == 0)
{
lean_dec_ref(v___f_1071_);
goto v___jp_1060_;
}
else
{
if (v___y_1082_ == 0)
{
lean_dec_ref(v___f_1071_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1083_; 
lean_dec_ref(v_head_1058_);
v___x_1083_ = lean_get_current_time();
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1086_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1098_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_tz_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_inc(v_a_1087_);
v_tz_1091_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1087_, v_a_1084_);
lean_inc(v_a_1084_);
lean_inc_ref(v_tz_1091_);
v___f_1092_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1092_, 0, v_tz_1091_);
lean_closure_set(v___f_1092_, 1, v_a_1084_);
v___x_1093_ = lean_mk_thunk(v___f_1092_);
v___x_1094_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_1084_);
lean_ctor_set(v___x_1094_, 2, v_a_1087_);
lean_ctor_set(v___x_1094_, 3, v_tz_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1094_);
v___x_1096_ = v___x_1089_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v_val_1073_ = v___x_1096_;
goto v___jp_1072_;
}
}
}
else
{
lean_object* v_a_1099_; 
lean_dec(v_a_1084_);
v_a_1099_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1086_, 1);
v_a_1079_ = v_a_1099_;
goto v___jp_1078_;
}
}
else
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1083_, 1);
v_a_1079_ = v_a_1100_;
goto v___jp_1078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1104_, lean_object* v_head_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1104_, v_head_1105_);
lean_dec_ref(v_config_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_00_u03b2_1108_, lean_object* v_m_1109_, lean_object* v_a_1110_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1109_, v_a_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object* v_00_u03b2_1112_, lean_object* v_m_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(v_00_u03b2_1112_, v_m_1113_, v_a_1114_);
lean_dec_ref(v_a_1114_);
lean_dec_ref(v_m_1113_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__5(lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_nat_to_int(v_a_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_nat_to_int(v_a_1119_);
v___x_1121_ = l_Rat_ofInt(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1122_, lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_a_1127_, lean_object* v_x_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1126_, v_a_1127_, v_x_1128_);
lean_dec(v_x_1128_);
lean_dec_ref(v_a_1127_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1131_, lean_object* v_data_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1134_, lean_object* v_i_1135_, lean_object* v_source_1136_, lean_object* v_target_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2___redArg(v_i_1135_, v_source_1136_, v_target_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1143_, lean_object* v_____r_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1143_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1150_, lean_object* v_____r_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1150_, v_____r_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v___f_1154_);
v_a_1157_ = lean_ctor_get(v_x_1155_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v_x_1155_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v_x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v_x_1155_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v_x_1155_, 1);
v___x_1167_ = lean_apply_2(v___f_1154_, v_a_1166_, lean_box(0));
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1168_, v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1172_, lean_object* v_body_1173_, lean_object* v___f_1174_, lean_object* v___f_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v___f_1175_);
lean_dec_ref(v___f_1174_);
lean_dec(v_body_1173_);
lean_dec_ref(v_close_1172_);
v_a_1178_ = lean_ctor_get(v_x_1176_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v_x_1176_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v_x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; uint8_t v___x_1188_; 
v_a_1187_ = lean_ctor_get(v_x_1176_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v_x_1176_, 1);
v___x_1188_ = lean_unbox(v_a_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v___f_1175_);
v___x_1189_ = lean_apply_2(v_close_1172_, v_body_1173_, lean_box(0));
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
v___x_1192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1190_, v___x_1191_, v___x_1189_, v___f_1174_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_a_1187_);
lean_dec_ref(v___f_1174_);
lean_dec(v_body_1173_);
lean_dec_ref(v_close_1172_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_apply_2(v___f_1175_, v___x_1193_, lean_box(0));
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1195_, lean_object* v_body_1196_, lean_object* v___f_1197_, lean_object* v___f_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1195_, v_body_1196_, v___f_1197_, v___f_1198_, v_x_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1202_, lean_object* v___f_1203_, lean_object* v___f_1204_, lean_object* v_x1_1205_, lean_object* v_x2_1206_){
_start:
{
lean_object* v_fst_1207_; uint8_t v___x_1208_; 
v_fst_1207_ = lean_ctor_get(v_x2_1206_, 0);
lean_inc(v_fst_1207_);
v___x_1208_ = lean_string_dec_eq(v___x_1202_, v_fst_1207_);
if (v___x_1208_ == 0)
{
lean_object* v_entries_1209_; lean_object* v_indexes_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1221_; 
v_entries_1209_ = lean_ctor_get(v_x1_1205_, 0);
v_indexes_1210_ = lean_ctor_get(v_x1_1205_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_x1_1205_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1212_ = v_x1_1205_;
v_isShared_1213_ = v_isSharedCheck_1221_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_indexes_1210_);
lean_inc(v_entries_1209_);
lean_dec(v_x1_1205_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1221_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_i_1214_; lean_object* v_f_1215_; lean_object* v_entries_1216_; lean_object* v_indexes_1217_; lean_object* v___x_1219_; 
v_i_1214_ = lean_array_get_size(v_entries_1209_);
v_f_1215_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1215_, 0, v_i_1214_);
v_entries_1216_ = lean_array_push(v_entries_1209_, v_x2_1206_);
v_indexes_1217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1203_, v___f_1204_, v_indexes_1210_, v_fst_1207_, v_f_1215_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v_indexes_1217_);
lean_ctor_set(v___x_1212_, 0, v_entries_1216_);
v___x_1219_ = v___x_1212_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_entries_1216_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_indexes_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_dec(v_fst_1207_);
lean_dec_ref(v_x2_1206_);
lean_dec_ref(v___f_1204_);
lean_dec_ref(v___f_1203_);
return v_x1_1205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1222_, lean_object* v___f_1223_, lean_object* v___f_1224_, lean_object* v_x1_1225_, lean_object* v_x2_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1222_, v___f_1223_, v___f_1224_, v_x1_1225_, v_x2_1226_);
lean_dec_ref(v___x_1222_);
return v_res_1227_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2(void){
_start:
{
lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; 
v___f_1230_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1231_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1232_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1231_, v___f_1230_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v___f_1255_; 
v___f_1252_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1253_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1254_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1255_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1255_, 0, v___x_1254_);
lean_closure_set(v___f_1255_, 1, v___f_1253_);
lean_closure_set(v___f_1255_, 2, v___f_1252_);
return v___f_1255_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14(void){
_start:
{
lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; 
v___f_1256_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1257_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1258_ = l_Std_Http_Header_Name_contentLength;
v___f_1259_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1259_, 0, v___x_1258_);
lean_closure_set(v___f_1259_, 1, v___f_1257_);
lean_closure_set(v___f_1259_, 2, v___f_1256_);
return v___f_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1260_, lean_object* v_body_1261_, lean_object* v_isClosed_1262_, lean_object* v_close_1263_, lean_object* v_x_1264_){
_start:
{
lean_object* v___y_1267_; uint8_t v_omitBody_1268_; lean_object* v___y_1281_; 
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_close_1263_);
lean_dec_ref(v_isClosed_1262_);
lean_dec(v_body_1261_);
lean_dec_ref(v___y_1260_);
v_a_1315_ = lean_ctor_get(v_x_1264_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1317_ = v_x_1264_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v_x_1264_);
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
lean_object* v_a_1324_; lean_object* v___y_1326_; uint8_t v___y_1327_; uint8_t v___y_1328_; uint8_t v___y_1329_; uint8_t v___y_1330_; uint8_t v___y_1331_; lean_object* v_writer_1339_; lean_object* v_reader_1340_; lean_object* v_config_1341_; lean_object* v_events_1342_; lean_object* v_error_1343_; lean_object* v_instant_1344_; uint8_t v_keepAlive_1345_; uint8_t v_forcedFlush_1346_; uint8_t v_pullBodyStalled_1347_; lean_object* v_userData_1348_; lean_object* v_outputData_1349_; lean_object* v_state_1350_; lean_object* v_knownSize_1351_; lean_object* v_messageHead_1352_; uint8_t v_sentMessage_1353_; uint8_t v_userClosedBody_1354_; uint8_t v_omitBody_1355_; lean_object* v_userDataBytes_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1439_; 
v_a_1324_ = lean_ctor_get(v_x_1264_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v_x_1264_, 1);
v_writer_1339_ = lean_ctor_get(v___y_1260_, 1);
lean_inc_ref(v_writer_1339_);
v_reader_1340_ = lean_ctor_get(v___y_1260_, 0);
v_config_1341_ = lean_ctor_get(v___y_1260_, 2);
v_events_1342_ = lean_ctor_get(v___y_1260_, 3);
v_error_1343_ = lean_ctor_get(v___y_1260_, 4);
v_instant_1344_ = lean_ctor_get(v___y_1260_, 5);
v_keepAlive_1345_ = lean_ctor_get_uint8(v___y_1260_, sizeof(void*)*6);
v_forcedFlush_1346_ = lean_ctor_get_uint8(v___y_1260_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1347_ = lean_ctor_get_uint8(v___y_1260_, sizeof(void*)*6 + 2);
v_userData_1348_ = lean_ctor_get(v_writer_1339_, 0);
v_outputData_1349_ = lean_ctor_get(v_writer_1339_, 1);
v_state_1350_ = lean_ctor_get(v_writer_1339_, 2);
v_knownSize_1351_ = lean_ctor_get(v_writer_1339_, 3);
v_messageHead_1352_ = lean_ctor_get(v_writer_1339_, 4);
v_sentMessage_1353_ = lean_ctor_get_uint8(v_writer_1339_, sizeof(void*)*6);
v_userClosedBody_1354_ = lean_ctor_get_uint8(v_writer_1339_, sizeof(void*)*6 + 1);
v_omitBody_1355_ = lean_ctor_get_uint8(v_writer_1339_, sizeof(void*)*6 + 2);
v_userDataBytes_1356_ = lean_ctor_get(v_writer_1339_, 5);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_writer_1339_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1358_ = v_writer_1339_;
v_isShared_1359_ = v_isSharedCheck_1439_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_userDataBytes_1356_);
lean_inc(v_messageHead_1352_);
lean_inc(v_knownSize_1351_);
lean_inc(v_state_1350_);
lean_inc(v_outputData_1349_);
lean_inc(v_userData_1348_);
lean_dec(v_writer_1339_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1439_;
goto v_resetjp_1357_;
}
v___jp_1325_:
{
lean_object* v_headerSize_1332_; lean_object* v_machine_1333_; lean_object* v_machine_1334_; lean_object* v_reader_1335_; lean_object* v_state_1336_; 
v_headerSize_1332_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1330_, v_a_1324_, v___y_1327_);
v_machine_1333_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1328_, v___y_1326_, v_headerSize_1332_, v___y_1331_);
v_machine_1334_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1328_, v_machine_1333_, v_a_1324_);
lean_dec(v_a_1324_);
v_reader_1335_ = lean_ctor_get(v_machine_1334_, 0);
lean_inc_ref(v_reader_1335_);
v_state_1336_ = lean_ctor_get(v_reader_1335_, 0);
lean_inc(v_state_1336_);
lean_dec_ref(v_reader_1335_);
if (lean_obj_tag(v_state_1336_) == 7)
{
lean_dec_ref_known(v_state_1336_, 1);
if (v___y_1329_ == 0)
{
lean_object* v_writer_1337_; uint8_t v_omitBody_1338_; 
v_writer_1337_ = lean_ctor_get(v_machine_1334_, 1);
lean_inc_ref(v_writer_1337_);
v_omitBody_1338_ = lean_ctor_get_uint8(v_writer_1337_, sizeof(void*)*6 + 2);
lean_dec_ref(v_writer_1337_);
v___y_1267_ = v_machine_1334_;
v_omitBody_1268_ = v_omitBody_1338_;
goto v___jp_1266_;
}
else
{
v___y_1281_ = v_machine_1334_;
goto v___jp_1280_;
}
}
else
{
lean_dec(v_state_1336_);
v___y_1281_ = v_machine_1334_;
goto v___jp_1280_;
}
}
v_resetjp_1357_:
{
uint8_t v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1425_; lean_object* v___x_1433_; uint8_t v___x_1434_; uint8_t v___y_1436_; 
v___x_1433_ = lean_box(1);
v___x_1434_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1350_, v___x_1433_);
if (v_sentMessage_1353_ == 0)
{
uint8_t v___x_1437_; 
v___x_1437_ = 1;
v___y_1436_ = v___x_1437_;
goto v___jp_1435_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = 0;
v___y_1436_ = v___x_1438_;
goto v___jp_1435_;
}
v___jp_1360_:
{
lean_object* v_message_1363_; lean_object* v___x_2263__overap_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v_message_1363_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1361_, v_a_1324_, v___y_1362_);
v___x_2263__overap_1364_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1361_);
v___x_1365_ = lean_apply_2(v___x_2263__overap_1364_, v_outputData_1349_, v_message_1363_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1365_);
v___x_1367_ = v___x_1358_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_userData_1348_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_state_1350_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_knownSize_1351_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_messageHead_1352_);
lean_ctor_set(v_reuseFailAlloc_1369_, 5, v_userDataBytes_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*6, v_sentMessage_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*6 + 1, v_userClosedBody_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*6 + 2, v_omitBody_1355_);
v___x_1367_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1368_, 0, v_reader_1340_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
lean_ctor_set(v___x_1368_, 2, v_config_1341_);
lean_ctor_set(v___x_1368_, 3, v_events_1342_);
lean_ctor_set(v___x_1368_, 4, v_error_1343_);
lean_ctor_set(v___x_1368_, 5, v_instant_1344_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*6, v_keepAlive_1345_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*6 + 1, v_forcedFlush_1346_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*6 + 2, v_pullBodyStalled_1347_);
v___y_1267_ = v___x_1368_;
v_omitBody_1268_ = v_omitBody_1355_;
goto v___jp_1266_;
}
}
v___jp_1370_:
{
lean_object* v___x_1373_; lean_object* v___f_1374_; lean_object* v___f_1375_; uint8_t v___x_1376_; 
v___x_1373_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1374_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1375_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1376_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1374_, v___f_1375_, v___x_1373_, v___y_1372_);
if (v___x_1376_ == 0)
{
v___y_1361_ = v___y_1371_;
v___y_1362_ = v___y_1372_;
goto v___jp_1360_;
}
else
{
lean_object* v_entries_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_entries_1377_ = lean_ctor_get(v___y_1372_, 0);
lean_inc_ref(v_entries_1377_);
lean_dec_ref(v___y_1372_);
v___x_1378_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_array_get_size(v_entries_1377_);
v___x_1381_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1382_ = lean_nat_dec_lt(v___x_1379_, v___x_1380_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_entries_1377_);
v___y_1361_ = v___y_1371_;
v___y_1362_ = v___x_1378_;
goto v___jp_1360_;
}
else
{
lean_object* v___f_1383_; size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___f_1383_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13);
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = lean_usize_of_nat(v___x_1380_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1381_, v___f_1383_, v_entries_1377_, v___x_1384_, v___x_1385_, v___x_1378_);
v___y_1361_ = v___y_1371_;
v___y_1362_ = v___x_1386_;
goto v___jp_1360_;
}
}
}
v___jp_1387_:
{
uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v_indexes_1394_; lean_object* v___x_1395_; lean_object* v_machine_1396_; lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___f_1399_; uint8_t v___x_1400_; 
v___x_1392_ = 1;
v___x_1393_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1392_, v_a_1324_);
v_indexes_1394_ = lean_ctor_get(v___x_1393_, 1);
lean_inc_ref(v_indexes_1394_);
lean_dec_ref(v___x_1393_);
lean_inc(v_a_1324_);
v___x_1395_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1395_, 0, v_userData_1348_);
lean_ctor_set(v___x_1395_, 1, v_outputData_1349_);
lean_ctor_set(v___x_1395_, 2, v_state_1350_);
lean_ctor_set(v___x_1395_, 3, v_knownSize_1351_);
lean_ctor_set(v___x_1395_, 4, v_a_1324_);
lean_ctor_set(v___x_1395_, 5, v_userDataBytes_1356_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*6, v___y_1389_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*6 + 1, v_userClosedBody_1354_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*6 + 2, v_omitBody_1355_);
v_machine_1396_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1396_, 0, v_reader_1340_);
lean_ctor_set(v_machine_1396_, 1, v___x_1395_);
lean_ctor_set(v_machine_1396_, 2, v_config_1341_);
lean_ctor_set(v_machine_1396_, 3, v_events_1342_);
lean_ctor_set(v_machine_1396_, 4, v_error_1343_);
lean_ctor_set(v_machine_1396_, 5, v_instant_1344_);
lean_ctor_set_uint8(v_machine_1396_, sizeof(void*)*6, v_keepAlive_1345_);
lean_ctor_set_uint8(v_machine_1396_, sizeof(void*)*6 + 1, v_forcedFlush_1346_);
lean_ctor_set_uint8(v_machine_1396_, sizeof(void*)*6 + 2, v_pullBodyStalled_1347_);
v___x_1397_ = l_Std_Http_Header_Name_contentLength;
v___f_1398_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1399_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1398_, v___f_1399_, v_indexes_1394_, v___x_1397_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1402_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1398_, v___f_1399_, v_indexes_1394_, v___x_1401_);
lean_dec_ref(v_indexes_1394_);
v___y_1326_ = v_machine_1396_;
v___y_1327_ = v___y_1388_;
v___y_1328_ = v___y_1390_;
v___y_1329_ = v___y_1391_;
v___y_1330_ = v___x_1392_;
v___y_1331_ = v___x_1402_;
goto v___jp_1325_;
}
else
{
lean_dec_ref(v_indexes_1394_);
v___y_1326_ = v_machine_1396_;
v___y_1327_ = v___y_1388_;
v___y_1328_ = v___y_1390_;
v___y_1329_ = v___y_1391_;
v___y_1330_ = v___x_1392_;
v___y_1331_ = v___x_1400_;
goto v___jp_1325_;
}
}
v___jp_1403_:
{
if (v___y_1406_ == 0)
{
lean_object* v_state_1407_; 
lean_del_object(v___x_1358_);
lean_dec(v_messageHead_1352_);
v_state_1407_ = lean_ctor_get(v_reader_1340_, 0);
if (lean_obj_tag(v_state_1407_) == 7)
{
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___y_1404_;
v___y_1390_ = v___y_1405_;
v___y_1391_ = v___y_1404_;
goto v___jp_1387_;
}
else
{
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___y_1404_;
v___y_1390_ = v___y_1405_;
v___y_1391_ = v___y_1406_;
goto v___jp_1387_;
}
}
else
{
uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; lean_object* v___f_1412_; uint8_t v___x_1413_; 
v___x_1408_ = 1;
v___x_1409_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1408_, v_a_1324_);
v___x_1410_ = l_Std_Http_Header_Name_contentLength;
v___f_1411_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1412_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1413_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1411_, v___f_1412_, v___x_1410_, v___x_1409_);
if (v___x_1413_ == 0)
{
v___y_1371_ = v___x_1408_;
v___y_1372_ = v___x_1409_;
goto v___jp_1370_;
}
else
{
lean_object* v_entries_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_entries_1414_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_entries_1414_);
lean_dec_ref(v___x_1409_);
v___x_1415_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v_entries_1414_);
v___x_1418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1419_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1419_ == 0)
{
lean_dec_ref(v_entries_1414_);
v___y_1371_ = v___x_1408_;
v___y_1372_ = v___x_1415_;
goto v___jp_1370_;
}
else
{
lean_object* v___f_1420_; size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v___f_1420_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = lean_usize_of_nat(v___x_1417_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1418_, v___f_1420_, v_entries_1414_, v___x_1421_, v___x_1422_, v___x_1415_);
v___y_1371_ = v___x_1408_;
v___y_1372_ = v___x_1423_;
goto v___jp_1370_;
}
}
}
}
v___jp_1424_:
{
if (v___y_1425_ == 0)
{
lean_del_object(v___x_1358_);
lean_dec(v_userDataBytes_1356_);
lean_dec(v_messageHead_1352_);
lean_dec(v_knownSize_1351_);
lean_dec(v_state_1350_);
lean_dec_ref(v_outputData_1349_);
lean_dec_ref(v_userData_1348_);
lean_dec(v_a_1324_);
v___y_1267_ = v___y_1260_;
v_omitBody_1268_ = v_omitBody_1355_;
goto v___jp_1266_;
}
else
{
lean_object* v_status_1426_; uint8_t v___x_1427_; uint16_t v___x_1428_; uint16_t v___x_1429_; uint8_t v___x_1430_; 
lean_inc(v_instant_1344_);
lean_inc(v_error_1343_);
lean_inc_ref(v_events_1342_);
lean_inc_ref(v_config_1341_);
lean_inc_ref(v_reader_1340_);
lean_dec_ref(v___y_1260_);
v_status_1426_ = lean_ctor_get(v_a_1324_, 0);
v___x_1427_ = 0;
v___x_1428_ = 100;
v___x_1429_ = l_Std_Http_Status_toCode(v_status_1426_);
v___x_1430_ = lean_uint16_dec_le(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
v___y_1404_ = v___y_1425_;
v___y_1405_ = v___x_1427_;
v___y_1406_ = v___x_1430_;
goto v___jp_1403_;
}
else
{
uint16_t v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = 200;
v___x_1432_ = lean_uint16_dec_lt(v___x_1429_, v___x_1431_);
v___y_1404_ = v___y_1425_;
v___y_1405_ = v___x_1427_;
v___y_1406_ = v___x_1432_;
goto v___jp_1403_;
}
}
}
v___jp_1435_:
{
if (v___x_1434_ == 0)
{
v___y_1425_ = v___x_1434_;
goto v___jp_1424_;
}
else
{
v___y_1425_ = v___y_1436_;
goto v___jp_1424_;
}
}
}
}
v___jp_1266_:
{
if (v_omitBody_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref(v_close_1263_);
lean_dec_ref(v_isClosed_1262_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_body_1261_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___y_1267_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___f_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; 
lean_inc(v_body_1261_);
v___x_1273_ = lean_apply_2(v_isClosed_1262_, v_body_1261_, lean_box(0));
v___f_1274_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1274_, 0, v___y_1267_);
lean_inc_ref(v___f_1274_);
v___f_1275_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1275_, 0, v___f_1274_);
v___f_1276_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1276_, 0, v_close_1263_);
lean_closure_set(v___f_1276_, 1, v_body_1261_);
lean_closure_set(v___f_1276_, 2, v___f_1275_);
lean_closure_set(v___f_1276_, 3, v___f_1274_);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = 0;
v___x_1279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1277_, v___x_1278_, v___x_1273_, v___f_1276_);
return v___x_1279_;
}
}
v___jp_1280_:
{
lean_object* v_writer_1282_; lean_object* v_reader_1283_; lean_object* v_config_1284_; lean_object* v_events_1285_; lean_object* v_error_1286_; lean_object* v_instant_1287_; uint8_t v_keepAlive_1288_; uint8_t v_forcedFlush_1289_; uint8_t v_pullBodyStalled_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1314_; 
v_writer_1282_ = lean_ctor_get(v___y_1281_, 1);
v_reader_1283_ = lean_ctor_get(v___y_1281_, 0);
v_config_1284_ = lean_ctor_get(v___y_1281_, 2);
v_events_1285_ = lean_ctor_get(v___y_1281_, 3);
v_error_1286_ = lean_ctor_get(v___y_1281_, 4);
v_instant_1287_ = lean_ctor_get(v___y_1281_, 5);
v_keepAlive_1288_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*6);
v_forcedFlush_1289_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1290_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*6 + 2);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___y_1281_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1292_ = v___y_1281_;
v_isShared_1293_ = v_isSharedCheck_1314_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_instant_1287_);
lean_inc(v_error_1286_);
lean_inc(v_events_1285_);
lean_inc(v_config_1284_);
lean_inc(v_writer_1282_);
lean_inc(v_reader_1283_);
lean_dec(v___y_1281_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1314_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_userData_1294_; lean_object* v_outputData_1295_; lean_object* v_knownSize_1296_; lean_object* v_messageHead_1297_; uint8_t v_sentMessage_1298_; uint8_t v_userClosedBody_1299_; uint8_t v_omitBody_1300_; lean_object* v_userDataBytes_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1312_; 
v_userData_1294_ = lean_ctor_get(v_writer_1282_, 0);
v_outputData_1295_ = lean_ctor_get(v_writer_1282_, 1);
v_knownSize_1296_ = lean_ctor_get(v_writer_1282_, 3);
v_messageHead_1297_ = lean_ctor_get(v_writer_1282_, 4);
v_sentMessage_1298_ = lean_ctor_get_uint8(v_writer_1282_, sizeof(void*)*6);
v_userClosedBody_1299_ = lean_ctor_get_uint8(v_writer_1282_, sizeof(void*)*6 + 1);
v_omitBody_1300_ = lean_ctor_get_uint8(v_writer_1282_, sizeof(void*)*6 + 2);
v_userDataBytes_1301_ = lean_ctor_get(v_writer_1282_, 5);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_writer_1282_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_writer_1282_, 2);
lean_dec(v_unused_1313_);
v___x_1303_ = v_writer_1282_;
v_isShared_1304_ = v_isSharedCheck_1312_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_userDataBytes_1301_);
lean_inc(v_messageHead_1297_);
lean_inc(v_knownSize_1296_);
lean_inc(v_outputData_1295_);
lean_inc(v_userData_1294_);
lean_dec(v_writer_1282_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1312_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(2);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 2, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_userData_1294_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_outputData_1295_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_knownSize_1296_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_messageHead_1297_);
lean_ctor_set(v_reuseFailAlloc_1311_, 5, v_userDataBytes_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*6, v_sentMessage_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*6 + 1, v_userClosedBody_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*6 + 2, v_omitBody_1300_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1307_);
v___x_1309_ = v___x_1292_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_reader_1283_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_config_1284_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_events_1285_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_error_1286_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_instant_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6, v_keepAlive_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6 + 1, v_forcedFlush_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6 + 2, v_pullBodyStalled_1290_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
v___y_1267_ = v___x_1309_;
v_omitBody_1268_ = v_omitBody_1300_;
goto v___jp_1266_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1440_, lean_object* v_body_1441_, lean_object* v_isClosed_1442_, lean_object* v_close_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1440_, v_body_1441_, v_isClosed_1442_, v_close_1443_, v_x_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_config_1447_, lean_object* v_line_1448_, lean_object* v_body_1449_, lean_object* v_isClosed_1450_, lean_object* v_close_1451_, lean_object* v_machine_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v___y_1456_; 
if (lean_obj_tag(v_x_1453_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_machine_1452_);
lean_dec_ref(v_close_1451_);
lean_dec_ref(v_isClosed_1450_);
lean_dec(v_body_1449_);
lean_dec_ref(v_line_1448_);
v_a_1462_ = lean_ctor_get(v_x_1453_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_x_1453_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_x_1453_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v_x_1453_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v_x_1453_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v_x_1453_, 1);
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_writer_1472_; lean_object* v_reader_1473_; lean_object* v_config_1474_; lean_object* v_events_1475_; lean_object* v_error_1476_; lean_object* v_instant_1477_; uint8_t v_keepAlive_1478_; uint8_t v_forcedFlush_1479_; uint8_t v_pullBodyStalled_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1503_; 
v_writer_1472_ = lean_ctor_get(v_machine_1452_, 1);
v_reader_1473_ = lean_ctor_get(v_machine_1452_, 0);
v_config_1474_ = lean_ctor_get(v_machine_1452_, 2);
v_events_1475_ = lean_ctor_get(v_machine_1452_, 3);
v_error_1476_ = lean_ctor_get(v_machine_1452_, 4);
v_instant_1477_ = lean_ctor_get(v_machine_1452_, 5);
v_keepAlive_1478_ = lean_ctor_get_uint8(v_machine_1452_, sizeof(void*)*6);
v_forcedFlush_1479_ = lean_ctor_get_uint8(v_machine_1452_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1480_ = lean_ctor_get_uint8(v_machine_1452_, sizeof(void*)*6 + 2);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_machine_1452_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1482_ = v_machine_1452_;
v_isShared_1483_ = v_isSharedCheck_1503_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_instant_1477_);
lean_inc(v_error_1476_);
lean_inc(v_events_1475_);
lean_inc(v_config_1474_);
lean_inc(v_writer_1472_);
lean_inc(v_reader_1473_);
lean_dec(v_machine_1452_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1503_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_userData_1484_; lean_object* v_outputData_1485_; lean_object* v_state_1486_; lean_object* v_messageHead_1487_; uint8_t v_sentMessage_1488_; uint8_t v_userClosedBody_1489_; uint8_t v_omitBody_1490_; lean_object* v_userDataBytes_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1501_; 
v_userData_1484_ = lean_ctor_get(v_writer_1472_, 0);
v_outputData_1485_ = lean_ctor_get(v_writer_1472_, 1);
v_state_1486_ = lean_ctor_get(v_writer_1472_, 2);
v_messageHead_1487_ = lean_ctor_get(v_writer_1472_, 4);
v_sentMessage_1488_ = lean_ctor_get_uint8(v_writer_1472_, sizeof(void*)*6);
v_userClosedBody_1489_ = lean_ctor_get_uint8(v_writer_1472_, sizeof(void*)*6 + 1);
v_omitBody_1490_ = lean_ctor_get_uint8(v_writer_1472_, sizeof(void*)*6 + 2);
v_userDataBytes_1491_ = lean_ctor_get(v_writer_1472_, 5);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_writer_1472_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_writer_1472_, 3);
lean_dec(v_unused_1502_);
v___x_1493_ = v_writer_1472_;
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_userDataBytes_1491_);
lean_inc(v_messageHead_1487_);
lean_inc(v_state_1486_);
lean_inc(v_outputData_1485_);
lean_inc(v_userData_1484_);
lean_dec(v_writer_1472_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 3, v_a_1471_);
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_userData_1484_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_outputData_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_state_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_a_1471_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_messageHead_1487_);
lean_ctor_set(v_reuseFailAlloc_1500_, 5, v_userDataBytes_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*6, v_sentMessage_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*6 + 1, v_userClosedBody_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*6 + 2, v_omitBody_1490_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1496_);
v___x_1498_ = v___x_1482_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_reader_1473_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_config_1474_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_events_1475_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_error_1476_);
lean_ctor_set(v_reuseFailAlloc_1499_, 5, v_instant_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*6, v_keepAlive_1478_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*6 + 1, v_forcedFlush_1479_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*6 + 2, v_pullBodyStalled_1480_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v___y_1456_ = v___x_1498_;
goto v___jp_1455_;
}
}
}
}
}
else
{
lean_dec(v_a_1471_);
v___y_1456_ = v_machine_1452_;
goto v___jp_1455_;
}
}
v___jp_1455_:
{
lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1457_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1447_, v_line_1448_);
v___f_1458_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1458_, 0, v___y_1456_);
lean_closure_set(v___f_1458_, 1, v_body_1449_);
lean_closure_set(v___f_1458_, 2, v_isClosed_1450_);
lean_closure_set(v___f_1458_, 3, v_close_1451_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = 0;
v___x_1461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1459_, v___x_1460_, v___x_1457_, v___f_1458_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_config_1504_, lean_object* v_line_1505_, lean_object* v_body_1506_, lean_object* v_isClosed_1507_, lean_object* v_close_1508_, lean_object* v_machine_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_config_1504_, v_line_1505_, v_body_1506_, v_isClosed_1507_, v_close_1508_, v_machine_1509_, v_x_1510_);
lean_dec_ref(v_config_1504_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1513_, lean_object* v_config_1514_, lean_object* v_machine_1515_, lean_object* v_res_1516_){
_start:
{
lean_object* v_close_1518_; lean_object* v_isClosed_1519_; lean_object* v_getKnownSize_1520_; lean_object* v_line_1521_; lean_object* v_body_1522_; lean_object* v___x_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
v_close_1518_ = lean_ctor_get(v_inst_1513_, 1);
lean_inc_ref(v_close_1518_);
v_isClosed_1519_ = lean_ctor_get(v_inst_1513_, 2);
lean_inc_ref(v_isClosed_1519_);
v_getKnownSize_1520_ = lean_ctor_get(v_inst_1513_, 5);
lean_inc_ref(v_getKnownSize_1520_);
lean_dec_ref(v_inst_1513_);
v_line_1521_ = lean_ctor_get(v_res_1516_, 0);
lean_inc_ref(v_line_1521_);
v_body_1522_ = lean_ctor_get(v_res_1516_, 1);
lean_inc_n(v_body_1522_, 2);
lean_dec_ref(v_res_1516_);
v___x_1523_ = lean_apply_2(v_getKnownSize_1520_, v_body_1522_, lean_box(0));
v___f_1524_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1524_, 0, v_config_1514_);
lean_closure_set(v___f_1524_, 1, v_line_1521_);
lean_closure_set(v___f_1524_, 2, v_body_1522_);
lean_closure_set(v___f_1524_, 3, v_isClosed_1519_);
lean_closure_set(v___f_1524_, 4, v_close_1518_);
lean_closure_set(v___f_1524_, 5, v_machine_1515_);
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = 0;
v___x_1527_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1525_, v___x_1526_, v___x_1523_, v___f_1524_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1528_, lean_object* v_config_1529_, lean_object* v_machine_1530_, lean_object* v_res_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1528_, v_config_1529_, v_machine_1530_, v_res_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1534_, lean_object* v_inst_1535_, lean_object* v_config_1536_, lean_object* v_machine_1537_, lean_object* v_res_1538_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1535_, v_config_1536_, v_machine_1537_, v_res_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1541_, lean_object* v_inst_1542_, lean_object* v_config_1543_, lean_object* v_machine_1544_, lean_object* v_res_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1541_, v_inst_1542_, v_config_1543_, v_machine_1544_, v_res_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v_closed_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_closed_1551_ = lean_ctor_get_uint8(v_____do__lift_1548_, sizeof(void*)*6);
v___x_1552_ = lean_box(v_closed_1551_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v_____do__lift_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v_pendingProducer_1567_; lean_object* v_pendingConsumer_1568_; lean_object* v_interestWaiter_1569_; uint8_t v_closed_1570_; lean_object* v_pendingIncompleteChunk_1571_; lean_object* v_closeError_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1581_; 
v___x_1566_ = lean_st_ref_take(v___y_1564_);
v_pendingProducer_1567_ = lean_ctor_get(v___x_1566_, 0);
v_pendingConsumer_1568_ = lean_ctor_get(v___x_1566_, 1);
v_interestWaiter_1569_ = lean_ctor_get(v___x_1566_, 2);
v_closed_1570_ = lean_ctor_get_uint8(v___x_1566_, sizeof(void*)*6);
v_pendingIncompleteChunk_1571_ = lean_ctor_get(v___x_1566_, 4);
v_closeError_1572_ = lean_ctor_get(v___x_1566_, 5);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v___x_1566_, 3);
lean_dec(v_unused_1582_);
v___x_1574_ = v___x_1566_;
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_closeError_1572_);
lean_inc(v_pendingIncompleteChunk_1571_);
lean_inc(v_interestWaiter_1569_);
lean_inc(v_pendingConsumer_1568_);
lean_inc(v_pendingProducer_1567_);
lean_dec(v___x_1566_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 3, v___x_1563_);
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_pendingProducer_1567_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_pendingConsumer_1568_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_interestWaiter_1569_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_pendingIncompleteChunk_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 5, v_closeError_1572_);
lean_ctor_set_uint8(v_reuseFailAlloc_1580_, sizeof(void*)*6, v_closed_1570_);
v___x_1577_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_st_ref_put(v___y_1564_, v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1583_, v___y_1584_);
lean_dec(v___y_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1587_, lean_object* v_x_1588_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v___x_1587_);
v_a_1590_ = lean_ctor_get(v_x_1588_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1588_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1592_ = v_x_1588_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v_x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
}
else
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1588_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_x_1588_, 0);
lean_dec(v_unused_1608_);
v___x_1600_ = v_x_1588_;
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_x_1588_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1587_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1609_, lean_object* v_x_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1609_, v_x_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1613_, lean_object* v_requestStream_1614_, lean_object* v_keepAliveTimeout_1615_, lean_object* v_currentTimeout_1616_, lean_object* v_headerTimeout_1617_, lean_object* v_response_1618_, lean_object* v_respStream_1619_, lean_object* v_expectData_1620_, uint8_t v_handlerDispatched_1621_, lean_object* v_____r_1622_){
_start:
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1624_ = 0;
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1626_, 0, v_machine_1613_);
lean_ctor_set(v___x_1626_, 1, v_requestStream_1614_);
lean_ctor_set(v___x_1626_, 2, v_keepAliveTimeout_1615_);
lean_ctor_set(v___x_1626_, 3, v_currentTimeout_1616_);
lean_ctor_set(v___x_1626_, 4, v_headerTimeout_1617_);
lean_ctor_set(v___x_1626_, 5, v_response_1618_);
lean_ctor_set(v___x_1626_, 6, v_respStream_1619_);
lean_ctor_set(v___x_1626_, 7, v_expectData_1620_);
lean_ctor_set(v___x_1626_, 8, v___x_1625_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*9, v___x_1624_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*9 + 1, v_handlerDispatched_1621_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1630_, lean_object* v_requestStream_1631_, lean_object* v_keepAliveTimeout_1632_, lean_object* v_currentTimeout_1633_, lean_object* v_headerTimeout_1634_, lean_object* v_response_1635_, lean_object* v_respStream_1636_, lean_object* v_expectData_1637_, lean_object* v_handlerDispatched_1638_, lean_object* v_____r_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v_handlerDispatched_boxed_1641_; lean_object* v_res_1642_; 
v_handlerDispatched_boxed_1641_ = lean_unbox(v_handlerDispatched_1638_);
v_res_1642_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1630_, v_requestStream_1631_, v_keepAliveTimeout_1632_, v_currentTimeout_1633_, v_headerTimeout_1634_, v_response_1635_, v_respStream_1636_, v_expectData_1637_, v_handlerDispatched_boxed_1641_, v_____r_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1643_, lean_object* v_x_1644_){
_start:
{
if (lean_obj_tag(v_x_1644_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v___f_1643_);
v_a_1646_ = lean_ctor_get(v_x_1644_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1644_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v_x_1644_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v_x_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1646_);
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
else
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v_x_1644_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v_x_1644_, 1);
v___x_1656_ = lean_apply_2(v___f_1643_, v_a_1655_, lean_box(0));
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1657_, v_x_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1661_, lean_object* v___f_1662_, lean_object* v___f_1663_, lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v___f_1663_);
lean_dec_ref(v___f_1662_);
lean_dec_ref(v_requestStream_1661_);
v_a_1666_ = lean_ctor_get(v_x_1664_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1664_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1668_ = v_x_1664_;
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v_x_1664_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1675_; uint8_t v___x_1676_; 
v_a_1675_ = lean_ctor_get(v_x_1664_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v_x_1664_, 1);
v___x_1676_ = lean_unbox(v_a_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v___f_1663_);
v___x_1677_ = l_Std_Http_Body_Stream_close(v_requestStream_1661_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_unbox(v_a_1675_);
lean_dec(v_a_1675_);
v___x_1680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1678_, v___x_1679_, v___x_1677_, v___f_1662_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v_a_1675_);
lean_dec_ref(v___f_1662_);
lean_dec_ref(v_requestStream_1661_);
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_apply_2(v___f_1663_, v___x_1681_, lean_box(0));
return v___x_1682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1683_, lean_object* v___f_1684_, lean_object* v___f_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1683_, v___f_1684_, v___f_1685_, v_x_1686_);
return v_res_1688_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1689_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1690_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; 
v___x_1696_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1697_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1698_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1698_, 0, v___f_1697_);
lean_closure_set(v___f_1698_, 1, v___x_1696_);
return v___f_1698_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; 
v___x_1707_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1708_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1709_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1709_, 0, v___f_1708_);
lean_closure_set(v___f_1709_, 1, v___x_1707_);
return v___f_1709_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1710_; lean_object* v___x_1711_; 
v___f_1710_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1711_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1711_, 0, lean_box(0));
lean_closure_set(v___x_1711_, 1, lean_box(0));
lean_closure_set(v___x_1711_, 2, lean_box(0));
lean_closure_set(v___x_1711_, 3, v___f_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1712_, lean_object* v___f_1713_, lean_object* v_x_1714_){
_start:
{
if (lean_obj_tag(v_x_1714_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v___f_1713_);
lean_dec_ref(v___y_1712_);
v_a_1716_ = lean_ctor_get(v_x_1714_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1714_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1718_ = v_x_1714_;
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v_x_1714_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
}
}
else
{
lean_object* v_machine_1725_; lean_object* v_requestStream_1726_; lean_object* v_keepAliveTimeout_1727_; lean_object* v_currentTimeout_1728_; lean_object* v_headerTimeout_1729_; lean_object* v_response_1730_; lean_object* v_respStream_1731_; lean_object* v_expectData_1732_; uint8_t v_handlerDispatched_1733_; lean_object* v___x_1734_; lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_4846__overap_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___f_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref_known(v_x_1714_, 1);
v_machine_1725_ = lean_ctor_get(v___y_1712_, 0);
lean_inc_ref(v_machine_1725_);
v_requestStream_1726_ = lean_ctor_get(v___y_1712_, 1);
lean_inc_ref_n(v_requestStream_1726_, 3);
v_keepAliveTimeout_1727_ = lean_ctor_get(v___y_1712_, 2);
lean_inc(v_keepAliveTimeout_1727_);
v_currentTimeout_1728_ = lean_ctor_get(v___y_1712_, 3);
lean_inc(v_currentTimeout_1728_);
v_headerTimeout_1729_ = lean_ctor_get(v___y_1712_, 4);
lean_inc(v_headerTimeout_1729_);
v_response_1730_ = lean_ctor_get(v___y_1712_, 5);
lean_inc_ref(v_response_1730_);
v_respStream_1731_ = lean_ctor_get(v___y_1712_, 6);
lean_inc(v_respStream_1731_);
v_expectData_1732_ = lean_ctor_get(v___y_1712_, 7);
lean_inc(v_expectData_1732_);
v_handlerDispatched_1733_ = lean_ctor_get_uint8(v___y_1712_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1712_);
v___x_1734_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1735_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1736_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1737_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1738_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1738_, 0, lean_box(0));
lean_closure_set(v___x_1738_, 1, lean_box(0));
lean_closure_set(v___x_1738_, 2, v___x_1734_);
lean_closure_set(v___x_1738_, 3, lean_box(0));
lean_closure_set(v___x_1738_, 4, lean_box(0));
lean_closure_set(v___x_1738_, 5, v___x_1737_);
lean_closure_set(v___x_1738_, 6, v___f_1713_);
v___x_4846__overap_1739_ = l_Std_Mutex_atomically___redArg(v___x_1734_, v___f_1735_, v___f_1736_, v_requestStream_1726_, v___x_1738_);
v___x_1740_ = lean_apply_1(v___x_4846__overap_1739_, lean_box(0));
v___x_1741_ = lean_box(v_handlerDispatched_1733_);
v___f_1742_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1742_, 0, v_machine_1725_);
lean_closure_set(v___f_1742_, 1, v_requestStream_1726_);
lean_closure_set(v___f_1742_, 2, v_keepAliveTimeout_1727_);
lean_closure_set(v___f_1742_, 3, v_currentTimeout_1728_);
lean_closure_set(v___f_1742_, 4, v_headerTimeout_1729_);
lean_closure_set(v___f_1742_, 5, v_response_1730_);
lean_closure_set(v___f_1742_, 6, v_respStream_1731_);
lean_closure_set(v___f_1742_, 7, v_expectData_1732_);
lean_closure_set(v___f_1742_, 8, v___x_1741_);
lean_inc_ref(v___f_1742_);
v___f_1743_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1743_, 0, v___f_1742_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1744_, 0, v_requestStream_1726_);
lean_closure_set(v___f_1744_, 1, v___f_1743_);
lean_closure_set(v___f_1744_, 2, v___f_1742_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = 0;
v___x_1747_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1745_, v___x_1746_, v___x_1740_, v___f_1744_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1748_, lean_object* v___f_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1748_, v___f_1749_, v_x_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1754_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___y_1753_);
v_a_1756_ = lean_ctor_get(v_x_1754_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_x_1754_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1758_ = v_x_1754_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v_x_1754_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
else
{
lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1773_; 
v_isSharedCheck_1773_ = !lean_is_exclusive(v_x_1754_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v_x_1754_, 0);
lean_dec(v_unused_1774_);
v___x_1766_ = v_x_1754_;
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v_x_1754_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___y_1753_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1775_, v_x_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1779_, lean_object* v___f_1780_, lean_object* v___y_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___f_1780_);
lean_dec_ref(v_requestStream_1779_);
v_a_1784_ = lean_ctor_get(v_x_1782_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_x_1782_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1786_ = v_x_1782_;
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v_x_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1807_; 
v_a_1793_ = lean_ctor_get(v_x_1782_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_x_1782_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1795_ = v_x_1782_;
v_isShared_1796_ = v_isSharedCheck_1807_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v_x_1782_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1807_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_unbox(v_a_1793_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; 
lean_del_object(v___x_1795_);
lean_dec_ref(v___y_1781_);
v___x_1798_ = l_Std_Http_Body_Stream_close(v_requestStream_1779_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_unbox(v_a_1793_);
lean_dec(v_a_1793_);
v___x_1801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1799_, v___x_1800_, v___x_1798_, v___f_1780_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_dec(v_a_1793_);
lean_dec_ref(v___f_1780_);
lean_dec_ref(v_requestStream_1779_);
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1781_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1802_);
v___x_1804_ = v___x_1795_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1808_, lean_object* v___f_1809_, lean_object* v___y_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1808_, v___f_1809_, v___y_1810_, v_x_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1814_, lean_object* v_machine_1815_, lean_object* v_a_1816_, uint8_t v_requiresData_1817_, lean_object* v_expectData_1818_, lean_object* v_pendingHead_1819_, lean_object* v_x_1820_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_pendingHead_1819_);
lean_dec(v_expectData_1818_);
lean_dec_ref(v_a_1816_);
lean_dec_ref(v_machine_1815_);
v_a_1822_ = lean_ctor_get(v_x_1820_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1824_ = v_x_1820_;
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v_x_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1845_; 
v_a_1831_ = lean_ctor_get(v_x_1820_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1833_ = v_x_1820_;
v_isShared_1834_ = v_isSharedCheck_1845_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v_x_1820_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1845_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_keepAliveTimeout_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v_keepAliveTimeout_1835_ = lean_ctor_get(v_config_1814_, 5);
lean_inc_n(v_keepAliveTimeout_1835_, 2);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_keepAliveTimeout_1835_);
v___x_1837_ = lean_box(0);
v___x_1838_ = 0;
v___x_1839_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1839_, 0, v_machine_1815_);
lean_ctor_set(v___x_1839_, 1, v_a_1816_);
lean_ctor_set(v___x_1839_, 2, v___x_1836_);
lean_ctor_set(v___x_1839_, 3, v_keepAliveTimeout_1835_);
lean_ctor_set(v___x_1839_, 4, v___x_1837_);
lean_ctor_set(v___x_1839_, 5, v_a_1831_);
lean_ctor_set(v___x_1839_, 6, v___x_1837_);
lean_ctor_set(v___x_1839_, 7, v_expectData_1818_);
lean_ctor_set(v___x_1839_, 8, v_pendingHead_1819_);
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*9, v_requiresData_1817_);
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*9 + 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1840_);
v___x_1842_ = v___x_1833_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1840_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1846_, lean_object* v_machine_1847_, lean_object* v_a_1848_, lean_object* v_requiresData_1849_, lean_object* v_expectData_1850_, lean_object* v_pendingHead_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v_requiresData_boxed_1854_; lean_object* v_res_1855_; 
v_requiresData_boxed_1854_ = lean_unbox(v_requiresData_1849_);
v_res_1855_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1846_, v_machine_1847_, v_a_1848_, v_requiresData_boxed_1854_, v_expectData_1850_, v_pendingHead_1851_, v_x_1852_);
lean_dec_ref(v_config_1846_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1856_, lean_object* v_machine_1857_, uint8_t v_requiresData_1858_, lean_object* v_expectData_1859_, lean_object* v_pendingHead_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_pendingHead_1860_);
lean_dec(v_expectData_1859_);
lean_dec_ref(v_machine_1857_);
lean_dec_ref(v_config_1856_);
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
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1887_; 
v_a_1872_ = lean_ctor_get(v_x_1861_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1861_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1874_ = v_x_1861_;
v_isShared_1875_ = v_isSharedCheck_1887_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_x_1861_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1887_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___x_1881_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = l_Std_CloseableChannel_new___redArg(v___x_1876_);
v___x_1878_ = lean_box(v_requiresData_1858_);
v___f_1879_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1879_, 0, v_config_1856_);
lean_closure_set(v___f_1879_, 1, v_machine_1857_);
lean_closure_set(v___f_1879_, 2, v_a_1872_);
lean_closure_set(v___f_1879_, 3, v___x_1878_);
lean_closure_set(v___f_1879_, 4, v_expectData_1859_);
lean_closure_set(v___f_1879_, 5, v_pendingHead_1860_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1877_);
v___x_1881_ = v___x_1874_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1877_);
v___x_1881_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = 0;
v___x_1885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1883_, v___x_1884_, v___x_1882_, v___f_1879_);
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1888_, lean_object* v_machine_1889_, lean_object* v_requiresData_1890_, lean_object* v_expectData_1891_, lean_object* v_pendingHead_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v_requiresData_boxed_1895_; lean_object* v_res_1896_; 
v_requiresData_boxed_1895_ = lean_unbox(v_requiresData_1890_);
v_res_1896_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1888_, v_machine_1889_, v_requiresData_boxed_1895_, v_expectData_1891_, v_pendingHead_1892_, v_x_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1897_, lean_object* v_____r_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = l_Std_Http_Body_mkStream();
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = 0;
v___x_1903_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1901_, v___x_1902_, v___x_1900_, v___f_1897_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1904_, lean_object* v_____r_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1904_, v_____r_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1908_, lean_object* v_val_1909_, lean_object* v___f_1910_, lean_object* v___f_1911_, lean_object* v_x_1912_){
_start:
{
if (lean_obj_tag(v_x_1912_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___f_1911_);
lean_dec_ref(v___f_1910_);
lean_dec(v_val_1909_);
lean_dec_ref(v_close_1908_);
v_a_1914_ = lean_ctor_get(v_x_1912_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1912_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1916_ = v_x_1912_;
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v_x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; uint8_t v___x_1924_; 
v_a_1923_ = lean_ctor_get(v_x_1912_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v_x_1912_, 1);
v___x_1924_ = lean_unbox(v_a_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; 
lean_dec_ref(v___f_1911_);
v___x_1925_ = lean_apply_2(v_close_1908_, v_val_1909_, lean_box(0));
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_unbox(v_a_1923_);
lean_dec(v_a_1923_);
v___x_1928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1926_, v___x_1927_, v___x_1925_, v___f_1910_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec(v_a_1923_);
lean_dec_ref(v___f_1910_);
lean_dec(v_val_1909_);
lean_dec_ref(v_close_1908_);
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_apply_2(v___f_1911_, v___x_1929_, lean_box(0));
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1931_, lean_object* v_val_1932_, lean_object* v___f_1933_, lean_object* v___f_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1931_, v_val_1932_, v___f_1933_, v___f_1934_, v_x_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1938_, lean_object* v_inst_1939_, lean_object* v___f_1940_, lean_object* v___f_1941_, lean_object* v_____r_1942_){
_start:
{
if (lean_obj_tag(v_respStream_1938_) == 1)
{
lean_object* v_val_1944_; lean_object* v_close_1945_; lean_object* v_isClosed_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; 
v_val_1944_ = lean_ctor_get(v_respStream_1938_, 0);
lean_inc_n(v_val_1944_, 2);
lean_dec_ref_known(v_respStream_1938_, 1);
v_close_1945_ = lean_ctor_get(v_inst_1939_, 1);
lean_inc_ref(v_close_1945_);
v_isClosed_1946_ = lean_ctor_get(v_inst_1939_, 2);
lean_inc_ref(v_isClosed_1946_);
lean_dec_ref(v_inst_1939_);
v___x_1947_ = lean_apply_2(v_isClosed_1946_, v_val_1944_, lean_box(0));
v___f_1948_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1948_, 0, v_close_1945_);
lean_closure_set(v___f_1948_, 1, v_val_1944_);
lean_closure_set(v___f_1948_, 2, v___f_1940_);
lean_closure_set(v___f_1948_, 3, v___f_1941_);
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = 0;
v___x_1951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1949_, v___x_1950_, v___x_1947_, v___f_1948_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec_ref(v___f_1940_);
lean_dec_ref(v_inst_1939_);
lean_dec(v_respStream_1938_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_apply_2(v___f_1941_, v___x_1952_, lean_box(0));
return v___x_1953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1954_, lean_object* v_inst_1955_, lean_object* v___f_1956_, lean_object* v___f_1957_, lean_object* v_____r_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1954_, v_inst_1955_, v___f_1956_, v___f_1957_, v_____r_1958_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1961_, lean_object* v_keepAliveTimeout_1962_, lean_object* v_currentTimeout_1963_, lean_object* v_headerTimeout_1964_, lean_object* v_response_1965_, lean_object* v_respStream_1966_, uint8_t v_requiresData_1967_, lean_object* v_expectData_1968_, uint8_t v_handlerDispatched_1969_, lean_object* v_pendingHead_1970_, lean_object* v_x_1971_){
_start:
{
if (lean_obj_tag(v_x_1971_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v_pendingHead_1970_);
lean_dec(v_expectData_1968_);
lean_dec(v_respStream_1966_);
lean_dec_ref(v_response_1965_);
lean_dec(v_headerTimeout_1964_);
lean_dec(v_currentTimeout_1963_);
lean_dec(v_keepAliveTimeout_1962_);
lean_dec_ref(v_requestStream_1961_);
v_a_1973_ = lean_ctor_get(v_x_1971_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_x_1971_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1975_ = v_x_1971_;
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v_x_1971_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2003_; 
v_a_1982_ = lean_ctor_get(v_x_1971_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1971_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1984_ = v_x_1971_;
v_isShared_1985_ = v_isSharedCheck_2003_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v_x_1971_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2003_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_snd_1986_; uint8_t v___x_1987_; 
v_snd_1986_ = lean_ctor_get(v_a_1982_, 1);
v___x_1987_ = lean_unbox(v_snd_1986_);
if (v___x_1987_ == 0)
{
lean_object* v_fst_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v_fst_1988_ = lean_ctor_get(v_a_1982_, 0);
lean_inc(v_fst_1988_);
lean_dec(v_a_1982_);
v___x_1989_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1989_, 0, v_fst_1988_);
lean_ctor_set(v___x_1989_, 1, v_requestStream_1961_);
lean_ctor_set(v___x_1989_, 2, v_keepAliveTimeout_1962_);
lean_ctor_set(v___x_1989_, 3, v_currentTimeout_1963_);
lean_ctor_set(v___x_1989_, 4, v_headerTimeout_1964_);
lean_ctor_set(v___x_1989_, 5, v_response_1965_);
lean_ctor_set(v___x_1989_, 6, v_respStream_1966_);
lean_ctor_set(v___x_1989_, 7, v_expectData_1968_);
lean_ctor_set(v___x_1989_, 8, v_pendingHead_1970_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*9, v_requiresData_1967_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*9 + 1, v_handlerDispatched_1969_);
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1990_);
v___x_1992_ = v___x_1984_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
else
{
lean_object* v_fst_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_pendingHead_1970_);
v_fst_1995_ = lean_ctor_get(v_a_1982_, 0);
lean_inc(v_fst_1995_);
lean_dec(v_a_1982_);
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1997_, 0, v_fst_1995_);
lean_ctor_set(v___x_1997_, 1, v_requestStream_1961_);
lean_ctor_set(v___x_1997_, 2, v_keepAliveTimeout_1962_);
lean_ctor_set(v___x_1997_, 3, v_currentTimeout_1963_);
lean_ctor_set(v___x_1997_, 4, v_headerTimeout_1964_);
lean_ctor_set(v___x_1997_, 5, v_response_1965_);
lean_ctor_set(v___x_1997_, 6, v_respStream_1966_);
lean_ctor_set(v___x_1997_, 7, v_expectData_1968_);
lean_ctor_set(v___x_1997_, 8, v___x_1996_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*9, v_requiresData_1967_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*9 + 1, v_handlerDispatched_1969_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1998_);
v___x_2000_ = v___x_1984_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2004_, lean_object* v_keepAliveTimeout_2005_, lean_object* v_currentTimeout_2006_, lean_object* v_headerTimeout_2007_, lean_object* v_response_2008_, lean_object* v_respStream_2009_, lean_object* v_requiresData_2010_, lean_object* v_expectData_2011_, lean_object* v_handlerDispatched_2012_, lean_object* v_pendingHead_2013_, lean_object* v_x_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v_requiresData_boxed_2016_; uint8_t v_handlerDispatched_boxed_2017_; lean_object* v_res_2018_; 
v_requiresData_boxed_2016_ = lean_unbox(v_requiresData_2010_);
v_handlerDispatched_boxed_2017_ = lean_unbox(v_handlerDispatched_2012_);
v_res_2018_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2004_, v_keepAliveTimeout_2005_, v_currentTimeout_2006_, v_headerTimeout_2007_, v_response_2008_, v_respStream_2009_, v_requiresData_boxed_2016_, v_expectData_2011_, v_handlerDispatched_boxed_2017_, v_pendingHead_2013_, v_x_2014_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2031_, lean_object* v_inst_2032_, lean_object* v___f_2033_, lean_object* v_handler_2034_, lean_object* v___f_2035_, lean_object* v___f_2036_, lean_object* v_inst_2037_, lean_object* v_connectionContext_2038_, lean_object* v_a_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_){
_start:
{
switch(lean_obj_tag(v_a_2039_))
{
case 0:
{
lean_object* v_head_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v_inst_2037_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2035_);
lean_dec(v_handler_2034_);
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2032_);
v_head_2043_ = lean_ctor_get(v_a_2039_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2045_ = v_a_2039_;
v_isShared_2046_ = v_isSharedCheck_2086_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_head_2043_);
lean_dec(v_a_2039_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2086_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v_machine_2047_; lean_object* v_requestStream_2048_; lean_object* v_response_2049_; lean_object* v_respStream_2050_; uint8_t v_requiresData_2051_; lean_object* v_expectData_2052_; uint8_t v_handlerDispatched_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2081_; 
v_machine_2047_ = lean_ctor_get(v___y_2041_, 0);
v_requestStream_2048_ = lean_ctor_get(v___y_2041_, 1);
v_response_2049_ = lean_ctor_get(v___y_2041_, 5);
v_respStream_2050_ = lean_ctor_get(v___y_2041_, 6);
v_requiresData_2051_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*9);
v_expectData_2052_ = lean_ctor_get(v___y_2041_, 7);
v_handlerDispatched_2053_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*9 + 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___y_2041_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; lean_object* v_unused_2085_; 
v_unused_2082_ = lean_ctor_get(v___y_2041_, 8);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v___y_2041_, 4);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v___y_2041_, 3);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v___y_2041_, 2);
lean_dec(v_unused_2085_);
v___x_2055_ = v___y_2041_;
v_isShared_2056_ = v_isSharedCheck_2081_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_expectData_2052_);
lean_inc(v_respStream_2050_);
lean_inc(v_response_2049_);
lean_inc(v_requestStream_2048_);
lean_inc(v_machine_2047_);
lean_dec(v___y_2041_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2081_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_lingeringTimeout_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v_lingeringTimeout_2057_ = lean_ctor_get(v_config_2031_, 4);
lean_inc(v_lingeringTimeout_2057_);
lean_dec_ref(v_config_2031_);
v___x_2058_ = lean_box(0);
lean_inc(v_head_2043_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 1);
v___x_2060_ = v___x_2045_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_head_2043_);
v___x_2060_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
lean_inc_ref(v_requestStream_2048_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 8, v___x_2060_);
lean_ctor_set(v___x_2055_, 4, v___x_2058_);
lean_ctor_set(v___x_2055_, 3, v_lingeringTimeout_2057_);
lean_ctor_set(v___x_2055_, 2, v___x_2058_);
v___x_2062_ = v___x_2055_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_machine_2047_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_requestStream_2048_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_lingeringTimeout_2057_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v_response_2049_);
lean_ctor_set(v_reuseFailAlloc_2079_, 6, v_respStream_2050_);
lean_ctor_set(v_reuseFailAlloc_2079_, 7, v_expectData_2052_);
lean_ctor_set(v_reuseFailAlloc_2079_, 8, v___x_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, sizeof(void*)*9, v_requiresData_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, sizeof(void*)*9 + 1, v_handlerDispatched_2053_);
v___x_2062_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
uint8_t v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = 0;
v___x_2064_ = 1;
v___x_2065_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2063_, v_head_2043_, v___x_2064_);
lean_dec(v_head_2043_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___f_2069_; lean_object* v___x_5039__overap_2070_; lean_object* v___x_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; 
v___f_2066_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2066_, 0, v___x_2065_);
v___x_2067_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2068_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2069_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5039__overap_2070_ = l_Std_Mutex_atomically___redArg(v___x_2067_, v___f_2068_, v___f_2069_, v_requestStream_2048_, v___f_2066_);
v___x_2071_ = lean_apply_1(v___x_5039__overap_2070_, lean_box(0));
v___f_2072_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2072_, 0, v___x_2062_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = 0;
v___x_2075_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2073_, v___x_2074_, v___x_2071_, v___f_2072_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v___x_2065_);
lean_dec_ref(v_requestStream_2048_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2062_);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v_inst_2037_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2035_);
lean_dec(v_handler_2034_);
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_config_2031_);
v_size_2087_ = lean_ctor_get(v_a_2039_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2089_ = v_a_2039_;
v_isShared_2090_ = v_isSharedCheck_2114_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_size_2087_);
lean_dec(v_a_2039_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2114_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_machine_2091_; lean_object* v_requestStream_2092_; lean_object* v_keepAliveTimeout_2093_; lean_object* v_currentTimeout_2094_; lean_object* v_headerTimeout_2095_; lean_object* v_response_2096_; lean_object* v_respStream_2097_; uint8_t v_handlerDispatched_2098_; lean_object* v_pendingHead_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2112_; 
v_machine_2091_ = lean_ctor_get(v___y_2041_, 0);
v_requestStream_2092_ = lean_ctor_get(v___y_2041_, 1);
v_keepAliveTimeout_2093_ = lean_ctor_get(v___y_2041_, 2);
v_currentTimeout_2094_ = lean_ctor_get(v___y_2041_, 3);
v_headerTimeout_2095_ = lean_ctor_get(v___y_2041_, 4);
v_response_2096_ = lean_ctor_get(v___y_2041_, 5);
v_respStream_2097_ = lean_ctor_get(v___y_2041_, 6);
v_handlerDispatched_2098_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*9 + 1);
v_pendingHead_2099_ = lean_ctor_get(v___y_2041_, 8);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___y_2041_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v___y_2041_, 7);
lean_dec(v_unused_2113_);
v___x_2101_ = v___y_2041_;
v_isShared_2102_ = v_isSharedCheck_2112_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_pendingHead_2099_);
lean_inc(v_respStream_2097_);
lean_inc(v_response_2096_);
lean_inc(v_headerTimeout_2095_);
lean_inc(v_currentTimeout_2094_);
lean_inc(v_keepAliveTimeout_2093_);
lean_inc(v_requestStream_2092_);
lean_inc(v_machine_2091_);
lean_dec(v___y_2041_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2112_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
uint8_t v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = 1;
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 7, v_size_2087_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_machine_2091_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_requestStream_2092_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_keepAliveTimeout_2093_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_currentTimeout_2094_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_headerTimeout_2095_);
lean_ctor_set(v_reuseFailAlloc_2111_, 5, v_response_2096_);
lean_ctor_set(v_reuseFailAlloc_2111_, 6, v_respStream_2097_);
lean_ctor_set(v_reuseFailAlloc_2111_, 7, v_size_2087_);
lean_ctor_set(v_reuseFailAlloc_2111_, 8, v_pendingHead_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*9 + 1, v_handlerDispatched_2098_);
v___x_2105_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*9, v___x_2103_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2105_);
v___x_2107_ = v___x_2089_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
return v___x_2109_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2115_; lean_object* v_onFailure_2116_; lean_object* v___f_2117_; lean_object* v___y_2119_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v_inst_2037_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v_config_2031_);
v_err_2115_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_err_2115_);
lean_dec_ref_known(v_a_2039_, 1);
v_onFailure_2116_ = lean_ctor_get(v_inst_2032_, 2);
lean_inc_ref(v_onFailure_2116_);
lean_dec_ref(v_inst_2032_);
v___f_2117_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2117_, 0, v___y_2041_);
lean_closure_set(v___f_2117_, 1, v___f_2033_);
switch(lean_obj_tag(v_err_2115_))
{
case 0:
{
lean_object* v___x_2125_; 
v___x_2125_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2119_ = v___x_2125_;
goto v___jp_2118_;
}
case 1:
{
lean_object* v___x_2126_; 
v___x_2126_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2119_ = v___x_2126_;
goto v___jp_2118_;
}
case 2:
{
lean_object* v___x_2127_; 
v___x_2127_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2119_ = v___x_2127_;
goto v___jp_2118_;
}
case 3:
{
lean_object* v___x_2128_; 
v___x_2128_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2119_ = v___x_2128_;
goto v___jp_2118_;
}
case 4:
{
lean_object* v___x_2129_; 
v___x_2129_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2119_ = v___x_2129_;
goto v___jp_2118_;
}
case 5:
{
lean_object* v___x_2130_; 
v___x_2130_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2119_ = v___x_2130_;
goto v___jp_2118_;
}
case 6:
{
lean_object* v___x_2131_; 
v___x_2131_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2119_ = v___x_2131_;
goto v___jp_2118_;
}
case 7:
{
lean_object* v___x_2132_; 
v___x_2132_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2119_ = v___x_2132_;
goto v___jp_2118_;
}
case 8:
{
lean_object* v___x_2133_; 
v___x_2133_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2119_ = v___x_2133_;
goto v___jp_2118_;
}
case 9:
{
lean_object* v___x_2134_; 
v___x_2134_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2119_ = v___x_2134_;
goto v___jp_2118_;
}
case 10:
{
lean_object* v___x_2135_; 
v___x_2135_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2119_ = v___x_2135_;
goto v___jp_2118_;
}
default: 
{
lean_object* v_message_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_message_2136_ = lean_ctor_get(v_err_2115_, 0);
lean_inc_ref(v_message_2136_);
lean_dec_ref_known(v_err_2115_, 1);
v___x_2137_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2138_ = lean_string_append(v___x_2137_, v_message_2136_);
lean_dec_ref(v_message_2136_);
v___y_2119_ = v___x_2138_;
goto v___jp_2118_;
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2120_ = lean_mk_io_user_error(v___y_2119_);
v___x_2121_ = lean_apply_3(v_onFailure_2116_, v_handler_2034_, v___x_2120_, lean_box(0));
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = 0;
v___x_2124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2122_, v___x_2123_, v___x_2121_, v___f_2117_);
return v___x_2124_;
}
}
case 4:
{
lean_object* v_requestStream_2139_; lean_object* v___x_2140_; lean_object* v___f_2141_; lean_object* v___f_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_5095__overap_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v_inst_2037_);
lean_dec_ref(v___f_2036_);
lean_dec(v_handler_2034_);
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_config_2031_);
v_requestStream_2139_ = lean_ctor_get(v___y_2041_, 1);
lean_inc_ref_n(v_requestStream_2139_, 2);
v___x_2140_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2141_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2142_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2143_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2144_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2144_, 0, lean_box(0));
lean_closure_set(v___x_2144_, 1, lean_box(0));
lean_closure_set(v___x_2144_, 2, v___x_2140_);
lean_closure_set(v___x_2144_, 3, lean_box(0));
lean_closure_set(v___x_2144_, 4, lean_box(0));
lean_closure_set(v___x_2144_, 5, v___x_2143_);
lean_closure_set(v___x_2144_, 6, v___f_2035_);
v___x_5095__overap_2145_ = l_Std_Mutex_atomically___redArg(v___x_2140_, v___f_2141_, v___f_2142_, v_requestStream_2139_, v___x_2144_);
v___x_2146_ = lean_apply_1(v___x_5095__overap_2145_, lean_box(0));
lean_inc_ref(v___y_2041_);
v___f_2147_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2147_, 0, v___y_2041_);
v___f_2148_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2148_, 0, v_requestStream_2139_);
lean_closure_set(v___f_2148_, 1, v___f_2147_);
lean_closure_set(v___f_2148_, 2, v___y_2041_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = 0;
v___x_2151_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2149_, v___x_2150_, v___x_2146_, v___f_2148_);
return v___x_2151_;
}
case 6:
{
lean_object* v_machine_2152_; lean_object* v_requestStream_2153_; lean_object* v_respStream_2154_; uint8_t v_requiresData_2155_; lean_object* v_expectData_2156_; lean_object* v_pendingHead_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_5116__overap_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v___f_2035_);
lean_dec(v_handler_2034_);
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2032_);
v_machine_2152_ = lean_ctor_get(v___y_2041_, 0);
lean_inc_ref(v_machine_2152_);
v_requestStream_2153_ = lean_ctor_get(v___y_2041_, 1);
lean_inc_ref_n(v_requestStream_2153_, 2);
v_respStream_2154_ = lean_ctor_get(v___y_2041_, 6);
lean_inc(v_respStream_2154_);
v_requiresData_2155_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*9);
v_expectData_2156_ = lean_ctor_get(v___y_2041_, 7);
lean_inc(v_expectData_2156_);
v_pendingHead_2157_ = lean_ctor_get(v___y_2041_, 8);
lean_inc(v_pendingHead_2157_);
lean_dec_ref(v___y_2041_);
v___x_2158_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2159_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2160_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2161_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2162_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2162_, 0, lean_box(0));
lean_closure_set(v___x_2162_, 1, lean_box(0));
lean_closure_set(v___x_2162_, 2, v___x_2158_);
lean_closure_set(v___x_2162_, 3, lean_box(0));
lean_closure_set(v___x_2162_, 4, lean_box(0));
lean_closure_set(v___x_2162_, 5, v___x_2161_);
lean_closure_set(v___x_2162_, 6, v___f_2036_);
v___x_5116__overap_2163_ = l_Std_Mutex_atomically___redArg(v___x_2158_, v___f_2159_, v___f_2160_, v_requestStream_2153_, v___x_2162_);
v___x_2164_ = lean_apply_1(v___x_5116__overap_2163_, lean_box(0));
v___x_2165_ = lean_box(v_requiresData_2155_);
v___f_2166_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2166_, 0, v_config_2031_);
lean_closure_set(v___f_2166_, 1, v_machine_2152_);
lean_closure_set(v___f_2166_, 2, v___x_2165_);
lean_closure_set(v___f_2166_, 3, v_expectData_2156_);
lean_closure_set(v___f_2166_, 4, v_pendingHead_2157_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2167_, 0, v___f_2166_);
lean_inc_ref(v___f_2167_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2168_, 0, v___f_2167_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2169_, 0, v_respStream_2154_);
lean_closure_set(v___f_2169_, 1, v_inst_2037_);
lean_closure_set(v___f_2169_, 2, v___f_2168_);
lean_closure_set(v___f_2169_, 3, v___f_2167_);
lean_inc_ref(v___f_2169_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2170_, 0, v___f_2169_);
v___f_2171_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2171_, 0, v_requestStream_2153_);
lean_closure_set(v___f_2171_, 1, v___f_2170_);
lean_closure_set(v___f_2171_, 2, v___f_2169_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = 0;
v___x_2174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2172_, v___x_2173_, v___x_2164_, v___f_2171_);
return v___x_2174_;
}
case 7:
{
lean_object* v_pendingHead_2175_; 
lean_dec_ref(v_inst_2037_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2033_);
v_pendingHead_2175_ = lean_ctor_get(v___y_2041_, 8);
if (lean_obj_tag(v_pendingHead_2175_) == 1)
{
lean_object* v_machine_2176_; lean_object* v_requestStream_2177_; lean_object* v_keepAliveTimeout_2178_; lean_object* v_currentTimeout_2179_; lean_object* v_headerTimeout_2180_; lean_object* v_response_2181_; lean_object* v_respStream_2182_; uint8_t v_requiresData_2183_; lean_object* v_expectData_2184_; uint8_t v_handlerDispatched_2185_; lean_object* v_val_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___f_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
lean_inc_ref(v_pendingHead_2175_);
v_machine_2176_ = lean_ctor_get(v___y_2041_, 0);
lean_inc_ref(v_machine_2176_);
v_requestStream_2177_ = lean_ctor_get(v___y_2041_, 1);
lean_inc_ref(v_requestStream_2177_);
v_keepAliveTimeout_2178_ = lean_ctor_get(v___y_2041_, 2);
lean_inc(v_keepAliveTimeout_2178_);
v_currentTimeout_2179_ = lean_ctor_get(v___y_2041_, 3);
lean_inc(v_currentTimeout_2179_);
v_headerTimeout_2180_ = lean_ctor_get(v___y_2041_, 4);
lean_inc(v_headerTimeout_2180_);
v_response_2181_ = lean_ctor_get(v___y_2041_, 5);
lean_inc_ref(v_response_2181_);
v_respStream_2182_ = lean_ctor_get(v___y_2041_, 6);
lean_inc(v_respStream_2182_);
v_requiresData_2183_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*9);
v_expectData_2184_ = lean_ctor_get(v___y_2041_, 7);
lean_inc(v_expectData_2184_);
v_handlerDispatched_2185_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2041_);
v_val_2186_ = lean_ctor_get(v_pendingHead_2175_, 0);
lean_inc(v_val_2186_);
v___x_2187_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2032_, v_handler_2034_, v_machine_2176_, v_val_2186_, v_config_2031_, v_connectionContext_2038_);
v___x_2188_ = lean_box(v_requiresData_2183_);
v___x_2189_ = lean_box(v_handlerDispatched_2185_);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2190_, 0, v_requestStream_2177_);
lean_closure_set(v___f_2190_, 1, v_keepAliveTimeout_2178_);
lean_closure_set(v___f_2190_, 2, v_currentTimeout_2179_);
lean_closure_set(v___f_2190_, 3, v_headerTimeout_2180_);
lean_closure_set(v___f_2190_, 4, v_response_2181_);
lean_closure_set(v___f_2190_, 5, v_respStream_2182_);
lean_closure_set(v___f_2190_, 6, v___x_2188_);
lean_closure_set(v___f_2190_, 7, v_expectData_2184_);
lean_closure_set(v___f_2190_, 8, v___x_2189_);
lean_closure_set(v___f_2190_, 9, v_pendingHead_2175_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = 0;
v___x_2193_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2191_, v___x_2192_, v___x_2187_, v___f_2190_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec(v_handler_2034_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_config_2031_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___y_2041_);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
}
default: 
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec(v_a_2039_);
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v_inst_2037_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2035_);
lean_dec(v_handler_2034_);
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_config_2031_);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2041_);
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2200_, lean_object* v_inst_2201_, lean_object* v___f_2202_, lean_object* v_handler_2203_, lean_object* v___f_2204_, lean_object* v___f_2205_, lean_object* v_inst_2206_, lean_object* v_connectionContext_2207_, lean_object* v_a_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2200_, v_inst_2201_, v___f_2202_, v_handler_2203_, v___f_2204_, v___f_2205_, v_inst_2206_, v_connectionContext_2207_, v_a_2208_, v_x_2209_, v___y_2210_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_x_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_handler_2223_, lean_object* v_config_2224_, lean_object* v_connectionContext_2225_, lean_object* v_events_2226_, lean_object* v_state_2227_){
_start:
{
lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; size_t v_sz_2232_; size_t v___x_2233_; lean_object* v___x_4070__overap_2234_; lean_object* v___x_2235_; lean_object* v___f_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; 
v___f_2229_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2230_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2230_, 0, v_config_2224_);
lean_closure_set(v___f_2230_, 1, v_inst_2221_);
lean_closure_set(v___f_2230_, 2, v___f_2229_);
lean_closure_set(v___f_2230_, 3, v_handler_2223_);
lean_closure_set(v___f_2230_, 4, v___f_2229_);
lean_closure_set(v___f_2230_, 5, v___f_2229_);
lean_closure_set(v___f_2230_, 6, v_inst_2222_);
lean_closure_set(v___f_2230_, 7, v_connectionContext_2225_);
v___x_2231_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2232_ = lean_array_size(v_events_2226_);
v___x_2233_ = ((size_t)0ULL);
v___x_4070__overap_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2231_, v_events_2226_, v___f_2230_, v_sz_2232_, v___x_2233_, v_state_2227_);
v___x_2235_ = lean_apply_1(v___x_4070__overap_2234_, lean_box(0));
v___f_2236_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2237_ = lean_unsigned_to_nat(0u);
v___x_2238_ = 0;
v___x_2239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2237_, v___x_2238_, v___x_2235_, v___f_2236_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_handler_2242_, lean_object* v_config_2243_, lean_object* v_connectionContext_2244_, lean_object* v_events_2245_, lean_object* v_state_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2240_, v_inst_2241_, v_handler_2242_, v_config_2243_, v_connectionContext_2244_, v_events_2245_, v_state_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2249_, lean_object* v_00_u03b2_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_handler_2253_, lean_object* v_config_2254_, lean_object* v_connectionContext_2255_, lean_object* v_events_2256_, lean_object* v_state_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2251_, v_inst_2252_, v_handler_2253_, v_config_2254_, v_connectionContext_2255_, v_events_2256_, v_state_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_handler_2264_, lean_object* v_config_2265_, lean_object* v_connectionContext_2266_, lean_object* v_events_2267_, lean_object* v_state_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2260_, v_00_u03b2_2261_, v_inst_2262_, v_inst_2263_, v_handler_2264_, v_config_2265_, v_connectionContext_2266_, v_events_2267_, v_state_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v_x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_x_2271_, 1);
v___x_2273_ = lean_task_pure(v_a_2272_);
return v___x_2273_;
}
else
{
lean_object* v_a_2274_; 
v_a_2274_ = lean_ctor_get(v_x_2271_, 0);
lean_inc_ref(v_a_2274_);
lean_dec_ref_known(v_x_2271_, 1);
return v_a_2274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2275_, lean_object* v_requestStream_2276_, lean_object* v_keepAliveTimeout_2277_, lean_object* v_currentTimeout_2278_, lean_object* v_headerTimeout_2279_, lean_object* v_response_2280_, lean_object* v_respStream_2281_, uint8_t v_requiresData_2282_, lean_object* v_expectData_2283_, lean_object* v_x_2284_){
_start:
{
if (lean_obj_tag(v_x_2284_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_expectData_2283_);
lean_dec(v_respStream_2281_);
lean_dec_ref(v_response_2280_);
lean_dec(v_headerTimeout_2279_);
lean_dec(v_currentTimeout_2278_);
lean_dec(v_keepAliveTimeout_2277_);
lean_dec_ref(v_requestStream_2276_);
lean_dec_ref(v_machine_2275_);
v_a_2286_ = lean_ctor_get(v_x_2284_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_x_2284_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2288_ = v_x_2284_;
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v_x_2284_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
}
}
else
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2305_; 
v_isSharedCheck_2305_ = !lean_is_exclusive(v_x_2284_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; 
v_unused_2306_ = lean_ctor_get(v_x_2284_, 0);
lean_dec(v_unused_2306_);
v___x_2296_ = v_x_2284_;
v_isShared_2297_ = v_isSharedCheck_2305_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v_x_2284_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2305_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2298_ = 1;
v___x_2299_ = lean_box(0);
v___x_2300_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2300_, 0, v_machine_2275_);
lean_ctor_set(v___x_2300_, 1, v_requestStream_2276_);
lean_ctor_set(v___x_2300_, 2, v_keepAliveTimeout_2277_);
lean_ctor_set(v___x_2300_, 3, v_currentTimeout_2278_);
lean_ctor_set(v___x_2300_, 4, v_headerTimeout_2279_);
lean_ctor_set(v___x_2300_, 5, v_response_2280_);
lean_ctor_set(v___x_2300_, 6, v_respStream_2281_);
lean_ctor_set(v___x_2300_, 7, v_expectData_2283_);
lean_ctor_set(v___x_2300_, 8, v___x_2299_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*9, v_requiresData_2282_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*9 + 1, v___x_2298_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2300_);
v___x_2302_ = v___x_2296_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2307_, lean_object* v_requestStream_2308_, lean_object* v_keepAliveTimeout_2309_, lean_object* v_currentTimeout_2310_, lean_object* v_headerTimeout_2311_, lean_object* v_response_2312_, lean_object* v_respStream_2313_, lean_object* v_requiresData_2314_, lean_object* v_expectData_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v_requiresData_boxed_2318_; lean_object* v_res_2319_; 
v_requiresData_boxed_2318_ = lean_unbox(v_requiresData_2314_);
v_res_2319_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2307_, v_requestStream_2308_, v_keepAliveTimeout_2309_, v_currentTimeout_2310_, v_headerTimeout_2311_, v_response_2312_, v_respStream_2313_, v_requiresData_boxed_2318_, v_expectData_2315_, v_x_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2320_, lean_object* v_response_2321_, lean_object* v___x_2322_, lean_object* v___f_2323_, lean_object* v_x_2324_){
_start:
{
if (lean_obj_tag(v_x_2324_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___f_2323_);
lean_dec(v___x_2322_);
lean_dec_ref(v_response_2321_);
lean_dec_ref(v_toFunctor_2320_);
v_a_2326_ = lean_ctor_get(v_x_2324_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2324_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v_x_2324_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v_x_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2349_; 
v_a_2335_ = lean_ctor_get(v_x_2324_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_x_2324_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2337_ = v_x_2324_;
v_isShared_2338_ = v_isSharedCheck_2349_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v_x_2324_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2349_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2339_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2339_, 0, lean_box(0));
lean_closure_set(v___x_2339_, 1, lean_box(0));
lean_closure_set(v___x_2339_, 2, v_toFunctor_2320_);
v___x_2340_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2340_, 0, lean_box(0));
lean_closure_set(v___x_2340_, 1, v_response_2321_);
v___x_2341_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2341_, 0, lean_box(0));
lean_closure_set(v___x_2341_, 1, lean_box(0));
lean_closure_set(v___x_2341_, 2, lean_box(0));
lean_closure_set(v___x_2341_, 3, v___x_2339_);
lean_closure_set(v___x_2341_, 4, v___x_2340_);
v___x_2342_ = 0;
lean_inc(v___x_2322_);
v___x_2343_ = l_BaseIO_chainTask___redArg(v_a_2335_, v___x_2341_, v___x_2322_, v___x_2342_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2343_);
v___x_2345_ = v___x_2337_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
v___x_2347_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2322_, v___x_2342_, v___x_2346_, v___f_2323_);
return v___x_2347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2350_, lean_object* v_response_2351_, lean_object* v___x_2352_, lean_object* v___f_2353_, lean_object* v_x_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2350_, v_response_2351_, v___x_2352_, v___f_2353_, v_x_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2358_, lean_object* v_handler_2359_, lean_object* v_extensions_2360_, lean_object* v_connectionContext_2361_, lean_object* v_state_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v_toApplicative_2365_; lean_object* v_pendingHead_2366_; 
v___x_2364_ = l_instMonadBaseIO;
v_toApplicative_2365_ = lean_ctor_get(v___x_2364_, 0);
v_pendingHead_2366_ = lean_ctor_get(v_state_2362_, 8);
lean_inc(v_pendingHead_2366_);
if (lean_obj_tag(v_pendingHead_2366_) == 1)
{
lean_object* v_toFunctor_2367_; lean_object* v_machine_2368_; lean_object* v_requestStream_2369_; lean_object* v_keepAliveTimeout_2370_; lean_object* v_currentTimeout_2371_; lean_object* v_headerTimeout_2372_; lean_object* v_response_2373_; lean_object* v_respStream_2374_; uint8_t v_requiresData_2375_; lean_object* v_expectData_2376_; lean_object* v_val_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2399_; 
v_toFunctor_2367_ = lean_ctor_get(v_toApplicative_2365_, 0);
v_machine_2368_ = lean_ctor_get(v_state_2362_, 0);
lean_inc_ref(v_machine_2368_);
v_requestStream_2369_ = lean_ctor_get(v_state_2362_, 1);
lean_inc_ref(v_requestStream_2369_);
v_keepAliveTimeout_2370_ = lean_ctor_get(v_state_2362_, 2);
lean_inc(v_keepAliveTimeout_2370_);
v_currentTimeout_2371_ = lean_ctor_get(v_state_2362_, 3);
lean_inc(v_currentTimeout_2371_);
v_headerTimeout_2372_ = lean_ctor_get(v_state_2362_, 4);
lean_inc(v_headerTimeout_2372_);
v_response_2373_ = lean_ctor_get(v_state_2362_, 5);
lean_inc_ref(v_response_2373_);
v_respStream_2374_ = lean_ctor_get(v_state_2362_, 6);
lean_inc(v_respStream_2374_);
v_requiresData_2375_ = lean_ctor_get_uint8(v_state_2362_, sizeof(void*)*9);
v_expectData_2376_ = lean_ctor_get(v_state_2362_, 7);
lean_inc(v_expectData_2376_);
lean_dec_ref(v_state_2362_);
v_val_2377_ = lean_ctor_get(v_pendingHead_2366_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_pendingHead_2366_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2379_ = v_pendingHead_2366_;
v_isShared_2380_ = v_isSharedCheck_2399_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_val_2377_);
lean_dec(v_pendingHead_2366_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2399_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_onRequest_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___f_2389_; lean_object* v___f_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v_onRequest_2381_ = lean_ctor_get(v_inst_2358_, 1);
lean_inc_ref(v_onRequest_2381_);
lean_dec_ref(v_inst_2358_);
lean_inc_ref(v_requestStream_2369_);
v___x_2382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2382_, 0, v_val_2377_);
lean_ctor_set(v___x_2382_, 1, v_requestStream_2369_);
lean_ctor_set(v___x_2382_, 2, v_extensions_2360_);
v___x_2383_ = lean_apply_3(v_onRequest_2381_, v_handler_2359_, v___x_2382_, v_connectionContext_2361_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2385_, 0, lean_box(0));
lean_closure_set(v___x_2385_, 1, v___x_2383_);
v___x_2386_ = lean_io_as_task(v___x_2385_, v___x_2384_);
v___f_2387_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2388_ = lean_box(v_requiresData_2375_);
lean_inc_ref(v_response_2373_);
v___f_2389_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2389_, 0, v_machine_2368_);
lean_closure_set(v___f_2389_, 1, v_requestStream_2369_);
lean_closure_set(v___f_2389_, 2, v_keepAliveTimeout_2370_);
lean_closure_set(v___f_2389_, 3, v_currentTimeout_2371_);
lean_closure_set(v___f_2389_, 4, v_headerTimeout_2372_);
lean_closure_set(v___f_2389_, 5, v_response_2373_);
lean_closure_set(v___f_2389_, 6, v_respStream_2374_);
lean_closure_set(v___f_2389_, 7, v___x_2388_);
lean_closure_set(v___f_2389_, 8, v_expectData_2376_);
lean_inc_ref(v_toFunctor_2367_);
v___f_2390_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2390_, 0, v_toFunctor_2367_);
lean_closure_set(v___f_2390_, 1, v_response_2373_);
lean_closure_set(v___f_2390_, 2, v___x_2384_);
lean_closure_set(v___f_2390_, 3, v___f_2389_);
v___x_2391_ = 1;
v___x_2392_ = lean_task_bind(v___x_2386_, v___f_2387_, v___x_2384_, v___x_2391_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2392_);
v___x_2394_ = v___x_2379_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
v___x_2396_ = 0;
v___x_2397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2384_, v___x_2396_, v___x_2395_, v___f_2390_);
return v___x_2397_;
}
}
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec(v_pendingHead_2366_);
lean_dec_ref(v_connectionContext_2361_);
lean_dec(v_extensions_2360_);
lean_dec(v_handler_2359_);
lean_dec_ref(v_inst_2358_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_state_2362_);
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2402_, lean_object* v_handler_2403_, lean_object* v_extensions_2404_, lean_object* v_connectionContext_2405_, lean_object* v_state_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2402_, v_handler_2403_, v_extensions_2404_, v_connectionContext_2405_, v_state_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2409_, lean_object* v_inst_2410_, lean_object* v_handler_2411_, lean_object* v_extensions_2412_, lean_object* v_connectionContext_2413_, lean_object* v_state_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2410_, v_handler_2411_, v_extensions_2412_, v_connectionContext_2413_, v_state_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2417_, lean_object* v_inst_2418_, lean_object* v_handler_2419_, lean_object* v_extensions_2420_, lean_object* v_connectionContext_2421_, lean_object* v_state_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2417_, v_inst_2418_, v_handler_2419_, v_extensions_2420_, v_connectionContext_2421_, v_state_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2425_, lean_object* v_____r_2426_){
_start:
{
lean_object* v_writer_2428_; lean_object* v_reader_2429_; lean_object* v_config_2430_; lean_object* v_events_2431_; lean_object* v_error_2432_; lean_object* v_instant_2433_; uint8_t v_keepAlive_2434_; uint8_t v_forcedFlush_2435_; uint8_t v_pullBodyStalled_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2463_; 
v_writer_2428_ = lean_ctor_get(v_machine_2425_, 1);
v_reader_2429_ = lean_ctor_get(v_machine_2425_, 0);
v_config_2430_ = lean_ctor_get(v_machine_2425_, 2);
v_events_2431_ = lean_ctor_get(v_machine_2425_, 3);
v_error_2432_ = lean_ctor_get(v_machine_2425_, 4);
v_instant_2433_ = lean_ctor_get(v_machine_2425_, 5);
v_keepAlive_2434_ = lean_ctor_get_uint8(v_machine_2425_, sizeof(void*)*6);
v_forcedFlush_2435_ = lean_ctor_get_uint8(v_machine_2425_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2436_ = lean_ctor_get_uint8(v_machine_2425_, sizeof(void*)*6 + 2);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_machine_2425_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2438_ = v_machine_2425_;
v_isShared_2439_ = v_isSharedCheck_2463_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_instant_2433_);
lean_inc(v_error_2432_);
lean_inc(v_events_2431_);
lean_inc(v_config_2430_);
lean_inc(v_writer_2428_);
lean_inc(v_reader_2429_);
lean_dec(v_machine_2425_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2463_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v_userData_2440_; lean_object* v_outputData_2441_; lean_object* v_state_2442_; lean_object* v_knownSize_2443_; lean_object* v_messageHead_2444_; uint8_t v_sentMessage_2445_; uint8_t v_omitBody_2446_; lean_object* v_userDataBytes_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2462_; 
v_userData_2440_ = lean_ctor_get(v_writer_2428_, 0);
v_outputData_2441_ = lean_ctor_get(v_writer_2428_, 1);
v_state_2442_ = lean_ctor_get(v_writer_2428_, 2);
v_knownSize_2443_ = lean_ctor_get(v_writer_2428_, 3);
v_messageHead_2444_ = lean_ctor_get(v_writer_2428_, 4);
v_sentMessage_2445_ = lean_ctor_get_uint8(v_writer_2428_, sizeof(void*)*6);
v_omitBody_2446_ = lean_ctor_get_uint8(v_writer_2428_, sizeof(void*)*6 + 2);
v_userDataBytes_2447_ = lean_ctor_get(v_writer_2428_, 5);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_writer_2428_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2449_ = v_writer_2428_;
v_isShared_2450_ = v_isSharedCheck_2462_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_userDataBytes_2447_);
lean_inc(v_messageHead_2444_);
lean_inc(v_knownSize_2443_);
lean_inc(v_state_2442_);
lean_inc(v_outputData_2441_);
lean_inc(v_userData_2440_);
lean_dec(v_writer_2428_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2462_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; lean_object* v___x_2453_; 
v___x_2451_ = 1;
if (v_isShared_2450_ == 0)
{
v___x_2453_ = v___x_2449_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_userData_2440_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_outputData_2441_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_state_2442_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_knownSize_2443_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_messageHead_2444_);
lean_ctor_set(v_reuseFailAlloc_2461_, 5, v_userDataBytes_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, sizeof(void*)*6, v_sentMessage_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, sizeof(void*)*6 + 2, v_omitBody_2446_);
v___x_2453_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2455_; 
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*6 + 1, v___x_2451_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 1, v___x_2453_);
v___x_2455_ = v___x_2438_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_reader_2429_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_config_2430_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_events_2431_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_error_2432_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v_instant_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, sizeof(void*)*6, v_keepAlive_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, sizeof(void*)*6 + 1, v_forcedFlush_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, sizeof(void*)*6 + 2, v_pullBodyStalled_2436_);
v___x_2455_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2464_, lean_object* v_____r_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2464_, v_____r_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2468_, lean_object* v_x2_2469_){
_start:
{
lean_object* v_data_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_data_2470_ = lean_ctor_get(v_x2_2469_, 0);
v___x_2471_ = lean_byte_array_size(v_data_2470_);
v___x_2472_ = lean_nat_add(v_x1_2468_, v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2473_, lean_object* v_x2_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2473_, v_x2_2474_);
lean_dec_ref(v_x2_2474_);
lean_dec(v_x1_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2476_, lean_object* v_machine_2477_, lean_object* v_isClosed_2478_, lean_object* v___f_2479_, lean_object* v___f_2480_, lean_object* v_x_2481_){
_start:
{
lean_object* v___y_2484_; 
if (lean_obj_tag(v_x_2481_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
lean_dec_ref(v___f_2480_);
lean_dec_ref(v___f_2479_);
lean_dec_ref(v_isClosed_2478_);
lean_dec_ref(v_machine_2477_);
lean_dec(v_body_2476_);
v_a_2489_ = lean_ctor_get(v_x_2481_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v_x_2481_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v_x_2481_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2561_; 
v_a_2498_ = lean_ctor_get(v_x_2481_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_x_2481_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2500_ = v_x_2481_;
v_isShared_2501_ = v_isSharedCheck_2561_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v_x_2481_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2561_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
if (lean_obj_tag(v_a_2498_) == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_dec_ref(v___f_2480_);
lean_dec_ref(v___f_2479_);
lean_dec_ref(v_isClosed_2478_);
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_body_2476_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_machine_2477_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2503_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
else
{
lean_object* v_val_2508_; 
lean_del_object(v___x_2500_);
v_val_2508_ = lean_ctor_get(v_a_2498_, 0);
lean_inc(v_val_2508_);
lean_dec_ref_known(v_a_2498_, 1);
if (lean_obj_tag(v_val_2508_) == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; 
lean_dec_ref(v___f_2480_);
lean_dec_ref(v_machine_2477_);
v___x_2509_ = lean_apply_2(v_isClosed_2478_, v_body_2476_, lean_box(0));
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = 0;
v___x_2512_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2510_, v___x_2511_, v___x_2509_, v___f_2479_);
return v___x_2512_;
}
else
{
lean_object* v_val_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
lean_dec_ref(v___f_2479_);
lean_dec_ref(v_isClosed_2478_);
v_val_2513_ = lean_ctor_get(v_val_2508_, 0);
lean_inc(v_val_2513_);
lean_dec_ref_known(v_val_2508_, 1);
v___x_2514_ = lean_unsigned_to_nat(1u);
v___x_2515_ = lean_mk_empty_array_with_capacity(v___x_2514_);
v___x_2516_ = lean_array_push(v___x_2515_, v_val_2513_);
v___x_2517_ = lean_array_get_size(v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_nat_dec_eq(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v_reader_2520_; lean_object* v_writer_2521_; lean_object* v_config_2522_; lean_object* v_events_2523_; lean_object* v_error_2524_; lean_object* v_instant_2525_; uint8_t v_keepAlive_2526_; uint8_t v_forcedFlush_2527_; uint8_t v_pullBodyStalled_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2560_; 
v_reader_2520_ = lean_ctor_get(v_machine_2477_, 0);
v_writer_2521_ = lean_ctor_get(v_machine_2477_, 1);
v_config_2522_ = lean_ctor_get(v_machine_2477_, 2);
v_events_2523_ = lean_ctor_get(v_machine_2477_, 3);
v_error_2524_ = lean_ctor_get(v_machine_2477_, 4);
v_instant_2525_ = lean_ctor_get(v_machine_2477_, 5);
v_keepAlive_2526_ = lean_ctor_get_uint8(v_machine_2477_, sizeof(void*)*6);
v_forcedFlush_2527_ = lean_ctor_get_uint8(v_machine_2477_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2528_ = lean_ctor_get_uint8(v_machine_2477_, sizeof(void*)*6 + 2);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_machine_2477_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2530_ = v_machine_2477_;
v_isShared_2531_ = v_isSharedCheck_2560_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_instant_2525_);
lean_inc(v_error_2524_);
lean_inc(v_events_2523_);
lean_inc(v_config_2522_);
lean_inc(v_writer_2521_);
lean_inc(v_reader_2520_);
lean_dec(v_machine_2477_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2560_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___y_2533_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2555_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_2556_ = lean_nat_dec_lt(v___x_2518_, v___x_2517_);
if (v___x_2556_ == 0)
{
lean_dec_ref(v___f_2480_);
v___y_2533_ = v___x_2518_;
goto v___jp_2532_;
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2517_);
lean_inc_ref(v___x_2516_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2555_, v___f_2480_, v___x_2516_, v___x_2557_, v___x_2558_, v___x_2518_);
v___y_2533_ = v___x_2559_;
goto v___jp_2532_;
}
v___jp_2532_:
{
lean_object* v_userData_2534_; lean_object* v_outputData_2535_; lean_object* v_state_2536_; lean_object* v_knownSize_2537_; lean_object* v_messageHead_2538_; uint8_t v_sentMessage_2539_; uint8_t v_userClosedBody_2540_; uint8_t v_omitBody_2541_; lean_object* v_userDataBytes_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2554_; 
v_userData_2534_ = lean_ctor_get(v_writer_2521_, 0);
v_outputData_2535_ = lean_ctor_get(v_writer_2521_, 1);
v_state_2536_ = lean_ctor_get(v_writer_2521_, 2);
v_knownSize_2537_ = lean_ctor_get(v_writer_2521_, 3);
v_messageHead_2538_ = lean_ctor_get(v_writer_2521_, 4);
v_sentMessage_2539_ = lean_ctor_get_uint8(v_writer_2521_, sizeof(void*)*6);
v_userClosedBody_2540_ = lean_ctor_get_uint8(v_writer_2521_, sizeof(void*)*6 + 1);
v_omitBody_2541_ = lean_ctor_get_uint8(v_writer_2521_, sizeof(void*)*6 + 2);
v_userDataBytes_2542_ = lean_ctor_get(v_writer_2521_, 5);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_writer_2521_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2544_ = v_writer_2521_;
v_isShared_2545_ = v_isSharedCheck_2554_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_userDataBytes_2542_);
lean_inc(v_messageHead_2538_);
lean_inc(v_knownSize_2537_);
lean_inc(v_state_2536_);
lean_inc(v_outputData_2535_);
lean_inc(v_userData_2534_);
lean_dec(v_writer_2521_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2554_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2546_ = l_Array_append___redArg(v_userData_2534_, v___x_2516_);
lean_dec_ref(v___x_2516_);
v___x_2547_ = lean_nat_add(v_userDataBytes_2542_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec(v_userDataBytes_2542_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 5, v___x_2547_);
lean_ctor_set(v___x_2544_, 0, v___x_2546_);
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_outputData_2535_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_state_2536_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_knownSize_2537_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_messageHead_2538_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v___x_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2553_, sizeof(void*)*6, v_sentMessage_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2553_, sizeof(void*)*6 + 1, v_userClosedBody_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2553_, sizeof(void*)*6 + 2, v_omitBody_2541_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2549_);
v___x_2551_ = v___x_2530_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_reader_2520_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_config_2522_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_events_2523_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_error_2524_);
lean_ctor_set(v_reuseFailAlloc_2552_, 5, v_instant_2525_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*6, v_keepAlive_2526_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*6 + 1, v_forcedFlush_2527_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*6 + 2, v_pullBodyStalled_2528_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
v___y_2484_ = v___x_2551_;
goto v___jp_2483_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2516_);
lean_dec_ref(v___f_2480_);
v___y_2484_ = v_machine_2477_;
goto v___jp_2483_;
}
}
}
}
}
v___jp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_body_2476_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___y_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2562_, lean_object* v_machine_2563_, lean_object* v_isClosed_2564_, lean_object* v___f_2565_, lean_object* v___f_2566_, lean_object* v_x_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2562_, v_machine_2563_, v_isClosed_2564_, v___f_2565_, v___f_2566_, v_x_2567_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2571_, lean_object* v_machine_2572_, lean_object* v_body_2573_){
_start:
{
lean_object* v_close_2575_; lean_object* v_isClosed_2576_; lean_object* v_tryRecv_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; 
v_close_2575_ = lean_ctor_get(v_inst_2571_, 1);
lean_inc_ref(v_close_2575_);
v_isClosed_2576_ = lean_ctor_get(v_inst_2571_, 2);
lean_inc_ref(v_isClosed_2576_);
v_tryRecv_2577_ = lean_ctor_get(v_inst_2571_, 4);
lean_inc_ref(v_tryRecv_2577_);
lean_dec_ref(v_inst_2571_);
lean_inc_n(v_body_2573_, 2);
v___x_2578_ = lean_apply_2(v_tryRecv_2577_, v_body_2573_, lean_box(0));
lean_inc_ref(v_machine_2572_);
v___f_2579_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2579_, 0, v_machine_2572_);
lean_inc_ref(v___f_2579_);
v___f_2580_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2580_, 0, v___f_2579_);
v___f_2581_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2581_, 0, v_close_2575_);
lean_closure_set(v___f_2581_, 1, v_body_2573_);
lean_closure_set(v___f_2581_, 2, v___f_2580_);
lean_closure_set(v___f_2581_, 3, v___f_2579_);
v___f_2582_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2583_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2583_, 0, v_body_2573_);
lean_closure_set(v___f_2583_, 1, v_machine_2572_);
lean_closure_set(v___f_2583_, 2, v_isClosed_2576_);
lean_closure_set(v___f_2583_, 3, v___f_2581_);
lean_closure_set(v___f_2583_, 4, v___f_2582_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = 0;
v___x_2586_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2584_, v___x_2585_, v___x_2578_, v___f_2583_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2587_, lean_object* v_machine_2588_, lean_object* v_body_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2587_, v_machine_2588_, v_body_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2592_, lean_object* v_inst_2593_, lean_object* v_machine_2594_, lean_object* v_body_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2593_, v_machine_2594_, v_body_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2598_, lean_object* v_inst_2599_, lean_object* v_machine_2600_, lean_object* v_body_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2598_, v_inst_2599_, v_machine_2600_, v_body_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2610_, lean_object* v_____r_2611_, lean_object* v_st_2612_){
_start:
{
lean_object* v_machine_2614_; lean_object* v_requestStream_2615_; lean_object* v_keepAliveTimeout_2616_; lean_object* v_currentTimeout_2617_; lean_object* v_headerTimeout_2618_; lean_object* v_response_2619_; lean_object* v_respStream_2620_; uint8_t v_requiresData_2621_; lean_object* v_expectData_2622_; uint8_t v_handlerDispatched_2623_; lean_object* v_pendingHead_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2709_; 
v_machine_2614_ = lean_ctor_get(v_st_2612_, 0);
v_requestStream_2615_ = lean_ctor_get(v_st_2612_, 1);
v_keepAliveTimeout_2616_ = lean_ctor_get(v_st_2612_, 2);
v_currentTimeout_2617_ = lean_ctor_get(v_st_2612_, 3);
v_headerTimeout_2618_ = lean_ctor_get(v_st_2612_, 4);
v_response_2619_ = lean_ctor_get(v_st_2612_, 5);
v_respStream_2620_ = lean_ctor_get(v_st_2612_, 6);
v_requiresData_2621_ = lean_ctor_get_uint8(v_st_2612_, sizeof(void*)*9);
v_expectData_2622_ = lean_ctor_get(v_st_2612_, 7);
v_handlerDispatched_2623_ = lean_ctor_get_uint8(v_st_2612_, sizeof(void*)*9 + 1);
v_pendingHead_2624_ = lean_ctor_get(v_st_2612_, 8);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_st_2612_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2626_ = v_st_2612_;
v_isShared_2627_ = v_isSharedCheck_2709_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_pendingHead_2624_);
lean_inc(v_expectData_2622_);
lean_inc(v_respStream_2620_);
lean_inc(v_response_2619_);
lean_inc(v_headerTimeout_2618_);
lean_inc(v_currentTimeout_2617_);
lean_inc(v_keepAliveTimeout_2616_);
lean_inc(v_requestStream_2615_);
lean_inc(v_machine_2614_);
lean_dec(v_st_2612_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2709_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___y_2629_; lean_object* v___y_2639_; lean_object* v___y_2640_; uint8_t v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; lean_object* v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v_reader_2674_; lean_object* v_writer_2675_; lean_object* v_config_2676_; lean_object* v_events_2677_; lean_object* v_error_2678_; lean_object* v_instant_2679_; uint8_t v_keepAlive_2680_; uint8_t v_forcedFlush_2681_; lean_object* v_state_2682_; lean_object* v_input_2683_; lean_object* v_messageHead_2684_; lean_object* v_messageCount_2685_; lean_object* v_bodyBytesRead_2686_; lean_object* v_headerBytesRead_2687_; uint8_t v_noMoreInput_2688_; uint8_t v___y_2690_; uint8_t v___y_2691_; uint8_t v___y_2704_; 
v_reader_2674_ = lean_ctor_get(v_machine_2614_, 0);
v_writer_2675_ = lean_ctor_get(v_machine_2614_, 1);
v_config_2676_ = lean_ctor_get(v_machine_2614_, 2);
v_events_2677_ = lean_ctor_get(v_machine_2614_, 3);
v_error_2678_ = lean_ctor_get(v_machine_2614_, 4);
v_instant_2679_ = lean_ctor_get(v_machine_2614_, 5);
v_keepAlive_2680_ = lean_ctor_get_uint8(v_machine_2614_, sizeof(void*)*6);
v_forcedFlush_2681_ = lean_ctor_get_uint8(v_machine_2614_, sizeof(void*)*6 + 1);
v_state_2682_ = lean_ctor_get(v_reader_2674_, 0);
v_input_2683_ = lean_ctor_get(v_reader_2674_, 1);
v_messageHead_2684_ = lean_ctor_get(v_reader_2674_, 2);
v_messageCount_2685_ = lean_ctor_get(v_reader_2674_, 3);
v_bodyBytesRead_2686_ = lean_ctor_get(v_reader_2674_, 4);
v_headerBytesRead_2687_ = lean_ctor_get(v_reader_2674_, 5);
v_noMoreInput_2688_ = lean_ctor_get_uint8(v_reader_2674_, sizeof(void*)*6);
if (lean_obj_tag(v_state_2682_) == 6)
{
uint8_t v___x_2707_; 
v___x_2707_ = 1;
v___y_2704_ = v___x_2707_;
goto v___jp_2703_;
}
else
{
uint8_t v___x_2708_; 
v___x_2708_ = 0;
v___y_2704_ = v___x_2708_;
goto v___jp_2703_;
}
v___jp_2628_:
{
lean_object* v___x_2631_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___y_2629_);
v___x_2631_ = v___x_2626_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___y_2629_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_requestStream_2615_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_keepAliveTimeout_2616_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_currentTimeout_2617_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_headerTimeout_2618_);
lean_ctor_set(v_reuseFailAlloc_2637_, 5, v_response_2619_);
lean_ctor_set(v_reuseFailAlloc_2637_, 6, v_respStream_2620_);
lean_ctor_set(v_reuseFailAlloc_2637_, 7, v_expectData_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 8, v_pendingHead_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2637_, sizeof(void*)*9, v_requiresData_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2637_, sizeof(void*)*9 + 1, v_handlerDispatched_2623_);
v___x_2631_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2632_ = 0;
v___x_2633_ = lean_box(v___x_2632_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2631_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
v___jp_2638_:
{
lean_object* v_maxHeaderBytes_2654_; lean_object* v_maxStartLineLength_2655_; lean_object* v_maxChunkLineLength_2656_; lean_object* v_maxBodySize_2657_; lean_object* v_array_2658_; lean_object* v_idx_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v_maxHeaderBytes_2654_ = lean_ctor_get(v___y_2639_, 2);
v_maxStartLineLength_2655_ = lean_ctor_get(v___y_2639_, 5);
v_maxChunkLineLength_2656_ = lean_ctor_get(v___y_2639_, 13);
v_maxBodySize_2657_ = lean_ctor_get(v___y_2639_, 15);
v_array_2658_ = lean_ctor_get(v___y_2653_, 0);
v_idx_2659_ = lean_ctor_get(v___y_2653_, 1);
v___x_2660_ = lean_nat_add(v_maxBodySize_2657_, v_maxHeaderBytes_2654_);
v___x_2661_ = lean_nat_add(v___x_2660_, v_maxStartLineLength_2655_);
lean_dec(v___x_2660_);
v___x_2662_ = lean_nat_add(v___x_2661_, v_maxChunkLineLength_2656_);
lean_dec(v___x_2661_);
v___x_2663_ = lean_byte_array_size(v_array_2658_);
v___x_2664_ = lean_nat_sub(v___x_2663_, v_idx_2659_);
v___x_2665_ = lean_nat_dec_lt(v___x_2662_, v___x_2664_);
lean_dec(v___x_2664_);
lean_dec(v___x_2662_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v_machine_2667_; 
v___x_2666_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2666_, 0, v___y_2652_);
lean_ctor_set(v___x_2666_, 1, v___y_2653_);
lean_ctor_set(v___x_2666_, 2, v___y_2650_);
lean_ctor_set(v___x_2666_, 3, v___y_2644_);
lean_ctor_set(v___x_2666_, 4, v___y_2648_);
lean_ctor_set(v___x_2666_, 5, v___y_2646_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*6, v___y_2647_);
v_machine_2667_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_2667_, 0, v___x_2666_);
lean_ctor_set(v_machine_2667_, 1, v___y_2651_);
lean_ctor_set(v_machine_2667_, 2, v___y_2639_);
lean_ctor_set(v_machine_2667_, 3, v___y_2642_);
lean_ctor_set(v_machine_2667_, 4, v___y_2645_);
lean_ctor_set(v_machine_2667_, 5, v___y_2640_);
lean_ctor_set_uint8(v_machine_2667_, sizeof(void*)*6, v___y_2649_);
lean_ctor_set_uint8(v_machine_2667_, sizeof(void*)*6 + 1, v___y_2643_);
lean_ctor_set_uint8(v_machine_2667_, sizeof(void*)*6 + 2, v___y_2641_);
v___y_2629_ = v_machine_2667_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v___y_2652_);
lean_dec(v___y_2645_);
v___x_2668_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2669_ = lean_array_push(v___y_2642_, v___x_2668_);
v___x_2670_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
v___x_2671_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v___y_2653_);
lean_ctor_set(v___x_2671_, 2, v___y_2650_);
lean_ctor_set(v___x_2671_, 3, v___y_2644_);
lean_ctor_set(v___x_2671_, 4, v___y_2648_);
lean_ctor_set(v___x_2671_, 5, v___y_2646_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*6, v___y_2647_);
v___x_2672_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
v___x_2673_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___y_2651_);
lean_ctor_set(v___x_2673_, 2, v___y_2639_);
lean_ctor_set(v___x_2673_, 3, v___x_2669_);
lean_ctor_set(v___x_2673_, 4, v___x_2672_);
lean_ctor_set(v___x_2673_, 5, v___y_2640_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*6, v___y_2649_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*6 + 1, v___y_2643_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*6 + 2, v___y_2641_);
v___y_2629_ = v___x_2673_;
goto v___jp_2628_;
}
}
v___jp_2689_:
{
if (v___y_2690_ == 0)
{
if (v___y_2691_ == 0)
{
lean_object* v_array_2692_; lean_object* v_idx_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
lean_inc(v_headerBytesRead_2687_);
lean_inc(v_bodyBytesRead_2686_);
lean_inc(v_messageCount_2685_);
lean_inc(v_messageHead_2684_);
lean_inc_ref(v_input_2683_);
lean_inc(v_state_2682_);
lean_inc(v_instant_2679_);
lean_inc(v_error_2678_);
lean_inc_ref(v_events_2677_);
lean_inc_ref(v_config_2676_);
lean_inc_ref(v_writer_2675_);
lean_dec_ref(v_machine_2614_);
v_array_2692_ = lean_ctor_get(v_input_2683_, 0);
lean_inc_ref(v_array_2692_);
v_idx_2693_ = lean_ctor_get(v_input_2683_, 1);
lean_inc(v_idx_2693_);
lean_dec_ref(v_input_2683_);
v___x_2694_ = lean_byte_array_size(v_array_2692_);
v___x_2695_ = lean_nat_dec_le(v___x_2694_, v_idx_2693_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2696_ = l_ByteArray_extract(v_array_2692_, v_idx_2693_, v___x_2694_);
lean_dec_ref(v_array_2692_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_byte_array_size(v___x_2696_);
v___x_2699_ = lean_byte_array_size(v_val_2610_);
v___x_2700_ = lean_byte_array_copy_slice(v_val_2610_, v___x_2697_, v___x_2696_, v___x_2698_, v___x_2699_, v___x_2695_);
lean_dec_ref(v_val_2610_);
v___x_2701_ = l_ByteArray_mkIterator(v___x_2700_);
v___y_2639_ = v_config_2676_;
v___y_2640_ = v_instant_2679_;
v___y_2641_ = v___y_2691_;
v___y_2642_ = v_events_2677_;
v___y_2643_ = v_forcedFlush_2681_;
v___y_2644_ = v_messageCount_2685_;
v___y_2645_ = v_error_2678_;
v___y_2646_ = v_headerBytesRead_2687_;
v___y_2647_ = v_noMoreInput_2688_;
v___y_2648_ = v_bodyBytesRead_2686_;
v___y_2649_ = v_keepAlive_2680_;
v___y_2650_ = v_messageHead_2684_;
v___y_2651_ = v_writer_2675_;
v___y_2652_ = v_state_2682_;
v___y_2653_ = v___x_2701_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2702_; 
lean_dec(v_idx_2693_);
lean_dec_ref(v_array_2692_);
v___x_2702_ = l_ByteArray_mkIterator(v_val_2610_);
v___y_2639_ = v_config_2676_;
v___y_2640_ = v_instant_2679_;
v___y_2641_ = v___y_2691_;
v___y_2642_ = v_events_2677_;
v___y_2643_ = v_forcedFlush_2681_;
v___y_2644_ = v_messageCount_2685_;
v___y_2645_ = v_error_2678_;
v___y_2646_ = v_headerBytesRead_2687_;
v___y_2647_ = v_noMoreInput_2688_;
v___y_2648_ = v_bodyBytesRead_2686_;
v___y_2649_ = v_keepAlive_2680_;
v___y_2650_ = v_messageHead_2684_;
v___y_2651_ = v_writer_2675_;
v___y_2652_ = v_state_2682_;
v___y_2653_ = v___x_2702_;
goto v___jp_2638_;
}
}
else
{
lean_dec_ref(v_val_2610_);
v___y_2629_ = v_machine_2614_;
goto v___jp_2628_;
}
}
else
{
lean_dec_ref(v_val_2610_);
v___y_2629_ = v_machine_2614_;
goto v___jp_2628_;
}
}
v___jp_2703_:
{
if (lean_obj_tag(v_state_2682_) == 7)
{
uint8_t v___x_2705_; 
v___x_2705_ = 1;
v___y_2690_ = v___y_2704_;
v___y_2691_ = v___x_2705_;
goto v___jp_2689_;
}
else
{
uint8_t v___x_2706_; 
v___x_2706_ = 0;
v___y_2690_ = v___y_2704_;
v___y_2691_ = v___x_2706_;
goto v___jp_2689_;
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
v___x_2741_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2742_ = lean_int_mul(v_headerTimeout_2738_, v___x_2741_);
v___x_2743_ = l_Std_Time_Duration_ofNanoseconds(v___x_2742_);
lean_dec(v___x_2742_);
v_second_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_second_2744_);
v_nano_2745_ = lean_ctor_get(v___x_2743_, 1);
lean_inc(v_nano_2745_);
lean_dec_ref(v___x_2743_);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
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
lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_6969__overap_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; 
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
v___x_6969__overap_2964_ = l_Std_Mutex_atomically___redArg(v___x_2959_, v___f_2960_, v___f_2961_, v_requestStream_2944_, v___x_2963_);
v___x_2965_ = lean_apply_1(v___x_6969__overap_2964_, lean_box(0));
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
uint8_t v_requiresData_boxed_3123_; uint8_t v___x_7791__boxed_3124_; lean_object* v_res_3125_; 
v_requiresData_boxed_3123_ = lean_unbox(v_requiresData_3117_);
v___x_7791__boxed_3124_ = lean_unbox(v___x_3119_);
v_res_3125_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3112_, v_keepAliveTimeout_3113_, v_currentTimeout_3114_, v_headerTimeout_3115_, v_response_3116_, v_requiresData_boxed_3123_, v_expectData_3118_, v___x_7791__boxed_3124_, v_pendingHead_3120_, v_____x_3121_);
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
uint8_t v___x_7859__boxed_3179_; lean_object* v_res_3180_; 
v___x_7859__boxed_3179_ = lean_unbox(v___x_3176_);
v_res_3180_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7859__boxed_3179_, v_x_3177_);
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
uint8_t v___x_7927__boxed_3212_; lean_object* v_res_3213_; 
v___x_7927__boxed_3212_ = lean_unbox(v___x_3208_);
v_res_3213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3207_, v___x_7927__boxed_3212_, v_fst_3209_, v_x_3210_);
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
uint8_t v___x_7985__boxed_3232_; lean_object* v_res_3233_; 
v___x_7985__boxed_3232_ = lean_unbox(v___x_3228_);
v_res_3233_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3226_, v_handler_3227_, v___x_7985__boxed_3232_, v___f_3229_, v_x_3230_);
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
uint8_t v___x_8010__boxed_3297_; uint8_t v___x_8014__boxed_3298_; lean_object* v_res_3299_; 
v___x_8010__boxed_3297_ = lean_unbox(v___x_3287_);
v___x_8014__boxed_3298_ = lean_unbox(v___x_3291_);
v_res_3299_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8010__boxed_3297_, v___f_3288_, v_inst_3289_, v___f_3290_, v___x_8014__boxed_3298_, v_inst_3292_, v_handler_3293_, v___f_3294_, v_x_3295_);
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
lean_object* v_x_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3579_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3353_);
v_x_3468_ = lean_ctor_get(v_event_3357_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_event_3357_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3470_ = v_event_3357_;
v_isShared_3471_ = v_isSharedCheck_3579_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_x_3468_);
lean_dec(v_event_3357_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3579_;
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
lean_object* v_val_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v_inst_3354_);
v_val_3497_ = lean_ctor_get(v_x_3468_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_x_3468_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3499_ = v_x_3468_;
v_isShared_3500_ = v_isSharedCheck_3578_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_val_3497_);
lean_dec(v_x_3468_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3578_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_machine_3501_; lean_object* v_requestStream_3502_; lean_object* v_keepAliveTimeout_3503_; lean_object* v_currentTimeout_3504_; lean_object* v_headerTimeout_3505_; lean_object* v_response_3506_; lean_object* v_respStream_3507_; uint8_t v_requiresData_3508_; lean_object* v_expectData_3509_; uint8_t v_handlerDispatched_3510_; lean_object* v_pendingHead_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3577_; 
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
v_isSharedCheck_3577_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3513_ = v_state_3358_;
v_isShared_3514_ = v_isSharedCheck_3577_;
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
v_isShared_3514_ = v_isSharedCheck_3577_;
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
lean_object* v_reader_3535_; lean_object* v_writer_3536_; lean_object* v_config_3537_; lean_object* v_events_3538_; lean_object* v_error_3539_; lean_object* v_instant_3540_; uint8_t v_keepAlive_3541_; uint8_t v_forcedFlush_3542_; uint8_t v_pullBodyStalled_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3576_; 
v_reader_3535_ = lean_ctor_get(v_machine_3501_, 0);
v_writer_3536_ = lean_ctor_get(v_machine_3501_, 1);
v_config_3537_ = lean_ctor_get(v_machine_3501_, 2);
v_events_3538_ = lean_ctor_get(v_machine_3501_, 3);
v_error_3539_ = lean_ctor_get(v_machine_3501_, 4);
v_instant_3540_ = lean_ctor_get(v_machine_3501_, 5);
v_keepAlive_3541_ = lean_ctor_get_uint8(v_machine_3501_, sizeof(void*)*6);
v_forcedFlush_3542_ = lean_ctor_get_uint8(v_machine_3501_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3543_ = lean_ctor_get_uint8(v_machine_3501_, sizeof(void*)*6 + 2);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_machine_3501_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3545_ = v_machine_3501_;
v_isShared_3546_ = v_isSharedCheck_3576_;
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
v_isShared_3546_ = v_isSharedCheck_3576_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___y_3548_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_3571_ = lean_nat_dec_lt(v___x_3533_, v___x_3532_);
if (v___x_3571_ == 0)
{
v___y_3548_ = v___x_3533_;
goto v___jp_3547_;
}
else
{
lean_object* v___f_3572_; size_t v___x_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v___f_3572_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3573_ = ((size_t)0ULL);
v___x_3574_ = lean_usize_of_nat(v___x_3532_);
lean_inc_ref(v___x_3531_);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3570_, v___f_3572_, v___x_3531_, v___x_3573_, v___x_3574_, v___x_3533_);
v___y_3548_ = v___x_3575_;
goto v___jp_3547_;
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
uint8_t v_x_3580_; 
lean_dec_ref(v_config_3356_);
lean_dec_ref(v_inst_3354_);
v_x_3580_ = lean_ctor_get_uint8(v_event_3357_, 0);
lean_dec_ref_known(v_event_3357_, 0);
if (v_x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3353_);
v___x_3581_ = lean_box(v_x_3580_);
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_state_3358_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
else
{
lean_object* v_machine_3585_; lean_object* v_requestStream_3586_; lean_object* v_keepAliveTimeout_3587_; lean_object* v_currentTimeout_3588_; lean_object* v_headerTimeout_3589_; lean_object* v_response_3590_; lean_object* v_respStream_3591_; uint8_t v_requiresData_3592_; lean_object* v_expectData_3593_; uint8_t v_handlerDispatched_3594_; lean_object* v_pendingHead_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3645_; 
v_machine_3585_ = lean_ctor_get(v_state_3358_, 0);
v_requestStream_3586_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3587_ = lean_ctor_get(v_state_3358_, 2);
v_currentTimeout_3588_ = lean_ctor_get(v_state_3358_, 3);
v_headerTimeout_3589_ = lean_ctor_get(v_state_3358_, 4);
v_response_3590_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3591_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3592_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3593_ = lean_ctor_get(v_state_3358_, 7);
v_handlerDispatched_3594_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9 + 1);
v_pendingHead_3595_ = lean_ctor_get(v_state_3358_, 8);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3597_ = v_state_3358_;
v_isShared_3598_ = v_isSharedCheck_3645_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_pendingHead_3595_);
lean_inc(v_expectData_3593_);
lean_inc(v_respStream_3591_);
lean_inc(v_response_3590_);
lean_inc(v_headerTimeout_3589_);
lean_inc(v_currentTimeout_3588_);
lean_inc(v_keepAliveTimeout_3587_);
lean_inc(v_requestStream_3586_);
lean_inc(v_machine_3585_);
lean_dec(v_state_3358_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3645_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
uint8_t v___x_3599_; lean_object* v___x_3600_; lean_object* v_fst_3601_; lean_object* v_snd_3602_; lean_object* v_reader_3603_; lean_object* v_writer_3604_; lean_object* v_config_3605_; lean_object* v_events_3606_; lean_object* v_error_3607_; lean_object* v_instant_3608_; uint8_t v_keepAlive_3609_; uint8_t v_forcedFlush_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3644_; 
v___x_3599_ = 0;
v___x_3600_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3599_, v_machine_3585_);
v_fst_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_fst_3601_);
v_snd_3602_ = lean_ctor_get(v___x_3600_, 1);
lean_inc(v_snd_3602_);
lean_dec_ref(v___x_3600_);
v_reader_3603_ = lean_ctor_get(v_fst_3601_, 0);
v_writer_3604_ = lean_ctor_get(v_fst_3601_, 1);
v_config_3605_ = lean_ctor_get(v_fst_3601_, 2);
v_events_3606_ = lean_ctor_get(v_fst_3601_, 3);
v_error_3607_ = lean_ctor_get(v_fst_3601_, 4);
v_instant_3608_ = lean_ctor_get(v_fst_3601_, 5);
v_keepAlive_3609_ = lean_ctor_get_uint8(v_fst_3601_, sizeof(void*)*6);
v_forcedFlush_3610_ = lean_ctor_get_uint8(v_fst_3601_, sizeof(void*)*6 + 1);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_fst_3601_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3612_ = v_fst_3601_;
v_isShared_3613_ = v_isSharedCheck_3644_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_instant_3608_);
lean_inc(v_error_3607_);
lean_inc(v_events_3606_);
lean_inc(v_config_3605_);
lean_inc(v_writer_3604_);
lean_inc(v_reader_3603_);
lean_dec(v_fst_3601_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3644_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___f_3614_; lean_object* v___f_3615_; uint8_t v___y_3617_; 
v___f_3614_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_3614_, 0, v_inst_3353_);
lean_closure_set(v___f_3614_, 1, v_handler_3355_);
v___f_3615_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
if (lean_obj_tag(v_snd_3602_) == 0)
{
uint8_t v_sentMessage_3640_; 
v_sentMessage_3640_ = lean_ctor_get_uint8(v_writer_3604_, sizeof(void*)*6);
if (v_sentMessage_3640_ == 0)
{
lean_object* v_state_3641_; 
v_state_3641_ = lean_ctor_get(v_reader_3603_, 0);
if (lean_obj_tag(v_state_3641_) == 2)
{
v___y_3617_ = v_x_3580_;
goto v___jp_3616_;
}
else
{
v___y_3617_ = v_sentMessage_3640_;
goto v___jp_3616_;
}
}
else
{
uint8_t v___x_3642_; 
v___x_3642_ = 0;
v___y_3617_ = v___x_3642_;
goto v___jp_3616_;
}
}
else
{
uint8_t v___x_3643_; 
v___x_3643_ = 0;
v___y_3617_ = v___x_3643_;
goto v___jp_3616_;
}
v___jp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3613_ == 0)
{
v___x_3619_ = v___x_3612_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_reader_3603_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_writer_3604_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_config_3605_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_events_3606_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_error_3607_);
lean_ctor_set(v_reuseFailAlloc_3639_, 5, v_instant_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*6, v_keepAlive_3609_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*6 + 1, v_forcedFlush_3610_);
v___x_3619_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v_st_3621_; 
lean_ctor_set_uint8(v___x_3619_, sizeof(void*)*6 + 2, v___y_3617_);
lean_inc_ref(v_requestStream_3586_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3619_);
v_st_3621_ = v___x_3597_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_requestStream_3586_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_keepAliveTimeout_3587_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v_currentTimeout_3588_);
lean_ctor_set(v_reuseFailAlloc_3638_, 4, v_headerTimeout_3589_);
lean_ctor_set(v_reuseFailAlloc_3638_, 5, v_response_3590_);
lean_ctor_set(v_reuseFailAlloc_3638_, 6, v_respStream_3591_);
lean_ctor_set(v_reuseFailAlloc_3638_, 7, v_expectData_3593_);
lean_ctor_set(v_reuseFailAlloc_3638_, 8, v_pendingHead_3595_);
lean_ctor_set_uint8(v_reuseFailAlloc_3638_, sizeof(void*)*9, v_requiresData_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3638_, sizeof(void*)*9 + 1, v_handlerDispatched_3594_);
v_st_3621_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___f_3622_; 
lean_inc_ref(v_st_3621_);
v___f_3622_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3622_, 0, v_st_3621_);
if (lean_obj_tag(v_snd_3602_) == 1)
{
lean_object* v_val_3623_; uint8_t v_final_3624_; uint8_t v_incomplete_3625_; lean_object* v_chunk_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___f_3631_; lean_object* v___f_3632_; lean_object* v___x_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; 
lean_dec_ref(v_st_3621_);
v_val_3623_ = lean_ctor_get(v_snd_3602_, 0);
lean_inc(v_val_3623_);
lean_dec_ref_known(v_snd_3602_, 1);
v_final_3624_ = lean_ctor_get_uint8(v_val_3623_, sizeof(void*)*1);
v_incomplete_3625_ = lean_ctor_get_uint8(v_val_3623_, sizeof(void*)*1 + 1);
v_chunk_3626_ = lean_ctor_get(v_val_3623_, 0);
lean_inc_ref(v_chunk_3626_);
lean_dec(v_val_3623_);
lean_inc_ref_n(v_requestStream_3586_, 2);
v___x_3627_ = l_Std_Http_Body_Stream_send(v_requestStream_3586_, v_chunk_3626_, v_incomplete_3625_);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = 0;
v___x_3630_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3628_, v___x_3629_, v___x_3627_, v___f_3614_);
lean_inc_ref_n(v___f_3622_, 2);
v___f_3631_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3631_, 0, v___f_3622_);
v___f_3632_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3632_, 0, v_requestStream_3586_);
lean_closure_set(v___f_3632_, 1, v___f_3631_);
lean_closure_set(v___f_3632_, 2, v___f_3622_);
v___x_3633_ = lean_box(v_final_3624_);
v___f_3634_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_3634_, 0, v___x_3633_);
lean_closure_set(v___f_3634_, 1, v___f_3622_);
lean_closure_set(v___f_3634_, 2, v___f_3615_);
lean_closure_set(v___f_3634_, 3, v_requestStream_3586_);
lean_closure_set(v___f_3634_, 4, v___f_3632_);
v___x_3635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3628_, v___x_3629_, v___x_3630_, v___f_3634_);
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_dec_ref(v___f_3622_);
lean_dec_ref(v___f_3614_);
lean_dec(v_snd_3602_);
lean_dec_ref(v_requestStream_3586_);
v___x_3636_ = lean_box(0);
v___x_3637_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3621_, v___x_3636_);
return v___x_3637_;
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
lean_object* v_x_3646_; 
v_x_3646_ = lean_ctor_get(v_event_3357_, 0);
lean_inc_ref(v_x_3646_);
lean_dec_ref_known(v_event_3357_, 1);
if (lean_obj_tag(v_x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v_onFailure_3648_; lean_object* v___x_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; 
lean_dec_ref(v_config_3356_);
lean_dec_ref(v_inst_3354_);
v_a_3647_ = lean_ctor_get(v_x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v_x_3646_, 1);
v_onFailure_3648_ = lean_ctor_get(v_inst_3353_, 2);
lean_inc_ref(v_onFailure_3648_);
lean_dec_ref(v_inst_3353_);
v___x_3649_ = lean_apply_3(v_onFailure_3648_, v_handler_3355_, v_a_3647_, lean_box(0));
v___f_3650_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3650_, 0, v_state_3358_);
v___x_3651_ = lean_unsigned_to_nat(0u);
v___x_3652_ = 0;
v___x_3653_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3651_, v___x_3652_, v___x_3649_, v___f_3650_);
return v___x_3653_;
}
else
{
lean_object* v_machine_3654_; lean_object* v_reader_3655_; lean_object* v_state_3656_; 
v_machine_3654_ = lean_ctor_get(v_state_3358_, 0);
lean_inc_ref(v_machine_3654_);
v_reader_3655_ = lean_ctor_get(v_machine_3654_, 0);
v_state_3656_ = lean_ctor_get(v_reader_3655_, 0);
if (lean_obj_tag(v_state_3656_) == 7)
{
lean_object* v_a_3657_; lean_object* v_requestStream_3658_; lean_object* v_keepAliveTimeout_3659_; lean_object* v_currentTimeout_3660_; lean_object* v_headerTimeout_3661_; lean_object* v_response_3662_; lean_object* v_respStream_3663_; uint8_t v_requiresData_3664_; lean_object* v_expectData_3665_; lean_object* v_pendingHead_3666_; lean_object* v_close_3667_; lean_object* v_isClosed_3668_; lean_object* v_body_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3353_);
v_a_3657_ = lean_ctor_get(v_x_3646_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v_x_3646_, 1);
v_requestStream_3658_ = lean_ctor_get(v_state_3358_, 1);
lean_inc_ref(v_requestStream_3658_);
v_keepAliveTimeout_3659_ = lean_ctor_get(v_state_3358_, 2);
lean_inc(v_keepAliveTimeout_3659_);
v_currentTimeout_3660_ = lean_ctor_get(v_state_3358_, 3);
lean_inc(v_currentTimeout_3660_);
v_headerTimeout_3661_ = lean_ctor_get(v_state_3358_, 4);
lean_inc(v_headerTimeout_3661_);
v_response_3662_ = lean_ctor_get(v_state_3358_, 5);
lean_inc_ref(v_response_3662_);
v_respStream_3663_ = lean_ctor_get(v_state_3358_, 6);
lean_inc(v_respStream_3663_);
v_requiresData_3664_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3665_ = lean_ctor_get(v_state_3358_, 7);
lean_inc(v_expectData_3665_);
v_pendingHead_3666_ = lean_ctor_get(v_state_3358_, 8);
lean_inc(v_pendingHead_3666_);
lean_dec_ref(v_state_3358_);
v_close_3667_ = lean_ctor_get(v_inst_3354_, 1);
lean_inc_ref(v_close_3667_);
v_isClosed_3668_ = lean_ctor_get(v_inst_3354_, 2);
lean_inc_ref(v_isClosed_3668_);
lean_dec_ref(v_inst_3354_);
v_body_3669_ = lean_ctor_get(v_a_3657_, 1);
lean_inc_n(v_body_3669_, 2);
lean_dec(v_a_3657_);
v___x_3670_ = lean_apply_2(v_isClosed_3668_, v_body_3669_, lean_box(0));
v___x_3671_ = lean_box(v_requiresData_3664_);
v___f_3672_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3672_, 0, v_machine_3654_);
lean_closure_set(v___f_3672_, 1, v_requestStream_3658_);
lean_closure_set(v___f_3672_, 2, v_keepAliveTimeout_3659_);
lean_closure_set(v___f_3672_, 3, v_currentTimeout_3660_);
lean_closure_set(v___f_3672_, 4, v_headerTimeout_3661_);
lean_closure_set(v___f_3672_, 5, v_response_3662_);
lean_closure_set(v___f_3672_, 6, v_respStream_3663_);
lean_closure_set(v___f_3672_, 7, v___x_3671_);
lean_closure_set(v___f_3672_, 8, v_expectData_3665_);
lean_closure_set(v___f_3672_, 9, v_pendingHead_3666_);
lean_inc_ref(v___f_3672_);
v___f_3673_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3673_, 0, v___f_3672_);
v___f_3674_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3674_, 0, v_close_3667_);
lean_closure_set(v___f_3674_, 1, v_body_3669_);
lean_closure_set(v___f_3674_, 2, v___f_3673_);
lean_closure_set(v___f_3674_, 3, v___f_3672_);
v___x_3675_ = lean_unsigned_to_nat(0u);
v___x_3676_ = 0;
v___x_3677_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3675_, v___x_3676_, v___x_3670_, v___f_3674_);
return v___x_3677_;
}
else
{
lean_object* v_a_3678_; lean_object* v_requestStream_3679_; lean_object* v_keepAliveTimeout_3680_; lean_object* v_currentTimeout_3681_; lean_object* v_headerTimeout_3682_; lean_object* v_response_3683_; uint8_t v_requiresData_3684_; lean_object* v_expectData_3685_; lean_object* v_pendingHead_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___f_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___f_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_a_3678_ = lean_ctor_get(v_x_3646_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v_x_3646_, 1);
v_requestStream_3679_ = lean_ctor_get(v_state_3358_, 1);
lean_inc_ref(v_requestStream_3679_);
v_keepAliveTimeout_3680_ = lean_ctor_get(v_state_3358_, 2);
lean_inc(v_keepAliveTimeout_3680_);
v_currentTimeout_3681_ = lean_ctor_get(v_state_3358_, 3);
lean_inc(v_currentTimeout_3681_);
v_headerTimeout_3682_ = lean_ctor_get(v_state_3358_, 4);
lean_inc(v_headerTimeout_3682_);
v_response_3683_ = lean_ctor_get(v_state_3358_, 5);
lean_inc_ref(v_response_3683_);
v_requiresData_3684_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3685_ = lean_ctor_get(v_state_3358_, 7);
lean_inc(v_expectData_3685_);
v_pendingHead_3686_ = lean_ctor_get(v_state_3358_, 8);
lean_inc(v_pendingHead_3686_);
lean_dec_ref(v_state_3358_);
lean_inc_ref(v_inst_3354_);
v___x_3687_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3354_, v_config_3356_, v_machine_3654_, v_a_3678_);
v___x_3688_ = 0;
v___x_3689_ = lean_box(v_requiresData_3684_);
v___x_3690_ = lean_box(v___x_3688_);
v___f_3691_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3691_, 0, v_requestStream_3679_);
lean_closure_set(v___f_3691_, 1, v_keepAliveTimeout_3680_);
lean_closure_set(v___f_3691_, 2, v_currentTimeout_3681_);
lean_closure_set(v___f_3691_, 3, v_headerTimeout_3682_);
lean_closure_set(v___f_3691_, 4, v_response_3683_);
lean_closure_set(v___f_3691_, 5, v___x_3689_);
lean_closure_set(v___f_3691_, 6, v_expectData_3685_);
lean_closure_set(v___f_3691_, 7, v___x_3690_);
lean_closure_set(v___f_3691_, 8, v_pendingHead_3686_);
v___f_3692_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3692_, 0, v___f_3691_);
v___f_3693_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3694_ = 1;
v___x_3695_ = lean_box(v___x_3688_);
v___x_3696_ = lean_box(v___x_3694_);
lean_inc_ref(v___f_3692_);
v___f_3697_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3697_, 0, v___x_3695_);
lean_closure_set(v___f_3697_, 1, v___f_3692_);
lean_closure_set(v___f_3697_, 2, v_inst_3354_);
lean_closure_set(v___f_3697_, 3, v___f_3693_);
lean_closure_set(v___f_3697_, 4, v___x_3696_);
lean_closure_set(v___f_3697_, 5, v_inst_3353_);
lean_closure_set(v___f_3697_, 6, v_handler_3355_);
lean_closure_set(v___f_3697_, 7, v___f_3692_);
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3698_, v___x_3688_, v___x_3687_, v___f_3697_);
return v___x_3699_;
}
}
}
case 4:
{
lean_object* v_onFailure_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___f_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; 
lean_dec_ref(v_config_3356_);
lean_dec_ref(v_inst_3354_);
v_onFailure_3700_ = lean_ctor_get(v_inst_3353_, 2);
lean_inc_ref(v_onFailure_3700_);
lean_dec_ref(v_inst_3353_);
v___x_3701_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3702_ = lean_apply_3(v_onFailure_3700_, v_handler_3355_, v___x_3701_, lean_box(0));
v___f_3703_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3703_, 0, v_state_3358_);
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = 0;
v___x_3706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3704_, v___x_3705_, v___x_3702_, v___f_3703_);
return v___x_3706_;
}
case 5:
{
lean_object* v_machine_3707_; lean_object* v_requestStream_3708_; lean_object* v_keepAliveTimeout_3709_; lean_object* v_currentTimeout_3710_; lean_object* v_headerTimeout_3711_; lean_object* v_response_3712_; lean_object* v_respStream_3713_; uint8_t v_requiresData_3714_; lean_object* v_expectData_3715_; lean_object* v_pendingHead_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3354_);
lean_dec_ref(v_inst_3353_);
v_machine_3707_ = lean_ctor_get(v_state_3358_, 0);
v_requestStream_3708_ = lean_ctor_get(v_state_3358_, 1);
v_keepAliveTimeout_3709_ = lean_ctor_get(v_state_3358_, 2);
v_currentTimeout_3710_ = lean_ctor_get(v_state_3358_, 3);
v_headerTimeout_3711_ = lean_ctor_get(v_state_3358_, 4);
v_response_3712_ = lean_ctor_get(v_state_3358_, 5);
v_respStream_3713_ = lean_ctor_get(v_state_3358_, 6);
v_requiresData_3714_ = lean_ctor_get_uint8(v_state_3358_, sizeof(void*)*9);
v_expectData_3715_ = lean_ctor_get(v_state_3358_, 7);
v_pendingHead_3716_ = lean_ctor_get(v_state_3358_, 8);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_state_3358_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3718_ = v_state_3358_;
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_pendingHead_3716_);
lean_inc(v_expectData_3715_);
lean_inc(v_respStream_3713_);
lean_inc(v_response_3712_);
lean_inc(v_headerTimeout_3711_);
lean_inc(v_currentTimeout_3710_);
lean_inc(v_keepAliveTimeout_3709_);
lean_inc(v_requestStream_3708_);
lean_inc(v_machine_3707_);
lean_dec(v_state_3358_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; lean_object* v___x_3724_; 
v___x_3720_ = lean_box(55);
v___x_3721_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3707_, v___x_3720_);
v___x_3722_ = 0;
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3721_);
v___x_3724_ = v___x_3718_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_requestStream_3708_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_keepAliveTimeout_3709_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_currentTimeout_3710_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_headerTimeout_3711_);
lean_ctor_set(v_reuseFailAlloc_3729_, 5, v_response_3712_);
lean_ctor_set(v_reuseFailAlloc_3729_, 6, v_respStream_3713_);
lean_ctor_set(v_reuseFailAlloc_3729_, 7, v_expectData_3715_);
lean_ctor_set(v_reuseFailAlloc_3729_, 8, v_pendingHead_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, sizeof(void*)*9, v_requiresData_3714_);
v___x_3724_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
lean_ctor_set_uint8(v___x_3724_, sizeof(void*)*9 + 1, v___x_3722_);
v___x_3725_ = lean_box(v___x_3722_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
}
}
default: 
{
uint8_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec_ref(v_config_3356_);
lean_dec(v_handler_3355_);
lean_dec_ref(v_inst_3354_);
lean_dec_ref(v_inst_3353_);
v___x_3731_ = 1;
v___x_3732_ = lean_box(v___x_3731_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_state_3358_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3736_, lean_object* v_inst_3737_, lean_object* v_handler_3738_, lean_object* v_config_3739_, lean_object* v_event_3740_, lean_object* v_state_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3736_, v_inst_3737_, v_handler_3738_, v_config_3739_, v_event_3740_, v_state_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3744_, lean_object* v_00_u03b2_3745_, lean_object* v_inst_3746_, lean_object* v_inst_3747_, lean_object* v_handler_3748_, lean_object* v_config_3749_, lean_object* v_event_3750_, lean_object* v_state_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3746_, v_inst_3747_, v_handler_3748_, v_config_3749_, v_event_3750_, v_state_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3754_, lean_object* v_00_u03b2_3755_, lean_object* v_inst_3756_, lean_object* v_inst_3757_, lean_object* v_handler_3758_, lean_object* v_config_3759_, lean_object* v_event_3760_, lean_object* v_state_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3754_, v_00_u03b2_3755_, v_inst_3756_, v_inst_3757_, v_handler_3758_, v_config_3759_, v_event_3760_, v_state_3761_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_expectData_3764_, lean_object* v_respStream_3765_, lean_object* v_currentTimeout_3766_, lean_object* v_keepAliveTimeout_3767_, lean_object* v_headerTimeout_3768_, lean_object* v_connectionContext_3769_, uint8_t v_handlerDispatched_3770_, lean_object* v_response_3771_, lean_object* v_socket_3772_, uint8_t v_requiresData_3773_, uint8_t v_sentMessage_3774_, lean_object* v_reader_3775_, uint8_t v_requestBodyInterested_3776_, lean_object* v_requestBody_3777_){
_start:
{
lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3786_; uint8_t v___y_3792_; uint8_t v___y_3795_; uint8_t v___y_3796_; uint8_t v___y_3798_; uint8_t v___y_3799_; uint8_t v___y_3800_; uint8_t v___y_3802_; uint8_t v___y_3803_; uint8_t v___y_3806_; 
if (v_handlerDispatched_3770_ == 0)
{
uint8_t v___x_3809_; 
v___x_3809_ = 1;
v___y_3806_ = v___x_3809_;
goto v___jp_3805_;
}
else
{
uint8_t v___x_3810_; 
v___x_3810_ = 0;
v___y_3806_ = v___x_3810_;
goto v___jp_3805_;
}
v___jp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3782_, 0, v___y_3780_);
lean_ctor_set(v___x_3782_, 1, v_expectData_3764_);
lean_ctor_set(v___x_3782_, 2, v___y_3781_);
lean_ctor_set(v___x_3782_, 3, v_respStream_3765_);
lean_ctor_set(v___x_3782_, 4, v_requestBody_3777_);
lean_ctor_set(v___x_3782_, 5, v_currentTimeout_3766_);
lean_ctor_set(v___x_3782_, 6, v_keepAliveTimeout_3767_);
lean_ctor_set(v___x_3782_, 7, v_headerTimeout_3768_);
lean_ctor_set(v___x_3782_, 8, v_connectionContext_3769_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
v___jp_3785_:
{
if (v_handlerDispatched_3770_ == 0)
{
lean_object* v___x_3787_; 
lean_dec_ref(v_response_3771_);
v___x_3787_ = lean_box(0);
v___y_3780_ = v___y_3786_;
v___y_3781_ = v___x_3787_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_response_3771_);
v___y_3780_ = v___y_3786_;
v___y_3781_ = v___x_3788_;
goto v___jp_3779_;
}
}
v___jp_3789_:
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v_socket_3772_);
v___y_3786_ = v___x_3790_;
goto v___jp_3785_;
}
v___jp_3791_:
{
if (v_requiresData_3773_ == 0)
{
if (v___y_3792_ == 0)
{
lean_object* v___x_3793_; 
lean_dec(v_socket_3772_);
v___x_3793_ = lean_box(0);
v___y_3786_ = v___x_3793_;
goto v___jp_3785_;
}
else
{
goto v___jp_3789_;
}
}
else
{
goto v___jp_3789_;
}
}
v___jp_3794_:
{
if (v___y_3795_ == 0)
{
v___y_3792_ = v___y_3796_;
goto v___jp_3791_;
}
else
{
v___y_3792_ = v___y_3795_;
goto v___jp_3791_;
}
}
v___jp_3797_:
{
if (v___y_3798_ == 0)
{
v___y_3795_ = v___y_3799_;
v___y_3796_ = v___y_3800_;
goto v___jp_3794_;
}
else
{
v___y_3795_ = v___y_3799_;
v___y_3796_ = v___y_3798_;
goto v___jp_3794_;
}
}
v___jp_3801_:
{
if (v_sentMessage_3774_ == 0)
{
lean_object* v_state_3804_; 
v_state_3804_ = lean_ctor_get(v_reader_3775_, 0);
if (lean_obj_tag(v_state_3804_) == 2)
{
v___y_3798_ = v___y_3803_;
v___y_3799_ = v___y_3802_;
v___y_3800_ = v_requestBodyInterested_3776_;
goto v___jp_3797_;
}
else
{
v___y_3798_ = v___y_3803_;
v___y_3799_ = v___y_3802_;
v___y_3800_ = v_sentMessage_3774_;
goto v___jp_3797_;
}
}
else
{
v___y_3798_ = v___y_3803_;
v___y_3799_ = v___y_3802_;
v___y_3800_ = v_sentMessage_3774_;
goto v___jp_3797_;
}
}
v___jp_3805_:
{
if (lean_obj_tag(v_respStream_3765_) == 0)
{
uint8_t v___x_3807_; 
v___x_3807_ = 0;
v___y_3802_ = v___y_3806_;
v___y_3803_ = v___x_3807_;
goto v___jp_3801_;
}
else
{
uint8_t v___x_3808_; 
v___x_3808_ = 1;
v___y_3802_ = v___y_3806_;
v___y_3803_ = v___x_3808_;
goto v___jp_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_expectData_3811_, lean_object* v_respStream_3812_, lean_object* v_currentTimeout_3813_, lean_object* v_keepAliveTimeout_3814_, lean_object* v_headerTimeout_3815_, lean_object* v_connectionContext_3816_, lean_object* v_handlerDispatched_3817_, lean_object* v_response_3818_, lean_object* v_socket_3819_, lean_object* v_requiresData_3820_, lean_object* v_sentMessage_3821_, lean_object* v_reader_3822_, lean_object* v_requestBodyInterested_3823_, lean_object* v_requestBody_3824_, lean_object* v___y_3825_){
_start:
{
uint8_t v_handlerDispatched_boxed_3826_; uint8_t v_requiresData_boxed_3827_; uint8_t v_sentMessage_boxed_3828_; uint8_t v_requestBodyInterested_boxed_3829_; lean_object* v_res_3830_; 
v_handlerDispatched_boxed_3826_ = lean_unbox(v_handlerDispatched_3817_);
v_requiresData_boxed_3827_ = lean_unbox(v_requiresData_3820_);
v_sentMessage_boxed_3828_ = lean_unbox(v_sentMessage_3821_);
v_requestBodyInterested_boxed_3829_ = lean_unbox(v_requestBodyInterested_3823_);
v_res_3830_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_expectData_3811_, v_respStream_3812_, v_currentTimeout_3813_, v_keepAliveTimeout_3814_, v_headerTimeout_3815_, v_connectionContext_3816_, v_handlerDispatched_boxed_3826_, v_response_3818_, v_socket_3819_, v_requiresData_boxed_3827_, v_sentMessage_boxed_3828_, v_reader_3822_, v_requestBodyInterested_boxed_3829_, v_requestBody_3824_);
lean_dec_ref(v_reader_3822_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3831_, lean_object* v_x_3832_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v___f_3831_);
v_a_3834_ = lean_ctor_get(v_x_3832_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_x_3832_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3836_ = v_x_3832_;
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v_x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
return v___x_3840_;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3844_; 
v_a_3843_ = lean_ctor_get(v_x_3832_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v_x_3832_, 1);
v___x_3844_ = lean_apply_2(v___f_3831_, v_a_3843_, lean_box(0));
return v___x_3844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3845_, lean_object* v_x_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3845_, v_x_3846_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_expectData_3853_, lean_object* v_respStream_3854_, lean_object* v_currentTimeout_3855_, lean_object* v_keepAliveTimeout_3856_, lean_object* v_headerTimeout_3857_, lean_object* v_connectionContext_3858_, uint8_t v_handlerDispatched_3859_, lean_object* v_response_3860_, lean_object* v_socket_3861_, uint8_t v_requiresData_3862_, uint8_t v_sentMessage_3863_, lean_object* v_reader_3864_, uint8_t v_pullBodyStalled_3865_, uint8_t v_requestBodyOpen_3866_, lean_object* v_requestStream_3867_, uint8_t v_requestBodyInterested_3868_){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___f_3874_; lean_object* v___f_3875_; uint8_t v___y_3877_; 
v___x_3870_ = lean_box(v_handlerDispatched_3859_);
v___x_3871_ = lean_box(v_requiresData_3862_);
v___x_3872_ = lean_box(v_sentMessage_3863_);
v___x_3873_ = lean_box(v_requestBodyInterested_3868_);
lean_inc_ref(v_reader_3864_);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3874_, 0, v_expectData_3853_);
lean_closure_set(v___f_3874_, 1, v_respStream_3854_);
lean_closure_set(v___f_3874_, 2, v_currentTimeout_3855_);
lean_closure_set(v___f_3874_, 3, v_keepAliveTimeout_3856_);
lean_closure_set(v___f_3874_, 4, v_headerTimeout_3857_);
lean_closure_set(v___f_3874_, 5, v_connectionContext_3858_);
lean_closure_set(v___f_3874_, 6, v___x_3870_);
lean_closure_set(v___f_3874_, 7, v_response_3860_);
lean_closure_set(v___f_3874_, 8, v_socket_3861_);
lean_closure_set(v___f_3874_, 9, v___x_3871_);
lean_closure_set(v___f_3874_, 10, v___x_3872_);
lean_closure_set(v___f_3874_, 11, v_reader_3864_);
lean_closure_set(v___f_3874_, 12, v___x_3873_);
v___f_3875_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3875_, 0, v___f_3874_);
if (v_sentMessage_3863_ == 0)
{
lean_object* v_state_3881_; 
v_state_3881_ = lean_ctor_get(v_reader_3864_, 0);
lean_inc(v_state_3881_);
lean_dec_ref(v_reader_3864_);
if (lean_obj_tag(v_state_3881_) == 2)
{
lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3892_; 
v_isSharedCheck_3892_ = !lean_is_exclusive(v_state_3881_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; 
v_unused_3893_ = lean_ctor_get(v_state_3881_, 0);
lean_dec(v_unused_3893_);
v___x_3883_ = v_state_3881_;
v_isShared_3884_ = v_isSharedCheck_3892_;
goto v_resetjp_3882_;
}
else
{
lean_dec(v_state_3881_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3892_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
if (v_pullBodyStalled_3865_ == 0)
{
if (v_requestBodyOpen_3866_ == 0)
{
lean_del_object(v___x_3883_);
lean_dec_ref(v_requestStream_3867_);
v___y_3877_ = v_requestBodyOpen_3866_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 1);
lean_ctor_set(v___x_3883_, 0, v_requestStream_3867_);
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_requestStream_3867_);
v___x_3886_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
v___x_3889_ = lean_unsigned_to_nat(0u);
v___x_3890_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3889_, v_pullBodyStalled_3865_, v___x_3888_, v___f_3875_);
return v___x_3890_;
}
}
}
else
{
lean_del_object(v___x_3883_);
lean_dec_ref(v_requestStream_3867_);
v___y_3877_ = v_sentMessage_3863_;
goto v___jp_3876_;
}
}
}
else
{
lean_dec(v_state_3881_);
lean_dec_ref(v_requestStream_3867_);
v___y_3877_ = v_sentMessage_3863_;
goto v___jp_3876_;
}
}
else
{
uint8_t v___x_3894_; 
lean_dec_ref(v_requestStream_3867_);
lean_dec_ref(v_reader_3864_);
v___x_3894_ = 0;
v___y_3877_ = v___x_3894_;
goto v___jp_3876_;
}
v___jp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3879_ = lean_unsigned_to_nat(0u);
v___x_3880_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3879_, v___y_3877_, v___x_3878_, v___f_3875_);
return v___x_3880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_expectData_3895_ = _args[0];
lean_object* v_respStream_3896_ = _args[1];
lean_object* v_currentTimeout_3897_ = _args[2];
lean_object* v_keepAliveTimeout_3898_ = _args[3];
lean_object* v_headerTimeout_3899_ = _args[4];
lean_object* v_connectionContext_3900_ = _args[5];
lean_object* v_handlerDispatched_3901_ = _args[6];
lean_object* v_response_3902_ = _args[7];
lean_object* v_socket_3903_ = _args[8];
lean_object* v_requiresData_3904_ = _args[9];
lean_object* v_sentMessage_3905_ = _args[10];
lean_object* v_reader_3906_ = _args[11];
lean_object* v_pullBodyStalled_3907_ = _args[12];
lean_object* v_requestBodyOpen_3908_ = _args[13];
lean_object* v_requestStream_3909_ = _args[14];
lean_object* v_requestBodyInterested_3910_ = _args[15];
lean_object* v___y_3911_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3912_; uint8_t v_requiresData_boxed_3913_; uint8_t v_sentMessage_boxed_3914_; uint8_t v_pullBodyStalled_boxed_3915_; uint8_t v_requestBodyOpen_boxed_3916_; uint8_t v_requestBodyInterested_boxed_3917_; lean_object* v_res_3918_; 
v_handlerDispatched_boxed_3912_ = lean_unbox(v_handlerDispatched_3901_);
v_requiresData_boxed_3913_ = lean_unbox(v_requiresData_3904_);
v_sentMessage_boxed_3914_ = lean_unbox(v_sentMessage_3905_);
v_pullBodyStalled_boxed_3915_ = lean_unbox(v_pullBodyStalled_3907_);
v_requestBodyOpen_boxed_3916_ = lean_unbox(v_requestBodyOpen_3908_);
v_requestBodyInterested_boxed_3917_ = lean_unbox(v_requestBodyInterested_3910_);
v_res_3918_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_expectData_3895_, v_respStream_3896_, v_currentTimeout_3897_, v_keepAliveTimeout_3898_, v_headerTimeout_3899_, v_connectionContext_3900_, v_handlerDispatched_boxed_3912_, v_response_3902_, v_socket_3903_, v_requiresData_boxed_3913_, v_sentMessage_boxed_3914_, v_reader_3906_, v_pullBodyStalled_boxed_3915_, v_requestBodyOpen_boxed_3916_, v_requestStream_3909_, v_requestBodyInterested_boxed_3917_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3919_, lean_object* v_x_3920_){
_start:
{
if (lean_obj_tag(v_x_3920_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v___f_3919_);
v_a_3922_ = lean_ctor_get(v_x_3920_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_x_3920_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3924_ = v_x_3920_;
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v_x_3920_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3932_; 
v_a_3931_ = lean_ctor_get(v_x_3920_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v_x_3920_, 1);
v___x_3932_ = lean_apply_2(v___f_3919_, v_a_3931_, lean_box(0));
return v___x_3932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3933_, lean_object* v_x_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3933_, v_x_3934_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_expectData_3937_, lean_object* v_respStream_3938_, lean_object* v_currentTimeout_3939_, lean_object* v_keepAliveTimeout_3940_, lean_object* v_headerTimeout_3941_, lean_object* v_connectionContext_3942_, uint8_t v_handlerDispatched_3943_, lean_object* v_response_3944_, lean_object* v_socket_3945_, uint8_t v_requiresData_3946_, uint8_t v_sentMessage_3947_, lean_object* v_reader_3948_, uint8_t v_pullBodyStalled_3949_, lean_object* v_requestStream_3950_, uint8_t v_requestBodyOpen_3951_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___f_3958_; lean_object* v___f_3959_; uint8_t v___y_3961_; 
v___x_3953_ = lean_box(v_handlerDispatched_3943_);
v___x_3954_ = lean_box(v_requiresData_3946_);
v___x_3955_ = lean_box(v_sentMessage_3947_);
v___x_3956_ = lean_box(v_pullBodyStalled_3949_);
v___x_3957_ = lean_box(v_requestBodyOpen_3951_);
lean_inc_ref(v_requestStream_3950_);
lean_inc_ref(v_reader_3948_);
v___f_3958_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3958_, 0, v_expectData_3937_);
lean_closure_set(v___f_3958_, 1, v_respStream_3938_);
lean_closure_set(v___f_3958_, 2, v_currentTimeout_3939_);
lean_closure_set(v___f_3958_, 3, v_keepAliveTimeout_3940_);
lean_closure_set(v___f_3958_, 4, v_headerTimeout_3941_);
lean_closure_set(v___f_3958_, 5, v_connectionContext_3942_);
lean_closure_set(v___f_3958_, 6, v___x_3953_);
lean_closure_set(v___f_3958_, 7, v_response_3944_);
lean_closure_set(v___f_3958_, 8, v_socket_3945_);
lean_closure_set(v___f_3958_, 9, v___x_3954_);
lean_closure_set(v___f_3958_, 10, v___x_3955_);
lean_closure_set(v___f_3958_, 11, v_reader_3948_);
lean_closure_set(v___f_3958_, 12, v___x_3956_);
lean_closure_set(v___f_3958_, 13, v___x_3957_);
lean_closure_set(v___f_3958_, 14, v_requestStream_3950_);
v___f_3959_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3959_, 0, v___f_3958_);
if (v_sentMessage_3947_ == 0)
{
lean_object* v_state_3967_; 
v_state_3967_ = lean_ctor_get(v_reader_3948_, 0);
lean_inc(v_state_3967_);
lean_dec_ref(v_reader_3948_);
if (lean_obj_tag(v_state_3967_) == 2)
{
lean_dec_ref_known(v_state_3967_, 1);
if (v_requestBodyOpen_3951_ == 0)
{
lean_dec_ref(v_requestStream_3950_);
v___y_3961_ = v_requestBodyOpen_3951_;
goto v___jp_3960_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3950_);
v___x_3969_ = lean_unsigned_to_nat(0u);
v___x_3970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3969_, v_sentMessage_3947_, v___x_3968_, v___f_3959_);
return v___x_3970_;
}
}
else
{
lean_dec(v_state_3967_);
lean_dec_ref(v_requestStream_3950_);
v___y_3961_ = v_sentMessage_3947_;
goto v___jp_3960_;
}
}
else
{
uint8_t v___x_3971_; 
lean_dec_ref(v_requestStream_3950_);
lean_dec_ref(v_reader_3948_);
v___x_3971_ = 0;
v___y_3961_ = v___x_3971_;
goto v___jp_3960_;
}
v___jp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3962_ = lean_box(v___y_3961_);
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v___x_3965_ = lean_unsigned_to_nat(0u);
v___x_3966_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3965_, v___y_3961_, v___x_3964_, v___f_3959_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_expectData_3972_, lean_object* v_respStream_3973_, lean_object* v_currentTimeout_3974_, lean_object* v_keepAliveTimeout_3975_, lean_object* v_headerTimeout_3976_, lean_object* v_connectionContext_3977_, lean_object* v_handlerDispatched_3978_, lean_object* v_response_3979_, lean_object* v_socket_3980_, lean_object* v_requiresData_3981_, lean_object* v_sentMessage_3982_, lean_object* v_reader_3983_, lean_object* v_pullBodyStalled_3984_, lean_object* v_requestStream_3985_, lean_object* v_requestBodyOpen_3986_, lean_object* v___y_3987_){
_start:
{
uint8_t v_handlerDispatched_boxed_3988_; uint8_t v_requiresData_boxed_3989_; uint8_t v_sentMessage_boxed_3990_; uint8_t v_pullBodyStalled_boxed_3991_; uint8_t v_requestBodyOpen_boxed_3992_; lean_object* v_res_3993_; 
v_handlerDispatched_boxed_3988_ = lean_unbox(v_handlerDispatched_3978_);
v_requiresData_boxed_3989_ = lean_unbox(v_requiresData_3981_);
v_sentMessage_boxed_3990_ = lean_unbox(v_sentMessage_3982_);
v_pullBodyStalled_boxed_3991_ = lean_unbox(v_pullBodyStalled_3984_);
v_requestBodyOpen_boxed_3992_ = lean_unbox(v_requestBodyOpen_3986_);
v_res_3993_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_expectData_3972_, v_respStream_3973_, v_currentTimeout_3974_, v_keepAliveTimeout_3975_, v_headerTimeout_3976_, v_connectionContext_3977_, v_handlerDispatched_boxed_3988_, v_response_3979_, v_socket_3980_, v_requiresData_boxed_3989_, v_sentMessage_boxed_3990_, v_reader_3983_, v_pullBodyStalled_boxed_3991_, v_requestStream_3985_, v_requestBodyOpen_boxed_3992_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3994_, lean_object* v___f_3995_, uint8_t v___x_3996_, lean_object* v_x_3997_){
_start:
{
uint8_t v___y_4000_; 
if (lean_obj_tag(v_x_3997_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v___f_3995_);
v_a_4006_ = lean_ctor_get(v_x_3997_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_x_3997_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4008_ = v_x_3997_;
v_isShared_4009_ = v_isSharedCheck_4014_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v_x_3997_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4014_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
return v___x_4012_;
}
}
}
else
{
lean_object* v_a_4015_; uint8_t v___x_4016_; 
v_a_4015_ = lean_ctor_get(v_x_3997_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v_x_3997_, 1);
v___x_4016_ = lean_unbox(v_a_4015_);
lean_dec(v_a_4015_);
if (v___x_4016_ == 0)
{
v___y_4000_ = v___x_3996_;
goto v___jp_3999_;
}
else
{
v___y_4000_ = v_sentMessage_3994_;
goto v___jp_3999_;
}
}
v___jp_3999_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4001_ = lean_box(v___y_4000_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
v___x_4004_ = lean_unsigned_to_nat(0u);
v___x_4005_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4004_, v_sentMessage_3994_, v___x_4003_, v___f_3995_);
return v___x_4005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4017_, lean_object* v___f_4018_, lean_object* v___x_4019_, lean_object* v_x_4020_, lean_object* v___y_4021_){
_start:
{
uint8_t v_sentMessage_boxed_4022_; uint8_t v___x_2561__boxed_4023_; lean_object* v_res_4024_; 
v_sentMessage_boxed_4022_ = lean_unbox(v_sentMessage_4017_);
v___x_2561__boxed_4023_ = lean_unbox(v___x_4019_);
v_res_4024_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4022_, v___f_4018_, v___x_2561__boxed_4023_, v_x_4020_);
return v_res_4024_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___f_4025_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4026_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4027_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4028_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4028_, 0, lean_box(0));
lean_closure_set(v___x_4028_, 1, lean_box(0));
lean_closure_set(v___x_4028_, 2, v___x_4027_);
lean_closure_set(v___x_4028_, 3, lean_box(0));
lean_closure_set(v___x_4028_, 4, lean_box(0));
lean_closure_set(v___x_4028_, 5, v___x_4026_);
lean_closure_set(v___x_4028_, 6, v___f_4025_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4029_, lean_object* v_connectionContext_4030_, lean_object* v_state_4031_){
_start:
{
lean_object* v_machine_4033_; lean_object* v_writer_4034_; lean_object* v_requestStream_4035_; lean_object* v_keepAliveTimeout_4036_; lean_object* v_currentTimeout_4037_; lean_object* v_headerTimeout_4038_; lean_object* v_response_4039_; lean_object* v_respStream_4040_; uint8_t v_requiresData_4041_; lean_object* v_expectData_4042_; uint8_t v_handlerDispatched_4043_; lean_object* v_reader_4044_; uint8_t v_pullBodyStalled_4045_; uint8_t v_sentMessage_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___f_4051_; lean_object* v___f_4052_; uint8_t v___y_4054_; 
v_machine_4033_ = lean_ctor_get(v_state_4031_, 0);
lean_inc_ref(v_machine_4033_);
v_writer_4034_ = lean_ctor_get(v_machine_4033_, 1);
lean_inc_ref(v_writer_4034_);
v_requestStream_4035_ = lean_ctor_get(v_state_4031_, 1);
lean_inc_ref_n(v_requestStream_4035_, 2);
v_keepAliveTimeout_4036_ = lean_ctor_get(v_state_4031_, 2);
lean_inc(v_keepAliveTimeout_4036_);
v_currentTimeout_4037_ = lean_ctor_get(v_state_4031_, 3);
lean_inc(v_currentTimeout_4037_);
v_headerTimeout_4038_ = lean_ctor_get(v_state_4031_, 4);
lean_inc(v_headerTimeout_4038_);
v_response_4039_ = lean_ctor_get(v_state_4031_, 5);
lean_inc_ref(v_response_4039_);
v_respStream_4040_ = lean_ctor_get(v_state_4031_, 6);
lean_inc(v_respStream_4040_);
v_requiresData_4041_ = lean_ctor_get_uint8(v_state_4031_, sizeof(void*)*9);
v_expectData_4042_ = lean_ctor_get(v_state_4031_, 7);
lean_inc(v_expectData_4042_);
v_handlerDispatched_4043_ = lean_ctor_get_uint8(v_state_4031_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4031_);
v_reader_4044_ = lean_ctor_get(v_machine_4033_, 0);
lean_inc_ref_n(v_reader_4044_, 2);
v_pullBodyStalled_4045_ = lean_ctor_get_uint8(v_machine_4033_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4033_);
v_sentMessage_4046_ = lean_ctor_get_uint8(v_writer_4034_, sizeof(void*)*6);
lean_dec_ref(v_writer_4034_);
v___x_4047_ = lean_box(v_handlerDispatched_4043_);
v___x_4048_ = lean_box(v_requiresData_4041_);
v___x_4049_ = lean_box(v_sentMessage_4046_);
v___x_4050_ = lean_box(v_pullBodyStalled_4045_);
v___f_4051_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4051_, 0, v_expectData_4042_);
lean_closure_set(v___f_4051_, 1, v_respStream_4040_);
lean_closure_set(v___f_4051_, 2, v_currentTimeout_4037_);
lean_closure_set(v___f_4051_, 3, v_keepAliveTimeout_4036_);
lean_closure_set(v___f_4051_, 4, v_headerTimeout_4038_);
lean_closure_set(v___f_4051_, 5, v_connectionContext_4030_);
lean_closure_set(v___f_4051_, 6, v___x_4047_);
lean_closure_set(v___f_4051_, 7, v_response_4039_);
lean_closure_set(v___f_4051_, 8, v_socket_4029_);
lean_closure_set(v___f_4051_, 9, v___x_4048_);
lean_closure_set(v___f_4051_, 10, v___x_4049_);
lean_closure_set(v___f_4051_, 11, v_reader_4044_);
lean_closure_set(v___f_4051_, 12, v___x_4050_);
lean_closure_set(v___f_4051_, 13, v_requestStream_4035_);
v___f_4052_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4052_, 0, v___f_4051_);
if (v_sentMessage_4046_ == 0)
{
lean_object* v_state_4060_; 
v_state_4060_ = lean_ctor_get(v_reader_4044_, 0);
lean_inc(v_state_4060_);
lean_dec_ref(v_reader_4044_);
if (lean_obj_tag(v_state_4060_) == 2)
{
lean_object* v___x_4061_; lean_object* v___f_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; lean_object* v___x_2027__overap_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___f_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_dec_ref_known(v_state_4060_, 1);
v___x_4061_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4062_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4063_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4064_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2027__overap_4065_ = l_Std_Mutex_atomically___redArg(v___x_4061_, v___f_4062_, v___f_4063_, v_requestStream_4035_, v___x_4064_);
v___x_4066_ = lean_apply_1(v___x_2027__overap_4065_, lean_box(0));
v___x_4067_ = 1;
v___x_4068_ = lean_box(v_sentMessage_4046_);
v___x_4069_ = lean_box(v___x_4067_);
v___f_4070_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4070_, 0, v___x_4068_);
lean_closure_set(v___f_4070_, 1, v___f_4052_);
lean_closure_set(v___f_4070_, 2, v___x_4069_);
v___x_4071_ = lean_unsigned_to_nat(0u);
v___x_4072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4071_, v_sentMessage_4046_, v___x_4066_, v___f_4070_);
return v___x_4072_;
}
else
{
lean_dec(v_state_4060_);
lean_dec_ref(v_requestStream_4035_);
v___y_4054_ = v_sentMessage_4046_;
goto v___jp_4053_;
}
}
else
{
uint8_t v___x_4073_; 
lean_dec_ref(v_reader_4044_);
lean_dec_ref(v_requestStream_4035_);
v___x_4073_ = 0;
v___y_4054_ = v___x_4073_;
goto v___jp_4053_;
}
v___jp_4053_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4055_ = lean_box(v___y_4054_);
v___x_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4058_, v___y_4054_, v___x_4057_, v___f_4052_);
return v___x_4059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4074_, lean_object* v_connectionContext_4075_, lean_object* v_state_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4074_, v_connectionContext_4075_, v_state_4076_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4079_, lean_object* v_00_u03b2_4080_, lean_object* v_inst_4081_, lean_object* v_socket_4082_, lean_object* v_connectionContext_4083_, lean_object* v_state_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4082_, v_connectionContext_4083_, v_state_4084_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4087_, lean_object* v_00_u03b2_4088_, lean_object* v_inst_4089_, lean_object* v_socket_4090_, lean_object* v_connectionContext_4091_, lean_object* v_state_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4087_, v_00_u03b2_4088_, v_inst_4089_, v_socket_4090_, v_connectionContext_4091_, v_state_4092_);
lean_dec_ref(v_inst_4089_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4099_){
_start:
{
if (lean_obj_tag(v_x_4099_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4109_; 
v_a_4101_ = lean_ctor_get(v_x_4099_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_x_4099_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4103_ = v_x_4099_;
v_isShared_4104_ = v_isSharedCheck_4109_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v_x_4099_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4109_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
return v___x_4107_;
}
}
}
else
{
lean_object* v___x_4110_; 
lean_dec_ref_known(v_x_4099_, 1);
v___x_4110_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___closed__1));
return v___x_4110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4111_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_onFailure_4114_, lean_object* v_handler_4115_, lean_object* v___f_4116_, lean_object* v_x_4117_){
_start:
{
if (lean_obj_tag(v_x_4117_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; 
v_a_4119_ = lean_ctor_get(v_x_4117_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v_x_4117_, 1);
v___x_4120_ = lean_apply_3(v_onFailure_4114_, v_handler_4115_, v_a_4119_, lean_box(0));
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = 0;
v___x_4123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4121_, v___x_4122_, v___x_4120_, v___f_4116_);
return v___x_4123_;
}
else
{
lean_object* v___x_4124_; 
lean_dec_ref(v___f_4116_);
lean_dec(v_handler_4115_);
lean_dec_ref(v_onFailure_4114_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_x_4117_);
return v___x_4124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_onFailure_4125_, lean_object* v_handler_4126_, lean_object* v___f_4127_, lean_object* v_x_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_onFailure_4125_, v_handler_4126_, v___f_4127_, v_x_4128_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_x_4131_){
_start:
{
if (lean_obj_tag(v_x_4131_) == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4141_; 
v_a_4133_ = lean_ctor_get(v_x_4131_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_x_4131_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4135_ = v_x_4131_;
v_isShared_4136_ = v_isSharedCheck_4141_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v_x_4131_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4141_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4133_);
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
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4151_; 
v_a_4142_ = lean_ctor_get(v_x_4131_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_x_4131_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4144_ = v_x_4131_;
v_isShared_4145_ = v_isSharedCheck_4151_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v_x_4131_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4151_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4146_; lean_object* v___x_4148_; 
v___x_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_a_4142_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v___x_4146_);
v___x_4148_ = v___x_4144_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; 
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_x_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_x_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4155_){
_start:
{
if (lean_obj_tag(v_x_4155_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4165_; 
v_a_4157_ = lean_ctor_get(v_x_4155_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_x_4155_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4159_ = v_x_4155_;
v_isShared_4160_ = v_isSharedCheck_4165_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v_x_4155_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4165_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
return v___x_4163_;
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4184_; 
v_a_4166_ = lean_ctor_get(v_x_4155_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_x_4155_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4168_ = v_x_4155_;
v_isShared_4169_ = v_isSharedCheck_4184_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v_x_4155_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4184_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v_snd_4170_; uint8_t v___x_4171_; 
v_snd_4170_ = lean_ctor_get(v_a_4166_, 1);
v___x_4171_ = lean_unbox(v_snd_4170_);
if (v___x_4171_ == 0)
{
lean_object* v_fst_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v_fst_4172_ = lean_ctor_get(v_a_4166_, 0);
lean_inc(v_fst_4172_);
lean_dec(v_a_4166_);
v___x_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_fst_4172_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4173_);
v___x_4175_ = v___x_4168_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4176_; 
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
else
{
lean_object* v_fst_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v_fst_4178_ = lean_ctor_get(v_a_4166_, 0);
lean_inc(v_fst_4178_);
lean_dec(v_a_4166_);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_fst_4178_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4179_);
v___x_4181_ = v___x_4168_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4182_; 
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
return v___x_4182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4185_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4188_, lean_object* v_socket_4189_, lean_object* v_____r_4190_){
_start:
{
lean_object* v_val_4193_; lean_object* v_close_4195_; lean_object* v___x_4196_; 
v_close_4195_ = lean_ctor_get(v_inst_4188_, 3);
lean_inc_ref(v_close_4195_);
lean_dec_ref(v_inst_4188_);
v___x_4196_ = lean_apply_2(v_close_4195_, v_socket_4189_, lean_box(0));
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set_tag(v___x_4199_, 1);
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
v_val_4193_ = v___x_4202_;
goto v___jp_4192_;
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_a_4205_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4196_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4196_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
lean_ctor_set_tag(v___x_4207_, 0);
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
v_val_4193_ = v___x_4210_;
goto v___jp_4192_;
}
}
}
v___jp_4192_:
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_val_4193_);
return v___x_4194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4213_, lean_object* v_socket_4214_, lean_object* v_____r_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4213_, v_socket_4214_, v_____r_4215_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4218_, lean_object* v_x_4219_){
_start:
{
if (lean_obj_tag(v_x_4219_) == 0)
{
lean_object* v___x_4221_; 
lean_dec_ref(v___f_4218_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_x_4219_);
return v___x_4221_;
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4223_; 
v_a_4222_ = lean_ctor_get(v_x_4219_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v_x_4219_, 1);
v___x_4223_ = lean_apply_2(v___f_4218_, v_a_4222_, lean_box(0));
return v___x_4223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4224_, lean_object* v_x_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4224_, v_x_4225_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4228_, lean_object* v_val_4229_, lean_object* v___f_4230_, lean_object* v___f_4231_, lean_object* v_x_4232_){
_start:
{
if (lean_obj_tag(v_x_4232_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v___f_4231_);
lean_dec_ref(v___f_4230_);
lean_dec(v_val_4229_);
lean_dec_ref(v_close_4228_);
v_a_4234_ = lean_ctor_get(v_x_4232_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_x_4232_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4236_ = v_x_4232_;
v_isShared_4237_ = v_isSharedCheck_4242_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v_x_4232_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4242_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
}
}
else
{
lean_object* v_a_4243_; uint8_t v___x_4244_; 
v_a_4243_ = lean_ctor_get(v_x_4232_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v_x_4232_, 1);
v___x_4244_ = lean_unbox(v_a_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; 
lean_dec_ref(v___f_4231_);
v___x_4245_ = lean_apply_2(v_close_4228_, v_val_4229_, lean_box(0));
v___x_4246_ = lean_unsigned_to_nat(0u);
v___x_4247_ = lean_unbox(v_a_4243_);
lean_dec(v_a_4243_);
v___x_4248_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4246_, v___x_4247_, v___x_4245_, v___f_4230_);
return v___x_4248_;
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
lean_dec(v_a_4243_);
lean_dec_ref(v___f_4230_);
lean_dec(v_val_4229_);
lean_dec_ref(v_close_4228_);
v___x_4249_ = lean_box(0);
v___x_4250_ = lean_apply_2(v___f_4231_, v___x_4249_, lean_box(0));
return v___x_4250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4251_, lean_object* v_val_4252_, lean_object* v___f_4253_, lean_object* v___f_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4251_, v_val_4252_, v___f_4253_, v___f_4254_, v_x_4255_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4258_, lean_object* v_responseBodyInstance_4259_, lean_object* v___f_4260_, lean_object* v___f_4261_, lean_object* v_____r_4262_){
_start:
{
if (lean_obj_tag(v_respStream_4258_) == 1)
{
lean_object* v_val_4264_; lean_object* v_close_4265_; lean_object* v_isClosed_4266_; lean_object* v___x_4267_; lean_object* v___f_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; 
v_val_4264_ = lean_ctor_get(v_respStream_4258_, 0);
lean_inc_n(v_val_4264_, 2);
lean_dec_ref_known(v_respStream_4258_, 1);
v_close_4265_ = lean_ctor_get(v_responseBodyInstance_4259_, 1);
lean_inc_ref(v_close_4265_);
v_isClosed_4266_ = lean_ctor_get(v_responseBodyInstance_4259_, 2);
lean_inc_ref(v_isClosed_4266_);
lean_dec_ref(v_responseBodyInstance_4259_);
v___x_4267_ = lean_apply_2(v_isClosed_4266_, v_val_4264_, lean_box(0));
v___f_4268_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4268_, 0, v_close_4265_);
lean_closure_set(v___f_4268_, 1, v_val_4264_);
lean_closure_set(v___f_4268_, 2, v___f_4260_);
lean_closure_set(v___f_4268_, 3, v___f_4261_);
v___x_4269_ = lean_unsigned_to_nat(0u);
v___x_4270_ = 0;
v___x_4271_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4269_, v___x_4270_, v___x_4267_, v___f_4268_);
return v___x_4271_;
}
else
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec_ref(v___f_4260_);
lean_dec_ref(v_responseBodyInstance_4259_);
lean_dec(v_respStream_4258_);
v___x_4272_ = lean_box(0);
v___x_4273_ = lean_apply_2(v___f_4261_, v___x_4272_, lean_box(0));
return v___x_4273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4274_, lean_object* v_responseBodyInstance_4275_, lean_object* v___f_4276_, lean_object* v___f_4277_, lean_object* v_____r_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4274_, v_responseBodyInstance_4275_, v___f_4276_, v___f_4277_, v_____r_4278_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4281_, lean_object* v___f_4282_, lean_object* v___f_4283_, lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4284_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v___f_4283_);
lean_dec_ref(v___f_4282_);
lean_dec_ref(v_requestStream_4281_);
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
lean_object* v_a_4295_; uint8_t v___x_4296_; 
v_a_4295_ = lean_ctor_get(v_x_4284_, 0);
lean_inc(v_a_4295_);
lean_dec_ref_known(v_x_4284_, 1);
v___x_4296_ = lean_unbox(v_a_4295_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; 
lean_dec_ref(v___f_4283_);
v___x_4297_ = l_Std_Http_Body_Stream_close(v_requestStream_4281_);
v___x_4298_ = lean_unsigned_to_nat(0u);
v___x_4299_ = lean_unbox(v_a_4295_);
lean_dec(v_a_4295_);
v___x_4300_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4298_, v___x_4299_, v___x_4297_, v___f_4282_);
return v___x_4300_;
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
lean_dec(v_a_4295_);
lean_dec_ref(v___f_4282_);
lean_dec_ref(v_requestStream_4281_);
v___x_4301_ = lean_box(0);
v___x_4302_ = lean_apply_2(v___f_4283_, v___x_4301_, lean_box(0));
return v___x_4302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4303_, lean_object* v___f_4304_, lean_object* v___f_4305_, lean_object* v_x_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4303_, v___f_4304_, v___f_4305_, v_x_4306_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___f_4309_, lean_object* v_responseBodyInstance_4310_, lean_object* v___f_4311_, lean_object* v___f_4312_, lean_object* v_x_4313_){
_start:
{
if (lean_obj_tag(v_x_4313_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v___f_4312_);
lean_dec_ref(v___f_4311_);
lean_dec_ref(v_responseBodyInstance_4310_);
lean_dec_ref(v___f_4309_);
v_a_4315_ = lean_ctor_get(v_x_4313_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_x_4313_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4317_ = v_x_4313_;
v_isShared_4318_ = v_isSharedCheck_4323_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v_x_4313_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4323_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v_requestStream_4325_; lean_object* v_respStream_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4409__overap_4332_; lean_object* v___x_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___f_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; 
v_a_4324_ = lean_ctor_get(v_x_4313_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v_x_4313_, 1);
v_requestStream_4325_ = lean_ctor_get(v_a_4324_, 1);
lean_inc_ref_n(v_requestStream_4325_, 2);
v_respStream_4326_ = lean_ctor_get(v_a_4324_, 6);
lean_inc(v_respStream_4326_);
lean_dec(v_a_4324_);
v___x_4327_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4328_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4329_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4330_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4331_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4331_, 0, lean_box(0));
lean_closure_set(v___x_4331_, 1, lean_box(0));
lean_closure_set(v___x_4331_, 2, v___x_4327_);
lean_closure_set(v___x_4331_, 3, lean_box(0));
lean_closure_set(v___x_4331_, 4, lean_box(0));
lean_closure_set(v___x_4331_, 5, v___x_4330_);
lean_closure_set(v___x_4331_, 6, v___f_4309_);
v___x_4409__overap_4332_ = l_Std_Mutex_atomically___redArg(v___x_4327_, v___f_4328_, v___f_4329_, v_requestStream_4325_, v___x_4331_);
v___x_4333_ = lean_apply_1(v___x_4409__overap_4332_, lean_box(0));
v___f_4334_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4334_, 0, v_respStream_4326_);
lean_closure_set(v___f_4334_, 1, v_responseBodyInstance_4310_);
lean_closure_set(v___f_4334_, 2, v___f_4311_);
lean_closure_set(v___f_4334_, 3, v___f_4312_);
lean_inc_ref(v___f_4334_);
v___f_4335_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4335_, 0, v___f_4334_);
v___f_4336_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4336_, 0, v_requestStream_4325_);
lean_closure_set(v___f_4336_, 1, v___f_4335_);
lean_closure_set(v___f_4336_, 2, v___f_4334_);
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = 0;
v___x_4339_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4337_, v___x_4338_, v___x_4333_, v___f_4336_);
return v___x_4339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___f_4340_, lean_object* v_responseBodyInstance_4341_, lean_object* v___f_4342_, lean_object* v___f_4343_, lean_object* v_x_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___f_4340_, v_responseBodyInstance_4341_, v___f_4342_, v___f_4343_, v_x_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4347_, lean_object* v_responseBodyInstance_4348_, lean_object* v_handler_4349_, lean_object* v_config_4350_, lean_object* v___x_4351_, uint8_t v___x_4352_, lean_object* v___f_4353_, lean_object* v_x_4354_){
_start:
{
if (lean_obj_tag(v_x_4354_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4364_; 
lean_dec_ref(v___f_4353_);
lean_dec_ref(v___x_4351_);
lean_dec_ref(v_config_4350_);
lean_dec(v_handler_4349_);
lean_dec_ref(v_responseBodyInstance_4348_);
lean_dec_ref(v_h_4347_);
v_a_4356_ = lean_ctor_get(v_x_4354_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_x_4354_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4358_ = v_x_4354_;
v_isShared_4359_ = v_isSharedCheck_4364_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v_x_4354_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4364_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; 
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v_a_4365_ = lean_ctor_get(v_x_4354_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v_x_4354_, 1);
v___x_4366_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4347_, v_responseBodyInstance_4348_, v_handler_4349_, v_config_4350_, v_a_4365_, v___x_4351_);
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4367_, v___x_4352_, v___x_4366_, v___f_4353_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4369_, lean_object* v_responseBodyInstance_4370_, lean_object* v_handler_4371_, lean_object* v_config_4372_, lean_object* v___x_4373_, lean_object* v___x_4374_, lean_object* v___f_4375_, lean_object* v_x_4376_, lean_object* v___y_4377_){
_start:
{
uint8_t v___x_5090__boxed_4378_; lean_object* v_res_4379_; 
v___x_5090__boxed_4378_ = lean_unbox(v___x_4374_);
v_res_4379_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4369_, v_responseBodyInstance_4370_, v_handler_4371_, v_config_4372_, v___x_4373_, v___x_5090__boxed_4378_, v___f_4375_, v_x_4376_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4380_, lean_object* v_h_4381_, lean_object* v_responseBodyInstance_4382_, lean_object* v_config_4383_, lean_object* v_handler_4384_, uint8_t v___x_4385_, lean_object* v___f_4386_, lean_object* v_x_4387_){
_start:
{
if (lean_obj_tag(v_x_4387_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4397_; 
lean_dec_ref(v___f_4386_);
lean_dec(v_handler_4384_);
lean_dec_ref(v_config_4383_);
lean_dec_ref(v_responseBodyInstance_4382_);
lean_dec_ref(v_h_4381_);
lean_dec_ref(v_inst_4380_);
v_a_4389_ = lean_ctor_get(v_x_4387_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_x_4387_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4391_ = v_x_4387_;
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v_x_4387_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; 
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
return v___x_4395_;
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v_a_4398_ = lean_ctor_get(v_x_4387_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v_x_4387_, 1);
v___x_4399_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4380_, v_h_4381_, v_responseBodyInstance_4382_, v_config_4383_, v_handler_4384_, v_a_4398_);
v___x_4400_ = lean_unsigned_to_nat(0u);
v___x_4401_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4400_, v___x_4385_, v___x_4399_, v___f_4386_);
return v___x_4401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4402_, lean_object* v_h_4403_, lean_object* v_responseBodyInstance_4404_, lean_object* v_config_4405_, lean_object* v_handler_4406_, lean_object* v___x_4407_, lean_object* v___f_4408_, lean_object* v_x_4409_, lean_object* v___y_4410_){
_start:
{
uint8_t v___x_5131__boxed_4411_; lean_object* v_res_4412_; 
v___x_5131__boxed_4411_ = lean_unbox(v___x_4407_);
v_res_4412_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4402_, v_h_4403_, v_responseBodyInstance_4404_, v_config_4405_, v_handler_4406_, v___x_5131__boxed_4411_, v___f_4408_, v_x_4409_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4413_, lean_object* v_socket_4414_, lean_object* v_connectionContext_4415_, lean_object* v_h_4416_, lean_object* v_responseBodyInstance_4417_, lean_object* v_handler_4418_, lean_object* v_config_4419_, lean_object* v___f_4420_, lean_object* v_inst_4421_, uint8_t v___x_4422_, lean_object* v_x_4423_){
_start:
{
if (lean_obj_tag(v_x_4423_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4433_; 
lean_dec_ref(v_inst_4421_);
lean_dec_ref(v___f_4420_);
lean_dec_ref(v_config_4419_);
lean_dec(v_handler_4418_);
lean_dec_ref(v_responseBodyInstance_4417_);
lean_dec_ref(v_h_4416_);
lean_dec_ref(v_connectionContext_4415_);
lean_dec(v_socket_4414_);
v_a_4425_ = lean_ctor_get(v_x_4423_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_x_4423_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4427_ = v_x_4423_;
v_isShared_4428_ = v_isSharedCheck_4433_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v_x_4423_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4433_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
return v___x_4431_;
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4476_; 
v_a_4434_ = lean_ctor_get(v_x_4423_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_x_4423_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4436_ = v_x_4423_;
v_isShared_4437_ = v_isSharedCheck_4476_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v_x_4423_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4476_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_machine_4438_; lean_object* v_requestStream_4439_; lean_object* v_keepAliveTimeout_4440_; lean_object* v_currentTimeout_4441_; lean_object* v_headerTimeout_4442_; lean_object* v_response_4443_; lean_object* v_respStream_4444_; uint8_t v_requiresData_4445_; lean_object* v_expectData_4446_; uint8_t v_handlerDispatched_4447_; lean_object* v_pendingHead_4448_; uint8_t v___y_4459_; uint8_t v___y_4466_; uint8_t v___y_4468_; uint8_t v___y_4469_; uint8_t v___y_4471_; 
v_machine_4438_ = lean_ctor_get(v_a_4434_, 0);
v_requestStream_4439_ = lean_ctor_get(v_a_4434_, 1);
v_keepAliveTimeout_4440_ = lean_ctor_get(v_a_4434_, 2);
v_currentTimeout_4441_ = lean_ctor_get(v_a_4434_, 3);
v_headerTimeout_4442_ = lean_ctor_get(v_a_4434_, 4);
v_response_4443_ = lean_ctor_get(v_a_4434_, 5);
v_respStream_4444_ = lean_ctor_get(v_a_4434_, 6);
v_requiresData_4445_ = lean_ctor_get_uint8(v_a_4434_, sizeof(void*)*9);
v_expectData_4446_ = lean_ctor_get(v_a_4434_, 7);
v_handlerDispatched_4447_ = lean_ctor_get_uint8(v_a_4434_, sizeof(void*)*9 + 1);
v_pendingHead_4448_ = lean_ctor_get(v_a_4434_, 8);
if (lean_obj_tag(v_respStream_4444_) == 0)
{
v___y_4471_ = v___x_4413_;
goto v___jp_4470_;
}
else
{
v___y_4471_ = v___x_4422_;
goto v___jp_4470_;
}
v___jp_4449_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___f_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4450_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4450_, 0, v_machine_4438_);
lean_ctor_set(v___x_4450_, 1, v_requestStream_4439_);
lean_ctor_set(v___x_4450_, 2, v_keepAliveTimeout_4440_);
lean_ctor_set(v___x_4450_, 3, v_currentTimeout_4441_);
lean_ctor_set(v___x_4450_, 4, v_headerTimeout_4442_);
lean_ctor_set(v___x_4450_, 5, v_response_4443_);
lean_ctor_set(v___x_4450_, 6, v_respStream_4444_);
lean_ctor_set(v___x_4450_, 7, v_expectData_4446_);
lean_ctor_set(v___x_4450_, 8, v_pendingHead_4448_);
lean_ctor_set_uint8(v___x_4450_, sizeof(void*)*9, v___x_4413_);
lean_ctor_set_uint8(v___x_4450_, sizeof(void*)*9 + 1, v_handlerDispatched_4447_);
lean_inc_ref(v___x_4450_);
v___x_4451_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4414_, v_connectionContext_4415_, v___x_4450_);
v___x_4452_ = lean_box(v___x_4413_);
lean_inc_ref(v_config_4419_);
lean_inc(v_handler_4418_);
lean_inc_ref(v_responseBodyInstance_4417_);
lean_inc_ref(v_h_4416_);
v___f_4453_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4453_, 0, v_h_4416_);
lean_closure_set(v___f_4453_, 1, v_responseBodyInstance_4417_);
lean_closure_set(v___f_4453_, 2, v_handler_4418_);
lean_closure_set(v___f_4453_, 3, v_config_4419_);
lean_closure_set(v___f_4453_, 4, v___x_4450_);
lean_closure_set(v___f_4453_, 5, v___x_4452_);
lean_closure_set(v___f_4453_, 6, v___f_4420_);
v___x_4454_ = lean_box(v___x_4413_);
v___f_4455_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4455_, 0, v_inst_4421_);
lean_closure_set(v___f_4455_, 1, v_h_4416_);
lean_closure_set(v___f_4455_, 2, v_responseBodyInstance_4417_);
lean_closure_set(v___f_4455_, 3, v_config_4419_);
lean_closure_set(v___f_4455_, 4, v_handler_4418_);
lean_closure_set(v___f_4455_, 5, v___x_4454_);
lean_closure_set(v___f_4455_, 6, v___f_4453_);
v___x_4456_ = lean_unsigned_to_nat(0u);
v___x_4457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4456_, v___x_4413_, v___x_4451_, v___f_4455_);
return v___x_4457_;
}
v___jp_4458_:
{
if (v_requiresData_4445_ == 0)
{
if (v___y_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
lean_dec_ref(v_inst_4421_);
lean_dec_ref(v___f_4420_);
lean_dec_ref(v_config_4419_);
lean_dec(v_handler_4418_);
lean_dec_ref(v_responseBodyInstance_4417_);
lean_dec_ref(v_h_4416_);
lean_dec_ref(v_connectionContext_4415_);
lean_dec(v_socket_4414_);
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v_a_4434_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v___x_4460_);
v___x_4462_ = v___x_4436_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
return v___x_4463_;
}
}
else
{
lean_inc(v_pendingHead_4448_);
lean_inc(v_expectData_4446_);
lean_inc(v_respStream_4444_);
lean_inc_ref(v_response_4443_);
lean_inc(v_headerTimeout_4442_);
lean_inc(v_currentTimeout_4441_);
lean_inc(v_keepAliveTimeout_4440_);
lean_inc_ref(v_requestStream_4439_);
lean_inc_ref(v_machine_4438_);
lean_del_object(v___x_4436_);
lean_dec(v_a_4434_);
goto v___jp_4449_;
}
}
else
{
lean_inc(v_pendingHead_4448_);
lean_inc(v_expectData_4446_);
lean_inc(v_respStream_4444_);
lean_inc_ref(v_response_4443_);
lean_inc(v_headerTimeout_4442_);
lean_inc(v_currentTimeout_4441_);
lean_inc(v_keepAliveTimeout_4440_);
lean_inc_ref(v_requestStream_4439_);
lean_inc_ref(v_machine_4438_);
lean_del_object(v___x_4436_);
lean_dec(v_a_4434_);
goto v___jp_4449_;
}
}
v___jp_4465_:
{
if (v_handlerDispatched_4447_ == 0)
{
v___y_4459_ = v___y_4466_;
goto v___jp_4458_;
}
else
{
v___y_4459_ = v_handlerDispatched_4447_;
goto v___jp_4458_;
}
}
v___jp_4467_:
{
if (v___y_4468_ == 0)
{
v___y_4466_ = v___y_4469_;
goto v___jp_4465_;
}
else
{
v___y_4466_ = v___y_4468_;
goto v___jp_4465_;
}
}
v___jp_4470_:
{
lean_object* v_writer_4472_; uint8_t v_sentMessage_4473_; 
v_writer_4472_ = lean_ctor_get(v_machine_4438_, 1);
v_sentMessage_4473_ = lean_ctor_get_uint8(v_writer_4472_, sizeof(void*)*6);
if (v_sentMessage_4473_ == 0)
{
lean_object* v_reader_4474_; lean_object* v_state_4475_; 
v_reader_4474_ = lean_ctor_get(v_machine_4438_, 0);
v_state_4475_ = lean_ctor_get(v_reader_4474_, 0);
if (lean_obj_tag(v_state_4475_) == 2)
{
v___y_4468_ = v___y_4471_;
v___y_4469_ = v___x_4422_;
goto v___jp_4467_;
}
else
{
v___y_4468_ = v___y_4471_;
v___y_4469_ = v_sentMessage_4473_;
goto v___jp_4467_;
}
}
else
{
v___y_4468_ = v___y_4471_;
v___y_4469_ = v___x_4413_;
goto v___jp_4467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4477_, lean_object* v_socket_4478_, lean_object* v_connectionContext_4479_, lean_object* v_h_4480_, lean_object* v_responseBodyInstance_4481_, lean_object* v_handler_4482_, lean_object* v_config_4483_, lean_object* v___f_4484_, lean_object* v_inst_4485_, lean_object* v___x_4486_, lean_object* v_x_4487_, lean_object* v___y_4488_){
_start:
{
uint8_t v___x_5171__boxed_4489_; uint8_t v___x_5174__boxed_4490_; lean_object* v_res_4491_; 
v___x_5171__boxed_4489_ = lean_unbox(v___x_4477_);
v___x_5174__boxed_4490_ = lean_unbox(v___x_4486_);
v_res_4491_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5171__boxed_4489_, v_socket_4478_, v_connectionContext_4479_, v_h_4480_, v_responseBodyInstance_4481_, v_handler_4482_, v_config_4483_, v___f_4484_, v_inst_4485_, v___x_5174__boxed_4490_, v_x_4487_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4492_, lean_object* v_handler_4493_, lean_object* v_extensions_4494_, lean_object* v_connectionContext_4495_, uint8_t v___x_4496_, lean_object* v___f_4497_, lean_object* v_x_4498_){
_start:
{
if (lean_obj_tag(v_x_4498_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v___f_4497_);
lean_dec_ref(v_connectionContext_4495_);
lean_dec(v_extensions_4494_);
lean_dec(v_handler_4493_);
lean_dec_ref(v_h_4492_);
v_a_4500_ = lean_ctor_get(v_x_4498_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_x_4498_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4502_ = v_x_4498_;
v_isShared_4503_ = v_isSharedCheck_4508_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v_x_4498_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4508_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
return v___x_4506_;
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v_a_4509_ = lean_ctor_get(v_x_4498_, 0);
lean_inc(v_a_4509_);
lean_dec_ref_known(v_x_4498_, 1);
v___x_4510_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4492_, v_handler_4493_, v_extensions_4494_, v_connectionContext_4495_, v_a_4509_);
v___x_4511_ = lean_unsigned_to_nat(0u);
v___x_4512_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4511_, v___x_4496_, v___x_4510_, v___f_4497_);
return v___x_4512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4513_, lean_object* v_handler_4514_, lean_object* v_extensions_4515_, lean_object* v_connectionContext_4516_, lean_object* v___x_4517_, lean_object* v___f_4518_, lean_object* v_x_4519_, lean_object* v___y_4520_){
_start:
{
uint8_t v___x_5265__boxed_4521_; lean_object* v_res_4522_; 
v___x_5265__boxed_4521_ = lean_unbox(v___x_4517_);
v_res_4522_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4513_, v_handler_4514_, v_extensions_4515_, v_connectionContext_4516_, v___x_5265__boxed_4521_, v___f_4518_, v_x_4519_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4523_, lean_object* v_responseBodyInstance_4524_, lean_object* v_handler_4525_, lean_object* v_config_4526_, lean_object* v_connectionContext_4527_, lean_object* v_events_4528_, lean_object* v___x_4529_, uint8_t v___x_4530_, lean_object* v___f_4531_, lean_object* v_____r_4532_){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4523_, v_responseBodyInstance_4524_, v_handler_4525_, v_config_4526_, v_connectionContext_4527_, v_events_4528_, v___x_4529_);
v___x_4535_ = lean_unsigned_to_nat(0u);
v___x_4536_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4535_, v___x_4530_, v___x_4534_, v___f_4531_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4537_, lean_object* v_responseBodyInstance_4538_, lean_object* v_handler_4539_, lean_object* v_config_4540_, lean_object* v_connectionContext_4541_, lean_object* v_events_4542_, lean_object* v___x_4543_, lean_object* v___x_4544_, lean_object* v___f_4545_, lean_object* v_____r_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v___x_5304__boxed_4548_; lean_object* v_res_4549_; 
v___x_5304__boxed_4548_ = lean_unbox(v___x_4544_);
v_res_4549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4537_, v_responseBodyInstance_4538_, v_handler_4539_, v_config_4540_, v_connectionContext_4541_, v_events_4542_, v___x_4543_, v___x_5304__boxed_4548_, v___f_4545_, v_____r_4546_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4550_, lean_object* v___f_4551_, lean_object* v_x_4552_){
_start:
{
if (lean_obj_tag(v_x_4552_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4562_; 
lean_dec_ref(v___f_4551_);
lean_dec_ref(v___x_4550_);
v_a_4554_ = lean_ctor_get(v_x_4552_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x_4552_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4556_ = v_x_4552_;
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v_x_4552_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4560_; 
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4574_; 
v_a_4563_ = lean_ctor_get(v_x_4552_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_x_4552_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4565_ = v_x_4552_;
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v_x_4552_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
if (lean_obj_tag(v_a_4563_) == 0)
{
lean_object* v___x_4567_; lean_object* v___x_4569_; 
lean_dec_ref(v___f_4551_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4550_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 0, v___x_4567_);
v___x_4569_ = v___x_4565_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4567_);
v___x_4569_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4570_; 
v___x_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
return v___x_4570_;
}
}
else
{
lean_object* v_val_4572_; lean_object* v___x_4573_; 
lean_del_object(v___x_4565_);
lean_dec_ref(v___x_4550_);
v_val_4572_ = lean_ctor_get(v_a_4563_, 0);
lean_inc(v_val_4572_);
lean_dec_ref_known(v_a_4563_, 1);
v___x_4573_ = lean_apply_2(v___f_4551_, v_val_4572_, lean_box(0));
return v___x_4573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4575_, lean_object* v___f_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4575_, v___f_4576_, v_x_4577_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(uint8_t v___x_4580_, lean_object* v_socket_4581_, lean_object* v_connectionContext_4582_, lean_object* v_h_4583_, lean_object* v_responseBodyInstance_4584_, lean_object* v_handler_4585_, lean_object* v_config_4586_, lean_object* v___f_4587_, lean_object* v_inst_4588_, lean_object* v_extensions_4589_, lean_object* v___f_4590_, lean_object* v___f_4591_, lean_object* v_x_4592_, lean_object* v_____s_4593_){
_start:
{
lean_object* v_machine_4595_; lean_object* v_reader_4596_; lean_object* v_requestStream_4597_; lean_object* v_keepAliveTimeout_4598_; lean_object* v_currentTimeout_4599_; lean_object* v_headerTimeout_4600_; lean_object* v_response_4601_; lean_object* v_respStream_4602_; uint8_t v_requiresData_4603_; lean_object* v_expectData_4604_; uint8_t v_handlerDispatched_4605_; lean_object* v_pendingHead_4606_; lean_object* v_writer_4607_; lean_object* v_state_4608_; uint8_t v___x_4609_; 
v_machine_4595_ = lean_ctor_get(v_____s_4593_, 0);
v_reader_4596_ = lean_ctor_get(v_machine_4595_, 0);
v_requestStream_4597_ = lean_ctor_get(v_____s_4593_, 1);
v_keepAliveTimeout_4598_ = lean_ctor_get(v_____s_4593_, 2);
v_currentTimeout_4599_ = lean_ctor_get(v_____s_4593_, 3);
v_headerTimeout_4600_ = lean_ctor_get(v_____s_4593_, 4);
v_response_4601_ = lean_ctor_get(v_____s_4593_, 5);
v_respStream_4602_ = lean_ctor_get(v_____s_4593_, 6);
v_requiresData_4603_ = lean_ctor_get_uint8(v_____s_4593_, sizeof(void*)*9);
v_expectData_4604_ = lean_ctor_get(v_____s_4593_, 7);
v_handlerDispatched_4605_ = lean_ctor_get_uint8(v_____s_4593_, sizeof(void*)*9 + 1);
v_pendingHead_4606_ = lean_ctor_get(v_____s_4593_, 8);
v_writer_4607_ = lean_ctor_get(v_machine_4595_, 1);
v_state_4608_ = lean_ctor_get(v_reader_4596_, 0);
v___x_4609_ = 0;
if (lean_obj_tag(v_state_4608_) == 6)
{
lean_object* v_state_4637_; 
v_state_4637_ = lean_ctor_get(v_writer_4607_, 2);
if (lean_obj_tag(v_state_4637_) == 7)
{
lean_object* v_outputData_4638_; lean_object* v_size_4639_; lean_object* v___x_4640_; uint8_t v___x_4641_; 
v_outputData_4638_ = lean_ctor_get(v_writer_4607_, 1);
v_size_4639_ = lean_ctor_get(v_outputData_4638_, 1);
v___x_4640_ = lean_unsigned_to_nat(0u);
v___x_4641_ = lean_nat_dec_eq(v_size_4639_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_inc(v_pendingHead_4606_);
lean_inc(v_expectData_4604_);
lean_inc(v_respStream_4602_);
lean_inc_ref(v_response_4601_);
lean_inc(v_headerTimeout_4600_);
lean_inc(v_currentTimeout_4599_);
lean_inc(v_keepAliveTimeout_4598_);
lean_inc_ref(v_requestStream_4597_);
lean_inc_ref(v_machine_4595_);
lean_dec_ref(v_____s_4593_);
goto v___jp_4610_;
}
else
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
lean_dec_ref(v___f_4591_);
lean_dec_ref(v___f_4590_);
lean_dec(v_extensions_4589_);
lean_dec_ref(v_inst_4588_);
lean_dec_ref(v___f_4587_);
lean_dec_ref(v_config_4586_);
lean_dec(v_handler_4585_);
lean_dec_ref(v_responseBodyInstance_4584_);
lean_dec_ref(v_h_4583_);
lean_dec_ref(v_connectionContext_4582_);
lean_dec(v_socket_4581_);
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v_____s_4593_);
v___x_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
return v___x_4644_;
}
}
else
{
lean_inc(v_pendingHead_4606_);
lean_inc(v_expectData_4604_);
lean_inc(v_respStream_4602_);
lean_inc_ref(v_response_4601_);
lean_inc(v_headerTimeout_4600_);
lean_inc(v_currentTimeout_4599_);
lean_inc(v_keepAliveTimeout_4598_);
lean_inc_ref(v_requestStream_4597_);
lean_inc_ref(v_machine_4595_);
lean_dec_ref(v_____s_4593_);
goto v___jp_4610_;
}
}
else
{
lean_inc(v_pendingHead_4606_);
lean_inc(v_expectData_4604_);
lean_inc(v_respStream_4602_);
lean_inc_ref(v_response_4601_);
lean_inc(v_headerTimeout_4600_);
lean_inc(v_currentTimeout_4599_);
lean_inc(v_keepAliveTimeout_4598_);
lean_inc_ref(v_requestStream_4597_);
lean_inc_ref(v_machine_4595_);
lean_dec_ref(v_____s_4593_);
goto v___jp_4610_;
}
v___jp_4610_:
{
lean_object* v___x_4611_; lean_object* v_snd_4612_; lean_object* v_output_4613_; lean_object* v_fst_4614_; lean_object* v_events_4615_; lean_object* v_data_4616_; lean_object* v_size_4617_; uint8_t v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___f_4621_; lean_object* v___x_4622_; lean_object* v___f_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___f_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4611_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4609_, v_machine_4595_);
v_snd_4612_ = lean_ctor_get(v___x_4611_, 1);
lean_inc(v_snd_4612_);
v_output_4613_ = lean_ctor_get(v_snd_4612_, 1);
lean_inc_ref(v_output_4613_);
v_fst_4614_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_fst_4614_);
lean_dec_ref(v___x_4611_);
v_events_4615_ = lean_ctor_get(v_snd_4612_, 0);
lean_inc_ref_n(v_events_4615_, 2);
lean_dec(v_snd_4612_);
v_data_4616_ = lean_ctor_get(v_output_4613_, 0);
lean_inc_ref(v_data_4616_);
v_size_4617_ = lean_ctor_get(v_output_4613_, 1);
lean_inc(v_size_4617_);
lean_dec_ref(v_output_4613_);
v___x_4618_ = 1;
v___x_4619_ = lean_box(v___x_4580_);
v___x_4620_ = lean_box(v___x_4618_);
lean_inc_ref(v_inst_4588_);
lean_inc_ref_n(v_config_4586_, 2);
lean_inc_n(v_handler_4585_, 3);
lean_inc_ref_n(v_responseBodyInstance_4584_, 2);
lean_inc_ref_n(v_h_4583_, 3);
lean_inc_ref_n(v_connectionContext_4582_, 3);
lean_inc(v_socket_4581_);
v___f_4621_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 12, 10);
lean_closure_set(v___f_4621_, 0, v___x_4619_);
lean_closure_set(v___f_4621_, 1, v_socket_4581_);
lean_closure_set(v___f_4621_, 2, v_connectionContext_4582_);
lean_closure_set(v___f_4621_, 3, v_h_4583_);
lean_closure_set(v___f_4621_, 4, v_responseBodyInstance_4584_);
lean_closure_set(v___f_4621_, 5, v_handler_4585_);
lean_closure_set(v___f_4621_, 6, v_config_4586_);
lean_closure_set(v___f_4621_, 7, v___f_4587_);
lean_closure_set(v___f_4621_, 8, v_inst_4588_);
lean_closure_set(v___f_4621_, 9, v___x_4620_);
v___x_4622_ = lean_box(v___x_4580_);
v___f_4623_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4623_, 0, v_h_4583_);
lean_closure_set(v___f_4623_, 1, v_handler_4585_);
lean_closure_set(v___f_4623_, 2, v_extensions_4589_);
lean_closure_set(v___f_4623_, 3, v_connectionContext_4582_);
lean_closure_set(v___f_4623_, 4, v___x_4622_);
lean_closure_set(v___f_4623_, 5, v___f_4621_);
v___x_4624_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4624_, 0, v_fst_4614_);
lean_ctor_set(v___x_4624_, 1, v_requestStream_4597_);
lean_ctor_set(v___x_4624_, 2, v_keepAliveTimeout_4598_);
lean_ctor_set(v___x_4624_, 3, v_currentTimeout_4599_);
lean_ctor_set(v___x_4624_, 4, v_headerTimeout_4600_);
lean_ctor_set(v___x_4624_, 5, v_response_4601_);
lean_ctor_set(v___x_4624_, 6, v_respStream_4602_);
lean_ctor_set(v___x_4624_, 7, v_expectData_4604_);
lean_ctor_set(v___x_4624_, 8, v_pendingHead_4606_);
lean_ctor_set_uint8(v___x_4624_, sizeof(void*)*9, v_requiresData_4603_);
lean_ctor_set_uint8(v___x_4624_, sizeof(void*)*9 + 1, v_handlerDispatched_4605_);
v___x_4625_ = lean_box(v___x_4580_);
lean_inc_ref(v___f_4623_);
lean_inc_ref(v___x_4624_);
v___f_4626_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4626_, 0, v_h_4583_);
lean_closure_set(v___f_4626_, 1, v_responseBodyInstance_4584_);
lean_closure_set(v___f_4626_, 2, v_handler_4585_);
lean_closure_set(v___f_4626_, 3, v_config_4586_);
lean_closure_set(v___f_4626_, 4, v_connectionContext_4582_);
lean_closure_set(v___f_4626_, 5, v_events_4615_);
lean_closure_set(v___f_4626_, 6, v___x_4624_);
lean_closure_set(v___f_4626_, 7, v___x_4625_);
lean_closure_set(v___f_4626_, 8, v___f_4623_);
v___x_4627_ = lean_unsigned_to_nat(0u);
v___x_4628_ = lean_nat_dec_lt(v___x_4627_, v_size_4617_);
lean_dec(v_size_4617_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
lean_dec_ref(v___f_4626_);
lean_dec_ref(v_data_4616_);
lean_dec_ref(v___f_4591_);
lean_dec_ref(v___f_4590_);
lean_dec_ref(v_inst_4588_);
lean_dec(v_socket_4581_);
v___x_4629_ = lean_box(0);
v___x_4630_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4583_, v_responseBodyInstance_4584_, v_handler_4585_, v_config_4586_, v_connectionContext_4582_, v_events_4615_, v___x_4624_, v___x_4580_, v___f_4623_, v___x_4629_);
return v___x_4630_;
}
else
{
lean_object* v_sendAll_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___f_4635_; lean_object* v___x_4636_; 
lean_dec_ref(v___f_4623_);
lean_dec_ref(v_events_4615_);
lean_dec_ref(v_config_4586_);
lean_dec(v_handler_4585_);
lean_dec_ref(v_responseBodyInstance_4584_);
lean_dec_ref(v_h_4583_);
lean_dec_ref(v_connectionContext_4582_);
v_sendAll_4631_ = lean_ctor_get(v_inst_4588_, 1);
lean_inc_ref(v_sendAll_4631_);
lean_dec_ref(v_inst_4588_);
v___x_4632_ = lean_apply_3(v_sendAll_4631_, v_socket_4581_, v_data_4616_, lean_box(0));
v___x_4633_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4627_, v___x_4580_, v___x_4632_, v___f_4590_);
v___x_4634_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4627_, v___x_4580_, v___x_4633_, v___f_4591_);
v___f_4635_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4635_, 0, v___x_4624_);
lean_closure_set(v___f_4635_, 1, v___f_4626_);
v___x_4636_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4627_, v___x_4580_, v___x_4634_, v___f_4635_);
return v___x_4636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v___x_4645_, lean_object* v_socket_4646_, lean_object* v_connectionContext_4647_, lean_object* v_h_4648_, lean_object* v_responseBodyInstance_4649_, lean_object* v_handler_4650_, lean_object* v_config_4651_, lean_object* v___f_4652_, lean_object* v_inst_4653_, lean_object* v_extensions_4654_, lean_object* v___f_4655_, lean_object* v___f_4656_, lean_object* v_x_4657_, lean_object* v_____s_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v___x_5378__boxed_4660_; lean_object* v_res_4661_; 
v___x_5378__boxed_4660_ = lean_unbox(v___x_4645_);
v_res_4661_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v___x_5378__boxed_4660_, v_socket_4646_, v_connectionContext_4647_, v_h_4648_, v_responseBodyInstance_4649_, v_handler_4650_, v_config_4651_, v___f_4652_, v_inst_4653_, v_extensions_4654_, v___f_4655_, v___f_4656_, v_x_4657_, v_____s_4658_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4662_, lean_object* v_x_4663_){
_start:
{
if (lean_obj_tag(v_x_4663_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4673_; 
v_a_4665_ = lean_ctor_get(v_x_4663_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_x_4663_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4667_ = v_x_4663_;
v_isShared_4668_ = v_isSharedCheck_4673_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v_x_4663_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4673_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4671_; 
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
}
}
else
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
lean_dec_ref_known(v_x_4663_, 1);
v___x_4674_ = l_IO_Promise_result_x21___redArg(v_a_4662_);
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
return v___x_4675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4676_, lean_object* v_x_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4676_, v_x_4677_);
lean_dec(v_a_4676_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4680_, lean_object* v___x_4681_, lean_object* v___x_4682_, uint8_t v___x_4683_, lean_object* v_x_4684_){
_start:
{
if (lean_obj_tag(v_x_4684_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v___x_4682_);
lean_dec(v___x_4681_);
lean_dec_ref(v___f_4680_);
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
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4706_; 
v_a_4695_ = lean_ctor_get(v_x_4684_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v_x_4684_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4697_ = v_x_4684_;
v_isShared_4698_ = v_isSharedCheck_4706_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v_x_4684_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4706_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; lean_object* v___f_4700_; lean_object* v___x_4702_; 
lean_inc(v_a_4695_);
lean_inc(v___x_4681_);
v___x_4699_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4680_, v___x_4681_, v_a_4695_, v___x_4682_);
v___f_4700_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4700_, 0, v_a_4695_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 0, v___x_4699_);
v___x_4702_ = v___x_4697_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4699_);
v___x_4702_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
v___x_4704_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4681_, v___x_4683_, v___x_4703_, v___f_4700_);
return v___x_4704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4707_, lean_object* v___x_4708_, lean_object* v___x_4709_, lean_object* v___x_4710_, lean_object* v_x_4711_, lean_object* v___y_4712_){
_start:
{
uint8_t v___x_5493__boxed_4713_; lean_object* v_res_4714_; 
v___x_5493__boxed_4713_ = lean_unbox(v___x_4710_);
v_res_4714_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4707_, v___x_4708_, v___x_4709_, v___x_5493__boxed_4713_, v_x_4711_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4715_, lean_object* v_machine_4716_, lean_object* v_a_4717_, lean_object* v___x_4718_, lean_object* v_socket_4719_, lean_object* v_connectionContext_4720_, lean_object* v_h_4721_, lean_object* v_responseBodyInstance_4722_, lean_object* v_handler_4723_, lean_object* v___f_4724_, lean_object* v_inst_4725_, lean_object* v_extensions_4726_, lean_object* v___f_4727_, lean_object* v___f_4728_, lean_object* v___f_4729_, lean_object* v_x_4730_){
_start:
{
if (lean_obj_tag(v_x_4730_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4740_; 
lean_dec_ref(v___f_4729_);
lean_dec_ref(v___f_4728_);
lean_dec_ref(v___f_4727_);
lean_dec(v_extensions_4726_);
lean_dec_ref(v_inst_4725_);
lean_dec_ref(v___f_4724_);
lean_dec(v_handler_4723_);
lean_dec_ref(v_responseBodyInstance_4722_);
lean_dec_ref(v_h_4721_);
lean_dec_ref(v_connectionContext_4720_);
lean_dec(v_socket_4719_);
lean_dec(v___x_4718_);
lean_dec_ref(v_a_4717_);
lean_dec_ref(v_machine_4716_);
lean_dec_ref(v_config_4715_);
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
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4762_; 
v_a_4741_ = lean_ctor_get(v_x_4730_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_x_4730_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4743_ = v_x_4730_;
v_isShared_4744_ = v_isSharedCheck_4762_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v_x_4730_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4762_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_keepAliveTimeout_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___f_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___f_4755_; lean_object* v___x_4757_; 
v_keepAliveTimeout_4745_ = lean_ctor_get(v_config_4715_, 5);
lean_inc_n(v_keepAliveTimeout_4745_, 2);
v___x_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4746_, 0, v_keepAliveTimeout_4745_);
v___x_4747_ = lean_box(0);
v___x_4748_ = 0;
v___x_4749_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4749_, 0, v_machine_4716_);
lean_ctor_set(v___x_4749_, 1, v_a_4717_);
lean_ctor_set(v___x_4749_, 2, v___x_4746_);
lean_ctor_set(v___x_4749_, 3, v_keepAliveTimeout_4745_);
lean_ctor_set(v___x_4749_, 4, v___x_4747_);
lean_ctor_set(v___x_4749_, 5, v_a_4741_);
lean_ctor_set(v___x_4749_, 6, v___x_4747_);
lean_ctor_set(v___x_4749_, 7, v___x_4718_);
lean_ctor_set(v___x_4749_, 8, v___x_4747_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*9, v___x_4748_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*9 + 1, v___x_4748_);
v___x_4750_ = lean_io_promise_new();
v___x_4751_ = lean_box(v___x_4748_);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 15, 12);
lean_closure_set(v___f_4752_, 0, v___x_4751_);
lean_closure_set(v___f_4752_, 1, v_socket_4719_);
lean_closure_set(v___f_4752_, 2, v_connectionContext_4720_);
lean_closure_set(v___f_4752_, 3, v_h_4721_);
lean_closure_set(v___f_4752_, 4, v_responseBodyInstance_4722_);
lean_closure_set(v___f_4752_, 5, v_handler_4723_);
lean_closure_set(v___f_4752_, 6, v_config_4715_);
lean_closure_set(v___f_4752_, 7, v___f_4724_);
lean_closure_set(v___f_4752_, 8, v_inst_4725_);
lean_closure_set(v___f_4752_, 9, v_extensions_4726_);
lean_closure_set(v___f_4752_, 10, v___f_4727_);
lean_closure_set(v___f_4752_, 11, v___f_4728_);
v___x_4753_ = lean_unsigned_to_nat(0u);
v___x_4754_ = lean_box(v___x_4748_);
v___f_4755_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4755_, 0, v___f_4752_);
lean_closure_set(v___f_4755_, 1, v___x_4753_);
lean_closure_set(v___f_4755_, 2, v___x_4749_);
lean_closure_set(v___f_4755_, 3, v___x_4754_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4750_);
v___x_4757_ = v___x_4743_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4750_);
v___x_4757_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
v___x_4759_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4753_, v___x_4748_, v___x_4758_, v___f_4755_);
v___x_4760_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4753_, v___x_4748_, v___x_4759_, v___f_4729_);
return v___x_4760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4763_ = _args[0];
lean_object* v_machine_4764_ = _args[1];
lean_object* v_a_4765_ = _args[2];
lean_object* v___x_4766_ = _args[3];
lean_object* v_socket_4767_ = _args[4];
lean_object* v_connectionContext_4768_ = _args[5];
lean_object* v_h_4769_ = _args[6];
lean_object* v_responseBodyInstance_4770_ = _args[7];
lean_object* v_handler_4771_ = _args[8];
lean_object* v___f_4772_ = _args[9];
lean_object* v_inst_4773_ = _args[10];
lean_object* v_extensions_4774_ = _args[11];
lean_object* v___f_4775_ = _args[12];
lean_object* v___f_4776_ = _args[13];
lean_object* v___f_4777_ = _args[14];
lean_object* v_x_4778_ = _args[15];
lean_object* v___y_4779_ = _args[16];
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4763_, v_machine_4764_, v_a_4765_, v___x_4766_, v_socket_4767_, v_connectionContext_4768_, v_h_4769_, v_responseBodyInstance_4770_, v_handler_4771_, v___f_4772_, v_inst_4773_, v_extensions_4774_, v___f_4775_, v___f_4776_, v___f_4777_, v_x_4778_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4781_, lean_object* v_machine_4782_, lean_object* v_socket_4783_, lean_object* v_connectionContext_4784_, lean_object* v_h_4785_, lean_object* v_responseBodyInstance_4786_, lean_object* v_handler_4787_, lean_object* v___f_4788_, lean_object* v_inst_4789_, lean_object* v_extensions_4790_, lean_object* v___f_4791_, lean_object* v___f_4792_, lean_object* v___f_4793_, lean_object* v_x_4794_){
_start:
{
if (lean_obj_tag(v_x_4794_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4804_; 
lean_dec_ref(v___f_4793_);
lean_dec_ref(v___f_4792_);
lean_dec_ref(v___f_4791_);
lean_dec(v_extensions_4790_);
lean_dec_ref(v_inst_4789_);
lean_dec_ref(v___f_4788_);
lean_dec(v_handler_4787_);
lean_dec_ref(v_responseBodyInstance_4786_);
lean_dec_ref(v_h_4785_);
lean_dec_ref(v_connectionContext_4784_);
lean_dec(v_socket_4783_);
lean_dec_ref(v_machine_4782_);
lean_dec_ref(v_config_4781_);
v_a_4796_ = lean_ctor_get(v_x_4794_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v_x_4794_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4798_ = v_x_4794_;
v_isShared_4799_ = v_isSharedCheck_4804_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v_x_4794_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4804_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4819_; 
v_a_4805_ = lean_ctor_get(v_x_4794_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_x_4794_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4807_ = v_x_4794_;
v_isShared_4808_ = v_isSharedCheck_4819_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v_x_4794_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4819_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___f_4811_; lean_object* v___x_4813_; 
v___x_4809_ = lean_box(0);
v___x_4810_ = l_Std_CloseableChannel_new___redArg(v___x_4809_);
v___f_4811_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4811_, 0, v_config_4781_);
lean_closure_set(v___f_4811_, 1, v_machine_4782_);
lean_closure_set(v___f_4811_, 2, v_a_4805_);
lean_closure_set(v___f_4811_, 3, v___x_4809_);
lean_closure_set(v___f_4811_, 4, v_socket_4783_);
lean_closure_set(v___f_4811_, 5, v_connectionContext_4784_);
lean_closure_set(v___f_4811_, 6, v_h_4785_);
lean_closure_set(v___f_4811_, 7, v_responseBodyInstance_4786_);
lean_closure_set(v___f_4811_, 8, v_handler_4787_);
lean_closure_set(v___f_4811_, 9, v___f_4788_);
lean_closure_set(v___f_4811_, 10, v_inst_4789_);
lean_closure_set(v___f_4811_, 11, v_extensions_4790_);
lean_closure_set(v___f_4811_, 12, v___f_4791_);
lean_closure_set(v___f_4811_, 13, v___f_4792_);
lean_closure_set(v___f_4811_, 14, v___f_4793_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 0, v___x_4810_);
v___x_4813_ = v___x_4807_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4810_);
v___x_4813_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; 
v___x_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4813_);
v___x_4815_ = lean_unsigned_to_nat(0u);
v___x_4816_ = 0;
v___x_4817_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4815_, v___x_4816_, v___x_4814_, v___f_4811_);
return v___x_4817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4820_, lean_object* v_machine_4821_, lean_object* v_socket_4822_, lean_object* v_connectionContext_4823_, lean_object* v_h_4824_, lean_object* v_responseBodyInstance_4825_, lean_object* v_handler_4826_, lean_object* v___f_4827_, lean_object* v_inst_4828_, lean_object* v_extensions_4829_, lean_object* v___f_4830_, lean_object* v___f_4831_, lean_object* v___f_4832_, lean_object* v_x_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4820_, v_machine_4821_, v_socket_4822_, v_connectionContext_4823_, v_h_4824_, v_responseBodyInstance_4825_, v_handler_4826_, v___f_4827_, v_inst_4828_, v_extensions_4829_, v___f_4830_, v___f_4831_, v___f_4832_, v_x_4833_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4839_, lean_object* v_h_4840_, lean_object* v_connection_4841_, lean_object* v_config_4842_, lean_object* v_connectionContext_4843_, lean_object* v_handler_4844_){
_start:
{
lean_object* v_responseBodyInstance_4846_; lean_object* v_onFailure_4847_; lean_object* v___x_4848_; lean_object* v_socket_4849_; lean_object* v_machine_4850_; lean_object* v_extensions_4851_; lean_object* v___f_4852_; lean_object* v___f_4853_; lean_object* v___f_4854_; lean_object* v___f_4855_; lean_object* v___f_4856_; lean_object* v___f_4857_; lean_object* v___f_4858_; lean_object* v___f_4859_; lean_object* v___f_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; 
v_responseBodyInstance_4846_ = lean_ctor_get(v_h_4840_, 0);
lean_inc_ref_n(v_responseBodyInstance_4846_, 2);
v_onFailure_4847_ = lean_ctor_get(v_h_4840_, 2);
v___x_4848_ = l_Std_Http_Body_mkStream();
v_socket_4849_ = lean_ctor_get(v_connection_4841_, 0);
lean_inc_n(v_socket_4849_, 2);
v_machine_4850_ = lean_ctor_get(v_connection_4841_, 1);
lean_inc_ref(v_machine_4850_);
v_extensions_4851_ = lean_ctor_get(v_connection_4841_, 2);
lean_inc(v_extensions_4851_);
lean_dec_ref(v_connection_4841_);
v___f_4852_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4853_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
lean_inc(v_handler_4844_);
lean_inc_ref(v_onFailure_4847_);
v___f_4854_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4854_, 0, v_onFailure_4847_);
lean_closure_set(v___f_4854_, 1, v_handler_4844_);
lean_closure_set(v___f_4854_, 2, v___f_4853_);
v___f_4855_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_4856_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4839_);
v___f_4857_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4857_, 0, v_inst_4839_);
lean_closure_set(v___f_4857_, 1, v_socket_4849_);
lean_inc_ref(v___f_4857_);
v___f_4858_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4858_, 0, v___f_4857_);
v___f_4859_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4859_, 0, v___f_4852_);
lean_closure_set(v___f_4859_, 1, v_responseBodyInstance_4846_);
lean_closure_set(v___f_4859_, 2, v___f_4858_);
lean_closure_set(v___f_4859_, 3, v___f_4857_);
v___f_4860_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4860_, 0, v_config_4842_);
lean_closure_set(v___f_4860_, 1, v_machine_4850_);
lean_closure_set(v___f_4860_, 2, v_socket_4849_);
lean_closure_set(v___f_4860_, 3, v_connectionContext_4843_);
lean_closure_set(v___f_4860_, 4, v_h_4840_);
lean_closure_set(v___f_4860_, 5, v_responseBodyInstance_4846_);
lean_closure_set(v___f_4860_, 6, v_handler_4844_);
lean_closure_set(v___f_4860_, 7, v___f_4856_);
lean_closure_set(v___f_4860_, 8, v_inst_4839_);
lean_closure_set(v___f_4860_, 9, v_extensions_4851_);
lean_closure_set(v___f_4860_, 10, v___f_4855_);
lean_closure_set(v___f_4860_, 11, v___f_4854_);
lean_closure_set(v___f_4860_, 12, v___f_4859_);
v___x_4861_ = lean_unsigned_to_nat(0u);
v___x_4862_ = 0;
v___x_4863_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4861_, v___x_4862_, v___x_4848_, v___f_4860_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4864_, lean_object* v_h_4865_, lean_object* v_connection_4866_, lean_object* v_config_4867_, lean_object* v_connectionContext_4868_, lean_object* v_handler_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4864_, v_h_4865_, v_connection_4866_, v_config_4867_, v_connectionContext_4868_, v_handler_4869_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4872_, lean_object* v_00_u03c3_4873_, lean_object* v_inst_4874_, lean_object* v_h_4875_, lean_object* v_connection_4876_, lean_object* v_config_4877_, lean_object* v_connectionContext_4878_, lean_object* v_handler_4879_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4874_, v_h_4875_, v_connection_4876_, v_config_4877_, v_connectionContext_4878_, v_handler_4879_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4882_, lean_object* v_00_u03c3_4883_, lean_object* v_inst_4884_, lean_object* v_h_4885_, lean_object* v_connection_4886_, lean_object* v_config_4887_, lean_object* v_connectionContext_4888_, lean_object* v_handler_4889_, lean_object* v_a_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4882_, v_00_u03c3_4883_, v_inst_4884_, v_h_4885_, v_connection_4886_, v_config_4887_, v_connectionContext_4888_, v_handler_4889_);
return v_res_4891_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = 0;
v___x_4893_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4892_);
return v___x_4893_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = lean_unsigned_to_nat(4096u);
v___x_4895_ = lean_mk_empty_byte_array(v___x_4894_);
return v___x_4895_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4897_ = l_ByteArray_mkIterator(v___x_4896_);
return v___x_4897_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4898_ = 0;
v___x_4899_ = lean_unsigned_to_nat(0u);
v___x_4900_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4901_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4902_ = lean_box(0);
v___x_4903_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
lean_ctor_set(v___x_4903_, 1, v___x_4901_);
lean_ctor_set(v___x_4903_, 2, v___x_4900_);
lean_ctor_set(v___x_4903_, 3, v___x_4899_);
lean_ctor_set(v___x_4903_, 4, v___x_4899_);
lean_ctor_set(v___x_4903_, 5, v___x_4899_);
lean_ctor_set_uint8(v___x_4903_, sizeof(void*)*6, v___x_4898_);
return v___x_4903_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = 1;
v___x_4912_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4911_);
return v___x_4912_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4913_; uint8_t v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = 0;
v___x_4915_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4916_ = lean_box(0);
v___x_4917_ = lean_box(0);
v___x_4918_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4919_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4920_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
lean_ctor_set(v___x_4920_, 1, v___x_4918_);
lean_ctor_set(v___x_4920_, 2, v___x_4917_);
lean_ctor_set(v___x_4920_, 3, v___x_4916_);
lean_ctor_set(v___x_4920_, 4, v___x_4915_);
lean_ctor_set(v___x_4920_, 5, v___x_4913_);
lean_ctor_set_uint8(v___x_4920_, sizeof(void*)*6, v___x_4914_);
lean_ctor_set_uint8(v___x_4920_, sizeof(void*)*6 + 1, v___x_4914_);
lean_ctor_set_uint8(v___x_4920_, sizeof(void*)*6 + 2, v___x_4914_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4921_, lean_object* v_client_4922_, lean_object* v_extensions_4923_, lean_object* v_inst_4924_, lean_object* v_inst_4925_, lean_object* v_handler_4926_, lean_object* v_x_4927_){
_start:
{
if (lean_obj_tag(v_x_4927_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4937_; 
lean_dec(v_handler_4926_);
lean_dec_ref(v_inst_4925_);
lean_dec_ref(v_inst_4924_);
lean_dec(v_extensions_4923_);
lean_dec(v_client_4922_);
lean_dec_ref(v_config_4921_);
v_a_4929_ = lean_ctor_get(v_x_4927_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v_x_4927_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4931_ = v_x_4927_;
v_isShared_4932_ = v_isSharedCheck_4937_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v_x_4927_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4937_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
lean_object* v___x_4935_; 
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
return v___x_4935_;
}
}
}
else
{
lean_object* v_a_4938_; uint8_t v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; uint8_t v_enableKeepAlive_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v_a_4938_ = lean_ctor_get(v_x_4927_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v_x_4927_, 1);
v___x_4939_ = 0;
v___x_4940_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4941_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4942_ = lean_box(0);
v___x_4943_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4944_ = l_Std_Http_Config_toH1Config(v_config_4921_);
v_enableKeepAlive_4945_ = lean_ctor_get_uint8(v___x_4944_, sizeof(void*)*18);
v___x_4946_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4946_, 0, v___x_4940_);
lean_ctor_set(v___x_4946_, 1, v___x_4943_);
lean_ctor_set(v___x_4946_, 2, v___x_4944_);
lean_ctor_set(v___x_4946_, 3, v___x_4941_);
lean_ctor_set(v___x_4946_, 4, v___x_4942_);
lean_ctor_set(v___x_4946_, 5, v___x_4942_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*6, v_enableKeepAlive_4945_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*6 + 1, v___x_4939_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*6 + 2, v___x_4939_);
v___x_4947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4947_, 0, v_client_4922_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
lean_ctor_set(v___x_4947_, 2, v_extensions_4923_);
v___x_4948_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4924_, v_inst_4925_, v___x_4947_, v_config_4921_, v_a_4938_, v_handler_4926_);
return v___x_4948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4949_, lean_object* v_client_4950_, lean_object* v_extensions_4951_, lean_object* v_inst_4952_, lean_object* v_inst_4953_, lean_object* v_handler_4954_, lean_object* v_x_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4949_, v_client_4950_, v_extensions_4951_, v_inst_4952_, v_inst_4953_, v_handler_4954_, v_x_4955_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4958_, lean_object* v_inst_4959_, lean_object* v_client_4960_, lean_object* v_handler_4961_, lean_object* v_config_4962_, lean_object* v_extensions_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v___f_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; uint8_t v___x_4970_; lean_object* v___x_4971_; 
v___f_4966_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4966_, 0, v_config_4962_);
lean_closure_set(v___f_4966_, 1, v_client_4960_);
lean_closure_set(v___f_4966_, 2, v_extensions_4963_);
lean_closure_set(v___f_4966_, 3, v_inst_4958_);
lean_closure_set(v___f_4966_, 4, v_inst_4959_);
lean_closure_set(v___f_4966_, 5, v_handler_4961_);
lean_inc_ref(v_a_4964_);
v___x_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4967_, 0, v_a_4964_);
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
v___x_4969_ = lean_unsigned_to_nat(0u);
v___x_4970_ = 0;
v___x_4971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4969_, v___x_4970_, v___x_4968_, v___f_4966_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4972_, lean_object* v_inst_4973_, lean_object* v_client_4974_, lean_object* v_handler_4975_, lean_object* v_config_4976_, lean_object* v_extensions_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4972_, v_inst_4973_, v_client_4974_, v_handler_4975_, v_config_4976_, v_extensions_4977_, v_a_4978_);
lean_dec_ref(v_a_4978_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4981_, lean_object* v_00_u03c3_4982_, lean_object* v_inst_4983_, lean_object* v_inst_4984_, lean_object* v_client_4985_, lean_object* v_handler_4986_, lean_object* v_config_4987_, lean_object* v_extensions_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4983_, v_inst_4984_, v_client_4985_, v_handler_4986_, v_config_4987_, v_extensions_4988_, v_a_4989_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4992_, lean_object* v_00_u03c3_4993_, lean_object* v_inst_4994_, lean_object* v_inst_4995_, lean_object* v_client_4996_, lean_object* v_handler_4997_, lean_object* v_config_4998_, lean_object* v_extensions_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Std_Http_Server_serveConnection(v_t_4992_, v_00_u03c3_4993_, v_inst_4994_, v_inst_4995_, v_client_4996_, v_handler_4997_, v_config_4998_, v_extensions_4999_, v_a_5000_);
lean_dec_ref(v_a_5000_);
return v_res_5002_;
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
