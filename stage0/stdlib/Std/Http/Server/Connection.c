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
lean_object* l_Std_Http_Body_Stream_close(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_send(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Http_Body_mkStream();
lean_object* l_Std_Http_Protocol_H1_Machine_canContinue(uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Async_Selector_sleep(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
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
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1_value;
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_a_195_; lean_object* v_onFailure_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_a_195_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v_x_193_, 1);
v_onFailure_196_ = lean_ctor_get(v_inst_190_, 2);
lean_inc_ref(v_onFailure_196_);
lean_dec_ref(v_inst_190_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = 0;
v___x_199_ = lean_apply_3(v_onFailure_196_, v_handler_191_, v_a_195_, lean_box(0));
v___x_200_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_197_, v___x_198_, v___x_199_, v___f_192_);
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
uint8_t v_x_3730__boxed_223_; lean_object* v_res_224_; 
v_x_3730__boxed_223_ = lean_unbox(v_x_221_);
v_res_224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3730__boxed_223_);
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
lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = 0;
v___x_269_ = l_Std_Async_Selectable_one___redArg(v_selectables_266_);
v___x_270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_267_, v___x_268_, v___x_269_, v___f_253_);
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
lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = 0;
v___x_307_ = l_Std_CancellationToken_getCancellationReason(v_token_301_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
v___x_310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_305_, v___x_306_, v___x_309_, v___f_302_);
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
lean_object* v_a_360_; lean_object* v_second_361_; lean_object* v_nano_362_; lean_object* v_second_363_; lean_object* v_nano_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_nanos_369_; lean_object* v___x_370_; lean_object* v_nanos_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_second_374_; lean_object* v_nano_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_millis_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
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
v_nanos_369_ = lean_int_add(v___x_368_, v_nano_364_);
lean_dec(v___x_368_);
v___x_370_ = lean_int_mul(v___x_365_, v___x_367_);
lean_dec(v___x_365_);
v_nanos_371_ = lean_int_add(v___x_370_, v___x_366_);
lean_dec(v___x_366_);
lean_dec(v___x_370_);
v___x_372_ = lean_int_add(v_nanos_369_, v_nanos_371_);
lean_dec(v_nanos_371_);
lean_dec(v_nanos_369_);
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
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = 0;
v___x_383_ = l_Std_Async_Selector_sleep(v_millis_380_);
lean_dec(v_millis_380_);
v___x_384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_381_, v___x_382_, v___x_383_, v___f_348_);
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
lean_object* v___y_408_; uint8_t v___y_409_; lean_object* v___y_410_; lean_object* v_val_411_; lean_object* v_socket_414_; lean_object* v_expect_415_; lean_object* v_response_416_; lean_object* v_responseBody_417_; lean_object* v_requestBody_418_; lean_object* v_timeout_419_; lean_object* v_keepAliveTimeout_420_; lean_object* v_headerTimeout_421_; lean_object* v_connectionContext_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___y_435_; lean_object* v___y_485_; 
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
lean_object* v_defaultPayloadBytes_488_; 
v_defaultPayloadBytes_488_ = lean_ctor_get(v_config_403_, 8);
lean_inc(v_defaultPayloadBytes_488_);
v___y_485_ = v_defaultPayloadBytes_488_;
goto v___jp_484_;
}
else
{
lean_object* v_val_489_; 
v_val_489_ = lean_ctor_get(v_expect_415_, 0);
lean_inc(v_val_489_);
lean_dec_ref_known(v_expect_415_, 1);
v___y_485_ = v_val_489_;
goto v___jp_484_;
}
v___jp_407_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_val_411_);
v___x_413_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_408_, v___y_409_, v___x_412_, v___y_410_);
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
lean_object* v_val_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; 
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
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = 0;
v___x_455_ = lean_get_current_time();
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 1);
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
v___y_408_ = v___x_453_;
v___y_409_ = v___x_454_;
v___y_410_ = v___f_452_;
v_val_411_ = v___x_461_;
goto v___jp_407_;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_a_464_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_455_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_455_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 0);
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v___y_408_ = v___x_453_;
v___y_409_ = v___x_454_;
v___y_410_ = v___f_452_;
v_val_411_ = v___x_469_;
goto v___jp_407_;
}
}
}
}
else
{
lean_object* v___f_472_; lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_headerTimeout_421_);
v___f_472_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_472_, 0, v___f_430_);
lean_closure_set(v___f_472_, 1, v_selectables_449_);
lean_closure_set(v___f_472_, 2, v___f_433_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = 0;
v___x_475_ = l_Std_Async_Selector_sleep(v_timeout_419_);
lean_dec(v_timeout_419_);
v___x_476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_473_, v___x_474_, v___x_475_, v___f_472_);
return v___x_476_;
}
}
else
{
lean_object* v___f_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref_known(v_keepAliveTimeout_420_, 1);
lean_dec(v_headerTimeout_421_);
v___f_477_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_477_, 0, v___f_431_);
lean_closure_set(v___f_477_, 1, v_selectables_449_);
lean_closure_set(v___f_477_, 2, v___f_433_);
v___x_478_ = 0;
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l_Std_Async_Selector_sleep(v_timeout_419_);
lean_dec(v_timeout_419_);
v___x_481_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_479_, v___x_478_, v___x_480_, v___f_477_);
return v___x_481_;
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v___y_435_);
lean_dec_ref(v___f_433_);
lean_dec(v_headerTimeout_421_);
lean_dec(v_keepAliveTimeout_420_);
lean_dec(v_timeout_419_);
lean_dec(v_socket_414_);
lean_dec_ref(v_inst_400_);
v___x_482_ = lean_box(0);
v___x_483_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_425_, v_response_416_, v___x_432_, v___f_426_, v_requestBody_418_, v___f_427_, v_responseBody_417_, v_inst_402_, v___f_428_, v___x_482_, v_selectables_442_);
return v___x_483_;
}
}
v___jp_484_:
{
lean_object* v_maximumRecvSize_486_; uint8_t v___x_487_; 
v_maximumRecvSize_486_ = lean_ctor_get(v_config_403_, 7);
lean_inc(v_maximumRecvSize_486_);
lean_dec_ref(v_config_403_);
v___x_487_ = lean_nat_dec_le(v___y_485_, v_maximumRecvSize_486_);
if (v___x_487_ == 0)
{
lean_dec(v___y_485_);
v___y_435_ = v_maximumRecvSize_486_;
goto v___jp_434_;
}
else
{
lean_dec(v_maximumRecvSize_486_);
v___y_435_ = v___y_485_;
goto v___jp_434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_config_493_, lean_object* v_handler_494_, lean_object* v_sources_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_490_, v_inst_491_, v_inst_492_, v_config_493_, v_handler_494_, v_sources_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_498_, lean_object* v_00_u03c3_499_, lean_object* v_00_u03b2_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_config_504_, lean_object* v_handler_505_, lean_object* v_sources_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_501_, v_inst_502_, v_inst_503_, v_config_504_, v_handler_505_, v_sources_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_509_, lean_object* v_00_u03c3_510_, lean_object* v_00_u03b2_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_config_515_, lean_object* v_handler_516_, lean_object* v_sources_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_509_, v_00_u03c3_510_, v_00_u03b2_511_, v_inst_512_, v_inst_513_, v_inst_514_, v_config_515_, v_handler_516_, v_sources_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___y_524_; uint8_t v___y_525_; 
if (lean_obj_tag(v_x_521_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_machine_520_);
v_a_530_ = lean_ctor_get(v_x_521_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_538_ == 0)
{
v___x_532_ = v_x_521_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v_x_521_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___y_541_; uint8_t v___x_547_; 
v_a_539_ = lean_ctor_get(v_x_521_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v_x_521_, 1);
v___x_547_ = lean_unbox(v_a_539_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(40);
v___y_541_ = v___x_548_;
goto v___jp_540_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
v___y_541_ = v___x_549_;
goto v___jp_540_;
}
v___jp_540_:
{
uint8_t v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = 0;
lean_inc(v___y_541_);
v___x_543_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_542_, v_machine_520_, v___y_541_);
v___x_544_ = lean_unbox(v_a_539_);
lean_dec(v_a_539_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = 1;
v___y_524_ = v___x_543_;
v___y_525_ = v___x_545_;
goto v___jp_523_;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = 0;
v___y_524_ = v___x_543_;
v___y_525_ = v___x_546_;
goto v___jp_523_;
}
}
}
v___jp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_box(v___y_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___y_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_550_, lean_object* v_x_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_550_, v_x_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_554_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(v___y_554_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___y_1377__boxed_561_; lean_object* v_res_562_; 
v___y_1377__boxed_561_ = lean_unbox(v___y_559_);
v_res_562_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1377__boxed_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v_x_563_, 1);
v___x_565_ = lean_task_pure(v_a_564_);
return v___x_565_;
}
else
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v_x_563_, 0);
lean_inc_ref(v_a_566_);
lean_dec_ref_known(v_x_563_, 1);
return v_a_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref_known(v_x_568_, 1);
v___x_570_ = 0;
v___x_571_ = lean_box(0);
v___x_572_ = lean_box(v___x_570_);
v___x_573_ = l_Std_Channel_send___redArg(v_a_567_, v___x_572_);
lean_dec_ref(v___x_573_);
return v___x_571_;
}
else
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_574_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v_x_568_, 1);
v___x_575_ = lean_box(0);
v___x_576_ = l_Std_Channel_send___redArg(v_a_567_, v_a_574_);
lean_dec_ref(v___x_576_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_577_, lean_object* v_x_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_577_, v_x_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_box(v___x_581_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_587_, lean_object* v_x_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___x_1421__boxed_590_; lean_object* v_res_591_; 
v___x_1421__boxed_590_ = lean_unbox(v___x_587_);
v_res_591_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1421__boxed_590_, v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_592_, uint8_t v___x_593_, lean_object* v_a_594_, lean_object* v___f_595_, lean_object* v___f_596_, lean_object* v___x_597_, uint8_t v___x_598_, lean_object* v___f_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v___f_599_);
lean_dec(v___x_597_);
lean_dec_ref(v___f_596_);
lean_dec_ref(v___f_595_);
lean_dec_ref(v_a_594_);
lean_dec_ref(v_connectionContext_592_);
v_a_602_ = lean_ctor_get(v_x_600_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_x_600_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v_x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v_token_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_a_611_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v_x_600_, 1);
v_token_612_ = lean_ctor_get(v_connectionContext_592_, 1);
lean_inc_ref(v_token_612_);
lean_dec_ref(v_connectionContext_592_);
v___x_613_ = lean_box(v___x_593_);
v___x_614_ = l_Std_Channel_recvSelector___redArg(v___x_613_, v_a_594_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___f_595_);
v___x_616_ = l_Std_CancellationToken_selector(v_token_612_);
lean_inc_ref(v___f_596_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___f_596_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_a_611_);
lean_ctor_set(v___x_618_, 1, v___f_596_);
v___x_619_ = lean_unsigned_to_nat(3u);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_619_);
v___x_621_ = lean_array_push(v___x_620_, v___x_615_);
v___x_622_ = lean_array_push(v___x_621_, v___x_617_);
v___x_623_ = lean_array_push(v___x_622_, v___x_618_);
v___x_624_ = l_Std_Async_Selectable_one___redArg(v___x_623_);
v___x_625_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_597_, v___x_598_, v___x_624_, v___f_599_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_626_, lean_object* v___x_627_, lean_object* v_a_628_, lean_object* v___f_629_, lean_object* v___f_630_, lean_object* v___x_631_, lean_object* v___x_632_, lean_object* v___f_633_, lean_object* v_x_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_1436__boxed_636_; uint8_t v___x_1441__boxed_637_; lean_object* v_res_638_; 
v___x_1436__boxed_636_ = lean_unbox(v___x_627_);
v___x_1441__boxed_637_ = lean_unbox(v___x_632_);
v_res_638_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_626_, v___x_1436__boxed_636_, v_a_628_, v___f_629_, v___f_630_, v___x_631_, v___x_1441__boxed_637_, v___f_633_, v_x_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_639_, lean_object* v___x_640_, uint8_t v___x_641_, lean_object* v___f_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v___f_642_);
lean_dec(v___x_640_);
v_a_645_ = lean_ctor_get(v_x_643_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_653_ == 0)
{
v___x_647_ = v_x_643_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v_x_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_652_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
else
{
lean_object* v_lingeringTimeout_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec_ref_known(v_x_643_, 1);
v_lingeringTimeout_654_ = lean_ctor_get(v_config_639_, 4);
v___x_655_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_654_);
v___x_656_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_640_, v___x_641_, v___x_655_, v___f_642_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_657_, lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v___f_660_, lean_object* v_x_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_1510__boxed_663_; lean_object* v_res_664_; 
v___x_1510__boxed_663_ = lean_unbox(v___x_659_);
v_res_664_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_657_, v___x_658_, v___x_1510__boxed_663_, v___f_660_, v_x_661_);
lean_dec_ref(v_config_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_668_, uint8_t v___x_669_, lean_object* v_a_670_, lean_object* v___f_671_, lean_object* v___x_672_, lean_object* v___f_673_, lean_object* v_config_674_, lean_object* v___f_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v___f_675_);
lean_dec_ref(v_config_674_);
lean_dec_ref(v___f_673_);
lean_dec(v___x_672_);
lean_dec_ref(v___f_671_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v_connectionContext_668_);
v_a_678_ = lean_ctor_get(v_x_676_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_686_ == 0)
{
v___x_680_ = v_x_676_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v_x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_704_; 
v_a_687_ = lean_ctor_get(v_x_676_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_704_ == 0)
{
v___x_689_ = v_x_676_;
v_isShared_690_ = v_isSharedCheck_704_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v_x_676_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_704_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___x_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_691_ = 0;
v___f_692_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_693_ = lean_box(v___x_669_);
v___x_694_ = lean_box(v___x_691_);
lean_inc_n(v___x_672_, 3);
v___f_695_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_695_, 0, v_connectionContext_668_);
lean_closure_set(v___f_695_, 1, v___x_693_);
lean_closure_set(v___f_695_, 2, v_a_670_);
lean_closure_set(v___f_695_, 3, v___f_671_);
lean_closure_set(v___f_695_, 4, v___f_692_);
lean_closure_set(v___f_695_, 5, v___x_672_);
lean_closure_set(v___f_695_, 6, v___x_694_);
lean_closure_set(v___f_695_, 7, v___f_673_);
v___x_696_ = lean_box(v___x_691_);
v___f_697_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_697_, 0, v_config_674_);
lean_closure_set(v___f_697_, 1, v___x_672_);
lean_closure_set(v___f_697_, 2, v___x_696_);
lean_closure_set(v___f_697_, 3, v___f_695_);
v___x_698_ = l_BaseIO_chainTask___redArg(v_a_687_, v___f_675_, v___x_672_, v___x_691_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_698_);
v___x_700_ = v___x_689_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_703_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
v___x_702_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_672_, v___x_691_, v___x_701_, v___f_697_);
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_705_, lean_object* v___x_706_, lean_object* v_a_707_, lean_object* v___f_708_, lean_object* v___x_709_, lean_object* v___f_710_, lean_object* v_config_711_, lean_object* v___f_712_, lean_object* v_x_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_1550__boxed_715_; lean_object* v_res_716_; 
v___x_1550__boxed_715_ = lean_unbox(v___x_706_);
v_res_716_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_705_, v___x_1550__boxed_715_, v_a_707_, v___f_708_, v___x_709_, v___f_710_, v_config_711_, v___f_712_, v_x_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_717_, lean_object* v_handler_718_, lean_object* v_head_719_, lean_object* v_connectionContext_720_, uint8_t v___x_721_, lean_object* v___f_722_, lean_object* v___f_723_, lean_object* v_config_724_, lean_object* v___f_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v___f_725_);
lean_dec_ref(v_config_724_);
lean_dec_ref(v___f_723_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v_connectionContext_720_);
lean_dec_ref(v_head_719_);
lean_dec(v_handler_718_);
lean_dec_ref(v_inst_717_);
v_a_728_ = lean_ctor_get(v_x_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_x_726_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v_x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_757_; 
v_a_737_ = lean_ctor_get(v_x_726_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_757_ == 0)
{
v___x_739_ = v_x_726_;
v_isShared_740_ = v_isSharedCheck_757_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v_x_726_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_757_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_onContinue_741_; lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___f_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v_onContinue_741_ = lean_ctor_get(v_inst_717_, 3);
lean_inc_ref(v_onContinue_741_);
lean_dec_ref(v_inst_717_);
lean_inc(v_a_737_);
v___f_742_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_742_, 0, v_a_737_);
v___x_743_ = lean_apply_2(v_onContinue_741_, v_handler_718_, v_head_719_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_box(v___x_721_);
v___f_746_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_746_, 0, v_connectionContext_720_);
lean_closure_set(v___f_746_, 1, v___x_745_);
lean_closure_set(v___f_746_, 2, v_a_737_);
lean_closure_set(v___f_746_, 3, v___f_722_);
lean_closure_set(v___f_746_, 4, v___x_744_);
lean_closure_set(v___f_746_, 5, v___f_723_);
lean_closure_set(v___f_746_, 6, v_config_724_);
lean_closure_set(v___f_746_, 7, v___f_742_);
v___x_747_ = 0;
v___x_748_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_748_, 0, lean_box(0));
lean_closure_set(v___x_748_, 1, v___x_743_);
v___x_749_ = lean_io_as_task(v___x_748_, v___x_744_);
v___x_750_ = 1;
v___x_751_ = lean_task_bind(v___x_749_, v___f_725_, v___x_744_, v___x_750_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_751_);
v___x_753_ = v___x_739_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_756_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_744_, v___x_747_, v___x_754_, v___f_746_);
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_758_, lean_object* v_handler_759_, lean_object* v_head_760_, lean_object* v_connectionContext_761_, lean_object* v___x_762_, lean_object* v___f_763_, lean_object* v___f_764_, lean_object* v_config_765_, lean_object* v___f_766_, lean_object* v_x_767_, lean_object* v___y_768_){
_start:
{
uint8_t v___x_1633__boxed_769_; lean_object* v_res_770_; 
v___x_1633__boxed_769_ = lean_unbox(v___x_762_);
v_res_770_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_758_, v_handler_759_, v_head_760_, v_connectionContext_761_, v___x_1633__boxed_769_, v___f_763_, v___f_764_, v_config_765_, v___f_766_, v_x_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_773_, lean_object* v_handler_774_, lean_object* v_machine_775_, lean_object* v_head_776_, lean_object* v_config_777_, lean_object* v_connectionContext_778_){
_start:
{
lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___f_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___f_780_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_780_, 0, v_machine_775_);
v___f_781_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_782_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_783_ = 0;
v___x_784_ = lean_box(v___x_783_);
v___f_785_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_785_, 0, v_inst_773_);
lean_closure_set(v___f_785_, 1, v_handler_774_);
lean_closure_set(v___f_785_, 2, v_head_776_);
lean_closure_set(v___f_785_, 3, v_connectionContext_778_);
lean_closure_set(v___f_785_, 4, v___x_784_);
lean_closure_set(v___f_785_, 5, v___f_781_);
lean_closure_set(v___f_785_, 6, v___f_780_);
lean_closure_set(v___f_785_, 7, v_config_777_);
lean_closure_set(v___f_785_, 8, v___f_782_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l_Std_CloseableChannel_new___redArg(v___x_786_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_787_, v___x_783_, v___x_790_, v___f_785_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_792_, lean_object* v_handler_793_, lean_object* v_machine_794_, lean_object* v_head_795_, lean_object* v_config_796_, lean_object* v_connectionContext_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_792_, v_handler_793_, v_machine_794_, v_head_795_, v_config_796_, v_connectionContext_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_800_, lean_object* v_inst_801_, lean_object* v_handler_802_, lean_object* v_machine_803_, lean_object* v_head_804_, lean_object* v_config_805_, lean_object* v_connectionContext_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_801_, v_handler_802_, v_machine_803_, v_head_804_, v_config_805_, v_connectionContext_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_809_, lean_object* v_inst_810_, lean_object* v_handler_811_, lean_object* v_machine_812_, lean_object* v_head_813_, lean_object* v_config_814_, lean_object* v_connectionContext_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_809_, v_inst_810_, v_handler_811_, v_machine_812_, v_head_813_, v_config_814_, v_connectionContext_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_a_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Rat_ofInt(v_a_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
return v_x_820_;
}
else
{
lean_object* v_key_822_; lean_object* v_value_823_; lean_object* v_tail_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_847_; 
v_key_822_ = lean_ctor_get(v_x_821_, 0);
v_value_823_ = lean_ctor_get(v_x_821_, 1);
v_tail_824_ = lean_ctor_get(v_x_821_, 2);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_847_ == 0)
{
v___x_826_ = v_x_821_;
v_isShared_827_ = v_isSharedCheck_847_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_tail_824_);
lean_inc(v_value_823_);
lean_inc(v_key_822_);
lean_dec(v_x_821_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_847_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v_fold_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_828_ = lean_array_get_size(v_x_820_);
v___x_829_ = lean_string_hash(v_key_822_);
v___x_830_ = 32ULL;
v___x_831_ = lean_uint64_shift_right(v___x_829_, v___x_830_);
v_fold_832_ = lean_uint64_xor(v___x_829_, v___x_831_);
v___x_833_ = 16ULL;
v___x_834_ = lean_uint64_shift_right(v_fold_832_, v___x_833_);
v___x_835_ = lean_uint64_xor(v_fold_832_, v___x_834_);
v___x_836_ = lean_uint64_to_usize(v___x_835_);
v___x_837_ = lean_usize_of_nat(v___x_828_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_sub(v___x_837_, v___x_838_);
v___x_840_ = lean_usize_land(v___x_836_, v___x_839_);
v___x_841_ = lean_array_uget_borrowed(v_x_820_, v___x_840_);
lean_inc(v___x_841_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 2, v___x_841_);
v___x_843_ = v___x_826_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_key_822_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_value_823_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___x_841_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_array_uset(v_x_820_, v___x_840_, v___x_843_);
v_x_820_ = v___x_844_;
v_x_821_ = v_tail_824_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object* v_i_848_, lean_object* v_source_849_, lean_object* v_target_850_){
_start:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_array_get_size(v_source_849_);
v___x_852_ = lean_nat_dec_lt(v_i_848_, v___x_851_);
if (v___x_852_ == 0)
{
lean_dec_ref(v_source_849_);
lean_dec(v_i_848_);
return v_target_850_;
}
else
{
lean_object* v_es_853_; lean_object* v___x_854_; lean_object* v_source_855_; lean_object* v_target_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_es_853_ = lean_array_fget(v_source_849_, v_i_848_);
v___x_854_ = lean_box(0);
v_source_855_ = lean_array_fset(v_source_849_, v_i_848_, v___x_854_);
v_target_856_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_target_850_, v_es_853_);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_add(v_i_848_, v___x_857_);
lean_dec(v_i_848_);
v_i_848_ = v___x_858_;
v_source_849_ = v_source_855_;
v_target_850_ = v_target_856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object* v_data_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_nbuckets_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_861_ = lean_array_get_size(v_data_860_);
v___x_862_ = lean_unsigned_to_nat(2u);
v_nbuckets_863_ = lean_nat_mul(v___x_861_, v___x_862_);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_box(0);
v___x_866_ = lean_mk_array(v_nbuckets_863_, v___x_865_);
v___x_867_ = lean_array_propagate_mark(v_data_860_, v___x_866_);
v___x_868_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v___x_864_, v_data_860_, v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_869_, lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_mk_empty_array_with_capacity(v___x_871_);
v___x_873_ = lean_array_push(v___x_872_, v_i_869_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_val_875_ = lean_ctor_get(v_x_870_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_870_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v_x_870_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v_x_870_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_array_push(v_val_875_, v_i_869_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_884_, lean_object* v_a_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_val_889_; lean_object* v___x_890_; 
v___x_887_ = lean_box(0);
v___x_888_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_884_, v___x_887_);
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec(v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_890_, 0, v_a_885_);
lean_ctor_set(v___x_890_, 1, v_val_889_);
lean_ctor_set(v___x_890_, 2, v_x_886_);
return v___x_890_;
}
else
{
lean_object* v_key_891_; lean_object* v_value_892_; lean_object* v_tail_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_908_; 
v_key_891_ = lean_ctor_get(v_x_886_, 0);
v_value_892_ = lean_ctor_get(v_x_886_, 1);
v_tail_893_ = lean_ctor_get(v_x_886_, 2);
v_isSharedCheck_908_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_908_ == 0)
{
v___x_895_ = v_x_886_;
v_isShared_896_ = v_isSharedCheck_908_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_tail_893_);
lean_inc(v_value_892_);
lean_inc(v_key_891_);
lean_dec(v_x_886_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_908_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
uint8_t v___x_897_; 
v___x_897_ = lean_string_dec_eq(v_key_891_, v_a_885_);
if (v___x_897_ == 0)
{
lean_object* v_tail_898_; lean_object* v___x_900_; 
v_tail_898_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_884_, v_a_885_, v_tail_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 2, v_tail_898_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_key_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_value_892_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_tail_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_val_904_; lean_object* v___x_906_; 
lean_dec(v_key_891_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v_value_892_);
v___x_903_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_884_, v___x_902_);
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec(v___x_903_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v_val_904_);
lean_ctor_set(v___x_895_, 0, v_a_885_);
v___x_906_ = v___x_895_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_val_904_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_tail_893_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
uint8_t v___x_911_; 
v___x_911_ = 0;
return v___x_911_;
}
else
{
lean_object* v_key_912_; lean_object* v_tail_913_; uint8_t v___x_914_; 
v_key_912_ = lean_ctor_get(v_x_910_, 0);
v_tail_913_ = lean_ctor_get(v_x_910_, 2);
v___x_914_ = lean_string_dec_eq(v_key_912_, v_a_909_);
if (v___x_914_ == 0)
{
v_x_910_ = v_tail_913_;
goto _start;
}
else
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_916_, lean_object* v_x_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_916_, v_x_917_);
lean_dec(v_x_917_);
lean_dec_ref(v_a_916_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_920_, lean_object* v_m_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_size_923_; lean_object* v_buckets_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_974_; 
v_size_923_ = lean_ctor_get(v_m_921_, 0);
v_buckets_924_ = lean_ctor_get(v_m_921_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_m_921_);
if (v_isSharedCheck_974_ == 0)
{
v___x_926_ = v_m_921_;
v_isShared_927_ = v_isSharedCheck_974_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_buckets_924_);
lean_inc(v_size_923_);
lean_dec(v_m_921_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_974_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v_fold_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v_bkt_941_; uint8_t v___x_942_; 
v___x_928_ = lean_array_get_size(v_buckets_924_);
v___x_929_ = lean_string_hash(v_a_922_);
v___x_930_ = 32ULL;
v___x_931_ = lean_uint64_shift_right(v___x_929_, v___x_930_);
v_fold_932_ = lean_uint64_xor(v___x_929_, v___x_931_);
v___x_933_ = 16ULL;
v___x_934_ = lean_uint64_shift_right(v_fold_932_, v___x_933_);
v___x_935_ = lean_uint64_xor(v_fold_932_, v___x_934_);
v___x_936_ = lean_uint64_to_usize(v___x_935_);
v___x_937_ = lean_usize_of_nat(v___x_928_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_sub(v___x_937_, v___x_938_);
v___x_940_ = lean_usize_land(v___x_936_, v___x_939_);
v_bkt_941_ = lean_array_uget_borrowed(v_buckets_924_, v___x_940_);
v___x_942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_922_, v_bkt_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_size_x27_946_; lean_object* v___x_947_; lean_object* v_buckets_x27_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_943_);
v___x_945_ = lean_array_push(v___x_944_, v_i_920_);
v_size_x27_946_ = lean_nat_add(v_size_923_, v___x_943_);
lean_dec(v_size_923_);
lean_inc(v_bkt_941_);
v___x_947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_947_, 0, v_a_922_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set(v___x_947_, 2, v_bkt_941_);
v_buckets_x27_948_ = lean_array_uset(v_buckets_924_, v___x_940_, v___x_947_);
v___x_949_ = lean_unsigned_to_nat(4u);
v___x_950_ = lean_nat_mul(v_size_x27_946_, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(3u);
v___x_952_ = lean_nat_div(v___x_950_, v___x_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_array_get_size(v_buckets_x27_948_);
v___x_954_ = lean_nat_dec_le(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
if (v___x_954_ == 0)
{
lean_object* v_val_955_; lean_object* v___x_957_; 
v_val_955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_948_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v_val_955_);
lean_ctor_set(v___x_926_, 0, v_size_x27_946_);
v___x_957_ = v___x_926_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_size_x27_946_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_val_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v___x_960_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v_buckets_x27_948_);
lean_ctor_set(v___x_926_, 0, v_size_x27_946_);
v___x_960_ = v___x_926_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_size_x27_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_buckets_x27_948_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_object* v___x_962_; lean_object* v_buckets_x27_963_; lean_object* v_bkt_x27_964_; lean_object* v___y_966_; uint8_t v___x_971_; 
lean_inc(v_bkt_941_);
v___x_962_ = lean_box(0);
v_buckets_x27_963_ = lean_array_uset(v_buckets_924_, v___x_940_, v___x_962_);
lean_inc_ref(v_a_922_);
v_bkt_x27_964_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_920_, v_a_922_, v_bkt_941_);
v___x_971_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_922_, v_bkt_x27_964_);
lean_dec_ref(v_a_922_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_sub(v_size_923_, v___x_972_);
lean_dec(v_size_923_);
v___y_966_ = v___x_973_;
goto v___jp_965_;
}
else
{
v___y_966_ = v_size_923_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_array_uset(v_buckets_x27_963_, v___x_940_, v_bkt_x27_964_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_967_);
lean_ctor_set(v___x_926_, 0, v___y_966_);
v___x_969_ = v___x_926_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___y_966_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_975_, lean_object* v___x_976_, lean_object* v_indexes_977_, lean_object* v_status_978_, uint8_t v_version_979_, lean_object* v_x_980_){
_start:
{
if (lean_obj_tag(v_x_980_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_status_978_);
lean_dec_ref(v_indexes_977_);
lean_dec_ref(v___x_976_);
lean_dec_ref(v_entries_975_);
v_a_982_ = lean_ctor_get(v_x_980_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_990_ == 0)
{
v___x_984_ = v_x_980_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v_x_980_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1007_; 
v_a_991_ = lean_ctor_get(v_x_980_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_993_ = v_x_980_;
v_isShared_994_ = v_isSharedCheck_1007_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v_x_980_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1007_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_i_997_; lean_object* v___x_998_; lean_object* v_entries_999_; lean_object* v_indexes_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_995_ = l_Std_Time_DateTime_toRFC822String(v_a_991_);
v___x_996_ = l_Std_Http_Header_Value_ofString_x21(v___x_995_);
v_i_997_ = lean_array_get_size(v_entries_975_);
lean_inc_ref(v___x_976_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_976_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
v_entries_999_ = lean_array_push(v_entries_975_, v___x_998_);
v_indexes_1000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_997_, v_indexes_977_, v___x_976_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_entries_999_);
lean_ctor_set(v___x_1001_, 1, v_indexes_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1002_, 0, v_status_978_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*2, v_version_979_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1002_);
v___x_1004_ = v___x_993_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_1008_, lean_object* v___x_1009_, lean_object* v_indexes_1010_, lean_object* v_status_1011_, lean_object* v_version_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v_version_boxed_1015_; lean_object* v_res_1016_; 
v_version_boxed_1015_ = lean_unbox(v_version_1012_);
v_res_1016_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_1008_, v___x_1009_, v_indexes_1010_, v_status_1011_, v_version_boxed_1015_, v_x_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1017_, lean_object* v_a_1018_, lean_object* v___x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v_offset_1021_; lean_object* v_second_1022_; lean_object* v_nano_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_nanos_1027_; lean_object* v___x_1028_; lean_object* v_nanos_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_offset_1021_ = lean_ctor_get(v_tz_1017_, 0);
v_second_1022_ = lean_ctor_get(v_a_1018_, 0);
v_nano_1023_ = lean_ctor_get(v_a_1018_, 1);
v___x_1024_ = lean_nat_to_int(v___x_1019_);
v___x_1025_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_1026_ = lean_int_mul(v_second_1022_, v___x_1025_);
v_nanos_1027_ = lean_int_add(v___x_1026_, v_nano_1023_);
lean_dec(v___x_1026_);
v___x_1028_ = lean_int_mul(v_offset_1021_, v___x_1025_);
v_nanos_1029_ = lean_int_add(v___x_1028_, v___x_1024_);
lean_dec(v___x_1024_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_int_add(v_nanos_1027_, v_nanos_1029_);
lean_dec(v_nanos_1029_);
lean_dec(v_nanos_1027_);
v___x_1031_ = l_Std_Time_Duration_ofNanoseconds(v___x_1030_);
lean_dec(v___x_1030_);
v___x_1032_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1033_, lean_object* v_a_1034_, lean_object* v___x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1033_, v_a_1034_, v___x_1035_, v_x_1036_);
lean_dec_ref(v_a_1034_);
lean_dec_ref(v_tz_1033_);
return v_res_1037_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_buckets_1040_; lean_object* v___x_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; uint64_t v_fold_1045_; uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v___x_1048_; size_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_buckets_1040_ = lean_ctor_get(v_m_1038_, 1);
v___x_1041_ = lean_array_get_size(v_buckets_1040_);
v___x_1042_ = lean_string_hash(v_a_1039_);
v___x_1043_ = 32ULL;
v___x_1044_ = lean_uint64_shift_right(v___x_1042_, v___x_1043_);
v_fold_1045_ = lean_uint64_xor(v___x_1042_, v___x_1044_);
v___x_1046_ = 16ULL;
v___x_1047_ = lean_uint64_shift_right(v_fold_1045_, v___x_1046_);
v___x_1048_ = lean_uint64_xor(v_fold_1045_, v___x_1047_);
v___x_1049_ = lean_uint64_to_usize(v___x_1048_);
v___x_1050_ = lean_usize_of_nat(v___x_1041_);
v___x_1051_ = ((size_t)1ULL);
v___x_1052_ = lean_usize_sub(v___x_1050_, v___x_1051_);
v___x_1053_ = lean_usize_land(v___x_1049_, v___x_1052_);
v___x_1054_ = lean_array_uget_borrowed(v_buckets_1040_, v___x_1053_);
v___x_1055_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1039_, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object* v_m_1056_, lean_object* v_a_1057_){
_start:
{
uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_res_1058_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1056_, v_a_1057_);
lean_dec_ref(v_a_1057_);
lean_dec_ref(v_m_1056_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1061_, lean_object* v_head_1062_){
_start:
{
lean_object* v_headers_1067_; uint8_t v_generateDate_1068_; lean_object* v_status_1069_; uint8_t v_version_1070_; lean_object* v_entries_1071_; lean_object* v_indexes_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___f_1075_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v_val_1079_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v_a_1085_; uint8_t v___y_1088_; uint8_t v___x_1109_; 
v_headers_1067_ = lean_ctor_get(v_head_1062_, 1);
v_generateDate_1068_ = lean_ctor_get_uint8(v_config_1061_, sizeof(void*)*24 + 1);
v_status_1069_ = lean_ctor_get(v_head_1062_, 0);
v_version_1070_ = lean_ctor_get_uint8(v_head_1062_, sizeof(void*)*2);
v_entries_1071_ = lean_ctor_get(v_headers_1067_, 0);
v_indexes_1072_ = lean_ctor_get(v_headers_1067_, 1);
v___x_1073_ = l_Std_Http_Header_Name_date;
v___x_1074_ = lean_box(v_version_1070_);
lean_inc(v_status_1069_);
lean_inc_ref(v_indexes_1072_);
lean_inc_ref(v_entries_1071_);
v___f_1075_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1075_, 0, v_entries_1071_);
lean_closure_set(v___f_1075_, 1, v___x_1073_);
lean_closure_set(v___f_1075_, 2, v_indexes_1072_);
lean_closure_set(v___f_1075_, 3, v_status_1069_);
lean_closure_set(v___f_1075_, 4, v___x_1074_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_1072_, v___x_1073_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; 
v___x_1110_ = 1;
v___y_1088_ = v___x_1110_;
goto v___jp_1087_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = 0;
v___y_1088_ = v___x_1111_;
goto v___jp_1087_;
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_head_1062_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
v___jp_1076_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_val_1079_);
v___x_1081_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_1077_, v___y_1078_, v___x_1080_, v___f_1075_);
return v___x_1081_;
}
v___jp_1082_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_a_1085_);
v___y_1077_ = v___y_1083_;
v___y_1078_ = v___y_1084_;
v_val_1079_ = v___x_1086_;
goto v___jp_1076_;
}
v___jp_1087_:
{
if (v_generateDate_1068_ == 0)
{
lean_dec_ref(v___f_1075_);
goto v___jp_1064_;
}
else
{
if (v___y_1088_ == 0)
{
lean_dec_ref(v___f_1075_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_head_1062_);
v___x_1089_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = 0;
v___x_1092_ = lean_get_current_time();
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1089_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1106_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_tz_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_inc(v_a_1095_);
v_tz_1099_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1095_, v_a_1093_);
lean_inc(v_a_1093_);
lean_inc_ref(v_tz_1099_);
v___f_1100_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1100_, 0, v_tz_1099_);
lean_closure_set(v___f_1100_, 1, v_a_1093_);
lean_closure_set(v___f_1100_, 2, v___x_1090_);
v___x_1101_ = lean_mk_thunk(v___f_1100_);
v___x_1102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_a_1093_);
lean_ctor_set(v___x_1102_, 2, v_a_1095_);
lean_ctor_set(v___x_1102_, 3, v_tz_1099_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 1);
lean_ctor_set(v___x_1097_, 0, v___x_1102_);
v___x_1104_ = v___x_1097_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v___y_1077_ = v___x_1090_;
v___y_1078_ = v___x_1091_;
v_val_1079_ = v___x_1104_;
goto v___jp_1076_;
}
}
}
else
{
lean_object* v_a_1107_; 
lean_dec(v_a_1093_);
v_a_1107_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1094_, 1);
v___y_1083_ = v___x_1090_;
v___y_1084_ = v___x_1091_;
v_a_1085_ = v_a_1107_;
goto v___jp_1082_;
}
}
else
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1092_, 1);
v___y_1083_ = v___x_1090_;
v___y_1084_ = v___x_1091_;
v_a_1085_ = v_a_1108_;
goto v___jp_1082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1112_, lean_object* v_head_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1112_, v_head_1113_);
lean_dec_ref(v_config_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_00_u03b2_1116_, lean_object* v_m_1117_, lean_object* v_a_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1117_, v_a_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(v_00_u03b2_1120_, v_m_1121_, v_a_1122_);
lean_dec_ref(v_a_1122_);
lean_dec_ref(v_m_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__5(lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_nat_to_int(v_a_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_nat_to_int(v_a_1127_);
v___x_1129_ = l_Rat_ofInt(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1130_, lean_object* v_a_1131_, lean_object* v_x_1132_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1131_, v_x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1134_, lean_object* v_a_1135_, lean_object* v_x_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1134_, v_a_1135_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec_ref(v_a_1135_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1139_, lean_object* v_data_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1142_, lean_object* v_i_1143_, lean_object* v_source_1144_, lean_object* v_target_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v_i_1143_, v_source_1144_, v_target_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_x_1148_, v_x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1151_, lean_object* v_____r_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___y_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1158_, lean_object* v_____r_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1158_, v_____r_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v___f_1162_);
v_a_1165_ = lean_ctor_get(v_x_1163_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_x_1163_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1167_ = v_x_1163_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v_x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1175_; 
v_a_1174_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v_x_1163_, 1);
v___x_1175_ = lean_apply_2(v___f_1162_, v_a_1174_, lean_box(0));
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1176_, v_x_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1180_, lean_object* v_body_1181_, lean_object* v___f_1182_, lean_object* v___f_1183_, lean_object* v_x_1184_){
_start:
{
if (lean_obj_tag(v_x_1184_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v___f_1183_);
lean_dec_ref(v___f_1182_);
lean_dec(v_body_1181_);
lean_dec_ref(v_close_1180_);
v_a_1186_ = lean_ctor_get(v_x_1184_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_x_1184_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v_x_1184_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v_x_1184_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; uint8_t v___x_1196_; 
v_a_1195_ = lean_ctor_get(v_x_1184_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v_x_1184_, 1);
v___x_1196_ = lean_unbox(v_a_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v___f_1183_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_apply_2(v_close_1180_, v_body_1181_, lean_box(0));
v___x_1199_ = lean_unbox(v_a_1195_);
lean_dec(v_a_1195_);
v___x_1200_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1197_, v___x_1199_, v___x_1198_, v___f_1182_);
return v___x_1200_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v_a_1195_);
lean_dec_ref(v___f_1182_);
lean_dec(v_body_1181_);
lean_dec_ref(v_close_1180_);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_apply_2(v___f_1183_, v___x_1201_, lean_box(0));
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1203_, lean_object* v_body_1204_, lean_object* v___f_1205_, lean_object* v___f_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1203_, v_body_1204_, v___f_1205_, v___f_1206_, v_x_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1210_, lean_object* v___f_1211_, lean_object* v___f_1212_, lean_object* v_x1_1213_, lean_object* v_x2_1214_){
_start:
{
lean_object* v_fst_1215_; uint8_t v___x_1216_; 
v_fst_1215_ = lean_ctor_get(v_x2_1214_, 0);
lean_inc(v_fst_1215_);
v___x_1216_ = lean_string_dec_eq(v___x_1210_, v_fst_1215_);
if (v___x_1216_ == 0)
{
lean_object* v_entries_1217_; lean_object* v_indexes_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
v_entries_1217_ = lean_ctor_get(v_x1_1213_, 0);
v_indexes_1218_ = lean_ctor_get(v_x1_1213_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x1_1213_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1220_ = v_x1_1213_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_indexes_1218_);
lean_inc(v_entries_1217_);
lean_dec(v_x1_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_i_1222_; lean_object* v_f_1223_; lean_object* v_entries_1224_; lean_object* v_indexes_1225_; lean_object* v___x_1227_; 
v_i_1222_ = lean_array_get_size(v_entries_1217_);
v_f_1223_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1223_, 0, v_i_1222_);
v_entries_1224_ = lean_array_push(v_entries_1217_, v_x2_1214_);
v_indexes_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1211_, v___f_1212_, v_indexes_1218_, v_fst_1215_, v_f_1223_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v_indexes_1225_);
lean_ctor_set(v___x_1220_, 0, v_entries_1224_);
v___x_1227_ = v___x_1220_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_entries_1224_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_indexes_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_dec(v_fst_1215_);
lean_dec_ref(v_x2_1214_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v___f_1211_);
return v_x1_1213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1230_, lean_object* v___f_1231_, lean_object* v___f_1232_, lean_object* v_x1_1233_, lean_object* v_x2_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1230_, v___f_1231_, v___f_1232_, v_x1_1233_, v_x2_1234_);
lean_dec_ref(v___x_1230_);
return v_res_1235_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_1238_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; 
v___f_1258_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1259_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1260_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1261_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1261_, 0, v___x_1260_);
lean_closure_set(v___f_1261_, 1, v___f_1259_);
lean_closure_set(v___f_1261_, 2, v___f_1258_);
return v___f_1261_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14(void){
_start:
{
lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; 
v___f_1262_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___f_1263_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___x_1264_ = l_Std_Http_Header_Name_contentLength;
v___f_1265_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1265_, 0, v___x_1264_);
lean_closure_set(v___f_1265_, 1, v___f_1263_);
lean_closure_set(v___f_1265_, 2, v___f_1262_);
return v___f_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1266_, lean_object* v_body_1267_, lean_object* v_close_1268_, lean_object* v_isClosed_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___y_1273_; uint8_t v_omitBody_1274_; lean_object* v___y_1287_; 
if (lean_obj_tag(v_x_1270_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_isClosed_1269_);
lean_dec_ref(v_close_1268_);
lean_dec(v_body_1267_);
lean_dec_ref(v___y_1266_);
v_a_1321_ = lean_ctor_get(v_x_1270_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v_x_1270_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v_x_1270_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___y_1332_; uint8_t v___y_1333_; uint8_t v___y_1334_; uint8_t v___y_1335_; uint8_t v___y_1336_; uint8_t v___y_1337_; lean_object* v_writer_1345_; lean_object* v_reader_1346_; lean_object* v_config_1347_; lean_object* v_events_1348_; lean_object* v_error_1349_; lean_object* v_instant_1350_; uint8_t v_keepAlive_1351_; uint8_t v_forcedFlush_1352_; uint8_t v_pullBodyStalled_1353_; lean_object* v_userData_1354_; lean_object* v_outputData_1355_; lean_object* v_state_1356_; lean_object* v_knownSize_1357_; lean_object* v_messageHead_1358_; uint8_t v_sentMessage_1359_; uint8_t v_userClosedBody_1360_; uint8_t v_omitBody_1361_; lean_object* v_userDataBytes_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1445_; 
v_a_1330_ = lean_ctor_get(v_x_1270_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v_x_1270_, 1);
v_writer_1345_ = lean_ctor_get(v___y_1266_, 1);
lean_inc_ref(v_writer_1345_);
v_reader_1346_ = lean_ctor_get(v___y_1266_, 0);
v_config_1347_ = lean_ctor_get(v___y_1266_, 2);
v_events_1348_ = lean_ctor_get(v___y_1266_, 3);
v_error_1349_ = lean_ctor_get(v___y_1266_, 4);
v_instant_1350_ = lean_ctor_get(v___y_1266_, 5);
v_keepAlive_1351_ = lean_ctor_get_uint8(v___y_1266_, sizeof(void*)*6);
v_forcedFlush_1352_ = lean_ctor_get_uint8(v___y_1266_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1353_ = lean_ctor_get_uint8(v___y_1266_, sizeof(void*)*6 + 2);
v_userData_1354_ = lean_ctor_get(v_writer_1345_, 0);
v_outputData_1355_ = lean_ctor_get(v_writer_1345_, 1);
v_state_1356_ = lean_ctor_get(v_writer_1345_, 2);
v_knownSize_1357_ = lean_ctor_get(v_writer_1345_, 3);
v_messageHead_1358_ = lean_ctor_get(v_writer_1345_, 4);
v_sentMessage_1359_ = lean_ctor_get_uint8(v_writer_1345_, sizeof(void*)*6);
v_userClosedBody_1360_ = lean_ctor_get_uint8(v_writer_1345_, sizeof(void*)*6 + 1);
v_omitBody_1361_ = lean_ctor_get_uint8(v_writer_1345_, sizeof(void*)*6 + 2);
v_userDataBytes_1362_ = lean_ctor_get(v_writer_1345_, 5);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_writer_1345_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1364_ = v_writer_1345_;
v_isShared_1365_ = v_isSharedCheck_1445_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_userDataBytes_1362_);
lean_inc(v_messageHead_1358_);
lean_inc(v_knownSize_1357_);
lean_inc(v_state_1356_);
lean_inc(v_outputData_1355_);
lean_inc(v_userData_1354_);
lean_dec(v_writer_1345_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1445_;
goto v_resetjp_1363_;
}
v___jp_1331_:
{
lean_object* v_headerSize_1338_; lean_object* v_machine_1339_; lean_object* v_machine_1340_; lean_object* v_reader_1341_; lean_object* v_state_1342_; 
v_headerSize_1338_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1336_, v_a_1330_, v___y_1333_);
v_machine_1339_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1334_, v___y_1332_, v_headerSize_1338_, v___y_1337_);
v_machine_1340_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1334_, v_machine_1339_, v_a_1330_);
lean_dec(v_a_1330_);
v_reader_1341_ = lean_ctor_get(v_machine_1340_, 0);
lean_inc_ref(v_reader_1341_);
v_state_1342_ = lean_ctor_get(v_reader_1341_, 0);
lean_inc(v_state_1342_);
lean_dec_ref(v_reader_1341_);
if (lean_obj_tag(v_state_1342_) == 7)
{
lean_dec_ref_known(v_state_1342_, 1);
if (v___y_1335_ == 0)
{
lean_object* v_writer_1343_; uint8_t v_omitBody_1344_; 
v_writer_1343_ = lean_ctor_get(v_machine_1340_, 1);
lean_inc_ref(v_writer_1343_);
v_omitBody_1344_ = lean_ctor_get_uint8(v_writer_1343_, sizeof(void*)*6 + 2);
lean_dec_ref(v_writer_1343_);
v___y_1273_ = v_machine_1340_;
v_omitBody_1274_ = v_omitBody_1344_;
goto v___jp_1272_;
}
else
{
v___y_1287_ = v_machine_1340_;
goto v___jp_1286_;
}
}
else
{
lean_dec(v_state_1342_);
v___y_1287_ = v_machine_1340_;
goto v___jp_1286_;
}
}
v_resetjp_1363_:
{
uint8_t v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1394_; uint8_t v___y_1395_; uint8_t v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1410_; uint8_t v___y_1411_; uint8_t v___y_1412_; uint8_t v___y_1431_; lean_object* v___x_1439_; uint8_t v___x_1440_; uint8_t v___y_1442_; 
v___x_1439_ = lean_box(1);
v___x_1440_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1356_, v___x_1439_);
if (v_sentMessage_1359_ == 0)
{
uint8_t v___x_1443_; 
v___x_1443_ = 1;
v___y_1442_ = v___x_1443_;
goto v___jp_1441_;
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = 0;
v___y_1442_ = v___x_1444_;
goto v___jp_1441_;
}
v___jp_1366_:
{
lean_object* v_message_1369_; lean_object* v___x_2271__overap_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_message_1369_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1367_, v_a_1330_, v___y_1368_);
v___x_2271__overap_1370_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1367_);
v___x_1371_ = lean_apply_2(v___x_2271__overap_1370_, v_outputData_1355_, v_message_1369_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1371_);
v___x_1373_ = v___x_1364_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_userData_1354_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_state_1356_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_knownSize_1357_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v_messageHead_1358_);
lean_ctor_set(v_reuseFailAlloc_1375_, 5, v_userDataBytes_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, sizeof(void*)*6, v_sentMessage_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, sizeof(void*)*6 + 1, v_userClosedBody_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, sizeof(void*)*6 + 2, v_omitBody_1361_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1374_, 0, v_reader_1346_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_ctor_set(v___x_1374_, 2, v_config_1347_);
lean_ctor_set(v___x_1374_, 3, v_events_1348_);
lean_ctor_set(v___x_1374_, 4, v_error_1349_);
lean_ctor_set(v___x_1374_, 5, v_instant_1350_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*6, v_keepAlive_1351_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*6 + 1, v_forcedFlush_1352_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*6 + 2, v_pullBodyStalled_1353_);
v___y_1273_ = v___x_1374_;
v_omitBody_1274_ = v_omitBody_1361_;
goto v___jp_1272_;
}
}
v___jp_1376_:
{
lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___f_1381_; uint8_t v___x_1382_; 
v___x_1379_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1380_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1381_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1382_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1380_, v___f_1381_, v___x_1379_, v___y_1378_);
if (v___x_1382_ == 0)
{
v___y_1367_ = v___y_1377_;
v___y_1368_ = v___y_1378_;
goto v___jp_1366_;
}
else
{
lean_object* v_entries_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_entries_1383_ = lean_ctor_get(v___y_1378_, 0);
lean_inc_ref(v_entries_1383_);
lean_dec_ref(v___y_1378_);
v___x_1384_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_array_get_size(v_entries_1383_);
v___x_1387_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1388_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v_entries_1383_);
v___y_1367_ = v___y_1377_;
v___y_1368_ = v___x_1384_;
goto v___jp_1366_;
}
else
{
lean_object* v___f_1389_; size_t v___x_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v___f_1389_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = lean_usize_of_nat(v___x_1386_);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1387_, v___f_1389_, v_entries_1383_, v___x_1390_, v___x_1391_, v___x_1384_);
v___y_1367_ = v___y_1377_;
v___y_1368_ = v___x_1392_;
goto v___jp_1366_;
}
}
}
v___jp_1393_:
{
uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v_indexes_1400_; lean_object* v___x_1401_; lean_object* v_machine_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___f_1405_; uint8_t v___x_1406_; 
v___x_1398_ = 1;
v___x_1399_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1398_, v_a_1330_);
v_indexes_1400_ = lean_ctor_get(v___x_1399_, 1);
lean_inc_ref(v_indexes_1400_);
lean_dec_ref(v___x_1399_);
lean_inc(v_a_1330_);
v___x_1401_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1401_, 0, v_userData_1354_);
lean_ctor_set(v___x_1401_, 1, v_outputData_1355_);
lean_ctor_set(v___x_1401_, 2, v_state_1356_);
lean_ctor_set(v___x_1401_, 3, v_knownSize_1357_);
lean_ctor_set(v___x_1401_, 4, v_a_1330_);
lean_ctor_set(v___x_1401_, 5, v_userDataBytes_1362_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*6, v___y_1395_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*6 + 1, v_userClosedBody_1360_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*6 + 2, v_omitBody_1361_);
v_machine_1402_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1402_, 0, v_reader_1346_);
lean_ctor_set(v_machine_1402_, 1, v___x_1401_);
lean_ctor_set(v_machine_1402_, 2, v_config_1347_);
lean_ctor_set(v_machine_1402_, 3, v_events_1348_);
lean_ctor_set(v_machine_1402_, 4, v_error_1349_);
lean_ctor_set(v_machine_1402_, 5, v_instant_1350_);
lean_ctor_set_uint8(v_machine_1402_, sizeof(void*)*6, v_keepAlive_1351_);
lean_ctor_set_uint8(v_machine_1402_, sizeof(void*)*6 + 1, v_forcedFlush_1352_);
lean_ctor_set_uint8(v_machine_1402_, sizeof(void*)*6 + 2, v_pullBodyStalled_1353_);
v___x_1403_ = l_Std_Http_Header_Name_contentLength;
v___f_1404_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1405_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1404_, v___f_1405_, v_indexes_1400_, v___x_1403_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1408_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1404_, v___f_1405_, v_indexes_1400_, v___x_1407_);
lean_dec_ref(v_indexes_1400_);
v___y_1332_ = v_machine_1402_;
v___y_1333_ = v___y_1394_;
v___y_1334_ = v___y_1396_;
v___y_1335_ = v___y_1397_;
v___y_1336_ = v___x_1398_;
v___y_1337_ = v___x_1408_;
goto v___jp_1331_;
}
else
{
lean_dec_ref(v_indexes_1400_);
v___y_1332_ = v_machine_1402_;
v___y_1333_ = v___y_1394_;
v___y_1334_ = v___y_1396_;
v___y_1335_ = v___y_1397_;
v___y_1336_ = v___x_1398_;
v___y_1337_ = v___x_1406_;
goto v___jp_1331_;
}
}
v___jp_1409_:
{
if (v___y_1412_ == 0)
{
lean_object* v_state_1413_; 
lean_del_object(v___x_1364_);
lean_dec(v_messageHead_1358_);
v_state_1413_ = lean_ctor_get(v_reader_1346_, 0);
if (lean_obj_tag(v_state_1413_) == 7)
{
v___y_1394_ = v___y_1412_;
v___y_1395_ = v___y_1410_;
v___y_1396_ = v___y_1411_;
v___y_1397_ = v___y_1410_;
goto v___jp_1393_;
}
else
{
v___y_1394_ = v___y_1412_;
v___y_1395_ = v___y_1410_;
v___y_1396_ = v___y_1411_;
v___y_1397_ = v___y_1412_;
goto v___jp_1393_;
}
}
else
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; uint8_t v___x_1419_; 
v___x_1414_ = 1;
v___x_1415_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1414_, v_a_1330_);
v___x_1416_ = l_Std_Http_Header_Name_contentLength;
v___f_1417_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1419_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1417_, v___f_1418_, v___x_1416_, v___x_1415_);
if (v___x_1419_ == 0)
{
v___y_1377_ = v___x_1414_;
v___y_1378_ = v___x_1415_;
goto v___jp_1376_;
}
else
{
lean_object* v_entries_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_entries_1420_ = lean_ctor_get(v___x_1415_, 0);
lean_inc_ref(v_entries_1420_);
lean_dec_ref(v___x_1415_);
v___x_1421_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_array_get_size(v_entries_1420_);
v___x_1424_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1425_ = lean_nat_dec_lt(v___x_1422_, v___x_1423_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v_entries_1420_);
v___y_1377_ = v___x_1414_;
v___y_1378_ = v___x_1421_;
goto v___jp_1376_;
}
else
{
lean_object* v___f_1426_; size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___f_1426_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14);
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1423_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1424_, v___f_1426_, v_entries_1420_, v___x_1427_, v___x_1428_, v___x_1421_);
v___y_1377_ = v___x_1414_;
v___y_1378_ = v___x_1429_;
goto v___jp_1376_;
}
}
}
}
v___jp_1430_:
{
if (v___y_1431_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec(v_userDataBytes_1362_);
lean_dec(v_messageHead_1358_);
lean_dec(v_knownSize_1357_);
lean_dec(v_state_1356_);
lean_dec_ref(v_outputData_1355_);
lean_dec_ref(v_userData_1354_);
lean_dec(v_a_1330_);
v___y_1273_ = v___y_1266_;
v_omitBody_1274_ = v_omitBody_1361_;
goto v___jp_1272_;
}
else
{
lean_object* v_status_1432_; uint8_t v___x_1433_; uint16_t v___x_1434_; uint16_t v___x_1435_; uint8_t v___x_1436_; 
lean_inc(v_instant_1350_);
lean_inc(v_error_1349_);
lean_inc_ref(v_events_1348_);
lean_inc_ref(v_config_1347_);
lean_inc_ref(v_reader_1346_);
lean_dec_ref(v___y_1266_);
v_status_1432_ = lean_ctor_get(v_a_1330_, 0);
v___x_1433_ = 0;
v___x_1434_ = 100;
v___x_1435_ = l_Std_Http_Status_toCode(v_status_1432_);
v___x_1436_ = lean_uint16_dec_le(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
v___y_1410_ = v___y_1431_;
v___y_1411_ = v___x_1433_;
v___y_1412_ = v___x_1436_;
goto v___jp_1409_;
}
else
{
uint16_t v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = 200;
v___x_1438_ = lean_uint16_dec_lt(v___x_1435_, v___x_1437_);
v___y_1410_ = v___y_1431_;
v___y_1411_ = v___x_1433_;
v___y_1412_ = v___x_1438_;
goto v___jp_1409_;
}
}
}
v___jp_1441_:
{
if (v___x_1440_ == 0)
{
v___y_1431_ = v___x_1440_;
goto v___jp_1430_;
}
else
{
v___y_1431_ = v___y_1442_;
goto v___jp_1430_;
}
}
}
}
v___jp_1272_:
{
if (v_omitBody_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_isClosed_1269_);
lean_dec_ref(v_close_1268_);
v___x_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_body_1267_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1273_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
else
{
lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___f_1279_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1279_, 0, v___y_1273_);
lean_inc_ref(v___f_1279_);
v___f_1280_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1280_, 0, v___f_1279_);
lean_inc(v_body_1267_);
v___f_1281_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1281_, 0, v_close_1268_);
lean_closure_set(v___f_1281_, 1, v_body_1267_);
lean_closure_set(v___f_1281_, 2, v___f_1280_);
lean_closure_set(v___f_1281_, 3, v___f_1279_);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = 0;
v___x_1284_ = lean_apply_2(v_isClosed_1269_, v_body_1267_, lean_box(0));
v___x_1285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1282_, v___x_1283_, v___x_1284_, v___f_1281_);
return v___x_1285_;
}
}
v___jp_1286_:
{
lean_object* v_writer_1288_; lean_object* v_reader_1289_; lean_object* v_config_1290_; lean_object* v_events_1291_; lean_object* v_error_1292_; lean_object* v_instant_1293_; uint8_t v_keepAlive_1294_; uint8_t v_forcedFlush_1295_; uint8_t v_pullBodyStalled_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1320_; 
v_writer_1288_ = lean_ctor_get(v___y_1287_, 1);
v_reader_1289_ = lean_ctor_get(v___y_1287_, 0);
v_config_1290_ = lean_ctor_get(v___y_1287_, 2);
v_events_1291_ = lean_ctor_get(v___y_1287_, 3);
v_error_1292_ = lean_ctor_get(v___y_1287_, 4);
v_instant_1293_ = lean_ctor_get(v___y_1287_, 5);
v_keepAlive_1294_ = lean_ctor_get_uint8(v___y_1287_, sizeof(void*)*6);
v_forcedFlush_1295_ = lean_ctor_get_uint8(v___y_1287_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1296_ = lean_ctor_get_uint8(v___y_1287_, sizeof(void*)*6 + 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___y_1287_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1298_ = v___y_1287_;
v_isShared_1299_ = v_isSharedCheck_1320_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_instant_1293_);
lean_inc(v_error_1292_);
lean_inc(v_events_1291_);
lean_inc(v_config_1290_);
lean_inc(v_writer_1288_);
lean_inc(v_reader_1289_);
lean_dec(v___y_1287_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1320_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_userData_1300_; lean_object* v_outputData_1301_; lean_object* v_knownSize_1302_; lean_object* v_messageHead_1303_; uint8_t v_sentMessage_1304_; uint8_t v_userClosedBody_1305_; uint8_t v_omitBody_1306_; lean_object* v_userDataBytes_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_userData_1300_ = lean_ctor_get(v_writer_1288_, 0);
v_outputData_1301_ = lean_ctor_get(v_writer_1288_, 1);
v_knownSize_1302_ = lean_ctor_get(v_writer_1288_, 3);
v_messageHead_1303_ = lean_ctor_get(v_writer_1288_, 4);
v_sentMessage_1304_ = lean_ctor_get_uint8(v_writer_1288_, sizeof(void*)*6);
v_userClosedBody_1305_ = lean_ctor_get_uint8(v_writer_1288_, sizeof(void*)*6 + 1);
v_omitBody_1306_ = lean_ctor_get_uint8(v_writer_1288_, sizeof(void*)*6 + 2);
v_userDataBytes_1307_ = lean_ctor_get(v_writer_1288_, 5);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_writer_1288_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_writer_1288_, 2);
lean_dec(v_unused_1319_);
v___x_1309_ = v_writer_1288_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_userDataBytes_1307_);
lean_inc(v_messageHead_1303_);
lean_inc(v_knownSize_1302_);
lean_inc(v_outputData_1301_);
lean_inc(v_userData_1300_);
lean_dec(v_writer_1288_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(2);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 2, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_userData_1300_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_outputData_1301_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_knownSize_1302_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_messageHead_1303_);
lean_ctor_set(v_reuseFailAlloc_1317_, 5, v_userDataBytes_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*6, v_sentMessage_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*6 + 1, v_userClosedBody_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*6 + 2, v_omitBody_1306_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 1, v___x_1313_);
v___x_1315_ = v___x_1298_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_reader_1289_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_config_1290_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_events_1291_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_error_1292_);
lean_ctor_set(v_reuseFailAlloc_1316_, 5, v_instant_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*6, v_keepAlive_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*6 + 1, v_forcedFlush_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*6 + 2, v_pullBodyStalled_1296_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
v___y_1273_ = v___x_1315_;
v_omitBody_1274_ = v_omitBody_1306_;
goto v___jp_1272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1446_, lean_object* v_body_1447_, lean_object* v_close_1448_, lean_object* v_isClosed_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1446_, v_body_1447_, v_close_1448_, v_isClosed_1449_, v_x_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_body_1453_, lean_object* v_close_1454_, lean_object* v_isClosed_1455_, lean_object* v_config_1456_, lean_object* v_line_1457_, lean_object* v_machine_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v___y_1462_; 
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_machine_1458_);
lean_dec_ref(v_line_1457_);
lean_dec_ref(v_isClosed_1455_);
lean_dec_ref(v_close_1454_);
lean_dec(v_body_1453_);
v_a_1468_ = lean_ctor_get(v_x_1459_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1459_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v_x_1459_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v_x_1459_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v_x_1459_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v_x_1459_, 1);
if (lean_obj_tag(v_a_1477_) == 1)
{
lean_object* v_writer_1478_; lean_object* v_reader_1479_; lean_object* v_config_1480_; lean_object* v_events_1481_; lean_object* v_error_1482_; lean_object* v_instant_1483_; uint8_t v_keepAlive_1484_; uint8_t v_forcedFlush_1485_; uint8_t v_pullBodyStalled_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1509_; 
v_writer_1478_ = lean_ctor_get(v_machine_1458_, 1);
v_reader_1479_ = lean_ctor_get(v_machine_1458_, 0);
v_config_1480_ = lean_ctor_get(v_machine_1458_, 2);
v_events_1481_ = lean_ctor_get(v_machine_1458_, 3);
v_error_1482_ = lean_ctor_get(v_machine_1458_, 4);
v_instant_1483_ = lean_ctor_get(v_machine_1458_, 5);
v_keepAlive_1484_ = lean_ctor_get_uint8(v_machine_1458_, sizeof(void*)*6);
v_forcedFlush_1485_ = lean_ctor_get_uint8(v_machine_1458_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1486_ = lean_ctor_get_uint8(v_machine_1458_, sizeof(void*)*6 + 2);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_machine_1458_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1488_ = v_machine_1458_;
v_isShared_1489_ = v_isSharedCheck_1509_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_instant_1483_);
lean_inc(v_error_1482_);
lean_inc(v_events_1481_);
lean_inc(v_config_1480_);
lean_inc(v_writer_1478_);
lean_inc(v_reader_1479_);
lean_dec(v_machine_1458_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1509_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_userData_1490_; lean_object* v_outputData_1491_; lean_object* v_state_1492_; lean_object* v_messageHead_1493_; uint8_t v_sentMessage_1494_; uint8_t v_userClosedBody_1495_; uint8_t v_omitBody_1496_; lean_object* v_userDataBytes_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1507_; 
v_userData_1490_ = lean_ctor_get(v_writer_1478_, 0);
v_outputData_1491_ = lean_ctor_get(v_writer_1478_, 1);
v_state_1492_ = lean_ctor_get(v_writer_1478_, 2);
v_messageHead_1493_ = lean_ctor_get(v_writer_1478_, 4);
v_sentMessage_1494_ = lean_ctor_get_uint8(v_writer_1478_, sizeof(void*)*6);
v_userClosedBody_1495_ = lean_ctor_get_uint8(v_writer_1478_, sizeof(void*)*6 + 1);
v_omitBody_1496_ = lean_ctor_get_uint8(v_writer_1478_, sizeof(void*)*6 + 2);
v_userDataBytes_1497_ = lean_ctor_get(v_writer_1478_, 5);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_writer_1478_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_writer_1478_, 3);
lean_dec(v_unused_1508_);
v___x_1499_ = v_writer_1478_;
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_userDataBytes_1497_);
lean_inc(v_messageHead_1493_);
lean_inc(v_state_1492_);
lean_inc(v_outputData_1491_);
lean_inc(v_userData_1490_);
lean_dec(v_writer_1478_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 3, v_a_1477_);
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_userData_1490_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_outputData_1491_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_state_1492_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_a_1477_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_messageHead_1493_);
lean_ctor_set(v_reuseFailAlloc_1506_, 5, v_userDataBytes_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*6, v_sentMessage_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*6 + 1, v_userClosedBody_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*6 + 2, v_omitBody_1496_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v___x_1502_);
v___x_1504_ = v___x_1488_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_reader_1479_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_config_1480_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v_events_1481_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v_error_1482_);
lean_ctor_set(v_reuseFailAlloc_1505_, 5, v_instant_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, sizeof(void*)*6, v_keepAlive_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, sizeof(void*)*6 + 1, v_forcedFlush_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, sizeof(void*)*6 + 2, v_pullBodyStalled_1486_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
v___y_1462_ = v___x_1504_;
goto v___jp_1461_;
}
}
}
}
}
else
{
lean_dec(v_a_1477_);
v___y_1462_ = v_machine_1458_;
goto v___jp_1461_;
}
}
v___jp_1461_:
{
lean_object* v___f_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___f_1463_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1463_, 0, v___y_1462_);
lean_closure_set(v___f_1463_, 1, v_body_1453_);
lean_closure_set(v___f_1463_, 2, v_close_1454_);
lean_closure_set(v___f_1463_, 3, v_isClosed_1455_);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = 0;
v___x_1466_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1456_, v_line_1457_);
v___x_1467_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1464_, v___x_1465_, v___x_1466_, v___f_1463_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_body_1510_, lean_object* v_close_1511_, lean_object* v_isClosed_1512_, lean_object* v_config_1513_, lean_object* v_line_1514_, lean_object* v_machine_1515_, lean_object* v_x_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_body_1510_, v_close_1511_, v_isClosed_1512_, v_config_1513_, v_line_1514_, v_machine_1515_, v_x_1516_);
lean_dec_ref(v_config_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1519_, lean_object* v_config_1520_, lean_object* v_machine_1521_, lean_object* v_res_1522_){
_start:
{
lean_object* v_close_1524_; lean_object* v_isClosed_1525_; lean_object* v_getKnownSize_1526_; lean_object* v_line_1527_; lean_object* v_body_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_close_1524_ = lean_ctor_get(v_inst_1519_, 1);
lean_inc_ref(v_close_1524_);
v_isClosed_1525_ = lean_ctor_get(v_inst_1519_, 2);
lean_inc_ref(v_isClosed_1525_);
v_getKnownSize_1526_ = lean_ctor_get(v_inst_1519_, 5);
lean_inc_ref(v_getKnownSize_1526_);
lean_dec_ref(v_inst_1519_);
v_line_1527_ = lean_ctor_get(v_res_1522_, 0);
lean_inc_ref(v_line_1527_);
v_body_1528_ = lean_ctor_get(v_res_1522_, 1);
lean_inc_n(v_body_1528_, 2);
lean_dec_ref(v_res_1522_);
v___f_1529_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1529_, 0, v_body_1528_);
lean_closure_set(v___f_1529_, 1, v_close_1524_);
lean_closure_set(v___f_1529_, 2, v_isClosed_1525_);
lean_closure_set(v___f_1529_, 3, v_config_1520_);
lean_closure_set(v___f_1529_, 4, v_line_1527_);
lean_closure_set(v___f_1529_, 5, v_machine_1521_);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = 0;
v___x_1532_ = lean_apply_2(v_getKnownSize_1526_, v_body_1528_, lean_box(0));
v___x_1533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1530_, v___x_1531_, v___x_1532_, v___f_1529_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1534_, lean_object* v_config_1535_, lean_object* v_machine_1536_, lean_object* v_res_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1534_, v_config_1535_, v_machine_1536_, v_res_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1540_, lean_object* v_inst_1541_, lean_object* v_config_1542_, lean_object* v_machine_1543_, lean_object* v_res_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1541_, v_config_1542_, v_machine_1543_, v_res_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1547_, lean_object* v_inst_1548_, lean_object* v_config_1549_, lean_object* v_machine_1550_, lean_object* v_res_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1547_, v_inst_1548_, v_config_1549_, v_machine_1550_, v_res_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v_closed_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_closed_1557_ = lean_ctor_get_uint8(v_____do__lift_1554_, sizeof(void*)*6);
v___x_1558_ = lean_box(v_closed_1557_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v_____do__lift_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v___x_1565_);
v_a_1568_ = lean_ctor_get(v_x_1566_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1570_ = v_x_1566_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v_x_1566_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
else
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
v_isSharedCheck_1585_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v_x_1566_, 0);
lean_dec(v_unused_1586_);
v___x_1578_ = v_x_1566_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v_x_1566_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1565_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1587_, lean_object* v_x_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1587_, v_x_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_pendingProducer_1599_; lean_object* v_pendingConsumer_1600_; lean_object* v_interestWaiter_1601_; uint8_t v_closed_1602_; lean_object* v_pendingIncompleteChunk_1603_; lean_object* v_closeError_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1613_; 
v___x_1598_ = lean_st_ref_take(v___y_1596_);
v_pendingProducer_1599_ = lean_ctor_get(v___x_1598_, 0);
v_pendingConsumer_1600_ = lean_ctor_get(v___x_1598_, 1);
v_interestWaiter_1601_ = lean_ctor_get(v___x_1598_, 2);
v_closed_1602_ = lean_ctor_get_uint8(v___x_1598_, sizeof(void*)*6);
v_pendingIncompleteChunk_1603_ = lean_ctor_get(v___x_1598_, 4);
v_closeError_1604_ = lean_ctor_get(v___x_1598_, 5);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1598_, 3);
lean_dec(v_unused_1614_);
v___x_1606_ = v___x_1598_;
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_closeError_1604_);
lean_inc(v_pendingIncompleteChunk_1603_);
lean_inc(v_interestWaiter_1601_);
lean_inc(v_pendingConsumer_1600_);
lean_inc(v_pendingProducer_1599_);
lean_dec(v___x_1598_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 3, v___x_1595_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_pendingProducer_1599_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_pendingConsumer_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_interestWaiter_1601_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_pendingIncompleteChunk_1603_);
lean_ctor_set(v_reuseFailAlloc_1612_, 5, v_closeError_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1612_, sizeof(void*)*6, v_closed_1602_);
v___x_1609_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_st_ref_put(v___y_1596_, v___x_1609_);
v___x_1611_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1615_, v___y_1616_);
lean_dec(v___y_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1619_, lean_object* v_requestStream_1620_, lean_object* v_keepAliveTimeout_1621_, lean_object* v_currentTimeout_1622_, lean_object* v_headerTimeout_1623_, lean_object* v_response_1624_, lean_object* v_respStream_1625_, lean_object* v_expectData_1626_, uint8_t v_handlerDispatched_1627_, lean_object* v_____r_1628_){
_start:
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1630_ = 0;
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1632_, 0, v_machine_1619_);
lean_ctor_set(v___x_1632_, 1, v_requestStream_1620_);
lean_ctor_set(v___x_1632_, 2, v_keepAliveTimeout_1621_);
lean_ctor_set(v___x_1632_, 3, v_currentTimeout_1622_);
lean_ctor_set(v___x_1632_, 4, v_headerTimeout_1623_);
lean_ctor_set(v___x_1632_, 5, v_response_1624_);
lean_ctor_set(v___x_1632_, 6, v_respStream_1625_);
lean_ctor_set(v___x_1632_, 7, v_expectData_1626_);
lean_ctor_set(v___x_1632_, 8, v___x_1631_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*9, v___x_1630_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*9 + 1, v_handlerDispatched_1627_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1636_, lean_object* v_requestStream_1637_, lean_object* v_keepAliveTimeout_1638_, lean_object* v_currentTimeout_1639_, lean_object* v_headerTimeout_1640_, lean_object* v_response_1641_, lean_object* v_respStream_1642_, lean_object* v_expectData_1643_, lean_object* v_handlerDispatched_1644_, lean_object* v_____r_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v_handlerDispatched_boxed_1647_; lean_object* v_res_1648_; 
v_handlerDispatched_boxed_1647_ = lean_unbox(v_handlerDispatched_1644_);
v_res_1648_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1636_, v_requestStream_1637_, v_keepAliveTimeout_1638_, v_currentTimeout_1639_, v_headerTimeout_1640_, v_response_1641_, v_respStream_1642_, v_expectData_1643_, v_handlerDispatched_boxed_1647_, v_____r_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1649_, lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1650_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v___f_1649_);
v_a_1652_ = lean_ctor_get(v_x_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1654_ = v_x_1650_;
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v_x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1652_);
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
else
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v_x_1650_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v_x_1650_, 1);
v___x_1662_ = lean_apply_2(v___f_1649_, v_a_1661_, lean_box(0));
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1663_, lean_object* v_x_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1663_, v_x_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1667_, lean_object* v___f_1668_, lean_object* v___f_1669_, lean_object* v_x_1670_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v___f_1668_);
lean_dec_ref(v_requestStream_1667_);
v_a_1672_ = lean_ctor_get(v_x_1670_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_x_1670_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v_x_1670_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v_x_1670_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; uint8_t v___x_1682_; 
v_a_1681_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v_x_1670_, 1);
v___x_1682_ = lean_unbox(v_a_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref(v___f_1669_);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = l_Std_Http_Body_Stream_close(v_requestStream_1667_);
v___x_1685_ = lean_unbox(v_a_1681_);
lean_dec(v_a_1681_);
v___x_1686_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1683_, v___x_1685_, v___x_1684_, v___f_1668_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_a_1681_);
lean_dec_ref(v___f_1668_);
lean_dec_ref(v_requestStream_1667_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_apply_2(v___f_1669_, v___x_1687_, lean_box(0));
return v___x_1688_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1689_, lean_object* v___f_1690_, lean_object* v___f_1691_, lean_object* v_x_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1689_, v___f_1690_, v___f_1691_, v_x_1692_);
return v_res_1694_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1695_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_1696_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; 
v___x_1702_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1703_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1704_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1704_, 0, v___f_1703_);
lean_closure_set(v___f_1704_, 1, v___x_1702_);
return v___f_1704_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; 
v___x_1713_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1714_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1715_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1715_, 0, v___f_1714_);
lean_closure_set(v___f_1715_, 1, v___x_1713_);
return v___f_1715_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1716_; lean_object* v___x_1717_; 
v___f_1716_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1717_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1717_, 0, lean_box(0));
lean_closure_set(v___x_1717_, 1, lean_box(0));
lean_closure_set(v___x_1717_, 2, lean_box(0));
lean_closure_set(v___x_1717_, 3, v___f_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1718_, lean_object* v___f_1719_, lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1720_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___f_1719_);
lean_dec_ref(v___y_1718_);
v_a_1722_ = lean_ctor_get(v_x_1720_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1720_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1724_ = v_x_1720_;
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v_x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
}
else
{
lean_object* v_machine_1731_; lean_object* v_requestStream_1732_; lean_object* v_keepAliveTimeout_1733_; lean_object* v_currentTimeout_1734_; lean_object* v_headerTimeout_1735_; lean_object* v_response_1736_; lean_object* v_respStream_1737_; lean_object* v_expectData_1738_; uint8_t v_handlerDispatched_1739_; lean_object* v___x_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_4870__overap_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref_known(v_x_1720_, 1);
v_machine_1731_ = lean_ctor_get(v___y_1718_, 0);
lean_inc_ref(v_machine_1731_);
v_requestStream_1732_ = lean_ctor_get(v___y_1718_, 1);
lean_inc_ref_n(v_requestStream_1732_, 3);
v_keepAliveTimeout_1733_ = lean_ctor_get(v___y_1718_, 2);
lean_inc(v_keepAliveTimeout_1733_);
v_currentTimeout_1734_ = lean_ctor_get(v___y_1718_, 3);
lean_inc(v_currentTimeout_1734_);
v_headerTimeout_1735_ = lean_ctor_get(v___y_1718_, 4);
lean_inc(v_headerTimeout_1735_);
v_response_1736_ = lean_ctor_get(v___y_1718_, 5);
lean_inc_ref(v_response_1736_);
v_respStream_1737_ = lean_ctor_get(v___y_1718_, 6);
lean_inc(v_respStream_1737_);
v_expectData_1738_ = lean_ctor_get(v___y_1718_, 7);
lean_inc(v_expectData_1738_);
v_handlerDispatched_1739_ = lean_ctor_get_uint8(v___y_1718_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1718_);
v___x_1740_ = lean_box(v_handlerDispatched_1739_);
v___f_1741_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1741_, 0, v_machine_1731_);
lean_closure_set(v___f_1741_, 1, v_requestStream_1732_);
lean_closure_set(v___f_1741_, 2, v_keepAliveTimeout_1733_);
lean_closure_set(v___f_1741_, 3, v_currentTimeout_1734_);
lean_closure_set(v___f_1741_, 4, v_headerTimeout_1735_);
lean_closure_set(v___f_1741_, 5, v_response_1736_);
lean_closure_set(v___f_1741_, 6, v_respStream_1737_);
lean_closure_set(v___f_1741_, 7, v_expectData_1738_);
lean_closure_set(v___f_1741_, 8, v___x_1740_);
lean_inc_ref(v___f_1741_);
v___f_1742_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1742_, 0, v___f_1741_);
v___f_1743_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1743_, 0, v_requestStream_1732_);
lean_closure_set(v___f_1743_, 1, v___f_1742_);
lean_closure_set(v___f_1743_, 2, v___f_1741_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = 0;
v___x_1746_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1747_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1748_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1749_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1750_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1750_, 0, lean_box(0));
lean_closure_set(v___x_1750_, 1, lean_box(0));
lean_closure_set(v___x_1750_, 2, v___x_1746_);
lean_closure_set(v___x_1750_, 3, lean_box(0));
lean_closure_set(v___x_1750_, 4, lean_box(0));
lean_closure_set(v___x_1750_, 5, v___x_1749_);
lean_closure_set(v___x_1750_, 6, v___f_1719_);
v___x_4870__overap_1751_ = l_Std_Mutex_atomically___redArg(v___x_1746_, v___f_1747_, v___f_1748_, v_requestStream_1732_, v___x_1750_);
v___x_1752_ = lean_apply_1(v___x_4870__overap_1751_, lean_box(0));
v___x_1753_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1744_, v___x_1745_, v___x_1752_, v___f_1743_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1754_, lean_object* v___f_1755_, lean_object* v_x_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1754_, v___f_1755_, v_x_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1759_, lean_object* v_x_1760_){
_start:
{
if (lean_obj_tag(v_x_1760_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v___y_1759_);
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
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1779_; 
v_isSharedCheck_1779_ = !lean_is_exclusive(v_x_1760_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_x_1760_, 0);
lean_dec(v_unused_1780_);
v___x_1772_ = v_x_1760_;
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v_x_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___y_1759_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1781_, lean_object* v_x_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1781_, v_x_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1785_, lean_object* v___f_1786_, lean_object* v___y_1787_, lean_object* v_x_1788_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v___y_1787_);
lean_dec_ref(v___f_1786_);
lean_dec_ref(v_requestStream_1785_);
v_a_1790_ = lean_ctor_get(v_x_1788_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_x_1788_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1792_ = v_x_1788_;
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v_x_1788_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1813_; 
v_a_1799_ = lean_ctor_get(v_x_1788_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1788_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1801_ = v_x_1788_;
v_isShared_1802_ = v_isSharedCheck_1813_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v_x_1788_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1813_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_unbox(v_a_1799_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; 
lean_del_object(v___x_1801_);
lean_dec_ref(v___y_1787_);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = l_Std_Http_Body_Stream_close(v_requestStream_1785_);
v___x_1806_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
v___x_1807_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1804_, v___x_1806_, v___x_1805_, v___f_1786_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_dec(v_a_1799_);
lean_dec_ref(v___f_1786_);
lean_dec_ref(v_requestStream_1785_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___y_1787_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1808_);
v___x_1810_ = v___x_1801_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1814_, lean_object* v___f_1815_, lean_object* v___y_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1814_, v___f_1815_, v___y_1816_, v_x_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1820_, lean_object* v_machine_1821_, lean_object* v_a_1822_, uint8_t v_requiresData_1823_, lean_object* v_expectData_1824_, lean_object* v_pendingHead_1825_, lean_object* v_x_1826_){
_start:
{
if (lean_obj_tag(v_x_1826_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_pendingHead_1825_);
lean_dec(v_expectData_1824_);
lean_dec_ref(v_a_1822_);
lean_dec_ref(v_machine_1821_);
v_a_1828_ = lean_ctor_get(v_x_1826_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_x_1826_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1830_ = v_x_1826_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v_x_1826_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1851_; 
v_a_1837_ = lean_ctor_get(v_x_1826_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_x_1826_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1839_ = v_x_1826_;
v_isShared_1840_ = v_isSharedCheck_1851_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v_x_1826_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1851_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_keepAliveTimeout_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v_keepAliveTimeout_1841_ = lean_ctor_get(v_config_1820_, 5);
lean_inc_n(v_keepAliveTimeout_1841_, 2);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_keepAliveTimeout_1841_);
v___x_1843_ = lean_box(0);
v___x_1844_ = 0;
v___x_1845_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1845_, 0, v_machine_1821_);
lean_ctor_set(v___x_1845_, 1, v_a_1822_);
lean_ctor_set(v___x_1845_, 2, v___x_1842_);
lean_ctor_set(v___x_1845_, 3, v_keepAliveTimeout_1841_);
lean_ctor_set(v___x_1845_, 4, v___x_1843_);
lean_ctor_set(v___x_1845_, 5, v_a_1837_);
lean_ctor_set(v___x_1845_, 6, v___x_1843_);
lean_ctor_set(v___x_1845_, 7, v_expectData_1824_);
lean_ctor_set(v___x_1845_, 8, v_pendingHead_1825_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*9, v_requiresData_1823_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*9 + 1, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1846_);
v___x_1848_ = v___x_1839_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1852_, lean_object* v_machine_1853_, lean_object* v_a_1854_, lean_object* v_requiresData_1855_, lean_object* v_expectData_1856_, lean_object* v_pendingHead_1857_, lean_object* v_x_1858_, lean_object* v___y_1859_){
_start:
{
uint8_t v_requiresData_boxed_1860_; lean_object* v_res_1861_; 
v_requiresData_boxed_1860_ = lean_unbox(v_requiresData_1855_);
v_res_1861_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1852_, v_machine_1853_, v_a_1854_, v_requiresData_boxed_1860_, v_expectData_1856_, v_pendingHead_1857_, v_x_1858_);
lean_dec_ref(v_config_1852_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1862_, lean_object* v_machine_1863_, uint8_t v_requiresData_1864_, lean_object* v_expectData_1865_, lean_object* v_pendingHead_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_pendingHead_1866_);
lean_dec(v_expectData_1865_);
lean_dec_ref(v_machine_1863_);
lean_dec_ref(v_config_1862_);
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
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1893_; 
v_a_1878_ = lean_ctor_get(v_x_1867_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1880_ = v_x_1867_;
v_isShared_1881_ = v_isSharedCheck_1893_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v_x_1867_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1893_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1882_ = lean_box(v_requiresData_1864_);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1883_, 0, v_config_1862_);
lean_closure_set(v___f_1883_, 1, v_machine_1863_);
lean_closure_set(v___f_1883_, 2, v_a_1878_);
lean_closure_set(v___f_1883_, 3, v___x_1882_);
lean_closure_set(v___f_1883_, 4, v_expectData_1865_);
lean_closure_set(v___f_1883_, 5, v_pendingHead_1866_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = 0;
v___x_1887_ = l_Std_CloseableChannel_new___redArg(v___x_1884_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1887_);
v___x_1889_ = v___x_1880_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
v___x_1891_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1885_, v___x_1886_, v___x_1890_, v___f_1883_);
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1894_, lean_object* v_machine_1895_, lean_object* v_requiresData_1896_, lean_object* v_expectData_1897_, lean_object* v_pendingHead_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v_requiresData_boxed_1901_; lean_object* v_res_1902_; 
v_requiresData_boxed_1901_ = lean_unbox(v_requiresData_1896_);
v_res_1902_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1894_, v_machine_1895_, v_requiresData_boxed_1901_, v_expectData_1897_, v_pendingHead_1898_, v_x_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1903_, lean_object* v_____r_1904_){
_start:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = 0;
v___x_1908_ = l_Std_Http_Body_mkStream();
v___x_1909_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1906_, v___x_1907_, v___x_1908_, v___f_1903_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1910_, lean_object* v_____r_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1910_, v_____r_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1914_, lean_object* v_val_1915_, lean_object* v___f_1916_, lean_object* v___f_1917_, lean_object* v_x_1918_){
_start:
{
if (lean_obj_tag(v_x_1918_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v___f_1917_);
lean_dec_ref(v___f_1916_);
lean_dec(v_val_1915_);
lean_dec_ref(v_close_1914_);
v_a_1920_ = lean_ctor_get(v_x_1918_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_x_1918_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v_x_1918_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v_x_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1929_; uint8_t v___x_1930_; 
v_a_1929_ = lean_ctor_get(v_x_1918_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v_x_1918_, 1);
v___x_1930_ = lean_unbox(v_a_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; 
lean_dec_ref(v___f_1917_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_apply_2(v_close_1914_, v_val_1915_, lean_box(0));
v___x_1933_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
v___x_1934_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1931_, v___x_1933_, v___x_1932_, v___f_1916_);
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec(v_a_1929_);
lean_dec_ref(v___f_1916_);
lean_dec(v_val_1915_);
lean_dec_ref(v_close_1914_);
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_apply_2(v___f_1917_, v___x_1935_, lean_box(0));
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1937_, lean_object* v_val_1938_, lean_object* v___f_1939_, lean_object* v___f_1940_, lean_object* v_x_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1937_, v_val_1938_, v___f_1939_, v___f_1940_, v_x_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1944_, lean_object* v_inst_1945_, lean_object* v___f_1946_, lean_object* v___f_1947_, lean_object* v_____r_1948_){
_start:
{
if (lean_obj_tag(v_respStream_1944_) == 1)
{
lean_object* v_val_1950_; lean_object* v_close_1951_; lean_object* v_isClosed_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_val_1950_ = lean_ctor_get(v_respStream_1944_, 0);
lean_inc_n(v_val_1950_, 2);
lean_dec_ref_known(v_respStream_1944_, 1);
v_close_1951_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc_ref(v_close_1951_);
v_isClosed_1952_ = lean_ctor_get(v_inst_1945_, 2);
lean_inc_ref(v_isClosed_1952_);
lean_dec_ref(v_inst_1945_);
v___f_1953_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1953_, 0, v_close_1951_);
lean_closure_set(v___f_1953_, 1, v_val_1950_);
lean_closure_set(v___f_1953_, 2, v___f_1946_);
lean_closure_set(v___f_1953_, 3, v___f_1947_);
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = 0;
v___x_1956_ = lean_apply_2(v_isClosed_1952_, v_val_1950_, lean_box(0));
v___x_1957_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1954_, v___x_1955_, v___x_1956_, v___f_1953_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v___f_1946_);
lean_dec_ref(v_inst_1945_);
lean_dec(v_respStream_1944_);
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_apply_2(v___f_1947_, v___x_1958_, lean_box(0));
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1960_, lean_object* v_inst_1961_, lean_object* v___f_1962_, lean_object* v___f_1963_, lean_object* v_____r_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1960_, v_inst_1961_, v___f_1962_, v___f_1963_, v_____r_1964_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1967_, lean_object* v_keepAliveTimeout_1968_, lean_object* v_currentTimeout_1969_, lean_object* v_headerTimeout_1970_, lean_object* v_response_1971_, lean_object* v_respStream_1972_, uint8_t v_requiresData_1973_, lean_object* v_expectData_1974_, uint8_t v_handlerDispatched_1975_, lean_object* v_pendingHead_1976_, lean_object* v_x_1977_){
_start:
{
if (lean_obj_tag(v_x_1977_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_pendingHead_1976_);
lean_dec(v_expectData_1974_);
lean_dec(v_respStream_1972_);
lean_dec_ref(v_response_1971_);
lean_dec(v_headerTimeout_1970_);
lean_dec(v_currentTimeout_1969_);
lean_dec(v_keepAliveTimeout_1968_);
lean_dec_ref(v_requestStream_1967_);
v_a_1979_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1981_ = v_x_1977_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v_x_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2009_; 
v_a_1988_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1990_ = v_x_1977_;
v_isShared_1991_ = v_isSharedCheck_2009_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v_x_1977_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2009_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_snd_1992_; uint8_t v___x_1993_; 
v_snd_1992_ = lean_ctor_get(v_a_1988_, 1);
v___x_1993_ = lean_unbox(v_snd_1992_);
if (v___x_1993_ == 0)
{
lean_object* v_fst_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v_fst_1994_ = lean_ctor_get(v_a_1988_, 0);
lean_inc(v_fst_1994_);
lean_dec(v_a_1988_);
v___x_1995_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1995_, 0, v_fst_1994_);
lean_ctor_set(v___x_1995_, 1, v_requestStream_1967_);
lean_ctor_set(v___x_1995_, 2, v_keepAliveTimeout_1968_);
lean_ctor_set(v___x_1995_, 3, v_currentTimeout_1969_);
lean_ctor_set(v___x_1995_, 4, v_headerTimeout_1970_);
lean_ctor_set(v___x_1995_, 5, v_response_1971_);
lean_ctor_set(v___x_1995_, 6, v_respStream_1972_);
lean_ctor_set(v___x_1995_, 7, v_expectData_1974_);
lean_ctor_set(v___x_1995_, 8, v_pendingHead_1976_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*9, v_requiresData_1973_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*9 + 1, v_handlerDispatched_1975_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1996_);
v___x_1998_ = v___x_1990_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
}
else
{
lean_object* v_fst_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec(v_pendingHead_1976_);
v_fst_2001_ = lean_ctor_get(v_a_1988_, 0);
lean_inc(v_fst_2001_);
lean_dec(v_a_1988_);
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2003_, 0, v_fst_2001_);
lean_ctor_set(v___x_2003_, 1, v_requestStream_1967_);
lean_ctor_set(v___x_2003_, 2, v_keepAliveTimeout_1968_);
lean_ctor_set(v___x_2003_, 3, v_currentTimeout_1969_);
lean_ctor_set(v___x_2003_, 4, v_headerTimeout_1970_);
lean_ctor_set(v___x_2003_, 5, v_response_1971_);
lean_ctor_set(v___x_2003_, 6, v_respStream_1972_);
lean_ctor_set(v___x_2003_, 7, v_expectData_1974_);
lean_ctor_set(v___x_2003_, 8, v___x_2002_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*9, v_requiresData_1973_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*9 + 1, v_handlerDispatched_1975_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2004_);
v___x_2006_ = v___x_1990_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
return v___x_2007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2010_, lean_object* v_keepAliveTimeout_2011_, lean_object* v_currentTimeout_2012_, lean_object* v_headerTimeout_2013_, lean_object* v_response_2014_, lean_object* v_respStream_2015_, lean_object* v_requiresData_2016_, lean_object* v_expectData_2017_, lean_object* v_handlerDispatched_2018_, lean_object* v_pendingHead_2019_, lean_object* v_x_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v_requiresData_boxed_2022_; uint8_t v_handlerDispatched_boxed_2023_; lean_object* v_res_2024_; 
v_requiresData_boxed_2022_ = lean_unbox(v_requiresData_2016_);
v_handlerDispatched_boxed_2023_ = lean_unbox(v_handlerDispatched_2018_);
v_res_2024_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2010_, v_keepAliveTimeout_2011_, v_currentTimeout_2012_, v_headerTimeout_2013_, v_response_2014_, v_respStream_2015_, v_requiresData_boxed_2022_, v_expectData_2017_, v_handlerDispatched_boxed_2023_, v_pendingHead_2019_, v_x_2020_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2037_, lean_object* v_inst_2038_, lean_object* v___f_2039_, lean_object* v_handler_2040_, lean_object* v___f_2041_, lean_object* v_inst_2042_, lean_object* v___f_2043_, lean_object* v_connectionContext_2044_, lean_object* v_a_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_){
_start:
{
switch(lean_obj_tag(v_a_2045_))
{
case 0:
{
lean_object* v_head_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_connectionContext_2044_);
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v___f_2041_);
lean_dec(v_handler_2040_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v_inst_2038_);
v_head_2049_ = lean_ctor_get(v_a_2045_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2045_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2051_ = v_a_2045_;
v_isShared_2052_ = v_isSharedCheck_2092_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_head_2049_);
lean_dec(v_a_2045_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2092_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_machine_2053_; lean_object* v_requestStream_2054_; lean_object* v_response_2055_; lean_object* v_respStream_2056_; uint8_t v_requiresData_2057_; lean_object* v_expectData_2058_; uint8_t v_handlerDispatched_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2087_; 
v_machine_2053_ = lean_ctor_get(v___y_2047_, 0);
v_requestStream_2054_ = lean_ctor_get(v___y_2047_, 1);
v_response_2055_ = lean_ctor_get(v___y_2047_, 5);
v_respStream_2056_ = lean_ctor_get(v___y_2047_, 6);
v_requiresData_2057_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*9);
v_expectData_2058_ = lean_ctor_get(v___y_2047_, 7);
v_handlerDispatched_2059_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*9 + 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___y_2047_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; lean_object* v_unused_2089_; lean_object* v_unused_2090_; lean_object* v_unused_2091_; 
v_unused_2088_ = lean_ctor_get(v___y_2047_, 8);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v___y_2047_, 4);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v___y_2047_, 3);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v___y_2047_, 2);
lean_dec(v_unused_2091_);
v___x_2061_ = v___y_2047_;
v_isShared_2062_ = v_isSharedCheck_2087_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_expectData_2058_);
lean_inc(v_respStream_2056_);
lean_inc(v_response_2055_);
lean_inc(v_requestStream_2054_);
lean_inc(v_machine_2053_);
lean_dec(v___y_2047_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2087_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_lingeringTimeout_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v_lingeringTimeout_2063_ = lean_ctor_get(v_config_2037_, 4);
lean_inc(v_lingeringTimeout_2063_);
lean_dec_ref(v_config_2037_);
v___x_2064_ = lean_box(0);
lean_inc(v_head_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 1);
v___x_2066_ = v___x_2051_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_head_2049_);
v___x_2066_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
lean_inc_ref(v_requestStream_2054_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 8, v___x_2066_);
lean_ctor_set(v___x_2061_, 4, v___x_2064_);
lean_ctor_set(v___x_2061_, 3, v_lingeringTimeout_2063_);
lean_ctor_set(v___x_2061_, 2, v___x_2064_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_machine_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_requestStream_2054_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_lingeringTimeout_2063_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2085_, 5, v_response_2055_);
lean_ctor_set(v_reuseFailAlloc_2085_, 6, v_respStream_2056_);
lean_ctor_set(v_reuseFailAlloc_2085_, 7, v_expectData_2058_);
lean_ctor_set(v_reuseFailAlloc_2085_, 8, v___x_2066_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*9, v_requiresData_2057_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*9 + 1, v_handlerDispatched_2059_);
v___x_2068_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
uint8_t v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = 0;
v___x_2070_ = 1;
v___x_2071_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2069_, v_head_2049_, v___x_2070_);
lean_dec(v_head_2049_);
if (lean_obj_tag(v___x_2071_) == 1)
{
lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___x_5061__overap_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___f_2072_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2072_, 0, v___x_2068_);
v___f_2073_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2073_, 0, v___x_2071_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = 0;
v___x_2076_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2077_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2078_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_2079_ = l_Std_Mutex_atomically___redArg(v___x_2076_, v___f_2077_, v___f_2078_, v_requestStream_2054_, v___f_2073_);
v___x_2080_ = lean_apply_1(v___x_5061__overap_2079_, lean_box(0));
v___x_2081_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2074_, v___x_2075_, v___x_2080_, v___f_2072_);
return v___x_2081_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec(v___x_2071_);
lean_dec_ref(v_requestStream_2054_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2068_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_connectionContext_2044_);
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v___f_2041_);
lean_dec(v_handler_2040_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v_inst_2038_);
lean_dec_ref(v_config_2037_);
v_size_2093_ = lean_ctor_get(v_a_2045_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_a_2045_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2095_ = v_a_2045_;
v_isShared_2096_ = v_isSharedCheck_2120_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_size_2093_);
lean_dec(v_a_2045_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2120_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_machine_2097_; lean_object* v_requestStream_2098_; lean_object* v_keepAliveTimeout_2099_; lean_object* v_currentTimeout_2100_; lean_object* v_headerTimeout_2101_; lean_object* v_response_2102_; lean_object* v_respStream_2103_; uint8_t v_handlerDispatched_2104_; lean_object* v_pendingHead_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2118_; 
v_machine_2097_ = lean_ctor_get(v___y_2047_, 0);
v_requestStream_2098_ = lean_ctor_get(v___y_2047_, 1);
v_keepAliveTimeout_2099_ = lean_ctor_get(v___y_2047_, 2);
v_currentTimeout_2100_ = lean_ctor_get(v___y_2047_, 3);
v_headerTimeout_2101_ = lean_ctor_get(v___y_2047_, 4);
v_response_2102_ = lean_ctor_get(v___y_2047_, 5);
v_respStream_2103_ = lean_ctor_get(v___y_2047_, 6);
v_handlerDispatched_2104_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*9 + 1);
v_pendingHead_2105_ = lean_ctor_get(v___y_2047_, 8);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___y_2047_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v___y_2047_, 7);
lean_dec(v_unused_2119_);
v___x_2107_ = v___y_2047_;
v_isShared_2108_ = v_isSharedCheck_2118_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_pendingHead_2105_);
lean_inc(v_respStream_2103_);
lean_inc(v_response_2102_);
lean_inc(v_headerTimeout_2101_);
lean_inc(v_currentTimeout_2100_);
lean_inc(v_keepAliveTimeout_2099_);
lean_inc(v_requestStream_2098_);
lean_inc(v_machine_2097_);
lean_dec(v___y_2047_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2118_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
uint8_t v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = 1;
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 7, v_size_2093_);
v___x_2111_ = v___x_2107_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_machine_2097_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_requestStream_2098_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_keepAliveTimeout_2099_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_currentTimeout_2100_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_headerTimeout_2101_);
lean_ctor_set(v_reuseFailAlloc_2117_, 5, v_response_2102_);
lean_ctor_set(v_reuseFailAlloc_2117_, 6, v_respStream_2103_);
lean_ctor_set(v_reuseFailAlloc_2117_, 7, v_size_2093_);
lean_ctor_set(v_reuseFailAlloc_2117_, 8, v_pendingHead_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*9 + 1, v_handlerDispatched_2104_);
v___x_2111_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2113_; 
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*9, v___x_2109_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2111_);
v___x_2113_ = v___x_2095_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2121_; lean_object* v_onFailure_2122_; lean_object* v___f_2123_; lean_object* v___y_2125_; 
lean_dec_ref(v_connectionContext_2044_);
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v___f_2041_);
lean_dec_ref(v_config_2037_);
v_err_2121_ = lean_ctor_get(v_a_2045_, 0);
lean_inc(v_err_2121_);
lean_dec_ref_known(v_a_2045_, 1);
v_onFailure_2122_ = lean_ctor_get(v_inst_2038_, 2);
lean_inc_ref(v_onFailure_2122_);
lean_dec_ref(v_inst_2038_);
v___f_2123_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2123_, 0, v___y_2047_);
lean_closure_set(v___f_2123_, 1, v___f_2039_);
switch(lean_obj_tag(v_err_2121_))
{
case 0:
{
lean_object* v___x_2131_; 
v___x_2131_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2125_ = v___x_2131_;
goto v___jp_2124_;
}
case 1:
{
lean_object* v___x_2132_; 
v___x_2132_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2125_ = v___x_2132_;
goto v___jp_2124_;
}
case 2:
{
lean_object* v___x_2133_; 
v___x_2133_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2125_ = v___x_2133_;
goto v___jp_2124_;
}
case 3:
{
lean_object* v___x_2134_; 
v___x_2134_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2125_ = v___x_2134_;
goto v___jp_2124_;
}
case 4:
{
lean_object* v___x_2135_; 
v___x_2135_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2125_ = v___x_2135_;
goto v___jp_2124_;
}
case 5:
{
lean_object* v___x_2136_; 
v___x_2136_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2125_ = v___x_2136_;
goto v___jp_2124_;
}
case 6:
{
lean_object* v___x_2137_; 
v___x_2137_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2125_ = v___x_2137_;
goto v___jp_2124_;
}
case 7:
{
lean_object* v___x_2138_; 
v___x_2138_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2125_ = v___x_2138_;
goto v___jp_2124_;
}
case 8:
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2125_ = v___x_2139_;
goto v___jp_2124_;
}
case 9:
{
lean_object* v___x_2140_; 
v___x_2140_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2125_ = v___x_2140_;
goto v___jp_2124_;
}
case 10:
{
lean_object* v___x_2141_; 
v___x_2141_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2125_ = v___x_2141_;
goto v___jp_2124_;
}
default: 
{
lean_object* v_message_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_message_2142_ = lean_ctor_get(v_err_2121_, 0);
lean_inc_ref(v_message_2142_);
lean_dec_ref_known(v_err_2121_, 1);
v___x_2143_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2144_ = lean_string_append(v___x_2143_, v_message_2142_);
lean_dec_ref(v_message_2142_);
v___y_2125_ = v___x_2144_;
goto v___jp_2124_;
}
}
v___jp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2126_ = lean_mk_io_user_error(v___y_2125_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = 0;
v___x_2129_ = lean_apply_3(v_onFailure_2122_, v_handler_2040_, v___x_2126_, lean_box(0));
v___x_2130_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2127_, v___x_2128_, v___x_2129_, v___f_2123_);
return v___x_2130_;
}
}
case 4:
{
lean_object* v_requestStream_2145_; lean_object* v___f_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___f_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_5118__overap_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_connectionContext_2044_);
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec(v_handler_2040_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v_inst_2038_);
lean_dec_ref(v_config_2037_);
v_requestStream_2145_ = lean_ctor_get(v___y_2047_, 1);
lean_inc_ref_n(v_requestStream_2145_, 2);
lean_inc_ref(v___y_2047_);
v___f_2146_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2146_, 0, v___y_2047_);
v___f_2147_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2147_, 0, v_requestStream_2145_);
lean_closure_set(v___f_2147_, 1, v___f_2146_);
lean_closure_set(v___f_2147_, 2, v___y_2047_);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = 0;
v___x_2150_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2151_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2152_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2153_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2154_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2154_, 0, lean_box(0));
lean_closure_set(v___x_2154_, 1, lean_box(0));
lean_closure_set(v___x_2154_, 2, v___x_2150_);
lean_closure_set(v___x_2154_, 3, lean_box(0));
lean_closure_set(v___x_2154_, 4, lean_box(0));
lean_closure_set(v___x_2154_, 5, v___x_2153_);
lean_closure_set(v___x_2154_, 6, v___f_2041_);
v___x_5118__overap_2155_ = l_Std_Mutex_atomically___redArg(v___x_2150_, v___f_2151_, v___f_2152_, v_requestStream_2145_, v___x_2154_);
v___x_2156_ = lean_apply_1(v___x_5118__overap_2155_, lean_box(0));
v___x_2157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2148_, v___x_2149_, v___x_2156_, v___f_2147_);
return v___x_2157_;
}
case 6:
{
lean_object* v_machine_2158_; lean_object* v_requestStream_2159_; lean_object* v_respStream_2160_; uint8_t v_requiresData_2161_; lean_object* v_expectData_2162_; lean_object* v_pendingHead_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_5143__overap_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v_connectionContext_2044_);
lean_dec_ref(v___f_2041_);
lean_dec(v_handler_2040_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v_inst_2038_);
v_machine_2158_ = lean_ctor_get(v___y_2047_, 0);
lean_inc_ref(v_machine_2158_);
v_requestStream_2159_ = lean_ctor_get(v___y_2047_, 1);
lean_inc_ref_n(v_requestStream_2159_, 2);
v_respStream_2160_ = lean_ctor_get(v___y_2047_, 6);
lean_inc(v_respStream_2160_);
v_requiresData_2161_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*9);
v_expectData_2162_ = lean_ctor_get(v___y_2047_, 7);
lean_inc(v_expectData_2162_);
v_pendingHead_2163_ = lean_ctor_get(v___y_2047_, 8);
lean_inc(v_pendingHead_2163_);
lean_dec_ref(v___y_2047_);
v___x_2164_ = lean_box(v_requiresData_2161_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2165_, 0, v_config_2037_);
lean_closure_set(v___f_2165_, 1, v_machine_2158_);
lean_closure_set(v___f_2165_, 2, v___x_2164_);
lean_closure_set(v___f_2165_, 3, v_expectData_2162_);
lean_closure_set(v___f_2165_, 4, v_pendingHead_2163_);
v___f_2166_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2166_, 0, v___f_2165_);
lean_inc_ref(v___f_2166_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2167_, 0, v___f_2166_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2168_, 0, v_respStream_2160_);
lean_closure_set(v___f_2168_, 1, v_inst_2042_);
lean_closure_set(v___f_2168_, 2, v___f_2167_);
lean_closure_set(v___f_2168_, 3, v___f_2166_);
lean_inc_ref(v___f_2168_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2169_, 0, v___f_2168_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2170_, 0, v_requestStream_2159_);
lean_closure_set(v___f_2170_, 1, v___f_2169_);
lean_closure_set(v___f_2170_, 2, v___f_2168_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = 0;
v___x_2173_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2174_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2175_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2176_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2177_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2177_, 0, lean_box(0));
lean_closure_set(v___x_2177_, 1, lean_box(0));
lean_closure_set(v___x_2177_, 2, v___x_2173_);
lean_closure_set(v___x_2177_, 3, lean_box(0));
lean_closure_set(v___x_2177_, 4, lean_box(0));
lean_closure_set(v___x_2177_, 5, v___x_2176_);
lean_closure_set(v___x_2177_, 6, v___f_2043_);
v___x_5143__overap_2178_ = l_Std_Mutex_atomically___redArg(v___x_2173_, v___f_2174_, v___f_2175_, v_requestStream_2159_, v___x_2177_);
v___x_2179_ = lean_apply_1(v___x_5143__overap_2178_, lean_box(0));
v___x_2180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2171_, v___x_2172_, v___x_2179_, v___f_2170_);
return v___x_2180_;
}
case 7:
{
lean_object* v_pendingHead_2181_; 
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v___f_2041_);
lean_dec_ref(v___f_2039_);
v_pendingHead_2181_ = lean_ctor_get(v___y_2047_, 8);
if (lean_obj_tag(v_pendingHead_2181_) == 1)
{
lean_object* v_machine_2182_; lean_object* v_requestStream_2183_; lean_object* v_keepAliveTimeout_2184_; lean_object* v_currentTimeout_2185_; lean_object* v_headerTimeout_2186_; lean_object* v_response_2187_; lean_object* v_respStream_2188_; uint8_t v_requiresData_2189_; lean_object* v_expectData_2190_; uint8_t v_handlerDispatched_2191_; lean_object* v_val_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_inc_ref(v_pendingHead_2181_);
v_machine_2182_ = lean_ctor_get(v___y_2047_, 0);
lean_inc_ref(v_machine_2182_);
v_requestStream_2183_ = lean_ctor_get(v___y_2047_, 1);
lean_inc_ref(v_requestStream_2183_);
v_keepAliveTimeout_2184_ = lean_ctor_get(v___y_2047_, 2);
lean_inc(v_keepAliveTimeout_2184_);
v_currentTimeout_2185_ = lean_ctor_get(v___y_2047_, 3);
lean_inc(v_currentTimeout_2185_);
v_headerTimeout_2186_ = lean_ctor_get(v___y_2047_, 4);
lean_inc(v_headerTimeout_2186_);
v_response_2187_ = lean_ctor_get(v___y_2047_, 5);
lean_inc_ref(v_response_2187_);
v_respStream_2188_ = lean_ctor_get(v___y_2047_, 6);
lean_inc(v_respStream_2188_);
v_requiresData_2189_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*9);
v_expectData_2190_ = lean_ctor_get(v___y_2047_, 7);
lean_inc(v_expectData_2190_);
v_handlerDispatched_2191_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2047_);
v_val_2192_ = lean_ctor_get(v_pendingHead_2181_, 0);
lean_inc(v_val_2192_);
v___x_2193_ = lean_box(v_requiresData_2189_);
v___x_2194_ = lean_box(v_handlerDispatched_2191_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2195_, 0, v_requestStream_2183_);
lean_closure_set(v___f_2195_, 1, v_keepAliveTimeout_2184_);
lean_closure_set(v___f_2195_, 2, v_currentTimeout_2185_);
lean_closure_set(v___f_2195_, 3, v_headerTimeout_2186_);
lean_closure_set(v___f_2195_, 4, v_response_2187_);
lean_closure_set(v___f_2195_, 5, v_respStream_2188_);
lean_closure_set(v___f_2195_, 6, v___x_2193_);
lean_closure_set(v___f_2195_, 7, v_expectData_2190_);
lean_closure_set(v___f_2195_, 8, v___x_2194_);
lean_closure_set(v___f_2195_, 9, v_pendingHead_2181_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = 0;
v___x_2198_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2038_, v_handler_2040_, v_machine_2182_, v_val_2192_, v_config_2037_, v_connectionContext_2044_);
v___x_2199_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2196_, v___x_2197_, v___x_2198_, v___f_2195_);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_connectionContext_2044_);
lean_dec(v_handler_2040_);
lean_dec_ref(v_inst_2038_);
lean_dec_ref(v_config_2037_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___y_2047_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
default: 
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_a_2045_);
lean_dec_ref(v_connectionContext_2044_);
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v___f_2041_);
lean_dec(v_handler_2040_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v_inst_2038_);
lean_dec_ref(v_config_2037_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___y_2047_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2206_, lean_object* v_inst_2207_, lean_object* v___f_2208_, lean_object* v_handler_2209_, lean_object* v___f_2210_, lean_object* v_inst_2211_, lean_object* v___f_2212_, lean_object* v_connectionContext_2213_, lean_object* v_a_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2206_, v_inst_2207_, v___f_2208_, v_handler_2209_, v___f_2210_, v_inst_2211_, v___f_2212_, v_connectionContext_2213_, v_a_2214_, v_x_2215_, v___y_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_x_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_handler_2229_, lean_object* v_config_2230_, lean_object* v_connectionContext_2231_, lean_object* v_events_2232_, lean_object* v_state_2233_){
_start:
{
lean_object* v___f_2235_; lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; size_t v_sz_2239_; size_t v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_4072__overap_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___f_2235_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2236_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2236_, 0, v_config_2230_);
lean_closure_set(v___f_2236_, 1, v_inst_2227_);
lean_closure_set(v___f_2236_, 2, v___f_2235_);
lean_closure_set(v___f_2236_, 3, v_handler_2229_);
lean_closure_set(v___f_2236_, 4, v___f_2235_);
lean_closure_set(v___f_2236_, 5, v_inst_2228_);
lean_closure_set(v___f_2236_, 6, v___f_2235_);
lean_closure_set(v___f_2236_, 7, v_connectionContext_2231_);
v___f_2237_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2238_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2239_ = lean_array_size(v_events_2232_);
v___x_2240_ = ((size_t)0ULL);
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = 0;
v___x_4072__overap_2243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2238_, v_events_2232_, v___f_2236_, v_sz_2239_, v___x_2240_, v_state_2233_);
v___x_2244_ = lean_apply_1(v___x_4072__overap_2243_, lean_box(0));
v___x_2245_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2241_, v___x_2242_, v___x_2244_, v___f_2237_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_handler_2248_, lean_object* v_config_2249_, lean_object* v_connectionContext_2250_, lean_object* v_events_2251_, lean_object* v_state_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2246_, v_inst_2247_, v_handler_2248_, v_config_2249_, v_connectionContext_2250_, v_events_2251_, v_state_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2255_, lean_object* v_00_u03b2_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_handler_2259_, lean_object* v_config_2260_, lean_object* v_connectionContext_2261_, lean_object* v_events_2262_, lean_object* v_state_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2257_, v_inst_2258_, v_handler_2259_, v_config_2260_, v_connectionContext_2261_, v_events_2262_, v_state_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2266_, lean_object* v_00_u03b2_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_handler_2270_, lean_object* v_config_2271_, lean_object* v_connectionContext_2272_, lean_object* v_events_2273_, lean_object* v_state_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2266_, v_00_u03b2_2267_, v_inst_2268_, v_inst_2269_, v_handler_2270_, v_config_2271_, v_connectionContext_2272_, v_events_2273_, v_state_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v_x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v_x_2277_, 1);
v___x_2279_ = lean_task_pure(v_a_2278_);
return v___x_2279_;
}
else
{
lean_object* v_a_2280_; 
v_a_2280_ = lean_ctor_get(v_x_2277_, 0);
lean_inc_ref(v_a_2280_);
lean_dec_ref_known(v_x_2277_, 1);
return v_a_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2281_, lean_object* v_requestStream_2282_, lean_object* v_keepAliveTimeout_2283_, lean_object* v_currentTimeout_2284_, lean_object* v_headerTimeout_2285_, lean_object* v_response_2286_, lean_object* v_respStream_2287_, uint8_t v_requiresData_2288_, lean_object* v_expectData_2289_, lean_object* v_x_2290_){
_start:
{
if (lean_obj_tag(v_x_2290_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_expectData_2289_);
lean_dec(v_respStream_2287_);
lean_dec_ref(v_response_2286_);
lean_dec(v_headerTimeout_2285_);
lean_dec(v_currentTimeout_2284_);
lean_dec(v_keepAliveTimeout_2283_);
lean_dec_ref(v_requestStream_2282_);
lean_dec_ref(v_machine_2281_);
v_a_2292_ = lean_ctor_get(v_x_2290_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_x_2290_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v_x_2290_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v_x_2290_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
else
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2311_; 
v_isSharedCheck_2311_ = !lean_is_exclusive(v_x_2290_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v_x_2290_, 0);
lean_dec(v_unused_2312_);
v___x_2302_ = v_x_2290_;
v_isShared_2303_ = v_isSharedCheck_2311_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v_x_2290_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2311_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2304_ = 1;
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2306_, 0, v_machine_2281_);
lean_ctor_set(v___x_2306_, 1, v_requestStream_2282_);
lean_ctor_set(v___x_2306_, 2, v_keepAliveTimeout_2283_);
lean_ctor_set(v___x_2306_, 3, v_currentTimeout_2284_);
lean_ctor_set(v___x_2306_, 4, v_headerTimeout_2285_);
lean_ctor_set(v___x_2306_, 5, v_response_2286_);
lean_ctor_set(v___x_2306_, 6, v_respStream_2287_);
lean_ctor_set(v___x_2306_, 7, v_expectData_2289_);
lean_ctor_set(v___x_2306_, 8, v___x_2305_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*9, v_requiresData_2288_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*9 + 1, v___x_2304_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2306_);
v___x_2308_ = v___x_2302_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2313_, lean_object* v_requestStream_2314_, lean_object* v_keepAliveTimeout_2315_, lean_object* v_currentTimeout_2316_, lean_object* v_headerTimeout_2317_, lean_object* v_response_2318_, lean_object* v_respStream_2319_, lean_object* v_requiresData_2320_, lean_object* v_expectData_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_){
_start:
{
uint8_t v_requiresData_boxed_2324_; lean_object* v_res_2325_; 
v_requiresData_boxed_2324_ = lean_unbox(v_requiresData_2320_);
v_res_2325_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2313_, v_requestStream_2314_, v_keepAliveTimeout_2315_, v_currentTimeout_2316_, v_headerTimeout_2317_, v_response_2318_, v_respStream_2319_, v_requiresData_boxed_2324_, v_expectData_2321_, v_x_2322_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2326_, lean_object* v_response_2327_, lean_object* v___x_2328_, lean_object* v___f_2329_, lean_object* v_x_2330_){
_start:
{
if (lean_obj_tag(v_x_2330_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v___f_2329_);
lean_dec(v___x_2328_);
lean_dec_ref(v_response_2327_);
lean_dec_ref(v_toFunctor_2326_);
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
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2355_; 
v_a_2341_ = lean_ctor_get(v_x_2330_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_x_2330_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2343_ = v_x_2330_;
v_isShared_2344_ = v_isSharedCheck_2355_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v_x_2330_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2355_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2345_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2345_, 0, lean_box(0));
lean_closure_set(v___x_2345_, 1, lean_box(0));
lean_closure_set(v___x_2345_, 2, v_toFunctor_2326_);
v___x_2346_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2346_, 0, lean_box(0));
lean_closure_set(v___x_2346_, 1, v_response_2327_);
v___x_2347_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2347_, 0, lean_box(0));
lean_closure_set(v___x_2347_, 1, lean_box(0));
lean_closure_set(v___x_2347_, 2, lean_box(0));
lean_closure_set(v___x_2347_, 3, v___x_2345_);
lean_closure_set(v___x_2347_, 4, v___x_2346_);
v___x_2348_ = 0;
lean_inc(v___x_2328_);
v___x_2349_ = l_BaseIO_chainTask___redArg(v_a_2341_, v___x_2347_, v___x_2328_, v___x_2348_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2349_);
v___x_2351_ = v___x_2343_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
v___x_2353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2328_, v___x_2348_, v___x_2352_, v___f_2329_);
return v___x_2353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2356_, lean_object* v_response_2357_, lean_object* v___x_2358_, lean_object* v___f_2359_, lean_object* v_x_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2356_, v_response_2357_, v___x_2358_, v___f_2359_, v_x_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2364_, lean_object* v_handler_2365_, lean_object* v_extensions_2366_, lean_object* v_connectionContext_2367_, lean_object* v_state_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v_toApplicative_2371_; lean_object* v_pendingHead_2372_; 
v___x_2370_ = l_instMonadBaseIO;
v_toApplicative_2371_ = lean_ctor_get(v___x_2370_, 0);
v_pendingHead_2372_ = lean_ctor_get(v_state_2368_, 8);
lean_inc(v_pendingHead_2372_);
if (lean_obj_tag(v_pendingHead_2372_) == 1)
{
lean_object* v_toFunctor_2373_; lean_object* v_machine_2374_; lean_object* v_requestStream_2375_; lean_object* v_keepAliveTimeout_2376_; lean_object* v_currentTimeout_2377_; lean_object* v_headerTimeout_2378_; lean_object* v_response_2379_; lean_object* v_respStream_2380_; uint8_t v_requiresData_2381_; lean_object* v_expectData_2382_; lean_object* v_val_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2405_; 
v_toFunctor_2373_ = lean_ctor_get(v_toApplicative_2371_, 0);
v_machine_2374_ = lean_ctor_get(v_state_2368_, 0);
lean_inc_ref(v_machine_2374_);
v_requestStream_2375_ = lean_ctor_get(v_state_2368_, 1);
lean_inc_ref(v_requestStream_2375_);
v_keepAliveTimeout_2376_ = lean_ctor_get(v_state_2368_, 2);
lean_inc(v_keepAliveTimeout_2376_);
v_currentTimeout_2377_ = lean_ctor_get(v_state_2368_, 3);
lean_inc(v_currentTimeout_2377_);
v_headerTimeout_2378_ = lean_ctor_get(v_state_2368_, 4);
lean_inc(v_headerTimeout_2378_);
v_response_2379_ = lean_ctor_get(v_state_2368_, 5);
lean_inc_ref(v_response_2379_);
v_respStream_2380_ = lean_ctor_get(v_state_2368_, 6);
lean_inc(v_respStream_2380_);
v_requiresData_2381_ = lean_ctor_get_uint8(v_state_2368_, sizeof(void*)*9);
v_expectData_2382_ = lean_ctor_get(v_state_2368_, 7);
lean_inc(v_expectData_2382_);
lean_dec_ref(v_state_2368_);
v_val_2383_ = lean_ctor_get(v_pendingHead_2372_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_pendingHead_2372_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2385_ = v_pendingHead_2372_;
v_isShared_2386_ = v_isSharedCheck_2405_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_val_2383_);
lean_dec(v_pendingHead_2372_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2405_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v_onRequest_2387_; lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
v_onRequest_2387_ = lean_ctor_get(v_inst_2364_, 1);
lean_inc_ref(v_onRequest_2387_);
lean_dec_ref(v_inst_2364_);
v___f_2388_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2389_ = lean_box(v_requiresData_2381_);
lean_inc_ref(v_response_2379_);
lean_inc_ref(v_requestStream_2375_);
v___f_2390_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2390_, 0, v_machine_2374_);
lean_closure_set(v___f_2390_, 1, v_requestStream_2375_);
lean_closure_set(v___f_2390_, 2, v_keepAliveTimeout_2376_);
lean_closure_set(v___f_2390_, 3, v_currentTimeout_2377_);
lean_closure_set(v___f_2390_, 4, v_headerTimeout_2378_);
lean_closure_set(v___f_2390_, 5, v_response_2379_);
lean_closure_set(v___f_2390_, 6, v_respStream_2380_);
lean_closure_set(v___f_2390_, 7, v___x_2389_);
lean_closure_set(v___f_2390_, 8, v_expectData_2382_);
v___x_2391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2391_, 0, v_val_2383_);
lean_ctor_set(v___x_2391_, 1, v_requestStream_2375_);
lean_ctor_set(v___x_2391_, 2, v_extensions_2366_);
v___x_2392_ = lean_apply_3(v_onRequest_2387_, v_handler_2365_, v___x_2391_, v_connectionContext_2367_);
v___x_2393_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2373_);
v___f_2394_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2394_, 0, v_toFunctor_2373_);
lean_closure_set(v___f_2394_, 1, v_response_2379_);
lean_closure_set(v___f_2394_, 2, v___x_2393_);
lean_closure_set(v___f_2394_, 3, v___f_2390_);
v___x_2395_ = 0;
v___x_2396_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2396_, 0, lean_box(0));
lean_closure_set(v___x_2396_, 1, v___x_2392_);
v___x_2397_ = lean_io_as_task(v___x_2396_, v___x_2393_);
v___x_2398_ = 1;
v___x_2399_ = lean_task_bind(v___x_2397_, v___f_2388_, v___x_2393_, v___x_2398_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2399_);
v___x_2401_ = v___x_2385_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
v___x_2403_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2393_, v___x_2395_, v___x_2402_, v___f_2394_);
return v___x_2403_;
}
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_pendingHead_2372_);
lean_dec_ref(v_connectionContext_2367_);
lean_dec(v_extensions_2366_);
lean_dec(v_handler_2365_);
lean_dec_ref(v_inst_2364_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v_state_2368_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2408_, lean_object* v_handler_2409_, lean_object* v_extensions_2410_, lean_object* v_connectionContext_2411_, lean_object* v_state_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2408_, v_handler_2409_, v_extensions_2410_, v_connectionContext_2411_, v_state_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2415_, lean_object* v_inst_2416_, lean_object* v_handler_2417_, lean_object* v_extensions_2418_, lean_object* v_connectionContext_2419_, lean_object* v_state_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2416_, v_handler_2417_, v_extensions_2418_, v_connectionContext_2419_, v_state_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2423_, lean_object* v_inst_2424_, lean_object* v_handler_2425_, lean_object* v_extensions_2426_, lean_object* v_connectionContext_2427_, lean_object* v_state_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2423_, v_inst_2424_, v_handler_2425_, v_extensions_2426_, v_connectionContext_2427_, v_state_2428_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2431_, lean_object* v_____r_2432_){
_start:
{
lean_object* v_writer_2434_; lean_object* v_reader_2435_; lean_object* v_config_2436_; lean_object* v_events_2437_; lean_object* v_error_2438_; lean_object* v_instant_2439_; uint8_t v_keepAlive_2440_; uint8_t v_forcedFlush_2441_; uint8_t v_pullBodyStalled_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2469_; 
v_writer_2434_ = lean_ctor_get(v_machine_2431_, 1);
v_reader_2435_ = lean_ctor_get(v_machine_2431_, 0);
v_config_2436_ = lean_ctor_get(v_machine_2431_, 2);
v_events_2437_ = lean_ctor_get(v_machine_2431_, 3);
v_error_2438_ = lean_ctor_get(v_machine_2431_, 4);
v_instant_2439_ = lean_ctor_get(v_machine_2431_, 5);
v_keepAlive_2440_ = lean_ctor_get_uint8(v_machine_2431_, sizeof(void*)*6);
v_forcedFlush_2441_ = lean_ctor_get_uint8(v_machine_2431_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2442_ = lean_ctor_get_uint8(v_machine_2431_, sizeof(void*)*6 + 2);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_machine_2431_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2444_ = v_machine_2431_;
v_isShared_2445_ = v_isSharedCheck_2469_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_instant_2439_);
lean_inc(v_error_2438_);
lean_inc(v_events_2437_);
lean_inc(v_config_2436_);
lean_inc(v_writer_2434_);
lean_inc(v_reader_2435_);
lean_dec(v_machine_2431_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2469_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v_userData_2446_; lean_object* v_outputData_2447_; lean_object* v_state_2448_; lean_object* v_knownSize_2449_; lean_object* v_messageHead_2450_; uint8_t v_sentMessage_2451_; uint8_t v_omitBody_2452_; lean_object* v_userDataBytes_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2468_; 
v_userData_2446_ = lean_ctor_get(v_writer_2434_, 0);
v_outputData_2447_ = lean_ctor_get(v_writer_2434_, 1);
v_state_2448_ = lean_ctor_get(v_writer_2434_, 2);
v_knownSize_2449_ = lean_ctor_get(v_writer_2434_, 3);
v_messageHead_2450_ = lean_ctor_get(v_writer_2434_, 4);
v_sentMessage_2451_ = lean_ctor_get_uint8(v_writer_2434_, sizeof(void*)*6);
v_omitBody_2452_ = lean_ctor_get_uint8(v_writer_2434_, sizeof(void*)*6 + 2);
v_userDataBytes_2453_ = lean_ctor_get(v_writer_2434_, 5);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_writer_2434_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2455_ = v_writer_2434_;
v_isShared_2456_ = v_isSharedCheck_2468_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_userDataBytes_2453_);
lean_inc(v_messageHead_2450_);
lean_inc(v_knownSize_2449_);
lean_inc(v_state_2448_);
lean_inc(v_outputData_2447_);
lean_inc(v_userData_2446_);
lean_dec(v_writer_2434_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2468_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
uint8_t v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = 1;
if (v_isShared_2456_ == 0)
{
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_userData_2446_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_outputData_2447_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_state_2448_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_knownSize_2449_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_messageHead_2450_);
lean_ctor_set(v_reuseFailAlloc_2467_, 5, v_userDataBytes_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2467_, sizeof(void*)*6, v_sentMessage_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2467_, sizeof(void*)*6 + 2, v_omitBody_2452_);
v___x_2459_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2461_; 
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*6 + 1, v___x_2457_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2459_);
v___x_2461_ = v___x_2444_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_reader_2435_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_config_2436_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_events_2437_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_error_2438_);
lean_ctor_set(v_reuseFailAlloc_2466_, 5, v_instant_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, sizeof(void*)*6, v_keepAlive_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, sizeof(void*)*6 + 1, v_forcedFlush_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, sizeof(void*)*6 + 2, v_pullBodyStalled_2442_);
v___x_2461_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2470_, lean_object* v_____r_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2470_, v_____r_2471_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2474_, lean_object* v_x2_2475_){
_start:
{
lean_object* v_data_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_data_2476_ = lean_ctor_get(v_x2_2475_, 0);
v___x_2477_ = lean_byte_array_size(v_data_2476_);
v___x_2478_ = lean_nat_add(v_x1_2474_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2479_, lean_object* v_x2_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2479_, v_x2_2480_);
lean_dec_ref(v_x2_2480_);
lean_dec(v_x1_2479_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2482_, lean_object* v_machine_2483_, lean_object* v_isClosed_2484_, lean_object* v___f_2485_, lean_object* v___f_2486_, lean_object* v_x_2487_){
_start:
{
lean_object* v___y_2490_; 
if (lean_obj_tag(v_x_2487_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v___f_2486_);
lean_dec_ref(v___f_2485_);
lean_dec_ref(v_isClosed_2484_);
lean_dec_ref(v_machine_2483_);
lean_dec(v_body_2482_);
v_a_2495_ = lean_ctor_get(v_x_2487_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_x_2487_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2497_ = v_x_2487_;
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v_x_2487_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2567_; 
v_a_2504_ = lean_ctor_get(v_x_2487_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_x_2487_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2506_ = v_x_2487_;
v_isShared_2507_ = v_isSharedCheck_2567_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v_x_2487_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2567_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
if (lean_obj_tag(v_a_2504_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_dec_ref(v___f_2486_);
lean_dec_ref(v___f_2485_);
lean_dec_ref(v_isClosed_2484_);
v___x_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_body_2482_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_machine_2483_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2509_);
v___x_2511_ = v___x_2506_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2509_);
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
else
{
lean_object* v_val_2514_; 
lean_del_object(v___x_2506_);
v_val_2514_ = lean_ctor_get(v_a_2504_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v_a_2504_, 1);
if (lean_obj_tag(v_val_2514_) == 0)
{
lean_object* v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec_ref(v___f_2486_);
lean_dec_ref(v_machine_2483_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = 0;
v___x_2517_ = lean_apply_2(v_isClosed_2484_, v_body_2482_, lean_box(0));
v___x_2518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2515_, v___x_2516_, v___x_2517_, v___f_2485_);
return v___x_2518_;
}
else
{
lean_object* v_val_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
lean_dec_ref(v___f_2485_);
lean_dec_ref(v_isClosed_2484_);
v_val_2519_ = lean_ctor_get(v_val_2514_, 0);
lean_inc(v_val_2519_);
lean_dec_ref_known(v_val_2514_, 1);
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = lean_mk_empty_array_with_capacity(v___x_2520_);
v___x_2522_ = lean_array_push(v___x_2521_, v_val_2519_);
v___x_2523_ = lean_array_get_size(v___x_2522_);
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = lean_nat_dec_eq(v___x_2523_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_object* v_reader_2526_; lean_object* v_writer_2527_; lean_object* v_config_2528_; lean_object* v_events_2529_; lean_object* v_error_2530_; lean_object* v_instant_2531_; uint8_t v_keepAlive_2532_; uint8_t v_forcedFlush_2533_; uint8_t v_pullBodyStalled_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2566_; 
v_reader_2526_ = lean_ctor_get(v_machine_2483_, 0);
v_writer_2527_ = lean_ctor_get(v_machine_2483_, 1);
v_config_2528_ = lean_ctor_get(v_machine_2483_, 2);
v_events_2529_ = lean_ctor_get(v_machine_2483_, 3);
v_error_2530_ = lean_ctor_get(v_machine_2483_, 4);
v_instant_2531_ = lean_ctor_get(v_machine_2483_, 5);
v_keepAlive_2532_ = lean_ctor_get_uint8(v_machine_2483_, sizeof(void*)*6);
v_forcedFlush_2533_ = lean_ctor_get_uint8(v_machine_2483_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2534_ = lean_ctor_get_uint8(v_machine_2483_, sizeof(void*)*6 + 2);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_machine_2483_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2536_ = v_machine_2483_;
v_isShared_2537_ = v_isSharedCheck_2566_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_instant_2531_);
lean_inc(v_error_2530_);
lean_inc(v_events_2529_);
lean_inc(v_config_2528_);
lean_inc(v_writer_2527_);
lean_inc(v_reader_2526_);
lean_dec(v_machine_2483_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2566_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___y_2539_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_2562_ = lean_nat_dec_lt(v___x_2524_, v___x_2523_);
if (v___x_2562_ == 0)
{
lean_dec_ref(v___f_2486_);
v___y_2539_ = v___x_2524_;
goto v___jp_2538_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2523_);
lean_inc_ref(v___x_2522_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2561_, v___f_2486_, v___x_2522_, v___x_2563_, v___x_2564_, v___x_2524_);
v___y_2539_ = v___x_2565_;
goto v___jp_2538_;
}
v___jp_2538_:
{
lean_object* v_userData_2540_; lean_object* v_outputData_2541_; lean_object* v_state_2542_; lean_object* v_knownSize_2543_; lean_object* v_messageHead_2544_; uint8_t v_sentMessage_2545_; uint8_t v_userClosedBody_2546_; uint8_t v_omitBody_2547_; lean_object* v_userDataBytes_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2560_; 
v_userData_2540_ = lean_ctor_get(v_writer_2527_, 0);
v_outputData_2541_ = lean_ctor_get(v_writer_2527_, 1);
v_state_2542_ = lean_ctor_get(v_writer_2527_, 2);
v_knownSize_2543_ = lean_ctor_get(v_writer_2527_, 3);
v_messageHead_2544_ = lean_ctor_get(v_writer_2527_, 4);
v_sentMessage_2545_ = lean_ctor_get_uint8(v_writer_2527_, sizeof(void*)*6);
v_userClosedBody_2546_ = lean_ctor_get_uint8(v_writer_2527_, sizeof(void*)*6 + 1);
v_omitBody_2547_ = lean_ctor_get_uint8(v_writer_2527_, sizeof(void*)*6 + 2);
v_userDataBytes_2548_ = lean_ctor_get(v_writer_2527_, 5);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_writer_2527_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2550_ = v_writer_2527_;
v_isShared_2551_ = v_isSharedCheck_2560_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_userDataBytes_2548_);
lean_inc(v_messageHead_2544_);
lean_inc(v_knownSize_2543_);
lean_inc(v_state_2542_);
lean_inc(v_outputData_2541_);
lean_inc(v_userData_2540_);
lean_dec(v_writer_2527_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2560_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = l_Array_append___redArg(v_userData_2540_, v___x_2522_);
lean_dec_ref(v___x_2522_);
v___x_2553_ = lean_nat_add(v_userDataBytes_2548_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec(v_userDataBytes_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 5, v___x_2553_);
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_outputData_2541_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_state_2542_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_knownSize_2543_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_messageHead_2544_);
lean_ctor_set(v_reuseFailAlloc_2559_, 5, v___x_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*6, v_sentMessage_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*6 + 1, v_userClosedBody_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*6 + 2, v_omitBody_2547_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v___x_2555_);
v___x_2557_ = v___x_2536_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_reader_2526_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_config_2528_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_events_2529_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_error_2530_);
lean_ctor_set(v_reuseFailAlloc_2558_, 5, v_instant_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*6, v_keepAlive_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*6 + 1, v_forcedFlush_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*6 + 2, v_pullBodyStalled_2534_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
v___y_2490_ = v___x_2557_;
goto v___jp_2489_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2522_);
lean_dec_ref(v___f_2486_);
v___y_2490_ = v_machine_2483_;
goto v___jp_2489_;
}
}
}
}
}
v___jp_2489_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_body_2482_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___y_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2568_, lean_object* v_machine_2569_, lean_object* v_isClosed_2570_, lean_object* v___f_2571_, lean_object* v___f_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2568_, v_machine_2569_, v_isClosed_2570_, v___f_2571_, v___f_2572_, v_x_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2577_, lean_object* v_machine_2578_, lean_object* v_body_2579_){
_start:
{
lean_object* v_close_2581_; lean_object* v_isClosed_2582_; lean_object* v_tryRecv_2583_; lean_object* v___f_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_close_2581_ = lean_ctor_get(v_inst_2577_, 1);
lean_inc_ref(v_close_2581_);
v_isClosed_2582_ = lean_ctor_get(v_inst_2577_, 2);
lean_inc_ref(v_isClosed_2582_);
v_tryRecv_2583_ = lean_ctor_get(v_inst_2577_, 4);
lean_inc_ref(v_tryRecv_2583_);
lean_dec_ref(v_inst_2577_);
lean_inc_ref(v_machine_2578_);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2584_, 0, v_machine_2578_);
lean_inc_ref(v___f_2584_);
v___f_2585_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2585_, 0, v___f_2584_);
lean_inc_n(v_body_2579_, 2);
v___f_2586_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2586_, 0, v_close_2581_);
lean_closure_set(v___f_2586_, 1, v_body_2579_);
lean_closure_set(v___f_2586_, 2, v___f_2585_);
lean_closure_set(v___f_2586_, 3, v___f_2584_);
v___f_2587_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2588_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2588_, 0, v_body_2579_);
lean_closure_set(v___f_2588_, 1, v_machine_2578_);
lean_closure_set(v___f_2588_, 2, v_isClosed_2582_);
lean_closure_set(v___f_2588_, 3, v___f_2586_);
lean_closure_set(v___f_2588_, 4, v___f_2587_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = 0;
v___x_2591_ = lean_apply_2(v_tryRecv_2583_, v_body_2579_, lean_box(0));
v___x_2592_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2589_, v___x_2590_, v___x_2591_, v___f_2588_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2593_, lean_object* v_machine_2594_, lean_object* v_body_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2593_, v_machine_2594_, v_body_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2598_, lean_object* v_inst_2599_, lean_object* v_machine_2600_, lean_object* v_body_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2599_, v_machine_2600_, v_body_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2604_, lean_object* v_inst_2605_, lean_object* v_machine_2606_, lean_object* v_body_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2604_, v_inst_2605_, v_machine_2606_, v_body_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2616_, lean_object* v_____r_2617_, lean_object* v_st_2618_){
_start:
{
lean_object* v_machine_2620_; lean_object* v_requestStream_2621_; lean_object* v_keepAliveTimeout_2622_; lean_object* v_currentTimeout_2623_; lean_object* v_headerTimeout_2624_; lean_object* v_response_2625_; lean_object* v_respStream_2626_; uint8_t v_requiresData_2627_; lean_object* v_expectData_2628_; uint8_t v_handlerDispatched_2629_; lean_object* v_pendingHead_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2715_; 
v_machine_2620_ = lean_ctor_get(v_st_2618_, 0);
v_requestStream_2621_ = lean_ctor_get(v_st_2618_, 1);
v_keepAliveTimeout_2622_ = lean_ctor_get(v_st_2618_, 2);
v_currentTimeout_2623_ = lean_ctor_get(v_st_2618_, 3);
v_headerTimeout_2624_ = lean_ctor_get(v_st_2618_, 4);
v_response_2625_ = lean_ctor_get(v_st_2618_, 5);
v_respStream_2626_ = lean_ctor_get(v_st_2618_, 6);
v_requiresData_2627_ = lean_ctor_get_uint8(v_st_2618_, sizeof(void*)*9);
v_expectData_2628_ = lean_ctor_get(v_st_2618_, 7);
v_handlerDispatched_2629_ = lean_ctor_get_uint8(v_st_2618_, sizeof(void*)*9 + 1);
v_pendingHead_2630_ = lean_ctor_get(v_st_2618_, 8);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_st_2618_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2632_ = v_st_2618_;
v_isShared_2633_ = v_isSharedCheck_2715_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_pendingHead_2630_);
lean_inc(v_expectData_2628_);
lean_inc(v_respStream_2626_);
lean_inc(v_response_2625_);
lean_inc(v_headerTimeout_2624_);
lean_inc(v_currentTimeout_2623_);
lean_inc(v_keepAliveTimeout_2622_);
lean_inc(v_requestStream_2621_);
lean_inc(v_machine_2620_);
lean_dec(v_st_2618_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2715_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___y_2635_; lean_object* v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; uint8_t v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v_reader_2680_; lean_object* v_writer_2681_; lean_object* v_config_2682_; lean_object* v_events_2683_; lean_object* v_error_2684_; lean_object* v_instant_2685_; uint8_t v_keepAlive_2686_; uint8_t v_forcedFlush_2687_; lean_object* v_state_2688_; lean_object* v_input_2689_; lean_object* v_messageHead_2690_; lean_object* v_messageCount_2691_; lean_object* v_bodyBytesRead_2692_; lean_object* v_headerBytesRead_2693_; uint8_t v_noMoreInput_2694_; uint8_t v___y_2696_; uint8_t v___y_2697_; uint8_t v___y_2710_; 
v_reader_2680_ = lean_ctor_get(v_machine_2620_, 0);
v_writer_2681_ = lean_ctor_get(v_machine_2620_, 1);
v_config_2682_ = lean_ctor_get(v_machine_2620_, 2);
v_events_2683_ = lean_ctor_get(v_machine_2620_, 3);
v_error_2684_ = lean_ctor_get(v_machine_2620_, 4);
v_instant_2685_ = lean_ctor_get(v_machine_2620_, 5);
v_keepAlive_2686_ = lean_ctor_get_uint8(v_machine_2620_, sizeof(void*)*6);
v_forcedFlush_2687_ = lean_ctor_get_uint8(v_machine_2620_, sizeof(void*)*6 + 1);
v_state_2688_ = lean_ctor_get(v_reader_2680_, 0);
v_input_2689_ = lean_ctor_get(v_reader_2680_, 1);
v_messageHead_2690_ = lean_ctor_get(v_reader_2680_, 2);
v_messageCount_2691_ = lean_ctor_get(v_reader_2680_, 3);
v_bodyBytesRead_2692_ = lean_ctor_get(v_reader_2680_, 4);
v_headerBytesRead_2693_ = lean_ctor_get(v_reader_2680_, 5);
v_noMoreInput_2694_ = lean_ctor_get_uint8(v_reader_2680_, sizeof(void*)*6);
if (lean_obj_tag(v_state_2688_) == 6)
{
uint8_t v___x_2713_; 
v___x_2713_ = 1;
v___y_2710_ = v___x_2713_;
goto v___jp_2709_;
}
else
{
uint8_t v___x_2714_; 
v___x_2714_ = 0;
v___y_2710_ = v___x_2714_;
goto v___jp_2709_;
}
v___jp_2634_:
{
lean_object* v___x_2637_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v___y_2635_);
v___x_2637_ = v___x_2632_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___y_2635_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_requestStream_2621_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_keepAliveTimeout_2622_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_currentTimeout_2623_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_headerTimeout_2624_);
lean_ctor_set(v_reuseFailAlloc_2643_, 5, v_response_2625_);
lean_ctor_set(v_reuseFailAlloc_2643_, 6, v_respStream_2626_);
lean_ctor_set(v_reuseFailAlloc_2643_, 7, v_expectData_2628_);
lean_ctor_set(v_reuseFailAlloc_2643_, 8, v_pendingHead_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*9, v_requiresData_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*9 + 1, v_handlerDispatched_2629_);
v___x_2637_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2638_ = 0;
v___x_2639_ = lean_box(v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2637_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
v___jp_2644_:
{
lean_object* v_maxHeaderBytes_2660_; lean_object* v_maxStartLineLength_2661_; lean_object* v_maxChunkLineLength_2662_; lean_object* v_maxBodySize_2663_; lean_object* v_array_2664_; lean_object* v_idx_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_maxHeaderBytes_2660_ = lean_ctor_get(v___y_2649_, 2);
v_maxStartLineLength_2661_ = lean_ctor_get(v___y_2649_, 5);
v_maxChunkLineLength_2662_ = lean_ctor_get(v___y_2649_, 13);
v_maxBodySize_2663_ = lean_ctor_get(v___y_2649_, 15);
v_array_2664_ = lean_ctor_get(v___y_2659_, 0);
v_idx_2665_ = lean_ctor_get(v___y_2659_, 1);
v___x_2666_ = lean_nat_add(v_maxBodySize_2663_, v_maxHeaderBytes_2660_);
v___x_2667_ = lean_nat_add(v___x_2666_, v_maxStartLineLength_2661_);
lean_dec(v___x_2666_);
v___x_2668_ = lean_nat_add(v___x_2667_, v_maxChunkLineLength_2662_);
lean_dec(v___x_2667_);
v___x_2669_ = lean_byte_array_size(v_array_2664_);
v___x_2670_ = lean_nat_sub(v___x_2669_, v_idx_2665_);
v___x_2671_ = lean_nat_dec_lt(v___x_2668_, v___x_2670_);
lean_dec(v___x_2670_);
lean_dec(v___x_2668_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v_machine_2673_; 
v___x_2672_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2672_, 0, v___y_2651_);
lean_ctor_set(v___x_2672_, 1, v___y_2659_);
lean_ctor_set(v___x_2672_, 2, v___y_2646_);
lean_ctor_set(v___x_2672_, 3, v___y_2657_);
lean_ctor_set(v___x_2672_, 4, v___y_2655_);
lean_ctor_set(v___x_2672_, 5, v___y_2652_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*6, v___y_2653_);
v_machine_2673_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_2673_, 0, v___x_2672_);
lean_ctor_set(v_machine_2673_, 1, v___y_2656_);
lean_ctor_set(v_machine_2673_, 2, v___y_2649_);
lean_ctor_set(v_machine_2673_, 3, v___y_2645_);
lean_ctor_set(v_machine_2673_, 4, v___y_2654_);
lean_ctor_set(v_machine_2673_, 5, v___y_2658_);
lean_ctor_set_uint8(v_machine_2673_, sizeof(void*)*6, v___y_2647_);
lean_ctor_set_uint8(v_machine_2673_, sizeof(void*)*6 + 1, v___y_2648_);
lean_ctor_set_uint8(v_machine_2673_, sizeof(void*)*6 + 2, v___y_2650_);
v___y_2635_ = v_machine_2673_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec(v___y_2654_);
lean_dec(v___y_2651_);
v___x_2674_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2675_ = lean_array_push(v___y_2645_, v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
v___x_2677_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___y_2659_);
lean_ctor_set(v___x_2677_, 2, v___y_2646_);
lean_ctor_set(v___x_2677_, 3, v___y_2657_);
lean_ctor_set(v___x_2677_, 4, v___y_2655_);
lean_ctor_set(v___x_2677_, 5, v___y_2652_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*6, v___y_2653_);
v___x_2678_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
v___x_2679_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___y_2656_);
lean_ctor_set(v___x_2679_, 2, v___y_2649_);
lean_ctor_set(v___x_2679_, 3, v___x_2675_);
lean_ctor_set(v___x_2679_, 4, v___x_2678_);
lean_ctor_set(v___x_2679_, 5, v___y_2658_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*6, v___y_2647_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*6 + 1, v___y_2648_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*6 + 2, v___y_2650_);
v___y_2635_ = v___x_2679_;
goto v___jp_2634_;
}
}
v___jp_2695_:
{
if (v___y_2696_ == 0)
{
if (v___y_2697_ == 0)
{
lean_object* v_array_2698_; lean_object* v_idx_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
lean_inc(v_headerBytesRead_2693_);
lean_inc(v_bodyBytesRead_2692_);
lean_inc(v_messageCount_2691_);
lean_inc(v_messageHead_2690_);
lean_inc_ref(v_input_2689_);
lean_inc(v_state_2688_);
lean_inc(v_instant_2685_);
lean_inc(v_error_2684_);
lean_inc_ref(v_events_2683_);
lean_inc_ref(v_config_2682_);
lean_inc_ref(v_writer_2681_);
lean_dec_ref(v_machine_2620_);
v_array_2698_ = lean_ctor_get(v_input_2689_, 0);
lean_inc_ref(v_array_2698_);
v_idx_2699_ = lean_ctor_get(v_input_2689_, 1);
lean_inc(v_idx_2699_);
lean_dec_ref(v_input_2689_);
v___x_2700_ = lean_byte_array_size(v_array_2698_);
v___x_2701_ = lean_nat_dec_le(v___x_2700_, v_idx_2699_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2702_ = l_ByteArray_extract(v_array_2698_, v_idx_2699_, v___x_2700_);
lean_dec_ref(v_array_2698_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_byte_array_size(v___x_2702_);
v___x_2705_ = lean_byte_array_size(v_val_2616_);
v___x_2706_ = lean_byte_array_copy_slice(v_val_2616_, v___x_2703_, v___x_2702_, v___x_2704_, v___x_2705_, v___x_2701_);
lean_dec_ref(v_val_2616_);
v___x_2707_ = l_ByteArray_mkIterator(v___x_2706_);
v___y_2645_ = v_events_2683_;
v___y_2646_ = v_messageHead_2690_;
v___y_2647_ = v_keepAlive_2686_;
v___y_2648_ = v_forcedFlush_2687_;
v___y_2649_ = v_config_2682_;
v___y_2650_ = v___y_2697_;
v___y_2651_ = v_state_2688_;
v___y_2652_ = v_headerBytesRead_2693_;
v___y_2653_ = v_noMoreInput_2694_;
v___y_2654_ = v_error_2684_;
v___y_2655_ = v_bodyBytesRead_2692_;
v___y_2656_ = v_writer_2681_;
v___y_2657_ = v_messageCount_2691_;
v___y_2658_ = v_instant_2685_;
v___y_2659_ = v___x_2707_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2708_; 
lean_dec(v_idx_2699_);
lean_dec_ref(v_array_2698_);
v___x_2708_ = l_ByteArray_mkIterator(v_val_2616_);
v___y_2645_ = v_events_2683_;
v___y_2646_ = v_messageHead_2690_;
v___y_2647_ = v_keepAlive_2686_;
v___y_2648_ = v_forcedFlush_2687_;
v___y_2649_ = v_config_2682_;
v___y_2650_ = v___y_2697_;
v___y_2651_ = v_state_2688_;
v___y_2652_ = v_headerBytesRead_2693_;
v___y_2653_ = v_noMoreInput_2694_;
v___y_2654_ = v_error_2684_;
v___y_2655_ = v_bodyBytesRead_2692_;
v___y_2656_ = v_writer_2681_;
v___y_2657_ = v_messageCount_2691_;
v___y_2658_ = v_instant_2685_;
v___y_2659_ = v___x_2708_;
goto v___jp_2644_;
}
}
else
{
lean_dec_ref(v_val_2616_);
v___y_2635_ = v_machine_2620_;
goto v___jp_2634_;
}
}
else
{
lean_dec_ref(v_val_2616_);
v___y_2635_ = v_machine_2620_;
goto v___jp_2634_;
}
}
v___jp_2709_:
{
if (lean_obj_tag(v_state_2688_) == 7)
{
uint8_t v___x_2711_; 
v___x_2711_ = 1;
v___y_2696_ = v___y_2710_;
v___y_2697_ = v___x_2711_;
goto v___jp_2695_;
}
else
{
uint8_t v___x_2712_; 
v___x_2712_ = 0;
v___y_2696_ = v___y_2710_;
v___y_2697_ = v___x_2712_;
goto v___jp_2695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2716_, lean_object* v_____r_2717_, lean_object* v_st_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2716_, v_____r_2717_, v_st_2718_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2721_, lean_object* v_machine_2722_, lean_object* v_requestStream_2723_, lean_object* v_currentTimeout_2724_, lean_object* v_response_2725_, lean_object* v_respStream_2726_, uint8_t v_requiresData_2727_, lean_object* v_expectData_2728_, uint8_t v_handlerDispatched_2729_, lean_object* v_pendingHead_2730_, lean_object* v___f_2731_, lean_object* v_x_2732_){
_start:
{
if (lean_obj_tag(v_x_2732_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v___f_2731_);
lean_dec(v_pendingHead_2730_);
lean_dec(v_expectData_2728_);
lean_dec(v_respStream_2726_);
lean_dec_ref(v_response_2725_);
lean_dec(v_currentTimeout_2724_);
lean_dec_ref(v_requestStream_2723_);
lean_dec_ref(v_machine_2722_);
v_a_2734_ = lean_ctor_get(v_x_2732_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_x_2732_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2736_ = v_x_2732_;
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v_x_2732_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
return v___x_2740_;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v_headerTimeout_2744_; lean_object* v_second_2745_; lean_object* v_nano_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v_second_2750_; lean_object* v_nano_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_nanos_2755_; lean_object* v___x_2756_; lean_object* v_nanos_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2743_ = lean_ctor_get(v_x_2732_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v_x_2732_, 1);
v_headerTimeout_2744_ = lean_ctor_get(v_config_2721_, 6);
v_second_2745_ = lean_ctor_get(v_a_2743_, 0);
lean_inc(v_second_2745_);
v_nano_2746_ = lean_ctor_get(v_a_2743_, 1);
lean_inc(v_nano_2746_);
lean_dec(v_a_2743_);
v___x_2747_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2748_ = lean_int_mul(v_headerTimeout_2744_, v___x_2747_);
v___x_2749_ = l_Std_Time_Duration_ofNanoseconds(v___x_2748_);
lean_dec(v___x_2748_);
v_second_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_second_2750_);
v_nano_2751_ = lean_ctor_get(v___x_2749_, 1);
lean_inc(v_nano_2751_);
lean_dec_ref(v___x_2749_);
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2754_ = lean_int_mul(v_second_2745_, v___x_2753_);
lean_dec(v_second_2745_);
v_nanos_2755_ = lean_int_add(v___x_2754_, v_nano_2746_);
lean_dec(v_nano_2746_);
lean_dec(v___x_2754_);
v___x_2756_ = lean_int_mul(v_second_2750_, v___x_2753_);
lean_dec(v_second_2750_);
v_nanos_2757_ = lean_int_add(v___x_2756_, v_nano_2751_);
lean_dec(v_nano_2751_);
lean_dec(v___x_2756_);
v___x_2758_ = lean_int_add(v_nanos_2755_, v_nanos_2757_);
lean_dec(v_nanos_2757_);
lean_dec(v_nanos_2755_);
v___x_2759_ = l_Std_Time_Duration_ofNanoseconds(v___x_2758_);
lean_dec(v___x_2758_);
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2761_, 0, v_machine_2722_);
lean_ctor_set(v___x_2761_, 1, v_requestStream_2723_);
lean_ctor_set(v___x_2761_, 2, v___x_2752_);
lean_ctor_set(v___x_2761_, 3, v_currentTimeout_2724_);
lean_ctor_set(v___x_2761_, 4, v___x_2760_);
lean_ctor_set(v___x_2761_, 5, v_response_2725_);
lean_ctor_set(v___x_2761_, 6, v_respStream_2726_);
lean_ctor_set(v___x_2761_, 7, v_expectData_2728_);
lean_ctor_set(v___x_2761_, 8, v_pendingHead_2730_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*9, v_requiresData_2727_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*9 + 1, v_handlerDispatched_2729_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_apply_3(v___f_2731_, v___x_2762_, v___x_2761_, lean_box(0));
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2764_, lean_object* v_machine_2765_, lean_object* v_requestStream_2766_, lean_object* v_currentTimeout_2767_, lean_object* v_response_2768_, lean_object* v_respStream_2769_, lean_object* v_requiresData_2770_, lean_object* v_expectData_2771_, lean_object* v_handlerDispatched_2772_, lean_object* v_pendingHead_2773_, lean_object* v___f_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v_requiresData_boxed_2777_; uint8_t v_handlerDispatched_boxed_2778_; lean_object* v_res_2779_; 
v_requiresData_boxed_2777_ = lean_unbox(v_requiresData_2770_);
v_handlerDispatched_boxed_2778_ = lean_unbox(v_handlerDispatched_2772_);
v_res_2779_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2764_, v_machine_2765_, v_requestStream_2766_, v_currentTimeout_2767_, v_response_2768_, v_respStream_2769_, v_requiresData_boxed_2777_, v_expectData_2771_, v_handlerDispatched_boxed_2778_, v_pendingHead_2773_, v___f_2774_, v_x_2775_);
lean_dec_ref(v_config_2764_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2780_, lean_object* v_requestStream_2781_, lean_object* v_keepAliveTimeout_2782_, lean_object* v_currentTimeout_2783_, lean_object* v_headerTimeout_2784_, lean_object* v_response_2785_, uint8_t v_requiresData_2786_, lean_object* v_expectData_2787_, uint8_t v_handlerDispatched_2788_, lean_object* v_pendingHead_2789_, lean_object* v_____r_2790_){
_start:
{
lean_object* v_writer_2792_; lean_object* v_reader_2793_; lean_object* v_config_2794_; lean_object* v_events_2795_; lean_object* v_error_2796_; lean_object* v_instant_2797_; uint8_t v_keepAlive_2798_; uint8_t v_forcedFlush_2799_; uint8_t v_pullBodyStalled_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2830_; 
v_writer_2792_ = lean_ctor_get(v_machine_2780_, 1);
v_reader_2793_ = lean_ctor_get(v_machine_2780_, 0);
v_config_2794_ = lean_ctor_get(v_machine_2780_, 2);
v_events_2795_ = lean_ctor_get(v_machine_2780_, 3);
v_error_2796_ = lean_ctor_get(v_machine_2780_, 4);
v_instant_2797_ = lean_ctor_get(v_machine_2780_, 5);
v_keepAlive_2798_ = lean_ctor_get_uint8(v_machine_2780_, sizeof(void*)*6);
v_forcedFlush_2799_ = lean_ctor_get_uint8(v_machine_2780_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2800_ = lean_ctor_get_uint8(v_machine_2780_, sizeof(void*)*6 + 2);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_machine_2780_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2802_ = v_machine_2780_;
v_isShared_2803_ = v_isSharedCheck_2830_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_instant_2797_);
lean_inc(v_error_2796_);
lean_inc(v_events_2795_);
lean_inc(v_config_2794_);
lean_inc(v_writer_2792_);
lean_inc(v_reader_2793_);
lean_dec(v_machine_2780_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2830_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_userData_2804_; lean_object* v_outputData_2805_; lean_object* v_state_2806_; lean_object* v_knownSize_2807_; lean_object* v_messageHead_2808_; uint8_t v_sentMessage_2809_; uint8_t v_omitBody_2810_; lean_object* v_userDataBytes_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2829_; 
v_userData_2804_ = lean_ctor_get(v_writer_2792_, 0);
v_outputData_2805_ = lean_ctor_get(v_writer_2792_, 1);
v_state_2806_ = lean_ctor_get(v_writer_2792_, 2);
v_knownSize_2807_ = lean_ctor_get(v_writer_2792_, 3);
v_messageHead_2808_ = lean_ctor_get(v_writer_2792_, 4);
v_sentMessage_2809_ = lean_ctor_get_uint8(v_writer_2792_, sizeof(void*)*6);
v_omitBody_2810_ = lean_ctor_get_uint8(v_writer_2792_, sizeof(void*)*6 + 2);
v_userDataBytes_2811_ = lean_ctor_get(v_writer_2792_, 5);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_writer_2792_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2813_ = v_writer_2792_;
v_isShared_2814_ = v_isSharedCheck_2829_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_userDataBytes_2811_);
lean_inc(v_messageHead_2808_);
lean_inc(v_knownSize_2807_);
lean_inc(v_state_2806_);
lean_inc(v_outputData_2805_);
lean_inc(v_userData_2804_);
lean_dec(v_writer_2792_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2829_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
uint8_t v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = 1;
if (v_isShared_2814_ == 0)
{
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_userData_2804_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_outputData_2805_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_state_2806_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_knownSize_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_messageHead_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_userDataBytes_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*6, v_sentMessage_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*6 + 2, v_omitBody_2810_);
v___x_2817_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2819_; 
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*6 + 1, v___x_2815_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v___x_2817_);
v___x_2819_ = v___x_2802_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_reader_2793_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_config_2794_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_events_2795_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v_error_2796_);
lean_ctor_set(v_reuseFailAlloc_2827_, 5, v_instant_2797_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*6, v_keepAlive_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*6 + 1, v_forcedFlush_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*6 + 2, v_pullBodyStalled_2800_);
v___x_2819_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v_requestStream_2781_);
lean_ctor_set(v___x_2821_, 2, v_keepAliveTimeout_2782_);
lean_ctor_set(v___x_2821_, 3, v_currentTimeout_2783_);
lean_ctor_set(v___x_2821_, 4, v_headerTimeout_2784_);
lean_ctor_set(v___x_2821_, 5, v_response_2785_);
lean_ctor_set(v___x_2821_, 6, v___x_2820_);
lean_ctor_set(v___x_2821_, 7, v_expectData_2787_);
lean_ctor_set(v___x_2821_, 8, v_pendingHead_2789_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*9, v_requiresData_2786_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*9 + 1, v_handlerDispatched_2788_);
v___x_2822_ = 0;
v___x_2823_ = lean_box(v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2831_, lean_object* v_requestStream_2832_, lean_object* v_keepAliveTimeout_2833_, lean_object* v_currentTimeout_2834_, lean_object* v_headerTimeout_2835_, lean_object* v_response_2836_, lean_object* v_requiresData_2837_, lean_object* v_expectData_2838_, lean_object* v_handlerDispatched_2839_, lean_object* v_pendingHead_2840_, lean_object* v_____r_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v_requiresData_boxed_2843_; uint8_t v_handlerDispatched_boxed_2844_; lean_object* v_res_2845_; 
v_requiresData_boxed_2843_ = lean_unbox(v_requiresData_2837_);
v_handlerDispatched_boxed_2844_ = lean_unbox(v_handlerDispatched_2839_);
v_res_2845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2831_, v_requestStream_2832_, v_keepAliveTimeout_2833_, v_currentTimeout_2834_, v_headerTimeout_2835_, v_response_2836_, v_requiresData_boxed_2843_, v_expectData_2838_, v_handlerDispatched_boxed_2844_, v_pendingHead_2840_, v_____r_2841_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2846_, lean_object* v_x_2847_){
_start:
{
if (lean_obj_tag(v_x_2847_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___f_2846_);
v_a_2849_ = lean_ctor_get(v_x_2847_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_x_2847_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2851_ = v_x_2847_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v_x_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v_x_2847_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v_x_2847_, 1);
v___x_2859_ = lean_apply_2(v___f_2846_, v_a_2858_, lean_box(0));
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2860_, lean_object* v_x_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2860_, v_x_2861_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2864_, lean_object* v_val_2865_, lean_object* v___f_2866_, lean_object* v___f_2867_, lean_object* v_x_2868_){
_start:
{
if (lean_obj_tag(v_x_2868_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v___f_2867_);
lean_dec_ref(v___f_2866_);
lean_dec(v_val_2865_);
lean_dec_ref(v_close_2864_);
v_a_2870_ = lean_ctor_get(v_x_2868_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_x_2868_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2872_ = v_x_2868_;
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v_x_2868_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2879_; uint8_t v___x_2880_; 
v_a_2879_ = lean_ctor_get(v_x_2868_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v_x_2868_, 1);
v___x_2880_ = lean_unbox(v_a_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref(v___f_2867_);
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = lean_apply_2(v_close_2864_, v_val_2865_, lean_box(0));
v___x_2883_ = lean_unbox(v_a_2879_);
lean_dec(v_a_2879_);
v___x_2884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2881_, v___x_2883_, v___x_2882_, v___f_2866_);
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_a_2879_);
lean_dec_ref(v___f_2866_);
lean_dec(v_val_2865_);
lean_dec_ref(v_close_2864_);
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_apply_2(v___f_2867_, v___x_2885_, lean_box(0));
return v___x_2886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2887_, lean_object* v_val_2888_, lean_object* v___f_2889_, lean_object* v___f_2890_, lean_object* v_x_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2887_, v_val_2888_, v___f_2889_, v___f_2890_, v_x_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_2894_, lean_object* v_handler_2895_, lean_object* v_x_2896_){
_start:
{
if (lean_obj_tag(v_x_2896_) == 0)
{
lean_object* v_a_2898_; lean_object* v_onFailure_2899_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v_x_2896_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v_x_2896_, 1);
v_onFailure_2899_ = lean_ctor_get(v_inst_2894_, 2);
lean_inc_ref(v_onFailure_2899_);
lean_dec_ref(v_inst_2894_);
v___x_2900_ = lean_apply_3(v_onFailure_2899_, v_handler_2895_, v_a_2898_, lean_box(0));
return v___x_2900_;
}
else
{
lean_object* v___x_2901_; 
lean_dec(v_handler_2895_);
lean_dec_ref(v_inst_2894_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_x_2896_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_2902_, lean_object* v_handler_2903_, lean_object* v_x_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2902_, v_handler_2903_, v_x_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_2907_, lean_object* v_____r_2908_){
_start:
{
uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2910_ = 0;
v___x_2911_ = lean_box(v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_st_2907_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_2915_, lean_object* v_____r_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2915_, v_____r_2916_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2919_, lean_object* v___f_2920_, lean_object* v___f_2921_, lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v___f_2921_);
lean_dec_ref(v___f_2920_);
lean_dec_ref(v_requestStream_2919_);
v_a_2924_ = lean_ctor_get(v_x_2922_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v_x_2922_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v_x_2922_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
else
{
lean_object* v_a_2933_; uint8_t v___x_2934_; 
v_a_2933_ = lean_ctor_get(v_x_2922_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v_x_2922_, 1);
v___x_2934_ = lean_unbox(v_a_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
lean_dec_ref(v___f_2921_);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = l_Std_Http_Body_Stream_close(v_requestStream_2919_);
v___x_2937_ = lean_unbox(v_a_2933_);
lean_dec(v_a_2933_);
v___x_2938_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2935_, v___x_2937_, v___x_2936_, v___f_2920_);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_dec(v_a_2933_);
lean_dec_ref(v___f_2920_);
lean_dec_ref(v_requestStream_2919_);
v___x_2939_ = lean_box(0);
v___x_2940_ = lean_apply_2(v___f_2921_, v___x_2939_, lean_box(0));
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2941_, lean_object* v___f_2942_, lean_object* v___f_2943_, lean_object* v_x_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2941_, v___f_2942_, v___f_2943_, v_x_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t v_final_2947_, lean_object* v___f_2948_, lean_object* v___f_2949_, lean_object* v_requestStream_2950_, lean_object* v___f_2951_, lean_object* v_x_2952_){
_start:
{
if (lean_obj_tag(v_x_2952_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v___f_2951_);
lean_dec_ref(v_requestStream_2950_);
lean_dec_ref(v___f_2949_);
lean_dec_ref(v___f_2948_);
v_a_2954_ = lean_ctor_get(v_x_2952_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2952_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2956_ = v_x_2952_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v_x_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
}
else
{
lean_dec_ref_known(v_x_2952_, 1);
if (v_final_2947_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_dec_ref(v___f_2951_);
lean_dec_ref(v_requestStream_2950_);
lean_dec_ref(v___f_2949_);
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_apply_2(v___f_2948_, v___x_2963_, lean_box(0));
return v___x_2964_;
}
else
{
lean_object* v___x_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_6987__overap_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref(v___f_2948_);
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = 0;
v___x_2967_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2968_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2969_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2970_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2971_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2971_, 0, lean_box(0));
lean_closure_set(v___x_2971_, 1, lean_box(0));
lean_closure_set(v___x_2971_, 2, v___x_2967_);
lean_closure_set(v___x_2971_, 3, lean_box(0));
lean_closure_set(v___x_2971_, 4, lean_box(0));
lean_closure_set(v___x_2971_, 5, v___x_2970_);
lean_closure_set(v___x_2971_, 6, v___f_2949_);
v___x_6987__overap_2972_ = l_Std_Mutex_atomically___redArg(v___x_2967_, v___f_2968_, v___f_2969_, v_requestStream_2950_, v___x_2971_);
v___x_2973_ = lean_apply_1(v___x_6987__overap_2972_, lean_box(0));
v___x_2974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2965_, v___x_2966_, v___x_2973_, v___f_2951_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_final_2975_, lean_object* v___f_2976_, lean_object* v___f_2977_, lean_object* v_requestStream_2978_, lean_object* v___f_2979_, lean_object* v_x_2980_, lean_object* v___y_2981_){
_start:
{
uint8_t v_final_boxed_2982_; lean_object* v_res_2983_; 
v_final_boxed_2982_ = lean_unbox(v_final_2975_);
v_res_2983_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_boxed_2982_, v___f_2976_, v___f_2977_, v_requestStream_2978_, v___f_2979_, v_x_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2984_, lean_object* v_x_2985_){
_start:
{
if (lean_obj_tag(v_x_2985_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_state_2984_);
v_a_2987_ = lean_ctor_get(v_x_2985_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_x_2985_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2989_ = v_x_2985_;
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v_x_2985_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
}
else
{
lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3025_; 
v_isSharedCheck_3025_ = !lean_is_exclusive(v_x_2985_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_x_2985_, 0);
lean_dec(v_unused_3026_);
v___x_2997_ = v_x_2985_;
v_isShared_2998_ = v_isSharedCheck_3025_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v_x_2985_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3025_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_machine_2999_; lean_object* v_requestStream_3000_; lean_object* v_keepAliveTimeout_3001_; lean_object* v_currentTimeout_3002_; lean_object* v_headerTimeout_3003_; lean_object* v_response_3004_; lean_object* v_respStream_3005_; uint8_t v_requiresData_3006_; lean_object* v_expectData_3007_; lean_object* v_pendingHead_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3024_; 
v_machine_2999_ = lean_ctor_get(v_state_2984_, 0);
v_requestStream_3000_ = lean_ctor_get(v_state_2984_, 1);
v_keepAliveTimeout_3001_ = lean_ctor_get(v_state_2984_, 2);
v_currentTimeout_3002_ = lean_ctor_get(v_state_2984_, 3);
v_headerTimeout_3003_ = lean_ctor_get(v_state_2984_, 4);
v_response_3004_ = lean_ctor_get(v_state_2984_, 5);
v_respStream_3005_ = lean_ctor_get(v_state_2984_, 6);
v_requiresData_3006_ = lean_ctor_get_uint8(v_state_2984_, sizeof(void*)*9);
v_expectData_3007_ = lean_ctor_get(v_state_2984_, 7);
v_pendingHead_3008_ = lean_ctor_get(v_state_2984_, 8);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_state_2984_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3010_ = v_state_2984_;
v_isShared_3011_ = v_isSharedCheck_3024_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_pendingHead_3008_);
lean_inc(v_expectData_3007_);
lean_inc(v_respStream_3005_);
lean_inc(v_response_3004_);
lean_inc(v_headerTimeout_3003_);
lean_inc(v_currentTimeout_3002_);
lean_inc(v_keepAliveTimeout_3001_);
lean_inc(v_requestStream_3000_);
lean_inc(v_machine_2999_);
lean_dec(v_state_2984_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3024_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3016_; 
v___x_3012_ = lean_box(52);
v___x_3013_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2999_, v___x_3012_);
v___x_3014_ = 0;
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3013_);
v___x_3016_ = v___x_3010_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_requestStream_3000_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_keepAliveTimeout_3001_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_currentTimeout_3002_);
lean_ctor_set(v_reuseFailAlloc_3023_, 4, v_headerTimeout_3003_);
lean_ctor_set(v_reuseFailAlloc_3023_, 5, v_response_3004_);
lean_ctor_set(v_reuseFailAlloc_3023_, 6, v_respStream_3005_);
lean_ctor_set(v_reuseFailAlloc_3023_, 7, v_expectData_3007_);
lean_ctor_set(v_reuseFailAlloc_3023_, 8, v_pendingHead_3008_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*9, v_requiresData_3006_);
v___x_3016_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*9 + 1, v___x_3014_);
v___x_3017_ = lean_box(v___x_3014_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3018_);
v___x_3020_ = v___x_2997_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
return v___x_3021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3027_, lean_object* v_x_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3027_, v_x_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3031_, lean_object* v_requestStream_3032_, lean_object* v_keepAliveTimeout_3033_, lean_object* v_currentTimeout_3034_, lean_object* v_headerTimeout_3035_, lean_object* v_response_3036_, lean_object* v_respStream_3037_, uint8_t v_requiresData_3038_, lean_object* v_expectData_3039_, lean_object* v_pendingHead_3040_, lean_object* v_____r_3041_){
_start:
{
uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3043_ = 0;
v___x_3044_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3044_, 0, v_machine_3031_);
lean_ctor_set(v___x_3044_, 1, v_requestStream_3032_);
lean_ctor_set(v___x_3044_, 2, v_keepAliveTimeout_3033_);
lean_ctor_set(v___x_3044_, 3, v_currentTimeout_3034_);
lean_ctor_set(v___x_3044_, 4, v_headerTimeout_3035_);
lean_ctor_set(v___x_3044_, 5, v_response_3036_);
lean_ctor_set(v___x_3044_, 6, v_respStream_3037_);
lean_ctor_set(v___x_3044_, 7, v_expectData_3039_);
lean_ctor_set(v___x_3044_, 8, v_pendingHead_3040_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*9, v_requiresData_3038_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*9 + 1, v___x_3043_);
v___x_3045_ = lean_box(v___x_3043_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3049_, lean_object* v_requestStream_3050_, lean_object* v_keepAliveTimeout_3051_, lean_object* v_currentTimeout_3052_, lean_object* v_headerTimeout_3053_, lean_object* v_response_3054_, lean_object* v_respStream_3055_, lean_object* v_requiresData_3056_, lean_object* v_expectData_3057_, lean_object* v_pendingHead_3058_, lean_object* v_____r_3059_, lean_object* v___y_3060_){
_start:
{
uint8_t v_requiresData_boxed_3061_; lean_object* v_res_3062_; 
v_requiresData_boxed_3061_ = lean_unbox(v_requiresData_3056_);
v_res_3062_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3049_, v_requestStream_3050_, v_keepAliveTimeout_3051_, v_currentTimeout_3052_, v_headerTimeout_3053_, v_response_3054_, v_respStream_3055_, v_requiresData_boxed_3061_, v_expectData_3057_, v_pendingHead_3058_, v_____r_3059_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3063_, lean_object* v_body_3064_, lean_object* v___f_3065_, lean_object* v___f_3066_, lean_object* v_x_3067_){
_start:
{
if (lean_obj_tag(v_x_3067_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v___f_3066_);
lean_dec_ref(v___f_3065_);
lean_dec(v_body_3064_);
lean_dec_ref(v_close_3063_);
v_a_3069_ = lean_ctor_get(v_x_3067_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_x_3067_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3071_ = v_x_3067_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v_x_3067_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3078_; uint8_t v___x_3079_; 
v_a_3078_ = lean_ctor_get(v_x_3067_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v_x_3067_, 1);
v___x_3079_ = lean_unbox(v_a_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; 
lean_dec_ref(v___f_3066_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = lean_apply_2(v_close_3063_, v_body_3064_, lean_box(0));
v___x_3082_ = lean_unbox(v_a_3078_);
lean_dec(v_a_3078_);
v___x_3083_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3080_, v___x_3082_, v___x_3081_, v___f_3065_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec(v_a_3078_);
lean_dec_ref(v___f_3065_);
lean_dec(v_body_3064_);
lean_dec_ref(v_close_3063_);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_apply_2(v___f_3066_, v___x_3084_, lean_box(0));
return v___x_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3086_, lean_object* v_body_3087_, lean_object* v___f_3088_, lean_object* v___f_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3086_, v_body_3087_, v___f_3088_, v___f_3089_, v_x_3090_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3093_, lean_object* v_keepAliveTimeout_3094_, lean_object* v_currentTimeout_3095_, lean_object* v_headerTimeout_3096_, lean_object* v_response_3097_, uint8_t v_requiresData_3098_, lean_object* v_expectData_3099_, uint8_t v___x_3100_, lean_object* v_pendingHead_3101_, lean_object* v_____x_3102_){
_start:
{
lean_object* v_snd_3104_; lean_object* v_fst_3105_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3117_; 
v_snd_3104_ = lean_ctor_get(v_____x_3102_, 1);
lean_inc(v_snd_3104_);
v_fst_3105_ = lean_ctor_get(v_____x_3102_, 0);
lean_inc(v_fst_3105_);
lean_dec_ref(v_____x_3102_);
v_fst_3106_ = lean_ctor_get(v_snd_3104_, 0);
v_snd_3107_ = lean_ctor_get(v_snd_3104_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_snd_3104_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3109_ = v_snd_3104_;
v_isShared_3110_ = v_isSharedCheck_3117_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snd_3107_);
lean_inc(v_fst_3106_);
lean_dec(v_snd_3104_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3117_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3111_, 0, v_fst_3105_);
lean_ctor_set(v___x_3111_, 1, v_requestStream_3093_);
lean_ctor_set(v___x_3111_, 2, v_keepAliveTimeout_3094_);
lean_ctor_set(v___x_3111_, 3, v_currentTimeout_3095_);
lean_ctor_set(v___x_3111_, 4, v_headerTimeout_3096_);
lean_ctor_set(v___x_3111_, 5, v_response_3097_);
lean_ctor_set(v___x_3111_, 6, v_fst_3106_);
lean_ctor_set(v___x_3111_, 7, v_expectData_3099_);
lean_ctor_set(v___x_3111_, 8, v_pendingHead_3101_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*9, v_requiresData_3098_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*9 + 1, v___x_3100_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_snd_3107_);
v___x_3113_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3118_, lean_object* v_keepAliveTimeout_3119_, lean_object* v_currentTimeout_3120_, lean_object* v_headerTimeout_3121_, lean_object* v_response_3122_, lean_object* v_requiresData_3123_, lean_object* v_expectData_3124_, lean_object* v___x_3125_, lean_object* v_pendingHead_3126_, lean_object* v_____x_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_requiresData_boxed_3129_; uint8_t v___x_7803__boxed_3130_; lean_object* v_res_3131_; 
v_requiresData_boxed_3129_ = lean_unbox(v_requiresData_3123_);
v___x_7803__boxed_3130_ = lean_unbox(v___x_3125_);
v_res_3131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3118_, v_keepAliveTimeout_3119_, v_currentTimeout_3120_, v_headerTimeout_3121_, v_response_3122_, v_requiresData_boxed_3129_, v_expectData_3124_, v___x_7803__boxed_3130_, v_pendingHead_3126_, v_____x_3127_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3132_, lean_object* v_x_3133_){
_start:
{
if (lean_obj_tag(v_x_3133_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v___f_3132_);
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
lean_object* v_a_3144_; lean_object* v___x_3145_; 
v_a_3144_ = lean_ctor_get(v_x_3133_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v_x_3133_, 1);
v___x_3145_ = lean_apply_2(v___f_3132_, v_a_3144_, lean_box(0));
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3146_, v_x_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3150_, lean_object* v_x_3151_){
_start:
{
if (lean_obj_tag(v_x_3151_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3161_; 
v_a_3153_ = lean_ctor_get(v_x_3151_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_x_3151_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3155_ = v_x_3151_;
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v_x_3151_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3153_);
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
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3181_; 
v_a_3162_ = lean_ctor_get(v_x_3151_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_x_3151_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3164_ = v_x_3151_;
v_isShared_3165_ = v_isSharedCheck_3181_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v_x_3151_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3181_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v_fst_3166_; lean_object* v_snd_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3180_; 
v_fst_3166_ = lean_ctor_get(v_a_3162_, 0);
v_snd_3167_ = lean_ctor_get(v_a_3162_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3162_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3169_ = v_a_3162_;
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_snd_3167_);
lean_inc(v_fst_3166_);
lean_dec(v_a_3162_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = lean_box(v___x_3150_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 1, v___x_3171_);
lean_ctor_set(v___x_3169_, 0, v_snd_3167_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_snd_3167_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_fst_3166_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3174_);
v___x_3176_ = v___x_3164_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v___x_7871__boxed_3185_; lean_object* v_res_3186_; 
v___x_7871__boxed_3185_ = lean_unbox(v___x_3182_);
v_res_3186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7871__boxed_3185_, v_x_3183_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3187_, uint8_t v___x_3188_, lean_object* v_fst_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v_fst_3189_);
lean_dec(v_snd_3187_);
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
lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3211_; 
v_isSharedCheck_3211_ = !lean_is_exclusive(v_x_3190_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v_x_3190_, 0);
lean_dec(v_unused_3212_);
v___x_3202_ = v_x_3190_;
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
else
{
lean_dec(v_x_3190_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3204_ = lean_box(v___x_3188_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v_snd_3187_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_fst_3189_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3206_);
v___x_3208_ = v___x_3202_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3206_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3213_, lean_object* v___x_3214_, lean_object* v_fst_3215_, lean_object* v_x_3216_, lean_object* v___y_3217_){
_start:
{
uint8_t v___x_7939__boxed_3218_; lean_object* v_res_3219_; 
v___x_7939__boxed_3218_ = lean_unbox(v___x_3214_);
v_res_3219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3213_, v___x_7939__boxed_3218_, v_fst_3215_, v_x_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3220_, lean_object* v_handler_3221_, uint8_t v___x_3222_, lean_object* v___f_3223_, lean_object* v_x_3224_){
_start:
{
if (lean_obj_tag(v_x_3224_) == 0)
{
lean_object* v_a_3226_; lean_object* v_onFailure_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v_a_3226_ = lean_ctor_get(v_x_3224_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v_x_3224_, 1);
v_onFailure_3227_ = lean_ctor_get(v_inst_3220_, 2);
lean_inc_ref(v_onFailure_3227_);
lean_dec_ref(v_inst_3220_);
v___x_3228_ = lean_unsigned_to_nat(0u);
v___x_3229_ = lean_apply_3(v_onFailure_3227_, v_handler_3221_, v_a_3226_, lean_box(0));
v___x_3230_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3228_, v___x_3222_, v___x_3229_, v___f_3223_);
return v___x_3230_;
}
else
{
lean_object* v___x_3231_; 
lean_dec_ref(v___f_3223_);
lean_dec(v_handler_3221_);
lean_dec_ref(v_inst_3220_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_x_3224_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3232_, lean_object* v_handler_3233_, lean_object* v___x_3234_, lean_object* v___f_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v___x_7997__boxed_3238_; lean_object* v_res_3239_; 
v___x_7997__boxed_3238_ = lean_unbox(v___x_3234_);
v_res_3239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3232_, v_handler_3233_, v___x_7997__boxed_3238_, v___f_3235_, v_x_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3240_, lean_object* v___f_3241_, uint8_t v___x_3242_, lean_object* v_inst_3243_, lean_object* v_handler_3244_, lean_object* v_inst_3245_, lean_object* v___f_3246_, lean_object* v___f_3247_, lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v___f_3247_);
lean_dec_ref(v___f_3246_);
lean_dec_ref(v_inst_3245_);
lean_dec(v_handler_3244_);
lean_dec_ref(v_inst_3243_);
lean_dec_ref(v___f_3241_);
v_a_3250_ = lean_ctor_get(v_x_3248_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_x_3248_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3252_ = v_x_3248_;
v_isShared_3253_ = v_isSharedCheck_3258_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v_x_3248_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3258_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3292_; 
v_a_3259_ = lean_ctor_get(v_x_3248_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_x_3248_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3261_ = v_x_3248_;
v_isShared_3262_ = v_isSharedCheck_3292_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v_x_3248_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3292_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v_snd_3263_; 
v_snd_3263_ = lean_ctor_get(v_a_3259_, 1);
lean_inc(v_snd_3263_);
if (lean_obj_tag(v_snd_3263_) == 0)
{
lean_object* v_fst_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v___f_3247_);
lean_dec_ref(v___f_3246_);
lean_dec_ref(v_inst_3245_);
lean_dec(v_handler_3244_);
lean_dec_ref(v_inst_3243_);
v_fst_3264_ = lean_ctor_get(v_a_3259_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_a_3259_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v_a_3259_, 1);
lean_dec(v_unused_3280_);
v___x_3266_ = v_a_3259_;
v_isShared_3267_ = v_isSharedCheck_3279_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_fst_3264_);
lean_dec(v_a_3259_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3279_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = lean_box(v___x_3240_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 1, v___x_3268_);
lean_ctor_set(v___x_3266_, 0, v_snd_3263_);
v___x_3270_ = v___x_3266_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_snd_3263_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_fst_3264_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_unsigned_to_nat(0u);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3271_);
v___x_3274_ = v___x_3261_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3271_);
v___x_3274_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
v___x_3276_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3272_, v___x_3240_, v___x_3275_, v___f_3241_);
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_fst_3281_; lean_object* v_val_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; lean_object* v___f_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_del_object(v___x_3261_);
lean_dec_ref(v___f_3241_);
v_fst_3281_ = lean_ctor_get(v_a_3259_, 0);
lean_inc_n(v_fst_3281_, 2);
lean_dec(v_a_3259_);
v_val_3282_ = lean_ctor_get(v_snd_3263_, 0);
lean_inc(v_val_3282_);
v___x_3283_ = lean_box(v___x_3242_);
v___f_3284_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3284_, 0, v_snd_3263_);
lean_closure_set(v___f_3284_, 1, v___x_3283_);
lean_closure_set(v___f_3284_, 2, v_fst_3281_);
v___x_3285_ = lean_box(v___x_3240_);
v___f_3286_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3286_, 0, v_inst_3243_);
lean_closure_set(v___f_3286_, 1, v_handler_3244_);
lean_closure_set(v___f_3286_, 2, v___x_3285_);
lean_closure_set(v___f_3286_, 3, v___f_3284_);
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3245_, v_fst_3281_, v_val_3282_);
v___x_3289_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3287_, v___x_3240_, v___x_3288_, v___f_3246_);
v___x_3290_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3287_, v___x_3240_, v___x_3289_, v___f_3286_);
v___x_3291_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3287_, v___x_3240_, v___x_3290_, v___f_3247_);
return v___x_3291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3293_, lean_object* v___f_3294_, lean_object* v___x_3295_, lean_object* v_inst_3296_, lean_object* v_handler_3297_, lean_object* v_inst_3298_, lean_object* v___f_3299_, lean_object* v___f_3300_, lean_object* v_x_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v___x_8022__boxed_3303_; uint8_t v___x_8024__boxed_3304_; lean_object* v_res_3305_; 
v___x_8022__boxed_3303_ = lean_unbox(v___x_3293_);
v___x_8024__boxed_3304_ = lean_unbox(v___x_3295_);
v_res_3305_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8022__boxed_3303_, v___f_3294_, v___x_8024__boxed_3304_, v_inst_3296_, v_handler_3297_, v_inst_3298_, v___f_3299_, v___f_3300_, v_x_3301_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3306_, lean_object* v_x_3307_){
_start:
{
if (lean_obj_tag(v_x_3307_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v_state_3306_);
v_a_3309_ = lean_ctor_get(v_x_3307_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_x_3307_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3311_ = v_x_3307_;
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v_x_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
}
else
{
lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3347_; 
v_isSharedCheck_3347_ = !lean_is_exclusive(v_x_3307_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v_x_3307_, 0);
lean_dec(v_unused_3348_);
v___x_3319_ = v_x_3307_;
v_isShared_3320_ = v_isSharedCheck_3347_;
goto v_resetjp_3318_;
}
else
{
lean_dec(v_x_3307_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3347_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_machine_3321_; lean_object* v_requestStream_3322_; lean_object* v_keepAliveTimeout_3323_; lean_object* v_currentTimeout_3324_; lean_object* v_headerTimeout_3325_; lean_object* v_response_3326_; lean_object* v_respStream_3327_; uint8_t v_requiresData_3328_; lean_object* v_expectData_3329_; lean_object* v_pendingHead_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3346_; 
v_machine_3321_ = lean_ctor_get(v_state_3306_, 0);
v_requestStream_3322_ = lean_ctor_get(v_state_3306_, 1);
v_keepAliveTimeout_3323_ = lean_ctor_get(v_state_3306_, 2);
v_currentTimeout_3324_ = lean_ctor_get(v_state_3306_, 3);
v_headerTimeout_3325_ = lean_ctor_get(v_state_3306_, 4);
v_response_3326_ = lean_ctor_get(v_state_3306_, 5);
v_respStream_3327_ = lean_ctor_get(v_state_3306_, 6);
v_requiresData_3328_ = lean_ctor_get_uint8(v_state_3306_, sizeof(void*)*9);
v_expectData_3329_ = lean_ctor_get(v_state_3306_, 7);
v_pendingHead_3330_ = lean_ctor_get(v_state_3306_, 8);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_state_3306_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3332_ = v_state_3306_;
v_isShared_3333_ = v_isSharedCheck_3346_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_pendingHead_3330_);
lean_inc(v_expectData_3329_);
lean_inc(v_respStream_3327_);
lean_inc(v_response_3326_);
lean_inc(v_headerTimeout_3325_);
lean_inc(v_currentTimeout_3324_);
lean_inc(v_keepAliveTimeout_3323_);
lean_inc(v_requestStream_3322_);
lean_inc(v_machine_3321_);
lean_dec(v_state_3306_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3346_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3338_; 
v___x_3334_ = lean_box(31);
v___x_3335_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3321_, v___x_3334_);
v___x_3336_ = 0;
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3335_);
v___x_3338_ = v___x_3332_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_requestStream_3322_);
lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_keepAliveTimeout_3323_);
lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_currentTimeout_3324_);
lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_headerTimeout_3325_);
lean_ctor_set(v_reuseFailAlloc_3345_, 5, v_response_3326_);
lean_ctor_set(v_reuseFailAlloc_3345_, 6, v_respStream_3327_);
lean_ctor_set(v_reuseFailAlloc_3345_, 7, v_expectData_3329_);
lean_ctor_set(v_reuseFailAlloc_3345_, 8, v_pendingHead_3330_);
lean_ctor_set_uint8(v_reuseFailAlloc_3345_, sizeof(void*)*9, v_requiresData_3328_);
v___x_3338_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
lean_ctor_set_uint8(v___x_3338_, sizeof(void*)*9 + 1, v___x_3336_);
v___x_3339_ = lean_box(v___x_3336_);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3340_);
v___x_3342_ = v___x_3319_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; 
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
return v___x_3343_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3349_, v_x_3350_);
return v_res_3352_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3358_ = lean_mk_io_user_error(v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_handler_3361_, lean_object* v_config_3362_, lean_object* v_event_3363_, lean_object* v_state_3364_){
_start:
{
switch(lean_obj_tag(v_event_3363_))
{
case 0:
{
lean_object* v_x_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_handler_3361_);
lean_dec_ref(v_inst_3360_);
lean_dec_ref(v_inst_3359_);
v_x_3366_ = lean_ctor_get(v_event_3363_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_event_3363_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3368_ = v_event_3363_;
v_isShared_3369_ = v_isSharedCheck_3473_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_x_3366_);
lean_dec(v_event_3363_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3473_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
if (lean_obj_tag(v_x_3366_) == 0)
{
lean_object* v_machine_3370_; lean_object* v_reader_3371_; lean_object* v_requestStream_3372_; lean_object* v_keepAliveTimeout_3373_; lean_object* v_currentTimeout_3374_; lean_object* v_headerTimeout_3375_; lean_object* v_response_3376_; lean_object* v_respStream_3377_; uint8_t v_requiresData_3378_; lean_object* v_expectData_3379_; uint8_t v_handlerDispatched_3380_; lean_object* v_pendingHead_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v_config_3362_);
v_machine_3370_ = lean_ctor_get(v_state_3364_, 0);
lean_inc_ref(v_machine_3370_);
v_reader_3371_ = lean_ctor_get(v_machine_3370_, 0);
lean_inc_ref(v_reader_3371_);
v_requestStream_3372_ = lean_ctor_get(v_state_3364_, 1);
v_keepAliveTimeout_3373_ = lean_ctor_get(v_state_3364_, 2);
v_currentTimeout_3374_ = lean_ctor_get(v_state_3364_, 3);
v_headerTimeout_3375_ = lean_ctor_get(v_state_3364_, 4);
v_response_3376_ = lean_ctor_get(v_state_3364_, 5);
v_respStream_3377_ = lean_ctor_get(v_state_3364_, 6);
v_requiresData_3378_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3379_ = lean_ctor_get(v_state_3364_, 7);
v_handlerDispatched_3380_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9 + 1);
v_pendingHead_3381_ = lean_ctor_get(v_state_3364_, 8);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_state_3364_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v_state_3364_, 0);
lean_dec(v_unused_3425_);
v___x_3383_ = v_state_3364_;
v_isShared_3384_ = v_isSharedCheck_3424_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_pendingHead_3381_);
lean_inc(v_expectData_3379_);
lean_inc(v_respStream_3377_);
lean_inc(v_response_3376_);
lean_inc(v_headerTimeout_3375_);
lean_inc(v_currentTimeout_3374_);
lean_inc(v_keepAliveTimeout_3373_);
lean_inc(v_requestStream_3372_);
lean_dec(v_state_3364_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3424_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_writer_3385_; lean_object* v_config_3386_; lean_object* v_events_3387_; lean_object* v_error_3388_; lean_object* v_instant_3389_; uint8_t v_keepAlive_3390_; uint8_t v_forcedFlush_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3422_; 
v_writer_3385_ = lean_ctor_get(v_machine_3370_, 1);
v_config_3386_ = lean_ctor_get(v_machine_3370_, 2);
v_events_3387_ = lean_ctor_get(v_machine_3370_, 3);
v_error_3388_ = lean_ctor_get(v_machine_3370_, 4);
v_instant_3389_ = lean_ctor_get(v_machine_3370_, 5);
v_keepAlive_3390_ = lean_ctor_get_uint8(v_machine_3370_, sizeof(void*)*6);
v_forcedFlush_3391_ = lean_ctor_get_uint8(v_machine_3370_, sizeof(void*)*6 + 1);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_machine_3370_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; 
v_unused_3423_ = lean_ctor_get(v_machine_3370_, 0);
lean_dec(v_unused_3423_);
v___x_3393_ = v_machine_3370_;
v_isShared_3394_ = v_isSharedCheck_3422_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_instant_3389_);
lean_inc(v_error_3388_);
lean_inc(v_events_3387_);
lean_inc(v_config_3386_);
lean_inc(v_writer_3385_);
lean_dec(v_machine_3370_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3422_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_state_3395_; lean_object* v_input_3396_; lean_object* v_messageHead_3397_; lean_object* v_messageCount_3398_; lean_object* v_bodyBytesRead_3399_; lean_object* v_headerBytesRead_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3421_; 
v_state_3395_ = lean_ctor_get(v_reader_3371_, 0);
v_input_3396_ = lean_ctor_get(v_reader_3371_, 1);
v_messageHead_3397_ = lean_ctor_get(v_reader_3371_, 2);
v_messageCount_3398_ = lean_ctor_get(v_reader_3371_, 3);
v_bodyBytesRead_3399_ = lean_ctor_get(v_reader_3371_, 4);
v_headerBytesRead_3400_ = lean_ctor_get(v_reader_3371_, 5);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_reader_3371_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3402_ = v_reader_3371_;
v_isShared_3403_ = v_isSharedCheck_3421_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_headerBytesRead_3400_);
lean_inc(v_bodyBytesRead_3399_);
lean_inc(v_messageCount_3398_);
lean_inc(v_messageHead_3397_);
lean_inc(v_input_3396_);
lean_inc(v_state_3395_);
lean_dec(v_reader_3371_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3421_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
uint8_t v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = 1;
if (v_isShared_3403_ == 0)
{
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_state_3395_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_input_3396_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_messageHead_3397_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_messageCount_3398_);
lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_bodyBytesRead_3399_);
lean_ctor_set(v_reuseFailAlloc_3420_, 5, v_headerBytesRead_3400_);
v___x_3406_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
uint8_t v___x_3407_; lean_object* v___x_3409_; 
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*6, v___x_3404_);
v___x_3407_ = 0;
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3406_);
v___x_3409_ = v___x_3393_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_writer_3385_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_config_3386_);
lean_ctor_set(v_reuseFailAlloc_3419_, 3, v_events_3387_);
lean_ctor_set(v_reuseFailAlloc_3419_, 4, v_error_3388_);
lean_ctor_set(v_reuseFailAlloc_3419_, 5, v_instant_3389_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*6, v_keepAlive_3390_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*6 + 1, v_forcedFlush_3391_);
v___x_3409_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3411_; 
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*6 + 2, v___x_3407_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3409_);
v___x_3411_ = v___x_3383_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_requestStream_3372_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_keepAliveTimeout_3373_);
lean_ctor_set(v_reuseFailAlloc_3418_, 3, v_currentTimeout_3374_);
lean_ctor_set(v_reuseFailAlloc_3418_, 4, v_headerTimeout_3375_);
lean_ctor_set(v_reuseFailAlloc_3418_, 5, v_response_3376_);
lean_ctor_set(v_reuseFailAlloc_3418_, 6, v_respStream_3377_);
lean_ctor_set(v_reuseFailAlloc_3418_, 7, v_expectData_3379_);
lean_ctor_set(v_reuseFailAlloc_3418_, 8, v_pendingHead_3381_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*9, v_requiresData_3378_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*9 + 1, v_handlerDispatched_3380_);
v___x_3411_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3412_ = lean_box(v___x_3407_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 1);
lean_ctor_set(v___x_3368_, 0, v___x_3413_);
v___x_3415_ = v___x_3368_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
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
lean_object* v_val_3426_; lean_object* v_machine_3427_; lean_object* v_requestStream_3428_; lean_object* v_keepAliveTimeout_3429_; lean_object* v_currentTimeout_3430_; lean_object* v_response_3431_; lean_object* v_respStream_3432_; uint8_t v_requiresData_3433_; lean_object* v_expectData_3434_; uint8_t v_handlerDispatched_3435_; lean_object* v_pendingHead_3436_; lean_object* v___f_3437_; 
lean_del_object(v___x_3368_);
v_val_3426_ = lean_ctor_get(v_x_3366_, 0);
lean_inc_n(v_val_3426_, 2);
lean_dec_ref_known(v_x_3366_, 1);
v_machine_3427_ = lean_ctor_get(v_state_3364_, 0);
v_requestStream_3428_ = lean_ctor_get(v_state_3364_, 1);
v_keepAliveTimeout_3429_ = lean_ctor_get(v_state_3364_, 2);
lean_inc(v_keepAliveTimeout_3429_);
v_currentTimeout_3430_ = lean_ctor_get(v_state_3364_, 3);
v_response_3431_ = lean_ctor_get(v_state_3364_, 5);
v_respStream_3432_ = lean_ctor_get(v_state_3364_, 6);
v_requiresData_3433_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3434_ = lean_ctor_get(v_state_3364_, 7);
v_handlerDispatched_3435_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9 + 1);
v_pendingHead_3436_ = lean_ctor_get(v_state_3364_, 8);
v___f_3437_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3437_, 0, v_val_3426_);
if (lean_obj_tag(v_keepAliveTimeout_3429_) == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec_ref(v___f_3437_);
lean_dec_ref(v_config_3362_);
v___x_3438_ = lean_box(0);
v___x_3439_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3426_, v___x_3438_, v_state_3364_);
return v___x_3439_;
}
else
{
lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3471_; 
lean_inc(v_pendingHead_3436_);
lean_inc(v_expectData_3434_);
lean_inc(v_respStream_3432_);
lean_inc_ref(v_response_3431_);
lean_inc(v_currentTimeout_3430_);
lean_inc_ref(v_requestStream_3428_);
lean_inc_ref(v_machine_3427_);
lean_dec(v_val_3426_);
lean_dec_ref(v_state_3364_);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_keepAliveTimeout_3429_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v_keepAliveTimeout_3429_, 0);
lean_dec(v_unused_3472_);
v___x_3441_ = v_keepAliveTimeout_3429_;
v_isShared_3442_ = v_isSharedCheck_3471_;
goto v_resetjp_3440_;
}
else
{
lean_dec(v_keepAliveTimeout_3429_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3471_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; lean_object* v_val_3449_; lean_object* v___x_3454_; 
v___x_3443_ = lean_box(v_requiresData_3433_);
v___x_3444_ = lean_box(v_handlerDispatched_3435_);
v___f_3445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3445_, 0, v_config_3362_);
lean_closure_set(v___f_3445_, 1, v_machine_3427_);
lean_closure_set(v___f_3445_, 2, v_requestStream_3428_);
lean_closure_set(v___f_3445_, 3, v_currentTimeout_3430_);
lean_closure_set(v___f_3445_, 4, v_response_3431_);
lean_closure_set(v___f_3445_, 5, v_respStream_3432_);
lean_closure_set(v___f_3445_, 6, v___x_3443_);
lean_closure_set(v___f_3445_, 7, v_expectData_3434_);
lean_closure_set(v___f_3445_, 8, v___x_3444_);
lean_closure_set(v___f_3445_, 9, v_pendingHead_3436_);
lean_closure_set(v___f_3445_, 10, v___f_3437_);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = 0;
v___x_3454_ = lean_get_current_time();
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 1);
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v_val_3449_ = v___x_3460_;
goto v___jp_3448_;
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
v_a_3463_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3454_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3454_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set_tag(v___x_3465_, 0);
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
v_val_3449_ = v___x_3468_;
goto v___jp_3448_;
}
}
}
v___jp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 0);
lean_ctor_set(v___x_3441_, 0, v_val_3449_);
v___x_3451_ = v___x_3441_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_val_3449_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3446_, v___x_3447_, v___x_3451_, v___f_3445_);
return v___x_3452_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3585_; 
lean_dec_ref(v_config_3362_);
lean_dec(v_handler_3361_);
lean_dec_ref(v_inst_3359_);
v_x_3474_ = lean_ctor_get(v_event_3363_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_event_3363_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3476_ = v_event_3363_;
v_isShared_3477_ = v_isSharedCheck_3585_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_x_3474_);
lean_dec(v_event_3363_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3585_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_x_3474_) == 0)
{
lean_object* v_machine_3478_; lean_object* v_requestStream_3479_; lean_object* v_keepAliveTimeout_3480_; lean_object* v_currentTimeout_3481_; lean_object* v_headerTimeout_3482_; lean_object* v_response_3483_; lean_object* v_respStream_3484_; uint8_t v_requiresData_3485_; lean_object* v_expectData_3486_; uint8_t v_handlerDispatched_3487_; lean_object* v_pendingHead_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; 
lean_del_object(v___x_3476_);
v_machine_3478_ = lean_ctor_get(v_state_3364_, 0);
lean_inc_ref_n(v_machine_3478_, 2);
v_requestStream_3479_ = lean_ctor_get(v_state_3364_, 1);
lean_inc_ref_n(v_requestStream_3479_, 2);
v_keepAliveTimeout_3480_ = lean_ctor_get(v_state_3364_, 2);
lean_inc_n(v_keepAliveTimeout_3480_, 2);
v_currentTimeout_3481_ = lean_ctor_get(v_state_3364_, 3);
lean_inc_n(v_currentTimeout_3481_, 2);
v_headerTimeout_3482_ = lean_ctor_get(v_state_3364_, 4);
lean_inc_n(v_headerTimeout_3482_, 2);
v_response_3483_ = lean_ctor_get(v_state_3364_, 5);
lean_inc_ref_n(v_response_3483_, 2);
v_respStream_3484_ = lean_ctor_get(v_state_3364_, 6);
lean_inc(v_respStream_3484_);
v_requiresData_3485_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3486_ = lean_ctor_get(v_state_3364_, 7);
lean_inc_n(v_expectData_3486_, 2);
v_handlerDispatched_3487_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9 + 1);
v_pendingHead_3488_ = lean_ctor_get(v_state_3364_, 8);
lean_inc_n(v_pendingHead_3488_, 2);
lean_dec_ref(v_state_3364_);
v___x_3489_ = lean_box(v_requiresData_3485_);
v___x_3490_ = lean_box(v_handlerDispatched_3487_);
v___f_3491_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3491_, 0, v_machine_3478_);
lean_closure_set(v___f_3491_, 1, v_requestStream_3479_);
lean_closure_set(v___f_3491_, 2, v_keepAliveTimeout_3480_);
lean_closure_set(v___f_3491_, 3, v_currentTimeout_3481_);
lean_closure_set(v___f_3491_, 4, v_headerTimeout_3482_);
lean_closure_set(v___f_3491_, 5, v_response_3483_);
lean_closure_set(v___f_3491_, 6, v___x_3489_);
lean_closure_set(v___f_3491_, 7, v_expectData_3486_);
lean_closure_set(v___f_3491_, 8, v___x_3490_);
lean_closure_set(v___f_3491_, 9, v_pendingHead_3488_);
if (lean_obj_tag(v_respStream_3484_) == 1)
{
lean_object* v_val_3492_; lean_object* v_close_3493_; lean_object* v_isClosed_3494_; lean_object* v___f_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec(v_pendingHead_3488_);
lean_dec(v_expectData_3486_);
lean_dec_ref(v_response_3483_);
lean_dec(v_headerTimeout_3482_);
lean_dec(v_currentTimeout_3481_);
lean_dec(v_keepAliveTimeout_3480_);
lean_dec_ref(v_requestStream_3479_);
lean_dec_ref(v_machine_3478_);
v_val_3492_ = lean_ctor_get(v_respStream_3484_, 0);
lean_inc_n(v_val_3492_, 2);
lean_dec_ref_known(v_respStream_3484_, 1);
v_close_3493_ = lean_ctor_get(v_inst_3360_, 1);
lean_inc_ref(v_close_3493_);
v_isClosed_3494_ = lean_ctor_get(v_inst_3360_, 2);
lean_inc_ref(v_isClosed_3494_);
lean_dec_ref(v_inst_3360_);
lean_inc_ref(v___f_3491_);
v___f_3495_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3495_, 0, v___f_3491_);
v___f_3496_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3496_, 0, v_close_3493_);
lean_closure_set(v___f_3496_, 1, v_val_3492_);
lean_closure_set(v___f_3496_, 2, v___f_3495_);
lean_closure_set(v___f_3496_, 3, v___f_3491_);
v___x_3497_ = lean_unsigned_to_nat(0u);
v___x_3498_ = 0;
v___x_3499_ = lean_apply_2(v_isClosed_3494_, v_val_3492_, lean_box(0));
v___x_3500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3497_, v___x_3498_, v___x_3499_, v___f_3496_);
return v___x_3500_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec_ref(v___f_3491_);
lean_dec(v_respStream_3484_);
lean_dec_ref(v_inst_3360_);
v___x_3501_ = lean_box(0);
v___x_3502_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3478_, v_requestStream_3479_, v_keepAliveTimeout_3480_, v_currentTimeout_3481_, v_headerTimeout_3482_, v_response_3483_, v_requiresData_3485_, v_expectData_3486_, v_handlerDispatched_3487_, v_pendingHead_3488_, v___x_3501_);
return v___x_3502_;
}
}
else
{
lean_object* v_val_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v_inst_3360_);
v_val_3503_ = lean_ctor_get(v_x_3474_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_x_3474_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3505_ = v_x_3474_;
v_isShared_3506_ = v_isSharedCheck_3584_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_val_3503_);
lean_dec(v_x_3474_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3584_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_machine_3507_; lean_object* v_requestStream_3508_; lean_object* v_keepAliveTimeout_3509_; lean_object* v_currentTimeout_3510_; lean_object* v_headerTimeout_3511_; lean_object* v_response_3512_; lean_object* v_respStream_3513_; uint8_t v_requiresData_3514_; lean_object* v_expectData_3515_; uint8_t v_handlerDispatched_3516_; lean_object* v_pendingHead_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3583_; 
v_machine_3507_ = lean_ctor_get(v_state_3364_, 0);
v_requestStream_3508_ = lean_ctor_get(v_state_3364_, 1);
v_keepAliveTimeout_3509_ = lean_ctor_get(v_state_3364_, 2);
v_currentTimeout_3510_ = lean_ctor_get(v_state_3364_, 3);
v_headerTimeout_3511_ = lean_ctor_get(v_state_3364_, 4);
v_response_3512_ = lean_ctor_get(v_state_3364_, 5);
v_respStream_3513_ = lean_ctor_get(v_state_3364_, 6);
v_requiresData_3514_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3515_ = lean_ctor_get(v_state_3364_, 7);
v_handlerDispatched_3516_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9 + 1);
v_pendingHead_3517_ = lean_ctor_get(v_state_3364_, 8);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_state_3364_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3519_ = v_state_3364_;
v_isShared_3520_ = v_isSharedCheck_3583_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_pendingHead_3517_);
lean_inc(v_expectData_3515_);
lean_inc(v_respStream_3513_);
lean_inc(v_response_3512_);
lean_inc(v_headerTimeout_3511_);
lean_inc(v_currentTimeout_3510_);
lean_inc(v_keepAliveTimeout_3509_);
lean_inc(v_requestStream_3508_);
lean_inc(v_machine_3507_);
lean_dec(v_state_3364_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3583_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___y_3522_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
v___x_3536_ = lean_mk_empty_array_with_capacity(v___x_3535_);
v___x_3537_ = lean_array_push(v___x_3536_, v_val_3503_);
v___x_3538_ = lean_array_get_size(v___x_3537_);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = lean_nat_dec_eq(v___x_3538_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v_reader_3541_; lean_object* v_writer_3542_; lean_object* v_config_3543_; lean_object* v_events_3544_; lean_object* v_error_3545_; lean_object* v_instant_3546_; uint8_t v_keepAlive_3547_; uint8_t v_forcedFlush_3548_; uint8_t v_pullBodyStalled_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3582_; 
v_reader_3541_ = lean_ctor_get(v_machine_3507_, 0);
v_writer_3542_ = lean_ctor_get(v_machine_3507_, 1);
v_config_3543_ = lean_ctor_get(v_machine_3507_, 2);
v_events_3544_ = lean_ctor_get(v_machine_3507_, 3);
v_error_3545_ = lean_ctor_get(v_machine_3507_, 4);
v_instant_3546_ = lean_ctor_get(v_machine_3507_, 5);
v_keepAlive_3547_ = lean_ctor_get_uint8(v_machine_3507_, sizeof(void*)*6);
v_forcedFlush_3548_ = lean_ctor_get_uint8(v_machine_3507_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3549_ = lean_ctor_get_uint8(v_machine_3507_, sizeof(void*)*6 + 2);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_machine_3507_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3551_ = v_machine_3507_;
v_isShared_3552_ = v_isSharedCheck_3582_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_instant_3546_);
lean_inc(v_error_3545_);
lean_inc(v_events_3544_);
lean_inc(v_config_3543_);
lean_inc(v_writer_3542_);
lean_inc(v_reader_3541_);
lean_dec(v_machine_3507_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3582_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___y_3554_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3576_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_3577_ = lean_nat_dec_lt(v___x_3539_, v___x_3538_);
if (v___x_3577_ == 0)
{
v___y_3554_ = v___x_3539_;
goto v___jp_3553_;
}
else
{
lean_object* v___f_3578_; size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_3581_; 
v___f_3578_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3579_ = ((size_t)0ULL);
v___x_3580_ = lean_usize_of_nat(v___x_3538_);
lean_inc_ref(v___x_3537_);
v___x_3581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3576_, v___f_3578_, v___x_3537_, v___x_3579_, v___x_3580_, v___x_3539_);
v___y_3554_ = v___x_3581_;
goto v___jp_3553_;
}
v___jp_3553_:
{
lean_object* v_userData_3555_; lean_object* v_outputData_3556_; lean_object* v_state_3557_; lean_object* v_knownSize_3558_; lean_object* v_messageHead_3559_; uint8_t v_sentMessage_3560_; uint8_t v_userClosedBody_3561_; uint8_t v_omitBody_3562_; lean_object* v_userDataBytes_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3575_; 
v_userData_3555_ = lean_ctor_get(v_writer_3542_, 0);
v_outputData_3556_ = lean_ctor_get(v_writer_3542_, 1);
v_state_3557_ = lean_ctor_get(v_writer_3542_, 2);
v_knownSize_3558_ = lean_ctor_get(v_writer_3542_, 3);
v_messageHead_3559_ = lean_ctor_get(v_writer_3542_, 4);
v_sentMessage_3560_ = lean_ctor_get_uint8(v_writer_3542_, sizeof(void*)*6);
v_userClosedBody_3561_ = lean_ctor_get_uint8(v_writer_3542_, sizeof(void*)*6 + 1);
v_omitBody_3562_ = lean_ctor_get_uint8(v_writer_3542_, sizeof(void*)*6 + 2);
v_userDataBytes_3563_ = lean_ctor_get(v_writer_3542_, 5);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_writer_3542_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3565_ = v_writer_3542_;
v_isShared_3566_ = v_isSharedCheck_3575_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_userDataBytes_3563_);
lean_inc(v_messageHead_3559_);
lean_inc(v_knownSize_3558_);
lean_inc(v_state_3557_);
lean_inc(v_outputData_3556_);
lean_inc(v_userData_3555_);
lean_dec(v_writer_3542_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3575_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3567_ = l_Array_append___redArg(v_userData_3555_, v___x_3537_);
lean_dec_ref(v___x_3537_);
v___x_3568_ = lean_nat_add(v_userDataBytes_3563_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec(v_userDataBytes_3563_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 5, v___x_3568_);
lean_ctor_set(v___x_3565_, 0, v___x_3567_);
v___x_3570_ = v___x_3565_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_outputData_3556_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_state_3557_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_knownSize_3558_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_messageHead_3559_);
lean_ctor_set(v_reuseFailAlloc_3574_, 5, v___x_3568_);
lean_ctor_set_uint8(v_reuseFailAlloc_3574_, sizeof(void*)*6, v_sentMessage_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3574_, sizeof(void*)*6 + 1, v_userClosedBody_3561_);
lean_ctor_set_uint8(v_reuseFailAlloc_3574_, sizeof(void*)*6 + 2, v_omitBody_3562_);
v___x_3570_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3572_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 1, v___x_3570_);
v___x_3572_ = v___x_3551_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_reader_3541_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v_config_3543_);
lean_ctor_set(v_reuseFailAlloc_3573_, 3, v_events_3544_);
lean_ctor_set(v_reuseFailAlloc_3573_, 4, v_error_3545_);
lean_ctor_set(v_reuseFailAlloc_3573_, 5, v_instant_3546_);
lean_ctor_set_uint8(v_reuseFailAlloc_3573_, sizeof(void*)*6, v_keepAlive_3547_);
lean_ctor_set_uint8(v_reuseFailAlloc_3573_, sizeof(void*)*6 + 1, v_forcedFlush_3548_);
lean_ctor_set_uint8(v_reuseFailAlloc_3573_, sizeof(void*)*6 + 2, v_pullBodyStalled_3549_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
v___y_3522_ = v___x_3572_;
goto v___jp_3521_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3537_);
v___y_3522_ = v_machine_3507_;
goto v___jp_3521_;
}
v___jp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___y_3522_);
v___x_3524_ = v___x_3519_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___y_3522_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_requestStream_3508_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_keepAliveTimeout_3509_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_currentTimeout_3510_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_headerTimeout_3511_);
lean_ctor_set(v_reuseFailAlloc_3534_, 5, v_response_3512_);
lean_ctor_set(v_reuseFailAlloc_3534_, 6, v_respStream_3513_);
lean_ctor_set(v_reuseFailAlloc_3534_, 7, v_expectData_3515_);
lean_ctor_set(v_reuseFailAlloc_3534_, 8, v_pendingHead_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*9, v_requiresData_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*9 + 1, v_handlerDispatched_3516_);
v___x_3524_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3525_ = 0;
v___x_3526_ = lean_box(v___x_3525_);
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3524_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3527_);
v___x_3529_ = v___x_3505_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set_tag(v___x_3476_, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3529_);
v___x_3531_ = v___x_3476_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
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
uint8_t v_x_3586_; 
lean_dec_ref(v_config_3362_);
lean_dec_ref(v_inst_3360_);
v_x_3586_ = lean_ctor_get_uint8(v_event_3363_, 0);
lean_dec_ref_known(v_event_3363_, 0);
if (v_x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec(v_handler_3361_);
lean_dec_ref(v_inst_3359_);
v___x_3587_ = lean_box(v_x_3586_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v_state_3364_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
else
{
lean_object* v_machine_3591_; lean_object* v_requestStream_3592_; lean_object* v_keepAliveTimeout_3593_; lean_object* v_currentTimeout_3594_; lean_object* v_headerTimeout_3595_; lean_object* v_response_3596_; lean_object* v_respStream_3597_; uint8_t v_requiresData_3598_; lean_object* v_expectData_3599_; uint8_t v_handlerDispatched_3600_; lean_object* v_pendingHead_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3651_; 
v_machine_3591_ = lean_ctor_get(v_state_3364_, 0);
v_requestStream_3592_ = lean_ctor_get(v_state_3364_, 1);
v_keepAliveTimeout_3593_ = lean_ctor_get(v_state_3364_, 2);
v_currentTimeout_3594_ = lean_ctor_get(v_state_3364_, 3);
v_headerTimeout_3595_ = lean_ctor_get(v_state_3364_, 4);
v_response_3596_ = lean_ctor_get(v_state_3364_, 5);
v_respStream_3597_ = lean_ctor_get(v_state_3364_, 6);
v_requiresData_3598_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3599_ = lean_ctor_get(v_state_3364_, 7);
v_handlerDispatched_3600_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9 + 1);
v_pendingHead_3601_ = lean_ctor_get(v_state_3364_, 8);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_state_3364_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3603_ = v_state_3364_;
v_isShared_3604_ = v_isSharedCheck_3651_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_pendingHead_3601_);
lean_inc(v_expectData_3599_);
lean_inc(v_respStream_3597_);
lean_inc(v_response_3596_);
lean_inc(v_headerTimeout_3595_);
lean_inc(v_currentTimeout_3594_);
lean_inc(v_keepAliveTimeout_3593_);
lean_inc(v_requestStream_3592_);
lean_inc(v_machine_3591_);
lean_dec(v_state_3364_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3651_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
uint8_t v___x_3605_; lean_object* v___x_3606_; lean_object* v_fst_3607_; lean_object* v_snd_3608_; lean_object* v_reader_3609_; lean_object* v_writer_3610_; lean_object* v_config_3611_; lean_object* v_events_3612_; lean_object* v_error_3613_; lean_object* v_instant_3614_; uint8_t v_keepAlive_3615_; uint8_t v_forcedFlush_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3650_; 
v___x_3605_ = 0;
v___x_3606_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3605_, v_machine_3591_);
v_fst_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_fst_3607_);
v_snd_3608_ = lean_ctor_get(v___x_3606_, 1);
lean_inc(v_snd_3608_);
lean_dec_ref(v___x_3606_);
v_reader_3609_ = lean_ctor_get(v_fst_3607_, 0);
v_writer_3610_ = lean_ctor_get(v_fst_3607_, 1);
v_config_3611_ = lean_ctor_get(v_fst_3607_, 2);
v_events_3612_ = lean_ctor_get(v_fst_3607_, 3);
v_error_3613_ = lean_ctor_get(v_fst_3607_, 4);
v_instant_3614_ = lean_ctor_get(v_fst_3607_, 5);
v_keepAlive_3615_ = lean_ctor_get_uint8(v_fst_3607_, sizeof(void*)*6);
v_forcedFlush_3616_ = lean_ctor_get_uint8(v_fst_3607_, sizeof(void*)*6 + 1);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_fst_3607_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3618_ = v_fst_3607_;
v_isShared_3619_ = v_isSharedCheck_3650_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_instant_3614_);
lean_inc(v_error_3613_);
lean_inc(v_events_3612_);
lean_inc(v_config_3611_);
lean_inc(v_writer_3610_);
lean_inc(v_reader_3609_);
lean_dec(v_fst_3607_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3650_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___f_3620_; lean_object* v___f_3621_; uint8_t v___y_3623_; 
v___f_3620_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_3621_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_3621_, 0, v_inst_3359_);
lean_closure_set(v___f_3621_, 1, v_handler_3361_);
if (lean_obj_tag(v_snd_3608_) == 0)
{
uint8_t v_sentMessage_3646_; 
v_sentMessage_3646_ = lean_ctor_get_uint8(v_writer_3610_, sizeof(void*)*6);
if (v_sentMessage_3646_ == 0)
{
lean_object* v_state_3647_; 
v_state_3647_ = lean_ctor_get(v_reader_3609_, 0);
if (lean_obj_tag(v_state_3647_) == 2)
{
v___y_3623_ = v_x_3586_;
goto v___jp_3622_;
}
else
{
v___y_3623_ = v_sentMessage_3646_;
goto v___jp_3622_;
}
}
else
{
uint8_t v___x_3648_; 
v___x_3648_ = 0;
v___y_3623_ = v___x_3648_;
goto v___jp_3622_;
}
}
else
{
uint8_t v___x_3649_; 
v___x_3649_ = 0;
v___y_3623_ = v___x_3649_;
goto v___jp_3622_;
}
v___jp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3619_ == 0)
{
v___x_3625_ = v___x_3618_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_reader_3609_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_writer_3610_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_config_3611_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_events_3612_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_error_3613_);
lean_ctor_set(v_reuseFailAlloc_3645_, 5, v_instant_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3645_, sizeof(void*)*6, v_keepAlive_3615_);
lean_ctor_set_uint8(v_reuseFailAlloc_3645_, sizeof(void*)*6 + 1, v_forcedFlush_3616_);
v___x_3625_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v_st_3627_; 
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*6 + 2, v___y_3623_);
lean_inc_ref(v_requestStream_3592_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3625_);
v_st_3627_ = v___x_3603_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_requestStream_3592_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_keepAliveTimeout_3593_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_currentTimeout_3594_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_headerTimeout_3595_);
lean_ctor_set(v_reuseFailAlloc_3644_, 5, v_response_3596_);
lean_ctor_set(v_reuseFailAlloc_3644_, 6, v_respStream_3597_);
lean_ctor_set(v_reuseFailAlloc_3644_, 7, v_expectData_3599_);
lean_ctor_set(v_reuseFailAlloc_3644_, 8, v_pendingHead_3601_);
lean_ctor_set_uint8(v_reuseFailAlloc_3644_, sizeof(void*)*9, v_requiresData_3598_);
lean_ctor_set_uint8(v_reuseFailAlloc_3644_, sizeof(void*)*9 + 1, v_handlerDispatched_3600_);
v_st_3627_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___f_3628_; 
lean_inc_ref(v_st_3627_);
v___f_3628_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3628_, 0, v_st_3627_);
if (lean_obj_tag(v_snd_3608_) == 1)
{
lean_object* v_val_3629_; uint8_t v_final_3630_; uint8_t v_incomplete_3631_; lean_object* v_chunk_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___f_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec_ref(v_st_3627_);
v_val_3629_ = lean_ctor_get(v_snd_3608_, 0);
lean_inc(v_val_3629_);
lean_dec_ref_known(v_snd_3608_, 1);
v_final_3630_ = lean_ctor_get_uint8(v_val_3629_, sizeof(void*)*1);
v_incomplete_3631_ = lean_ctor_get_uint8(v_val_3629_, sizeof(void*)*1 + 1);
v_chunk_3632_ = lean_ctor_get(v_val_3629_, 0);
lean_inc_ref(v_chunk_3632_);
lean_dec(v_val_3629_);
lean_inc_ref_n(v___f_3628_, 2);
v___f_3633_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3633_, 0, v___f_3628_);
lean_inc_ref_n(v_requestStream_3592_, 2);
v___f_3634_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3634_, 0, v_requestStream_3592_);
lean_closure_set(v___f_3634_, 1, v___f_3633_);
lean_closure_set(v___f_3634_, 2, v___f_3628_);
v___x_3635_ = lean_box(v_final_3630_);
v___f_3636_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_3636_, 0, v___x_3635_);
lean_closure_set(v___f_3636_, 1, v___f_3628_);
lean_closure_set(v___f_3636_, 2, v___f_3620_);
lean_closure_set(v___f_3636_, 3, v_requestStream_3592_);
lean_closure_set(v___f_3636_, 4, v___f_3634_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = 0;
v___x_3639_ = l_Std_Http_Body_Stream_send(v_requestStream_3592_, v_chunk_3632_, v_incomplete_3631_);
v___x_3640_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3637_, v___x_3638_, v___x_3639_, v___f_3621_);
v___x_3641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3637_, v___x_3638_, v___x_3640_, v___f_3636_);
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
lean_dec_ref(v___f_3628_);
lean_dec_ref(v___f_3621_);
lean_dec(v_snd_3608_);
lean_dec_ref(v_requestStream_3592_);
v___x_3642_ = lean_box(0);
v___x_3643_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3627_, v___x_3642_);
return v___x_3643_;
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
lean_object* v_x_3652_; 
v_x_3652_ = lean_ctor_get(v_event_3363_, 0);
lean_inc_ref(v_x_3652_);
lean_dec_ref_known(v_event_3363_, 1);
if (lean_obj_tag(v_x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v_onFailure_3654_; lean_object* v___f_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v_config_3362_);
lean_dec_ref(v_inst_3360_);
v_a_3653_ = lean_ctor_get(v_x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v_x_3652_, 1);
v_onFailure_3654_ = lean_ctor_get(v_inst_3359_, 2);
lean_inc_ref(v_onFailure_3654_);
lean_dec_ref(v_inst_3359_);
v___f_3655_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3655_, 0, v_state_3364_);
v___x_3656_ = lean_unsigned_to_nat(0u);
v___x_3657_ = 0;
v___x_3658_ = lean_apply_3(v_onFailure_3654_, v_handler_3361_, v_a_3653_, lean_box(0));
v___x_3659_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3656_, v___x_3657_, v___x_3658_, v___f_3655_);
return v___x_3659_;
}
else
{
lean_object* v_machine_3660_; lean_object* v_reader_3661_; lean_object* v_state_3662_; 
v_machine_3660_ = lean_ctor_get(v_state_3364_, 0);
lean_inc_ref(v_machine_3660_);
v_reader_3661_ = lean_ctor_get(v_machine_3660_, 0);
v_state_3662_ = lean_ctor_get(v_reader_3661_, 0);
if (lean_obj_tag(v_state_3662_) == 7)
{
lean_object* v_a_3663_; lean_object* v_requestStream_3664_; lean_object* v_keepAliveTimeout_3665_; lean_object* v_currentTimeout_3666_; lean_object* v_headerTimeout_3667_; lean_object* v_response_3668_; lean_object* v_respStream_3669_; uint8_t v_requiresData_3670_; lean_object* v_expectData_3671_; lean_object* v_pendingHead_3672_; lean_object* v_close_3673_; lean_object* v_isClosed_3674_; lean_object* v_body_3675_; lean_object* v___x_3676_; lean_object* v___f_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_dec_ref(v_config_3362_);
lean_dec(v_handler_3361_);
lean_dec_ref(v_inst_3359_);
v_a_3663_ = lean_ctor_get(v_x_3652_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v_x_3652_, 1);
v_requestStream_3664_ = lean_ctor_get(v_state_3364_, 1);
lean_inc_ref(v_requestStream_3664_);
v_keepAliveTimeout_3665_ = lean_ctor_get(v_state_3364_, 2);
lean_inc(v_keepAliveTimeout_3665_);
v_currentTimeout_3666_ = lean_ctor_get(v_state_3364_, 3);
lean_inc(v_currentTimeout_3666_);
v_headerTimeout_3667_ = lean_ctor_get(v_state_3364_, 4);
lean_inc(v_headerTimeout_3667_);
v_response_3668_ = lean_ctor_get(v_state_3364_, 5);
lean_inc_ref(v_response_3668_);
v_respStream_3669_ = lean_ctor_get(v_state_3364_, 6);
lean_inc(v_respStream_3669_);
v_requiresData_3670_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3671_ = lean_ctor_get(v_state_3364_, 7);
lean_inc(v_expectData_3671_);
v_pendingHead_3672_ = lean_ctor_get(v_state_3364_, 8);
lean_inc(v_pendingHead_3672_);
lean_dec_ref(v_state_3364_);
v_close_3673_ = lean_ctor_get(v_inst_3360_, 1);
lean_inc_ref(v_close_3673_);
v_isClosed_3674_ = lean_ctor_get(v_inst_3360_, 2);
lean_inc_ref(v_isClosed_3674_);
lean_dec_ref(v_inst_3360_);
v_body_3675_ = lean_ctor_get(v_a_3663_, 1);
lean_inc_n(v_body_3675_, 2);
lean_dec(v_a_3663_);
v___x_3676_ = lean_box(v_requiresData_3670_);
v___f_3677_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3677_, 0, v_machine_3660_);
lean_closure_set(v___f_3677_, 1, v_requestStream_3664_);
lean_closure_set(v___f_3677_, 2, v_keepAliveTimeout_3665_);
lean_closure_set(v___f_3677_, 3, v_currentTimeout_3666_);
lean_closure_set(v___f_3677_, 4, v_headerTimeout_3667_);
lean_closure_set(v___f_3677_, 5, v_response_3668_);
lean_closure_set(v___f_3677_, 6, v_respStream_3669_);
lean_closure_set(v___f_3677_, 7, v___x_3676_);
lean_closure_set(v___f_3677_, 8, v_expectData_3671_);
lean_closure_set(v___f_3677_, 9, v_pendingHead_3672_);
lean_inc_ref(v___f_3677_);
v___f_3678_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3678_, 0, v___f_3677_);
v___f_3679_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3679_, 0, v_close_3673_);
lean_closure_set(v___f_3679_, 1, v_body_3675_);
lean_closure_set(v___f_3679_, 2, v___f_3678_);
lean_closure_set(v___f_3679_, 3, v___f_3677_);
v___x_3680_ = lean_unsigned_to_nat(0u);
v___x_3681_ = 0;
v___x_3682_ = lean_apply_2(v_isClosed_3674_, v_body_3675_, lean_box(0));
v___x_3683_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3680_, v___x_3681_, v___x_3682_, v___f_3679_);
return v___x_3683_;
}
else
{
lean_object* v_a_3684_; lean_object* v_requestStream_3685_; lean_object* v_keepAliveTimeout_3686_; lean_object* v_currentTimeout_3687_; lean_object* v_headerTimeout_3688_; lean_object* v_response_3689_; uint8_t v_requiresData_3690_; lean_object* v_expectData_3691_; lean_object* v_pendingHead_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___f_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_a_3684_ = lean_ctor_get(v_x_3652_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v_x_3652_, 1);
v_requestStream_3685_ = lean_ctor_get(v_state_3364_, 1);
lean_inc_ref(v_requestStream_3685_);
v_keepAliveTimeout_3686_ = lean_ctor_get(v_state_3364_, 2);
lean_inc(v_keepAliveTimeout_3686_);
v_currentTimeout_3687_ = lean_ctor_get(v_state_3364_, 3);
lean_inc(v_currentTimeout_3687_);
v_headerTimeout_3688_ = lean_ctor_get(v_state_3364_, 4);
lean_inc(v_headerTimeout_3688_);
v_response_3689_ = lean_ctor_get(v_state_3364_, 5);
lean_inc_ref(v_response_3689_);
v_requiresData_3690_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3691_ = lean_ctor_get(v_state_3364_, 7);
lean_inc(v_expectData_3691_);
v_pendingHead_3692_ = lean_ctor_get(v_state_3364_, 8);
lean_inc(v_pendingHead_3692_);
lean_dec_ref(v_state_3364_);
v___x_3693_ = 0;
v___x_3694_ = lean_box(v_requiresData_3690_);
v___x_3695_ = lean_box(v___x_3693_);
v___f_3696_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3696_, 0, v_requestStream_3685_);
lean_closure_set(v___f_3696_, 1, v_keepAliveTimeout_3686_);
lean_closure_set(v___f_3696_, 2, v_currentTimeout_3687_);
lean_closure_set(v___f_3696_, 3, v_headerTimeout_3688_);
lean_closure_set(v___f_3696_, 4, v_response_3689_);
lean_closure_set(v___f_3696_, 5, v___x_3694_);
lean_closure_set(v___f_3696_, 6, v_expectData_3691_);
lean_closure_set(v___f_3696_, 7, v___x_3695_);
lean_closure_set(v___f_3696_, 8, v_pendingHead_3692_);
v___f_3697_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3697_, 0, v___f_3696_);
v___f_3698_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3699_ = 1;
v___x_3700_ = lean_box(v___x_3693_);
v___x_3701_ = lean_box(v___x_3699_);
lean_inc_ref(v_inst_3360_);
lean_inc_ref(v___f_3697_);
v___f_3702_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3702_, 0, v___x_3700_);
lean_closure_set(v___f_3702_, 1, v___f_3697_);
lean_closure_set(v___f_3702_, 2, v___x_3701_);
lean_closure_set(v___f_3702_, 3, v_inst_3359_);
lean_closure_set(v___f_3702_, 4, v_handler_3361_);
lean_closure_set(v___f_3702_, 5, v_inst_3360_);
lean_closure_set(v___f_3702_, 6, v___f_3698_);
lean_closure_set(v___f_3702_, 7, v___f_3697_);
v___x_3703_ = lean_unsigned_to_nat(0u);
v___x_3704_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3360_, v_config_3362_, v_machine_3660_, v_a_3684_);
v___x_3705_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3703_, v___x_3693_, v___x_3704_, v___f_3702_);
return v___x_3705_;
}
}
}
case 4:
{
lean_object* v_onFailure_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec_ref(v_config_3362_);
lean_dec_ref(v_inst_3360_);
v_onFailure_3706_ = lean_ctor_get(v_inst_3359_, 2);
lean_inc_ref(v_onFailure_3706_);
lean_dec_ref(v_inst_3359_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3707_, 0, v_state_3364_);
v___x_3708_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = 0;
v___x_3711_ = lean_apply_3(v_onFailure_3706_, v_handler_3361_, v___x_3708_, lean_box(0));
v___x_3712_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3709_, v___x_3710_, v___x_3711_, v___f_3707_);
return v___x_3712_;
}
case 5:
{
lean_object* v_machine_3713_; lean_object* v_requestStream_3714_; lean_object* v_keepAliveTimeout_3715_; lean_object* v_currentTimeout_3716_; lean_object* v_headerTimeout_3717_; lean_object* v_response_3718_; lean_object* v_respStream_3719_; uint8_t v_requiresData_3720_; lean_object* v_expectData_3721_; lean_object* v_pendingHead_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v_config_3362_);
lean_dec(v_handler_3361_);
lean_dec_ref(v_inst_3360_);
lean_dec_ref(v_inst_3359_);
v_machine_3713_ = lean_ctor_get(v_state_3364_, 0);
v_requestStream_3714_ = lean_ctor_get(v_state_3364_, 1);
v_keepAliveTimeout_3715_ = lean_ctor_get(v_state_3364_, 2);
v_currentTimeout_3716_ = lean_ctor_get(v_state_3364_, 3);
v_headerTimeout_3717_ = lean_ctor_get(v_state_3364_, 4);
v_response_3718_ = lean_ctor_get(v_state_3364_, 5);
v_respStream_3719_ = lean_ctor_get(v_state_3364_, 6);
v_requiresData_3720_ = lean_ctor_get_uint8(v_state_3364_, sizeof(void*)*9);
v_expectData_3721_ = lean_ctor_get(v_state_3364_, 7);
v_pendingHead_3722_ = lean_ctor_get(v_state_3364_, 8);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_state_3364_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3724_ = v_state_3364_;
v_isShared_3725_ = v_isSharedCheck_3736_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_pendingHead_3722_);
lean_inc(v_expectData_3721_);
lean_inc(v_respStream_3719_);
lean_inc(v_response_3718_);
lean_inc(v_headerTimeout_3717_);
lean_inc(v_currentTimeout_3716_);
lean_inc(v_keepAliveTimeout_3715_);
lean_inc(v_requestStream_3714_);
lean_inc(v_machine_3713_);
lean_dec(v_state_3364_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3736_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3730_; 
v___x_3726_ = lean_box(55);
v___x_3727_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3713_, v___x_3726_);
v___x_3728_ = 0;
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3727_);
v___x_3730_ = v___x_3724_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_requestStream_3714_);
lean_ctor_set(v_reuseFailAlloc_3735_, 2, v_keepAliveTimeout_3715_);
lean_ctor_set(v_reuseFailAlloc_3735_, 3, v_currentTimeout_3716_);
lean_ctor_set(v_reuseFailAlloc_3735_, 4, v_headerTimeout_3717_);
lean_ctor_set(v_reuseFailAlloc_3735_, 5, v_response_3718_);
lean_ctor_set(v_reuseFailAlloc_3735_, 6, v_respStream_3719_);
lean_ctor_set(v_reuseFailAlloc_3735_, 7, v_expectData_3721_);
lean_ctor_set(v_reuseFailAlloc_3735_, 8, v_pendingHead_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, sizeof(void*)*9, v_requiresData_3720_);
v___x_3730_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*9 + 1, v___x_3728_);
v___x_3731_ = lean_box(v___x_3728_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
}
default: 
{
uint8_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec_ref(v_config_3362_);
lean_dec(v_handler_3361_);
lean_dec_ref(v_inst_3360_);
lean_dec_ref(v_inst_3359_);
v___x_3737_ = 1;
v___x_3738_ = lean_box(v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_state_3364_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
return v___x_3741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3742_, lean_object* v_inst_3743_, lean_object* v_handler_3744_, lean_object* v_config_3745_, lean_object* v_event_3746_, lean_object* v_state_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3742_, v_inst_3743_, v_handler_3744_, v_config_3745_, v_event_3746_, v_state_3747_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3750_, lean_object* v_00_u03b2_3751_, lean_object* v_inst_3752_, lean_object* v_inst_3753_, lean_object* v_handler_3754_, lean_object* v_config_3755_, lean_object* v_event_3756_, lean_object* v_state_3757_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3752_, v_inst_3753_, v_handler_3754_, v_config_3755_, v_event_3756_, v_state_3757_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3760_, lean_object* v_00_u03b2_3761_, lean_object* v_inst_3762_, lean_object* v_inst_3763_, lean_object* v_handler_3764_, lean_object* v_config_3765_, lean_object* v_event_3766_, lean_object* v_state_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3760_, v_00_u03b2_3761_, v_inst_3762_, v_inst_3763_, v_handler_3764_, v_config_3765_, v_event_3766_, v_state_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_expectData_3770_, lean_object* v_respStream_3771_, lean_object* v_currentTimeout_3772_, lean_object* v_keepAliveTimeout_3773_, lean_object* v_headerTimeout_3774_, lean_object* v_connectionContext_3775_, uint8_t v_handlerDispatched_3776_, lean_object* v_response_3777_, lean_object* v_socket_3778_, uint8_t v_requiresData_3779_, uint8_t v_sentMessage_3780_, lean_object* v_reader_3781_, uint8_t v_requestBodyInterested_3782_, lean_object* v_requestBody_3783_){
_start:
{
lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3792_; uint8_t v___y_3798_; uint8_t v___y_3801_; uint8_t v___y_3802_; uint8_t v___y_3804_; uint8_t v___y_3805_; uint8_t v___y_3806_; uint8_t v___y_3808_; uint8_t v___y_3809_; uint8_t v___y_3812_; 
if (v_handlerDispatched_3776_ == 0)
{
uint8_t v___x_3815_; 
v___x_3815_ = 1;
v___y_3812_ = v___x_3815_;
goto v___jp_3811_;
}
else
{
uint8_t v___x_3816_; 
v___x_3816_ = 0;
v___y_3812_ = v___x_3816_;
goto v___jp_3811_;
}
v___jp_3785_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3788_, 0, v___y_3786_);
lean_ctor_set(v___x_3788_, 1, v_expectData_3770_);
lean_ctor_set(v___x_3788_, 2, v___y_3787_);
lean_ctor_set(v___x_3788_, 3, v_respStream_3771_);
lean_ctor_set(v___x_3788_, 4, v_requestBody_3783_);
lean_ctor_set(v___x_3788_, 5, v_currentTimeout_3772_);
lean_ctor_set(v___x_3788_, 6, v_keepAliveTimeout_3773_);
lean_ctor_set(v___x_3788_, 7, v_headerTimeout_3774_);
lean_ctor_set(v___x_3788_, 8, v_connectionContext_3775_);
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
return v___x_3790_;
}
v___jp_3791_:
{
if (v_handlerDispatched_3776_ == 0)
{
lean_object* v___x_3793_; 
lean_dec_ref(v_response_3777_);
v___x_3793_ = lean_box(0);
v___y_3786_ = v___y_3792_;
v___y_3787_ = v___x_3793_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v_response_3777_);
v___y_3786_ = v___y_3792_;
v___y_3787_ = v___x_3794_;
goto v___jp_3785_;
}
}
v___jp_3795_:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_socket_3778_);
v___y_3792_ = v___x_3796_;
goto v___jp_3791_;
}
v___jp_3797_:
{
if (v_requiresData_3779_ == 0)
{
if (v___y_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_socket_3778_);
v___x_3799_ = lean_box(0);
v___y_3792_ = v___x_3799_;
goto v___jp_3791_;
}
else
{
goto v___jp_3795_;
}
}
else
{
goto v___jp_3795_;
}
}
v___jp_3800_:
{
if (v___y_3801_ == 0)
{
v___y_3798_ = v___y_3802_;
goto v___jp_3797_;
}
else
{
v___y_3798_ = v___y_3801_;
goto v___jp_3797_;
}
}
v___jp_3803_:
{
if (v___y_3804_ == 0)
{
v___y_3801_ = v___y_3805_;
v___y_3802_ = v___y_3806_;
goto v___jp_3800_;
}
else
{
v___y_3801_ = v___y_3805_;
v___y_3802_ = v___y_3804_;
goto v___jp_3800_;
}
}
v___jp_3807_:
{
if (v_sentMessage_3780_ == 0)
{
lean_object* v_state_3810_; 
v_state_3810_ = lean_ctor_get(v_reader_3781_, 0);
if (lean_obj_tag(v_state_3810_) == 2)
{
v___y_3804_ = v___y_3809_;
v___y_3805_ = v___y_3808_;
v___y_3806_ = v_requestBodyInterested_3782_;
goto v___jp_3803_;
}
else
{
v___y_3804_ = v___y_3809_;
v___y_3805_ = v___y_3808_;
v___y_3806_ = v_sentMessage_3780_;
goto v___jp_3803_;
}
}
else
{
v___y_3804_ = v___y_3809_;
v___y_3805_ = v___y_3808_;
v___y_3806_ = v_sentMessage_3780_;
goto v___jp_3803_;
}
}
v___jp_3811_:
{
if (lean_obj_tag(v_respStream_3771_) == 0)
{
uint8_t v___x_3813_; 
v___x_3813_ = 0;
v___y_3808_ = v___y_3812_;
v___y_3809_ = v___x_3813_;
goto v___jp_3807_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = 1;
v___y_3808_ = v___y_3812_;
v___y_3809_ = v___x_3814_;
goto v___jp_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_expectData_3817_, lean_object* v_respStream_3818_, lean_object* v_currentTimeout_3819_, lean_object* v_keepAliveTimeout_3820_, lean_object* v_headerTimeout_3821_, lean_object* v_connectionContext_3822_, lean_object* v_handlerDispatched_3823_, lean_object* v_response_3824_, lean_object* v_socket_3825_, lean_object* v_requiresData_3826_, lean_object* v_sentMessage_3827_, lean_object* v_reader_3828_, lean_object* v_requestBodyInterested_3829_, lean_object* v_requestBody_3830_, lean_object* v___y_3831_){
_start:
{
uint8_t v_handlerDispatched_boxed_3832_; uint8_t v_requiresData_boxed_3833_; uint8_t v_sentMessage_boxed_3834_; uint8_t v_requestBodyInterested_boxed_3835_; lean_object* v_res_3836_; 
v_handlerDispatched_boxed_3832_ = lean_unbox(v_handlerDispatched_3823_);
v_requiresData_boxed_3833_ = lean_unbox(v_requiresData_3826_);
v_sentMessage_boxed_3834_ = lean_unbox(v_sentMessage_3827_);
v_requestBodyInterested_boxed_3835_ = lean_unbox(v_requestBodyInterested_3829_);
v_res_3836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_expectData_3817_, v_respStream_3818_, v_currentTimeout_3819_, v_keepAliveTimeout_3820_, v_headerTimeout_3821_, v_connectionContext_3822_, v_handlerDispatched_boxed_3832_, v_response_3824_, v_socket_3825_, v_requiresData_boxed_3833_, v_sentMessage_boxed_3834_, v_reader_3828_, v_requestBodyInterested_boxed_3835_, v_requestBody_3830_);
lean_dec_ref(v_reader_3828_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3837_, lean_object* v_x_3838_){
_start:
{
if (lean_obj_tag(v_x_3838_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v___f_3837_);
v_a_3840_ = lean_ctor_get(v_x_3838_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_x_3838_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3842_ = v_x_3838_;
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v_x_3838_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
return v___x_3846_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3850_; 
v_a_3849_ = lean_ctor_get(v_x_3838_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v_x_3838_, 1);
v___x_3850_ = lean_apply_2(v___f_3837_, v_a_3849_, lean_box(0));
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3851_, lean_object* v_x_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3851_, v_x_3852_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_expectData_3859_, lean_object* v_respStream_3860_, lean_object* v_currentTimeout_3861_, lean_object* v_keepAliveTimeout_3862_, lean_object* v_headerTimeout_3863_, lean_object* v_connectionContext_3864_, uint8_t v_handlerDispatched_3865_, lean_object* v_response_3866_, lean_object* v_socket_3867_, uint8_t v_requiresData_3868_, uint8_t v_sentMessage_3869_, lean_object* v_reader_3870_, uint8_t v_pullBodyStalled_3871_, uint8_t v_requestBodyOpen_3872_, lean_object* v_requestStream_3873_, uint8_t v_requestBodyInterested_3874_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___f_3880_; lean_object* v___f_3881_; uint8_t v___y_3883_; 
v___x_3876_ = lean_box(v_handlerDispatched_3865_);
v___x_3877_ = lean_box(v_requiresData_3868_);
v___x_3878_ = lean_box(v_sentMessage_3869_);
v___x_3879_ = lean_box(v_requestBodyInterested_3874_);
lean_inc_ref(v_reader_3870_);
v___f_3880_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3880_, 0, v_expectData_3859_);
lean_closure_set(v___f_3880_, 1, v_respStream_3860_);
lean_closure_set(v___f_3880_, 2, v_currentTimeout_3861_);
lean_closure_set(v___f_3880_, 3, v_keepAliveTimeout_3862_);
lean_closure_set(v___f_3880_, 4, v_headerTimeout_3863_);
lean_closure_set(v___f_3880_, 5, v_connectionContext_3864_);
lean_closure_set(v___f_3880_, 6, v___x_3876_);
lean_closure_set(v___f_3880_, 7, v_response_3866_);
lean_closure_set(v___f_3880_, 8, v_socket_3867_);
lean_closure_set(v___f_3880_, 9, v___x_3877_);
lean_closure_set(v___f_3880_, 10, v___x_3878_);
lean_closure_set(v___f_3880_, 11, v_reader_3870_);
lean_closure_set(v___f_3880_, 12, v___x_3879_);
v___f_3881_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3881_, 0, v___f_3880_);
if (v_sentMessage_3869_ == 0)
{
lean_object* v_state_3887_; 
v_state_3887_ = lean_ctor_get(v_reader_3870_, 0);
lean_inc(v_state_3887_);
lean_dec_ref(v_reader_3870_);
if (lean_obj_tag(v_state_3887_) == 2)
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3898_; 
v_isSharedCheck_3898_ = !lean_is_exclusive(v_state_3887_);
if (v_isSharedCheck_3898_ == 0)
{
lean_object* v_unused_3899_; 
v_unused_3899_ = lean_ctor_get(v_state_3887_, 0);
lean_dec(v_unused_3899_);
v___x_3889_ = v_state_3887_;
v_isShared_3890_ = v_isSharedCheck_3898_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v_state_3887_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3898_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
if (v_pullBodyStalled_3871_ == 0)
{
if (v_requestBodyOpen_3872_ == 0)
{
lean_del_object(v___x_3889_);
lean_dec_ref(v_requestStream_3873_);
v___y_3883_ = v_requestBodyOpen_3872_;
goto v___jp_3882_;
}
else
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set_tag(v___x_3889_, 1);
lean_ctor_set(v___x_3889_, 0, v_requestStream_3873_);
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_requestStream_3873_);
v___x_3892_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
v___x_3896_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3893_, v_pullBodyStalled_3871_, v___x_3895_, v___f_3881_);
return v___x_3896_;
}
}
}
else
{
lean_del_object(v___x_3889_);
lean_dec_ref(v_requestStream_3873_);
v___y_3883_ = v_sentMessage_3869_;
goto v___jp_3882_;
}
}
}
else
{
lean_dec(v_state_3887_);
lean_dec_ref(v_requestStream_3873_);
v___y_3883_ = v_sentMessage_3869_;
goto v___jp_3882_;
}
}
else
{
uint8_t v___x_3900_; 
lean_dec_ref(v_requestStream_3873_);
lean_dec_ref(v_reader_3870_);
v___x_3900_ = 0;
v___y_3883_ = v___x_3900_;
goto v___jp_3882_;
}
v___jp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_unsigned_to_nat(0u);
v___x_3885_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3886_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3884_, v___y_3883_, v___x_3885_, v___f_3881_);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_expectData_3901_ = _args[0];
lean_object* v_respStream_3902_ = _args[1];
lean_object* v_currentTimeout_3903_ = _args[2];
lean_object* v_keepAliveTimeout_3904_ = _args[3];
lean_object* v_headerTimeout_3905_ = _args[4];
lean_object* v_connectionContext_3906_ = _args[5];
lean_object* v_handlerDispatched_3907_ = _args[6];
lean_object* v_response_3908_ = _args[7];
lean_object* v_socket_3909_ = _args[8];
lean_object* v_requiresData_3910_ = _args[9];
lean_object* v_sentMessage_3911_ = _args[10];
lean_object* v_reader_3912_ = _args[11];
lean_object* v_pullBodyStalled_3913_ = _args[12];
lean_object* v_requestBodyOpen_3914_ = _args[13];
lean_object* v_requestStream_3915_ = _args[14];
lean_object* v_requestBodyInterested_3916_ = _args[15];
lean_object* v___y_3917_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3918_; uint8_t v_requiresData_boxed_3919_; uint8_t v_sentMessage_boxed_3920_; uint8_t v_pullBodyStalled_boxed_3921_; uint8_t v_requestBodyOpen_boxed_3922_; uint8_t v_requestBodyInterested_boxed_3923_; lean_object* v_res_3924_; 
v_handlerDispatched_boxed_3918_ = lean_unbox(v_handlerDispatched_3907_);
v_requiresData_boxed_3919_ = lean_unbox(v_requiresData_3910_);
v_sentMessage_boxed_3920_ = lean_unbox(v_sentMessage_3911_);
v_pullBodyStalled_boxed_3921_ = lean_unbox(v_pullBodyStalled_3913_);
v_requestBodyOpen_boxed_3922_ = lean_unbox(v_requestBodyOpen_3914_);
v_requestBodyInterested_boxed_3923_ = lean_unbox(v_requestBodyInterested_3916_);
v_res_3924_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_expectData_3901_, v_respStream_3902_, v_currentTimeout_3903_, v_keepAliveTimeout_3904_, v_headerTimeout_3905_, v_connectionContext_3906_, v_handlerDispatched_boxed_3918_, v_response_3908_, v_socket_3909_, v_requiresData_boxed_3919_, v_sentMessage_boxed_3920_, v_reader_3912_, v_pullBodyStalled_boxed_3921_, v_requestBodyOpen_boxed_3922_, v_requestStream_3915_, v_requestBodyInterested_boxed_3923_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3925_, lean_object* v_x_3926_){
_start:
{
if (lean_obj_tag(v_x_3926_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v___f_3925_);
v_a_3928_ = lean_ctor_get(v_x_3926_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_x_3926_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v_x_3926_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v_x_3926_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3938_; 
v_a_3937_ = lean_ctor_get(v_x_3926_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v_x_3926_, 1);
v___x_3938_ = lean_apply_2(v___f_3925_, v_a_3937_, lean_box(0));
return v___x_3938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3939_, lean_object* v_x_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3939_, v_x_3940_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_expectData_3943_, lean_object* v_respStream_3944_, lean_object* v_currentTimeout_3945_, lean_object* v_keepAliveTimeout_3946_, lean_object* v_headerTimeout_3947_, lean_object* v_connectionContext_3948_, uint8_t v_handlerDispatched_3949_, lean_object* v_response_3950_, lean_object* v_socket_3951_, uint8_t v_requiresData_3952_, uint8_t v_sentMessage_3953_, lean_object* v_reader_3954_, uint8_t v_pullBodyStalled_3955_, lean_object* v_requestStream_3956_, uint8_t v_requestBodyOpen_3957_){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___f_3964_; lean_object* v___f_3965_; uint8_t v___y_3967_; 
v___x_3959_ = lean_box(v_handlerDispatched_3949_);
v___x_3960_ = lean_box(v_requiresData_3952_);
v___x_3961_ = lean_box(v_sentMessage_3953_);
v___x_3962_ = lean_box(v_pullBodyStalled_3955_);
v___x_3963_ = lean_box(v_requestBodyOpen_3957_);
lean_inc_ref(v_requestStream_3956_);
lean_inc_ref(v_reader_3954_);
v___f_3964_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3964_, 0, v_expectData_3943_);
lean_closure_set(v___f_3964_, 1, v_respStream_3944_);
lean_closure_set(v___f_3964_, 2, v_currentTimeout_3945_);
lean_closure_set(v___f_3964_, 3, v_keepAliveTimeout_3946_);
lean_closure_set(v___f_3964_, 4, v_headerTimeout_3947_);
lean_closure_set(v___f_3964_, 5, v_connectionContext_3948_);
lean_closure_set(v___f_3964_, 6, v___x_3959_);
lean_closure_set(v___f_3964_, 7, v_response_3950_);
lean_closure_set(v___f_3964_, 8, v_socket_3951_);
lean_closure_set(v___f_3964_, 9, v___x_3960_);
lean_closure_set(v___f_3964_, 10, v___x_3961_);
lean_closure_set(v___f_3964_, 11, v_reader_3954_);
lean_closure_set(v___f_3964_, 12, v___x_3962_);
lean_closure_set(v___f_3964_, 13, v___x_3963_);
lean_closure_set(v___f_3964_, 14, v_requestStream_3956_);
v___f_3965_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3965_, 0, v___f_3964_);
if (v_sentMessage_3953_ == 0)
{
lean_object* v_state_3973_; 
v_state_3973_ = lean_ctor_get(v_reader_3954_, 0);
lean_inc(v_state_3973_);
lean_dec_ref(v_reader_3954_);
if (lean_obj_tag(v_state_3973_) == 2)
{
lean_dec_ref_known(v_state_3973_, 1);
if (v_requestBodyOpen_3957_ == 0)
{
lean_dec_ref(v_requestStream_3956_);
v___y_3967_ = v_requestBodyOpen_3957_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3956_);
v___x_3976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3974_, v_sentMessage_3953_, v___x_3975_, v___f_3965_);
return v___x_3976_;
}
}
else
{
lean_dec(v_state_3973_);
lean_dec_ref(v_requestStream_3956_);
v___y_3967_ = v_sentMessage_3953_;
goto v___jp_3966_;
}
}
else
{
uint8_t v___x_3977_; 
lean_dec_ref(v_requestStream_3956_);
lean_dec_ref(v_reader_3954_);
v___x_3977_ = 0;
v___y_3967_ = v___x_3977_;
goto v___jp_3966_;
}
v___jp_3966_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = lean_box(v___y_3967_);
v___x_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3968_, v___y_3967_, v___x_3971_, v___f_3965_);
return v___x_3972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_expectData_3978_, lean_object* v_respStream_3979_, lean_object* v_currentTimeout_3980_, lean_object* v_keepAliveTimeout_3981_, lean_object* v_headerTimeout_3982_, lean_object* v_connectionContext_3983_, lean_object* v_handlerDispatched_3984_, lean_object* v_response_3985_, lean_object* v_socket_3986_, lean_object* v_requiresData_3987_, lean_object* v_sentMessage_3988_, lean_object* v_reader_3989_, lean_object* v_pullBodyStalled_3990_, lean_object* v_requestStream_3991_, lean_object* v_requestBodyOpen_3992_, lean_object* v___y_3993_){
_start:
{
uint8_t v_handlerDispatched_boxed_3994_; uint8_t v_requiresData_boxed_3995_; uint8_t v_sentMessage_boxed_3996_; uint8_t v_pullBodyStalled_boxed_3997_; uint8_t v_requestBodyOpen_boxed_3998_; lean_object* v_res_3999_; 
v_handlerDispatched_boxed_3994_ = lean_unbox(v_handlerDispatched_3984_);
v_requiresData_boxed_3995_ = lean_unbox(v_requiresData_3987_);
v_sentMessage_boxed_3996_ = lean_unbox(v_sentMessage_3988_);
v_pullBodyStalled_boxed_3997_ = lean_unbox(v_pullBodyStalled_3990_);
v_requestBodyOpen_boxed_3998_ = lean_unbox(v_requestBodyOpen_3992_);
v_res_3999_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_expectData_3978_, v_respStream_3979_, v_currentTimeout_3980_, v_keepAliveTimeout_3981_, v_headerTimeout_3982_, v_connectionContext_3983_, v_handlerDispatched_boxed_3994_, v_response_3985_, v_socket_3986_, v_requiresData_boxed_3995_, v_sentMessage_boxed_3996_, v_reader_3989_, v_pullBodyStalled_boxed_3997_, v_requestStream_3991_, v_requestBodyOpen_boxed_3998_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_4000_, lean_object* v___f_4001_, uint8_t v___x_4002_, lean_object* v_x_4003_){
_start:
{
uint8_t v___y_4006_; 
if (lean_obj_tag(v_x_4003_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4020_; 
lean_dec_ref(v___f_4001_);
v_a_4012_ = lean_ctor_get(v_x_4003_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_x_4003_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4014_ = v_x_4003_;
v_isShared_4015_ = v_isSharedCheck_4020_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v_x_4003_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4020_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4018_; 
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
}
else
{
lean_object* v_a_4021_; uint8_t v___x_4022_; 
v_a_4021_ = lean_ctor_get(v_x_4003_, 0);
lean_inc(v_a_4021_);
lean_dec_ref_known(v_x_4003_, 1);
v___x_4022_ = lean_unbox(v_a_4021_);
lean_dec(v_a_4021_);
if (v___x_4022_ == 0)
{
v___y_4006_ = v___x_4002_;
goto v___jp_4005_;
}
else
{
v___y_4006_ = v_sentMessage_4000_;
goto v___jp_4005_;
}
}
v___jp_4005_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4007_ = lean_unsigned_to_nat(0u);
v___x_4008_ = lean_box(v___y_4006_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
v___x_4011_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4007_, v_sentMessage_4000_, v___x_4010_, v___f_4001_);
return v___x_4011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4023_, lean_object* v___f_4024_, lean_object* v___x_4025_, lean_object* v_x_4026_, lean_object* v___y_4027_){
_start:
{
uint8_t v_sentMessage_boxed_4028_; uint8_t v___x_2565__boxed_4029_; lean_object* v_res_4030_; 
v_sentMessage_boxed_4028_ = lean_unbox(v_sentMessage_4023_);
v___x_2565__boxed_4029_ = lean_unbox(v___x_4025_);
v_res_4030_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4028_, v___f_4024_, v___x_2565__boxed_4029_, v_x_4026_);
return v_res_4030_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___f_4031_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4032_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4033_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4034_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4034_, 0, lean_box(0));
lean_closure_set(v___x_4034_, 1, lean_box(0));
lean_closure_set(v___x_4034_, 2, v___x_4033_);
lean_closure_set(v___x_4034_, 3, lean_box(0));
lean_closure_set(v___x_4034_, 4, lean_box(0));
lean_closure_set(v___x_4034_, 5, v___x_4032_);
lean_closure_set(v___x_4034_, 6, v___f_4031_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4035_, lean_object* v_connectionContext_4036_, lean_object* v_state_4037_){
_start:
{
lean_object* v_machine_4039_; lean_object* v_writer_4040_; lean_object* v_requestStream_4041_; lean_object* v_keepAliveTimeout_4042_; lean_object* v_currentTimeout_4043_; lean_object* v_headerTimeout_4044_; lean_object* v_response_4045_; lean_object* v_respStream_4046_; uint8_t v_requiresData_4047_; lean_object* v_expectData_4048_; uint8_t v_handlerDispatched_4049_; lean_object* v_reader_4050_; uint8_t v_pullBodyStalled_4051_; uint8_t v_sentMessage_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___f_4057_; lean_object* v___f_4058_; uint8_t v___y_4060_; 
v_machine_4039_ = lean_ctor_get(v_state_4037_, 0);
lean_inc_ref(v_machine_4039_);
v_writer_4040_ = lean_ctor_get(v_machine_4039_, 1);
lean_inc_ref(v_writer_4040_);
v_requestStream_4041_ = lean_ctor_get(v_state_4037_, 1);
lean_inc_ref_n(v_requestStream_4041_, 2);
v_keepAliveTimeout_4042_ = lean_ctor_get(v_state_4037_, 2);
lean_inc(v_keepAliveTimeout_4042_);
v_currentTimeout_4043_ = lean_ctor_get(v_state_4037_, 3);
lean_inc(v_currentTimeout_4043_);
v_headerTimeout_4044_ = lean_ctor_get(v_state_4037_, 4);
lean_inc(v_headerTimeout_4044_);
v_response_4045_ = lean_ctor_get(v_state_4037_, 5);
lean_inc_ref(v_response_4045_);
v_respStream_4046_ = lean_ctor_get(v_state_4037_, 6);
lean_inc(v_respStream_4046_);
v_requiresData_4047_ = lean_ctor_get_uint8(v_state_4037_, sizeof(void*)*9);
v_expectData_4048_ = lean_ctor_get(v_state_4037_, 7);
lean_inc(v_expectData_4048_);
v_handlerDispatched_4049_ = lean_ctor_get_uint8(v_state_4037_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4037_);
v_reader_4050_ = lean_ctor_get(v_machine_4039_, 0);
lean_inc_ref_n(v_reader_4050_, 2);
v_pullBodyStalled_4051_ = lean_ctor_get_uint8(v_machine_4039_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4039_);
v_sentMessage_4052_ = lean_ctor_get_uint8(v_writer_4040_, sizeof(void*)*6);
lean_dec_ref(v_writer_4040_);
v___x_4053_ = lean_box(v_handlerDispatched_4049_);
v___x_4054_ = lean_box(v_requiresData_4047_);
v___x_4055_ = lean_box(v_sentMessage_4052_);
v___x_4056_ = lean_box(v_pullBodyStalled_4051_);
v___f_4057_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4057_, 0, v_expectData_4048_);
lean_closure_set(v___f_4057_, 1, v_respStream_4046_);
lean_closure_set(v___f_4057_, 2, v_currentTimeout_4043_);
lean_closure_set(v___f_4057_, 3, v_keepAliveTimeout_4042_);
lean_closure_set(v___f_4057_, 4, v_headerTimeout_4044_);
lean_closure_set(v___f_4057_, 5, v_connectionContext_4036_);
lean_closure_set(v___f_4057_, 6, v___x_4053_);
lean_closure_set(v___f_4057_, 7, v_response_4045_);
lean_closure_set(v___f_4057_, 8, v_socket_4035_);
lean_closure_set(v___f_4057_, 9, v___x_4054_);
lean_closure_set(v___f_4057_, 10, v___x_4055_);
lean_closure_set(v___f_4057_, 11, v_reader_4050_);
lean_closure_set(v___f_4057_, 12, v___x_4056_);
lean_closure_set(v___f_4057_, 13, v_requestStream_4041_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4058_, 0, v___f_4057_);
if (v_sentMessage_4052_ == 0)
{
lean_object* v_state_4066_; 
v_state_4066_ = lean_ctor_get(v_reader_4050_, 0);
lean_inc(v_state_4066_);
lean_dec_ref(v_reader_4050_);
if (lean_obj_tag(v_state_4066_) == 2)
{
uint8_t v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___f_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___f_4073_; lean_object* v___f_4074_; lean_object* v___x_4075_; lean_object* v___x_2095__overap_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec_ref_known(v_state_4066_, 1);
v___x_4067_ = 1;
v___x_4068_ = lean_box(v_sentMessage_4052_);
v___x_4069_ = lean_box(v___x_4067_);
v___f_4070_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4070_, 0, v___x_4068_);
lean_closure_set(v___f_4070_, 1, v___f_4058_);
lean_closure_set(v___f_4070_, 2, v___x_4069_);
v___x_4071_ = lean_unsigned_to_nat(0u);
v___x_4072_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4073_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4074_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4075_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2095__overap_4076_ = l_Std_Mutex_atomically___redArg(v___x_4072_, v___f_4073_, v___f_4074_, v_requestStream_4041_, v___x_4075_);
v___x_4077_ = lean_apply_1(v___x_2095__overap_4076_, lean_box(0));
v___x_4078_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4071_, v_sentMessage_4052_, v___x_4077_, v___f_4070_);
return v___x_4078_;
}
else
{
lean_dec(v_state_4066_);
lean_dec_ref(v_requestStream_4041_);
v___y_4060_ = v_sentMessage_4052_;
goto v___jp_4059_;
}
}
else
{
uint8_t v___x_4079_; 
lean_dec_ref(v_reader_4050_);
lean_dec_ref(v_requestStream_4041_);
v___x_4079_ = 0;
v___y_4060_ = v___x_4079_;
goto v___jp_4059_;
}
v___jp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4061_ = lean_unsigned_to_nat(0u);
v___x_4062_ = lean_box(v___y_4060_);
v___x_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
v___x_4065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4061_, v___y_4060_, v___x_4064_, v___f_4058_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4080_, lean_object* v_connectionContext_4081_, lean_object* v_state_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4080_, v_connectionContext_4081_, v_state_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4085_, lean_object* v_00_u03b2_4086_, lean_object* v_inst_4087_, lean_object* v_socket_4088_, lean_object* v_connectionContext_4089_, lean_object* v_state_4090_){
_start:
{
lean_object* v___x_4092_; 
v___x_4092_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4088_, v_connectionContext_4089_, v_state_4090_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4093_, lean_object* v_00_u03b2_4094_, lean_object* v_inst_4095_, lean_object* v_socket_4096_, lean_object* v_connectionContext_4097_, lean_object* v_state_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4093_, v_00_u03b2_4094_, v_inst_4095_, v_socket_4096_, v_connectionContext_4097_, v_state_4098_);
lean_dec_ref(v_inst_4095_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4101_){
_start:
{
if (lean_obj_tag(v_x_4101_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4111_; 
v_a_4103_ = lean_ctor_get(v_x_4101_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v_x_4101_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4105_ = v_x_4101_;
v_isShared_4106_ = v_isSharedCheck_4111_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v_x_4101_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4111_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4103_);
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
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4121_; 
v_a_4112_ = lean_ctor_get(v_x_4101_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_x_4101_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4114_ = v_x_4101_;
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v_x_4101_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_a_4112_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v___x_4116_);
v___x_4118_ = v___x_4114_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4122_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4129_){
_start:
{
if (lean_obj_tag(v_x_4129_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4139_; 
v_a_4131_ = lean_ctor_get(v_x_4129_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_x_4129_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4133_ = v_x_4129_;
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v_x_4129_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4131_);
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
else
{
lean_object* v___x_4140_; 
lean_dec_ref_known(v_x_4129_, 1);
v___x_4140_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4141_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_4144_, lean_object* v_handler_4145_, lean_object* v___f_4146_, lean_object* v_x_4147_){
_start:
{
if (lean_obj_tag(v_x_4147_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_a_4149_ = lean_ctor_get(v_x_4147_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v_x_4147_, 1);
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = 0;
v___x_4152_ = lean_apply_3(v_onFailure_4144_, v_handler_4145_, v_a_4149_, lean_box(0));
v___x_4153_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4150_, v___x_4151_, v___x_4152_, v___f_4146_);
return v___x_4153_;
}
else
{
lean_object* v___x_4154_; 
lean_dec_ref(v___f_4146_);
lean_dec(v_handler_4145_);
lean_dec_ref(v_onFailure_4144_);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v_x_4147_);
return v___x_4154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_4155_, lean_object* v_handler_4156_, lean_object* v___f_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_4155_, v_handler_4156_, v___f_4157_, v_x_4158_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4161_){
_start:
{
if (lean_obj_tag(v_x_4161_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4171_; 
v_a_4163_ = lean_ctor_get(v_x_4161_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_x_4161_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4165_ = v_x_4161_;
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v_x_4161_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4190_; 
v_a_4172_ = lean_ctor_get(v_x_4161_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_x_4161_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4174_ = v_x_4161_;
v_isShared_4175_ = v_isSharedCheck_4190_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v_x_4161_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4190_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v_snd_4176_; uint8_t v___x_4177_; 
v_snd_4176_ = lean_ctor_get(v_a_4172_, 1);
v___x_4177_ = lean_unbox(v_snd_4176_);
if (v___x_4177_ == 0)
{
lean_object* v_fst_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v_fst_4178_ = lean_ctor_get(v_a_4172_, 0);
lean_inc(v_fst_4178_);
lean_dec(v_a_4172_);
v___x_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_fst_4178_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4179_);
v___x_4181_ = v___x_4174_;
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
else
{
lean_object* v_fst_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
v_fst_4184_ = lean_ctor_get(v_a_4172_, 0);
lean_inc(v_fst_4184_);
lean_dec(v_a_4172_);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v_fst_4184_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4185_);
v___x_4187_ = v___x_4174_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4191_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4194_, lean_object* v_socket_4195_, lean_object* v_____r_4196_){
_start:
{
lean_object* v_val_4199_; lean_object* v_close_4201_; lean_object* v___x_4202_; 
v_close_4201_ = lean_ctor_get(v_inst_4194_, 3);
lean_inc_ref(v_close_4201_);
lean_dec_ref(v_inst_4194_);
v___x_4202_ = lean_apply_2(v_close_4201_, v_socket_4195_, lean_box(0));
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4202_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4202_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
lean_ctor_set_tag(v___x_4205_, 1);
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
v_val_4199_ = v___x_4208_;
goto v___jp_4198_;
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4202_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4202_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
lean_ctor_set_tag(v___x_4213_, 0);
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
v_val_4199_ = v___x_4216_;
goto v___jp_4198_;
}
}
}
v___jp_4198_:
{
lean_object* v___x_4200_; 
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v_val_4199_);
return v___x_4200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4219_, lean_object* v_socket_4220_, lean_object* v_____r_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4219_, v_socket_4220_, v_____r_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4224_, lean_object* v_x_4225_){
_start:
{
if (lean_obj_tag(v_x_4225_) == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref(v___f_4224_);
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_x_4225_);
return v___x_4227_;
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v_x_4225_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v_x_4225_, 1);
v___x_4229_ = lean_apply_2(v___f_4224_, v_a_4228_, lean_box(0));
return v___x_4229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4230_, lean_object* v_x_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4230_, v_x_4231_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4234_, lean_object* v_val_4235_, lean_object* v___f_4236_, lean_object* v___f_4237_, lean_object* v_x_4238_){
_start:
{
if (lean_obj_tag(v_x_4238_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___f_4237_);
lean_dec_ref(v___f_4236_);
lean_dec(v_val_4235_);
lean_dec_ref(v_close_4234_);
v_a_4240_ = lean_ctor_get(v_x_4238_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_x_4238_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4242_ = v_x_4238_;
v_isShared_4243_ = v_isSharedCheck_4248_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v_x_4238_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4248_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
}
}
else
{
lean_object* v_a_4249_; uint8_t v___x_4250_; 
v_a_4249_ = lean_ctor_get(v_x_4238_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v_x_4238_, 1);
v___x_4250_ = lean_unbox(v_a_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; lean_object* v___x_4254_; 
lean_dec_ref(v___f_4237_);
v___x_4251_ = lean_unsigned_to_nat(0u);
v___x_4252_ = lean_apply_2(v_close_4234_, v_val_4235_, lean_box(0));
v___x_4253_ = lean_unbox(v_a_4249_);
lean_dec(v_a_4249_);
v___x_4254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4251_, v___x_4253_, v___x_4252_, v___f_4236_);
return v___x_4254_;
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
lean_dec(v_a_4249_);
lean_dec_ref(v___f_4236_);
lean_dec(v_val_4235_);
lean_dec_ref(v_close_4234_);
v___x_4255_ = lean_box(0);
v___x_4256_ = lean_apply_2(v___f_4237_, v___x_4255_, lean_box(0));
return v___x_4256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4257_, lean_object* v_val_4258_, lean_object* v___f_4259_, lean_object* v___f_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4257_, v_val_4258_, v___f_4259_, v___f_4260_, v_x_4261_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4264_, lean_object* v_responseBodyInstance_4265_, lean_object* v___f_4266_, lean_object* v___f_4267_, lean_object* v_____r_4268_){
_start:
{
if (lean_obj_tag(v_respStream_4264_) == 1)
{
lean_object* v_val_4270_; lean_object* v_close_4271_; lean_object* v_isClosed_4272_; lean_object* v___f_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_val_4270_ = lean_ctor_get(v_respStream_4264_, 0);
lean_inc_n(v_val_4270_, 2);
lean_dec_ref_known(v_respStream_4264_, 1);
v_close_4271_ = lean_ctor_get(v_responseBodyInstance_4265_, 1);
lean_inc_ref(v_close_4271_);
v_isClosed_4272_ = lean_ctor_get(v_responseBodyInstance_4265_, 2);
lean_inc_ref(v_isClosed_4272_);
lean_dec_ref(v_responseBodyInstance_4265_);
v___f_4273_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4273_, 0, v_close_4271_);
lean_closure_set(v___f_4273_, 1, v_val_4270_);
lean_closure_set(v___f_4273_, 2, v___f_4266_);
lean_closure_set(v___f_4273_, 3, v___f_4267_);
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = 0;
v___x_4276_ = lean_apply_2(v_isClosed_4272_, v_val_4270_, lean_box(0));
v___x_4277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4274_, v___x_4275_, v___x_4276_, v___f_4273_);
return v___x_4277_;
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v___f_4266_);
lean_dec_ref(v_responseBodyInstance_4265_);
lean_dec(v_respStream_4264_);
v___x_4278_ = lean_box(0);
v___x_4279_ = lean_apply_2(v___f_4267_, v___x_4278_, lean_box(0));
return v___x_4279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4280_, lean_object* v_responseBodyInstance_4281_, lean_object* v___f_4282_, lean_object* v___f_4283_, lean_object* v_____r_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4280_, v_responseBodyInstance_4281_, v___f_4282_, v___f_4283_, v_____r_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4287_, lean_object* v___f_4288_, lean_object* v___f_4289_, lean_object* v_x_4290_){
_start:
{
if (lean_obj_tag(v_x_4290_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4300_; 
lean_dec_ref(v___f_4289_);
lean_dec_ref(v___f_4288_);
lean_dec_ref(v_requestStream_4287_);
v_a_4292_ = lean_ctor_get(v_x_4290_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_x_4290_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4294_ = v_x_4290_;
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v_x_4290_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; 
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
}
}
else
{
lean_object* v_a_4301_; uint8_t v___x_4302_; 
v_a_4301_ = lean_ctor_get(v_x_4290_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v_x_4290_, 1);
v___x_4302_ = lean_unbox(v_a_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; 
lean_dec_ref(v___f_4289_);
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = l_Std_Http_Body_Stream_close(v_requestStream_4287_);
v___x_4305_ = lean_unbox(v_a_4301_);
lean_dec(v_a_4301_);
v___x_4306_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4303_, v___x_4305_, v___x_4304_, v___f_4288_);
return v___x_4306_;
}
else
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
lean_dec(v_a_4301_);
lean_dec_ref(v___f_4288_);
lean_dec_ref(v_requestStream_4287_);
v___x_4307_ = lean_box(0);
v___x_4308_ = lean_apply_2(v___f_4289_, v___x_4307_, lean_box(0));
return v___x_4308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4309_, lean_object* v___f_4310_, lean_object* v___f_4311_, lean_object* v_x_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4309_, v___f_4310_, v___f_4311_, v_x_4312_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4315_, lean_object* v___f_4316_, lean_object* v___f_4317_, lean_object* v___f_4318_, lean_object* v_x_4319_){
_start:
{
if (lean_obj_tag(v_x_4319_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4329_; 
lean_dec_ref(v___f_4318_);
lean_dec_ref(v___f_4317_);
lean_dec_ref(v___f_4316_);
lean_dec_ref(v_responseBodyInstance_4315_);
v_a_4321_ = lean_ctor_get(v_x_4319_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v_x_4319_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4323_ = v_x_4319_;
v_isShared_4324_ = v_isSharedCheck_4329_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v_x_4319_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4329_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
return v___x_4327_;
}
}
}
else
{
lean_object* v_a_4330_; lean_object* v_requestStream_4331_; lean_object* v_respStream_4332_; lean_object* v___f_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___f_4339_; lean_object* v___f_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4427__overap_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v_a_4330_ = lean_ctor_get(v_x_4319_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v_x_4319_, 1);
v_requestStream_4331_ = lean_ctor_get(v_a_4330_, 1);
lean_inc_ref_n(v_requestStream_4331_, 2);
v_respStream_4332_ = lean_ctor_get(v_a_4330_, 6);
lean_inc(v_respStream_4332_);
lean_dec(v_a_4330_);
v___f_4333_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4333_, 0, v_respStream_4332_);
lean_closure_set(v___f_4333_, 1, v_responseBodyInstance_4315_);
lean_closure_set(v___f_4333_, 2, v___f_4316_);
lean_closure_set(v___f_4333_, 3, v___f_4317_);
lean_inc_ref(v___f_4333_);
v___f_4334_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4334_, 0, v___f_4333_);
v___f_4335_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4335_, 0, v_requestStream_4331_);
lean_closure_set(v___f_4335_, 1, v___f_4334_);
lean_closure_set(v___f_4335_, 2, v___f_4333_);
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = 0;
v___x_4338_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4339_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4340_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4341_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4342_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4342_, 0, lean_box(0));
lean_closure_set(v___x_4342_, 1, lean_box(0));
lean_closure_set(v___x_4342_, 2, v___x_4338_);
lean_closure_set(v___x_4342_, 3, lean_box(0));
lean_closure_set(v___x_4342_, 4, lean_box(0));
lean_closure_set(v___x_4342_, 5, v___x_4341_);
lean_closure_set(v___x_4342_, 6, v___f_4318_);
v___x_4427__overap_4343_ = l_Std_Mutex_atomically___redArg(v___x_4338_, v___f_4339_, v___f_4340_, v_requestStream_4331_, v___x_4342_);
v___x_4344_ = lean_apply_1(v___x_4427__overap_4343_, lean_box(0));
v___x_4345_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4336_, v___x_4337_, v___x_4344_, v___f_4335_);
return v___x_4345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4346_, lean_object* v___f_4347_, lean_object* v___f_4348_, lean_object* v___f_4349_, lean_object* v_x_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4346_, v___f_4347_, v___f_4348_, v___f_4349_, v_x_4350_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4353_, lean_object* v_responseBodyInstance_4354_, lean_object* v_handler_4355_, lean_object* v_config_4356_, lean_object* v___x_4357_, uint8_t v___x_4358_, lean_object* v___f_4359_, lean_object* v_x_4360_){
_start:
{
if (lean_obj_tag(v_x_4360_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref(v___f_4359_);
lean_dec_ref(v___x_4357_);
lean_dec_ref(v_config_4356_);
lean_dec(v_handler_4355_);
lean_dec_ref(v_responseBodyInstance_4354_);
lean_dec_ref(v_h_4353_);
v_a_4362_ = lean_ctor_get(v_x_4360_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v_x_4360_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4364_ = v_x_4360_;
v_isShared_4365_ = v_isSharedCheck_4370_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v_x_4360_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4370_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
return v___x_4368_;
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_a_4371_ = lean_ctor_get(v_x_4360_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v_x_4360_, 1);
v___x_4372_ = lean_unsigned_to_nat(0u);
v___x_4373_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4353_, v_responseBodyInstance_4354_, v_handler_4355_, v_config_4356_, v_a_4371_, v___x_4357_);
v___x_4374_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4372_, v___x_4358_, v___x_4373_, v___f_4359_);
return v___x_4374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4375_, lean_object* v_responseBodyInstance_4376_, lean_object* v_handler_4377_, lean_object* v_config_4378_, lean_object* v___x_4379_, lean_object* v___x_4380_, lean_object* v___f_4381_, lean_object* v_x_4382_, lean_object* v___y_4383_){
_start:
{
uint8_t v___x_5103__boxed_4384_; lean_object* v_res_4385_; 
v___x_5103__boxed_4384_ = lean_unbox(v___x_4380_);
v_res_4385_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4375_, v_responseBodyInstance_4376_, v_handler_4377_, v_config_4378_, v___x_4379_, v___x_5103__boxed_4384_, v___f_4381_, v_x_4382_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4386_, lean_object* v_h_4387_, lean_object* v_responseBodyInstance_4388_, lean_object* v_config_4389_, lean_object* v_handler_4390_, uint8_t v___x_4391_, lean_object* v___f_4392_, lean_object* v_x_4393_){
_start:
{
if (lean_obj_tag(v_x_4393_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4403_; 
lean_dec_ref(v___f_4392_);
lean_dec(v_handler_4390_);
lean_dec_ref(v_config_4389_);
lean_dec_ref(v_responseBodyInstance_4388_);
lean_dec_ref(v_h_4387_);
lean_dec_ref(v_inst_4386_);
v_a_4395_ = lean_ctor_get(v_x_4393_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_x_4393_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4397_ = v_x_4393_;
v_isShared_4398_ = v_isSharedCheck_4403_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v_x_4393_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4403_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
return v___x_4401_;
}
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_a_4404_ = lean_ctor_get(v_x_4393_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v_x_4393_, 1);
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4386_, v_h_4387_, v_responseBodyInstance_4388_, v_config_4389_, v_handler_4390_, v_a_4404_);
v___x_4407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4405_, v___x_4391_, v___x_4406_, v___f_4392_);
return v___x_4407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4408_, lean_object* v_h_4409_, lean_object* v_responseBodyInstance_4410_, lean_object* v_config_4411_, lean_object* v_handler_4412_, lean_object* v___x_4413_, lean_object* v___f_4414_, lean_object* v_x_4415_, lean_object* v___y_4416_){
_start:
{
uint8_t v___x_5144__boxed_4417_; lean_object* v_res_4418_; 
v___x_5144__boxed_4417_ = lean_unbox(v___x_4413_);
v_res_4418_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4408_, v_h_4409_, v_responseBodyInstance_4410_, v_config_4411_, v_handler_4412_, v___x_5144__boxed_4417_, v___f_4414_, v_x_4415_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4419_, lean_object* v_h_4420_, lean_object* v_responseBodyInstance_4421_, lean_object* v_handler_4422_, lean_object* v_config_4423_, lean_object* v___f_4424_, lean_object* v_inst_4425_, lean_object* v_socket_4426_, lean_object* v_connectionContext_4427_, uint8_t v___x_4428_, lean_object* v_x_4429_){
_start:
{
if (lean_obj_tag(v_x_4429_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4439_; 
lean_dec_ref(v_connectionContext_4427_);
lean_dec(v_socket_4426_);
lean_dec_ref(v_inst_4425_);
lean_dec_ref(v___f_4424_);
lean_dec_ref(v_config_4423_);
lean_dec(v_handler_4422_);
lean_dec_ref(v_responseBodyInstance_4421_);
lean_dec_ref(v_h_4420_);
v_a_4431_ = lean_ctor_get(v_x_4429_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_x_4429_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4433_ = v_x_4429_;
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v_x_4429_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4436_);
return v___x_4437_;
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4482_; 
v_a_4440_ = lean_ctor_get(v_x_4429_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_x_4429_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4442_ = v_x_4429_;
v_isShared_4443_ = v_isSharedCheck_4482_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v_x_4429_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4482_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v_machine_4444_; lean_object* v_requestStream_4445_; lean_object* v_keepAliveTimeout_4446_; lean_object* v_currentTimeout_4447_; lean_object* v_headerTimeout_4448_; lean_object* v_response_4449_; lean_object* v_respStream_4450_; uint8_t v_requiresData_4451_; lean_object* v_expectData_4452_; uint8_t v_handlerDispatched_4453_; lean_object* v_pendingHead_4454_; uint8_t v___y_4465_; uint8_t v___y_4472_; uint8_t v___y_4474_; uint8_t v___y_4475_; uint8_t v___y_4477_; 
v_machine_4444_ = lean_ctor_get(v_a_4440_, 0);
v_requestStream_4445_ = lean_ctor_get(v_a_4440_, 1);
v_keepAliveTimeout_4446_ = lean_ctor_get(v_a_4440_, 2);
v_currentTimeout_4447_ = lean_ctor_get(v_a_4440_, 3);
v_headerTimeout_4448_ = lean_ctor_get(v_a_4440_, 4);
v_response_4449_ = lean_ctor_get(v_a_4440_, 5);
v_respStream_4450_ = lean_ctor_get(v_a_4440_, 6);
v_requiresData_4451_ = lean_ctor_get_uint8(v_a_4440_, sizeof(void*)*9);
v_expectData_4452_ = lean_ctor_get(v_a_4440_, 7);
v_handlerDispatched_4453_ = lean_ctor_get_uint8(v_a_4440_, sizeof(void*)*9 + 1);
v_pendingHead_4454_ = lean_ctor_get(v_a_4440_, 8);
if (lean_obj_tag(v_respStream_4450_) == 0)
{
v___y_4477_ = v___x_4419_;
goto v___jp_4476_;
}
else
{
v___y_4477_ = v___x_4428_;
goto v___jp_4476_;
}
v___jp_4455_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___f_4458_; lean_object* v___x_4459_; lean_object* v___f_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4456_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4456_, 0, v_machine_4444_);
lean_ctor_set(v___x_4456_, 1, v_requestStream_4445_);
lean_ctor_set(v___x_4456_, 2, v_keepAliveTimeout_4446_);
lean_ctor_set(v___x_4456_, 3, v_currentTimeout_4447_);
lean_ctor_set(v___x_4456_, 4, v_headerTimeout_4448_);
lean_ctor_set(v___x_4456_, 5, v_response_4449_);
lean_ctor_set(v___x_4456_, 6, v_respStream_4450_);
lean_ctor_set(v___x_4456_, 7, v_expectData_4452_);
lean_ctor_set(v___x_4456_, 8, v_pendingHead_4454_);
lean_ctor_set_uint8(v___x_4456_, sizeof(void*)*9, v___x_4419_);
lean_ctor_set_uint8(v___x_4456_, sizeof(void*)*9 + 1, v_handlerDispatched_4453_);
v___x_4457_ = lean_box(v___x_4419_);
lean_inc_ref(v___x_4456_);
lean_inc_ref(v_config_4423_);
lean_inc(v_handler_4422_);
lean_inc_ref(v_responseBodyInstance_4421_);
lean_inc_ref(v_h_4420_);
v___f_4458_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4458_, 0, v_h_4420_);
lean_closure_set(v___f_4458_, 1, v_responseBodyInstance_4421_);
lean_closure_set(v___f_4458_, 2, v_handler_4422_);
lean_closure_set(v___f_4458_, 3, v_config_4423_);
lean_closure_set(v___f_4458_, 4, v___x_4456_);
lean_closure_set(v___f_4458_, 5, v___x_4457_);
lean_closure_set(v___f_4458_, 6, v___f_4424_);
v___x_4459_ = lean_box(v___x_4419_);
v___f_4460_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4460_, 0, v_inst_4425_);
lean_closure_set(v___f_4460_, 1, v_h_4420_);
lean_closure_set(v___f_4460_, 2, v_responseBodyInstance_4421_);
lean_closure_set(v___f_4460_, 3, v_config_4423_);
lean_closure_set(v___f_4460_, 4, v_handler_4422_);
lean_closure_set(v___f_4460_, 5, v___x_4459_);
lean_closure_set(v___f_4460_, 6, v___f_4458_);
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4426_, v_connectionContext_4427_, v___x_4456_);
v___x_4463_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4461_, v___x_4419_, v___x_4462_, v___f_4460_);
return v___x_4463_;
}
v___jp_4464_:
{
if (v_requiresData_4451_ == 0)
{
if (v___y_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec_ref(v_connectionContext_4427_);
lean_dec(v_socket_4426_);
lean_dec_ref(v_inst_4425_);
lean_dec_ref(v___f_4424_);
lean_dec_ref(v_config_4423_);
lean_dec(v_handler_4422_);
lean_dec_ref(v_responseBodyInstance_4421_);
lean_dec_ref(v_h_4420_);
v___x_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4466_, 0, v_a_4440_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4466_);
v___x_4468_ = v___x_4442_;
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
lean_inc(v_pendingHead_4454_);
lean_inc(v_expectData_4452_);
lean_inc(v_respStream_4450_);
lean_inc_ref(v_response_4449_);
lean_inc(v_headerTimeout_4448_);
lean_inc(v_currentTimeout_4447_);
lean_inc(v_keepAliveTimeout_4446_);
lean_inc_ref(v_requestStream_4445_);
lean_inc_ref(v_machine_4444_);
lean_del_object(v___x_4442_);
lean_dec(v_a_4440_);
goto v___jp_4455_;
}
}
else
{
lean_inc(v_pendingHead_4454_);
lean_inc(v_expectData_4452_);
lean_inc(v_respStream_4450_);
lean_inc_ref(v_response_4449_);
lean_inc(v_headerTimeout_4448_);
lean_inc(v_currentTimeout_4447_);
lean_inc(v_keepAliveTimeout_4446_);
lean_inc_ref(v_requestStream_4445_);
lean_inc_ref(v_machine_4444_);
lean_del_object(v___x_4442_);
lean_dec(v_a_4440_);
goto v___jp_4455_;
}
}
v___jp_4471_:
{
if (v_handlerDispatched_4453_ == 0)
{
v___y_4465_ = v___y_4472_;
goto v___jp_4464_;
}
else
{
v___y_4465_ = v_handlerDispatched_4453_;
goto v___jp_4464_;
}
}
v___jp_4473_:
{
if (v___y_4474_ == 0)
{
v___y_4472_ = v___y_4475_;
goto v___jp_4471_;
}
else
{
v___y_4472_ = v___y_4474_;
goto v___jp_4471_;
}
}
v___jp_4476_:
{
lean_object* v_writer_4478_; uint8_t v_sentMessage_4479_; 
v_writer_4478_ = lean_ctor_get(v_machine_4444_, 1);
v_sentMessage_4479_ = lean_ctor_get_uint8(v_writer_4478_, sizeof(void*)*6);
if (v_sentMessage_4479_ == 0)
{
lean_object* v_reader_4480_; lean_object* v_state_4481_; 
v_reader_4480_ = lean_ctor_get(v_machine_4444_, 0);
v_state_4481_ = lean_ctor_get(v_reader_4480_, 0);
if (lean_obj_tag(v_state_4481_) == 2)
{
v___y_4474_ = v___y_4477_;
v___y_4475_ = v___x_4428_;
goto v___jp_4473_;
}
else
{
v___y_4474_ = v___y_4477_;
v___y_4475_ = v_sentMessage_4479_;
goto v___jp_4473_;
}
}
else
{
v___y_4474_ = v___y_4477_;
v___y_4475_ = v___x_4419_;
goto v___jp_4473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4483_, lean_object* v_h_4484_, lean_object* v_responseBodyInstance_4485_, lean_object* v_handler_4486_, lean_object* v_config_4487_, lean_object* v___f_4488_, lean_object* v_inst_4489_, lean_object* v_socket_4490_, lean_object* v_connectionContext_4491_, lean_object* v___x_4492_, lean_object* v_x_4493_, lean_object* v___y_4494_){
_start:
{
uint8_t v___x_5184__boxed_4495_; uint8_t v___x_5187__boxed_4496_; lean_object* v_res_4497_; 
v___x_5184__boxed_4495_ = lean_unbox(v___x_4483_);
v___x_5187__boxed_4496_ = lean_unbox(v___x_4492_);
v_res_4497_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5184__boxed_4495_, v_h_4484_, v_responseBodyInstance_4485_, v_handler_4486_, v_config_4487_, v___f_4488_, v_inst_4489_, v_socket_4490_, v_connectionContext_4491_, v___x_5187__boxed_4496_, v_x_4493_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4498_, lean_object* v_handler_4499_, lean_object* v_extensions_4500_, lean_object* v_connectionContext_4501_, uint8_t v___x_4502_, lean_object* v___f_4503_, lean_object* v_x_4504_){
_start:
{
if (lean_obj_tag(v_x_4504_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4514_; 
lean_dec_ref(v___f_4503_);
lean_dec_ref(v_connectionContext_4501_);
lean_dec(v_extensions_4500_);
lean_dec(v_handler_4499_);
lean_dec_ref(v_h_4498_);
v_a_4506_ = lean_ctor_get(v_x_4504_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_x_4504_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4508_ = v_x_4504_;
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v_x_4504_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_a_4515_ = lean_ctor_get(v_x_4504_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v_x_4504_, 1);
v___x_4516_ = lean_unsigned_to_nat(0u);
v___x_4517_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4498_, v_handler_4499_, v_extensions_4500_, v_connectionContext_4501_, v_a_4515_);
v___x_4518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4516_, v___x_4502_, v___x_4517_, v___f_4503_);
return v___x_4518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4519_, lean_object* v_handler_4520_, lean_object* v_extensions_4521_, lean_object* v_connectionContext_4522_, lean_object* v___x_4523_, lean_object* v___f_4524_, lean_object* v_x_4525_, lean_object* v___y_4526_){
_start:
{
uint8_t v___x_5278__boxed_4527_; lean_object* v_res_4528_; 
v___x_5278__boxed_4527_ = lean_unbox(v___x_4523_);
v_res_4528_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4519_, v_handler_4520_, v_extensions_4521_, v_connectionContext_4522_, v___x_5278__boxed_4527_, v___f_4524_, v_x_4525_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4529_, lean_object* v_responseBodyInstance_4530_, lean_object* v_handler_4531_, lean_object* v_config_4532_, lean_object* v_connectionContext_4533_, lean_object* v_events_4534_, lean_object* v___x_4535_, uint8_t v___x_4536_, lean_object* v___f_4537_, lean_object* v_____r_4538_){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_unsigned_to_nat(0u);
v___x_4541_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4529_, v_responseBodyInstance_4530_, v_handler_4531_, v_config_4532_, v_connectionContext_4533_, v_events_4534_, v___x_4535_);
v___x_4542_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4540_, v___x_4536_, v___x_4541_, v___f_4537_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4543_, lean_object* v_responseBodyInstance_4544_, lean_object* v_handler_4545_, lean_object* v_config_4546_, lean_object* v_connectionContext_4547_, lean_object* v_events_4548_, lean_object* v___x_4549_, lean_object* v___x_4550_, lean_object* v___f_4551_, lean_object* v_____r_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v___x_5317__boxed_4554_; lean_object* v_res_4555_; 
v___x_5317__boxed_4554_ = lean_unbox(v___x_4550_);
v_res_4555_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4543_, v_responseBodyInstance_4544_, v_handler_4545_, v_config_4546_, v_connectionContext_4547_, v_events_4548_, v___x_4549_, v___x_5317__boxed_4554_, v___f_4551_, v_____r_4552_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4556_, lean_object* v___f_4557_, lean_object* v_x_4558_){
_start:
{
if (lean_obj_tag(v_x_4558_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v___f_4557_);
lean_dec_ref(v___x_4556_);
v_a_4560_ = lean_ctor_get(v_x_4558_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v_x_4558_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4562_ = v_x_4558_;
v_isShared_4563_ = v_isSharedCheck_4568_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v_x_4558_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4568_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4580_; 
v_a_4569_ = lean_ctor_get(v_x_4558_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_x_4558_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4571_ = v_x_4558_;
v_isShared_4572_ = v_isSharedCheck_4580_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v_x_4558_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4580_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
if (lean_obj_tag(v_a_4569_) == 0)
{
lean_object* v___x_4573_; lean_object* v___x_4575_; 
lean_dec_ref(v___f_4557_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4556_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 0, v___x_4573_);
v___x_4575_ = v___x_4571_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4573_);
v___x_4575_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
lean_object* v___x_4576_; 
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
return v___x_4576_;
}
}
else
{
lean_object* v_val_4578_; lean_object* v___x_4579_; 
lean_del_object(v___x_4571_);
lean_dec_ref(v___x_4556_);
v_val_4578_ = lean_ctor_get(v_a_4569_, 0);
lean_inc(v_val_4578_);
lean_dec_ref_known(v_a_4569_, 1);
v___x_4579_ = lean_apply_2(v___f_4557_, v_val_4578_, lean_box(0));
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4581_, lean_object* v___f_4582_, lean_object* v_x_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4581_, v___f_4582_, v_x_4583_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(uint8_t v___x_4586_, lean_object* v_h_4587_, lean_object* v_responseBodyInstance_4588_, lean_object* v_handler_4589_, lean_object* v_config_4590_, lean_object* v___f_4591_, lean_object* v_inst_4592_, lean_object* v_socket_4593_, lean_object* v_connectionContext_4594_, lean_object* v_extensions_4595_, lean_object* v___f_4596_, lean_object* v___f_4597_, lean_object* v_x_4598_, lean_object* v_____s_4599_){
_start:
{
lean_object* v_machine_4601_; lean_object* v_reader_4602_; lean_object* v_requestStream_4603_; lean_object* v_keepAliveTimeout_4604_; lean_object* v_currentTimeout_4605_; lean_object* v_headerTimeout_4606_; lean_object* v_response_4607_; lean_object* v_respStream_4608_; uint8_t v_requiresData_4609_; lean_object* v_expectData_4610_; uint8_t v_handlerDispatched_4611_; lean_object* v_pendingHead_4612_; lean_object* v_writer_4613_; lean_object* v_state_4614_; uint8_t v___x_4615_; 
v_machine_4601_ = lean_ctor_get(v_____s_4599_, 0);
v_reader_4602_ = lean_ctor_get(v_machine_4601_, 0);
v_requestStream_4603_ = lean_ctor_get(v_____s_4599_, 1);
v_keepAliveTimeout_4604_ = lean_ctor_get(v_____s_4599_, 2);
v_currentTimeout_4605_ = lean_ctor_get(v_____s_4599_, 3);
v_headerTimeout_4606_ = lean_ctor_get(v_____s_4599_, 4);
v_response_4607_ = lean_ctor_get(v_____s_4599_, 5);
v_respStream_4608_ = lean_ctor_get(v_____s_4599_, 6);
v_requiresData_4609_ = lean_ctor_get_uint8(v_____s_4599_, sizeof(void*)*9);
v_expectData_4610_ = lean_ctor_get(v_____s_4599_, 7);
v_handlerDispatched_4611_ = lean_ctor_get_uint8(v_____s_4599_, sizeof(void*)*9 + 1);
v_pendingHead_4612_ = lean_ctor_get(v_____s_4599_, 8);
v_writer_4613_ = lean_ctor_get(v_machine_4601_, 1);
v_state_4614_ = lean_ctor_get(v_reader_4602_, 0);
v___x_4615_ = 0;
if (lean_obj_tag(v_state_4614_) == 6)
{
lean_object* v_state_4643_; 
v_state_4643_ = lean_ctor_get(v_writer_4613_, 2);
if (lean_obj_tag(v_state_4643_) == 7)
{
lean_object* v_outputData_4644_; lean_object* v_size_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; 
v_outputData_4644_ = lean_ctor_get(v_writer_4613_, 1);
v_size_4645_ = lean_ctor_get(v_outputData_4644_, 1);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_nat_dec_eq(v_size_4645_, v___x_4646_);
if (v___x_4647_ == 0)
{
lean_inc(v_pendingHead_4612_);
lean_inc(v_expectData_4610_);
lean_inc(v_respStream_4608_);
lean_inc_ref(v_response_4607_);
lean_inc(v_headerTimeout_4606_);
lean_inc(v_currentTimeout_4605_);
lean_inc(v_keepAliveTimeout_4604_);
lean_inc_ref(v_requestStream_4603_);
lean_inc_ref(v_machine_4601_);
lean_dec_ref(v_____s_4599_);
goto v___jp_4616_;
}
else
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
lean_dec_ref(v___f_4597_);
lean_dec_ref(v___f_4596_);
lean_dec(v_extensions_4595_);
lean_dec_ref(v_connectionContext_4594_);
lean_dec(v_socket_4593_);
lean_dec_ref(v_inst_4592_);
lean_dec_ref(v___f_4591_);
lean_dec_ref(v_config_4590_);
lean_dec(v_handler_4589_);
lean_dec_ref(v_responseBodyInstance_4588_);
lean_dec_ref(v_h_4587_);
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v_____s_4599_);
v___x_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
v___x_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
else
{
lean_inc(v_pendingHead_4612_);
lean_inc(v_expectData_4610_);
lean_inc(v_respStream_4608_);
lean_inc_ref(v_response_4607_);
lean_inc(v_headerTimeout_4606_);
lean_inc(v_currentTimeout_4605_);
lean_inc(v_keepAliveTimeout_4604_);
lean_inc_ref(v_requestStream_4603_);
lean_inc_ref(v_machine_4601_);
lean_dec_ref(v_____s_4599_);
goto v___jp_4616_;
}
}
else
{
lean_inc(v_pendingHead_4612_);
lean_inc(v_expectData_4610_);
lean_inc(v_respStream_4608_);
lean_inc_ref(v_response_4607_);
lean_inc(v_headerTimeout_4606_);
lean_inc(v_currentTimeout_4605_);
lean_inc(v_keepAliveTimeout_4604_);
lean_inc_ref(v_requestStream_4603_);
lean_inc_ref(v_machine_4601_);
lean_dec_ref(v_____s_4599_);
goto v___jp_4616_;
}
v___jp_4616_:
{
lean_object* v___x_4617_; lean_object* v_snd_4618_; lean_object* v_output_4619_; lean_object* v_fst_4620_; lean_object* v_events_4621_; lean_object* v_data_4622_; lean_object* v_size_4623_; uint8_t v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___f_4627_; lean_object* v___x_4628_; lean_object* v___f_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___f_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4617_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4615_, v_machine_4601_);
v_snd_4618_ = lean_ctor_get(v___x_4617_, 1);
lean_inc(v_snd_4618_);
v_output_4619_ = lean_ctor_get(v_snd_4618_, 1);
lean_inc_ref(v_output_4619_);
v_fst_4620_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_fst_4620_);
lean_dec_ref(v___x_4617_);
v_events_4621_ = lean_ctor_get(v_snd_4618_, 0);
lean_inc_ref_n(v_events_4621_, 2);
lean_dec(v_snd_4618_);
v_data_4622_ = lean_ctor_get(v_output_4619_, 0);
lean_inc_ref(v_data_4622_);
v_size_4623_ = lean_ctor_get(v_output_4619_, 1);
lean_inc(v_size_4623_);
lean_dec_ref(v_output_4619_);
v___x_4624_ = 1;
v___x_4625_ = lean_box(v___x_4586_);
v___x_4626_ = lean_box(v___x_4624_);
lean_inc_ref_n(v_connectionContext_4594_, 3);
lean_inc(v_socket_4593_);
lean_inc_ref(v_inst_4592_);
lean_inc_ref_n(v_config_4590_, 2);
lean_inc_n(v_handler_4589_, 3);
lean_inc_ref_n(v_responseBodyInstance_4588_, 2);
lean_inc_ref_n(v_h_4587_, 3);
v___f_4627_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 12, 10);
lean_closure_set(v___f_4627_, 0, v___x_4625_);
lean_closure_set(v___f_4627_, 1, v_h_4587_);
lean_closure_set(v___f_4627_, 2, v_responseBodyInstance_4588_);
lean_closure_set(v___f_4627_, 3, v_handler_4589_);
lean_closure_set(v___f_4627_, 4, v_config_4590_);
lean_closure_set(v___f_4627_, 5, v___f_4591_);
lean_closure_set(v___f_4627_, 6, v_inst_4592_);
lean_closure_set(v___f_4627_, 7, v_socket_4593_);
lean_closure_set(v___f_4627_, 8, v_connectionContext_4594_);
lean_closure_set(v___f_4627_, 9, v___x_4626_);
v___x_4628_ = lean_box(v___x_4586_);
v___f_4629_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4629_, 0, v_h_4587_);
lean_closure_set(v___f_4629_, 1, v_handler_4589_);
lean_closure_set(v___f_4629_, 2, v_extensions_4595_);
lean_closure_set(v___f_4629_, 3, v_connectionContext_4594_);
lean_closure_set(v___f_4629_, 4, v___x_4628_);
lean_closure_set(v___f_4629_, 5, v___f_4627_);
v___x_4630_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4630_, 0, v_fst_4620_);
lean_ctor_set(v___x_4630_, 1, v_requestStream_4603_);
lean_ctor_set(v___x_4630_, 2, v_keepAliveTimeout_4604_);
lean_ctor_set(v___x_4630_, 3, v_currentTimeout_4605_);
lean_ctor_set(v___x_4630_, 4, v_headerTimeout_4606_);
lean_ctor_set(v___x_4630_, 5, v_response_4607_);
lean_ctor_set(v___x_4630_, 6, v_respStream_4608_);
lean_ctor_set(v___x_4630_, 7, v_expectData_4610_);
lean_ctor_set(v___x_4630_, 8, v_pendingHead_4612_);
lean_ctor_set_uint8(v___x_4630_, sizeof(void*)*9, v_requiresData_4609_);
lean_ctor_set_uint8(v___x_4630_, sizeof(void*)*9 + 1, v_handlerDispatched_4611_);
v___x_4631_ = lean_box(v___x_4586_);
lean_inc_ref(v___f_4629_);
lean_inc_ref(v___x_4630_);
v___f_4632_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4632_, 0, v_h_4587_);
lean_closure_set(v___f_4632_, 1, v_responseBodyInstance_4588_);
lean_closure_set(v___f_4632_, 2, v_handler_4589_);
lean_closure_set(v___f_4632_, 3, v_config_4590_);
lean_closure_set(v___f_4632_, 4, v_connectionContext_4594_);
lean_closure_set(v___f_4632_, 5, v_events_4621_);
lean_closure_set(v___f_4632_, 6, v___x_4630_);
lean_closure_set(v___f_4632_, 7, v___x_4631_);
lean_closure_set(v___f_4632_, 8, v___f_4629_);
v___x_4633_ = lean_unsigned_to_nat(0u);
v___x_4634_ = lean_nat_dec_lt(v___x_4633_, v_size_4623_);
lean_dec(v_size_4623_);
if (v___x_4634_ == 0)
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
lean_dec_ref(v___f_4632_);
lean_dec_ref(v_data_4622_);
lean_dec_ref(v___f_4597_);
lean_dec_ref(v___f_4596_);
lean_dec(v_socket_4593_);
lean_dec_ref(v_inst_4592_);
v___x_4635_ = lean_box(0);
v___x_4636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4587_, v_responseBodyInstance_4588_, v_handler_4589_, v_config_4590_, v_connectionContext_4594_, v_events_4621_, v___x_4630_, v___x_4586_, v___f_4629_, v___x_4635_);
return v___x_4636_;
}
else
{
lean_object* v_sendAll_4637_; lean_object* v___f_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
lean_dec_ref(v___f_4629_);
lean_dec_ref(v_events_4621_);
lean_dec_ref(v_connectionContext_4594_);
lean_dec_ref(v_config_4590_);
lean_dec(v_handler_4589_);
lean_dec_ref(v_responseBodyInstance_4588_);
lean_dec_ref(v_h_4587_);
v_sendAll_4637_ = lean_ctor_get(v_inst_4592_, 1);
lean_inc_ref(v_sendAll_4637_);
lean_dec_ref(v_inst_4592_);
v___f_4638_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4638_, 0, v___x_4630_);
lean_closure_set(v___f_4638_, 1, v___f_4632_);
v___x_4639_ = lean_apply_3(v_sendAll_4637_, v_socket_4593_, v_data_4622_, lean_box(0));
v___x_4640_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4633_, v___x_4586_, v___x_4639_, v___f_4596_);
v___x_4641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4633_, v___x_4586_, v___x_4640_, v___f_4597_);
v___x_4642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4633_, v___x_4586_, v___x_4641_, v___f_4638_);
return v___x_4642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v___x_4651_, lean_object* v_h_4652_, lean_object* v_responseBodyInstance_4653_, lean_object* v_handler_4654_, lean_object* v_config_4655_, lean_object* v___f_4656_, lean_object* v_inst_4657_, lean_object* v_socket_4658_, lean_object* v_connectionContext_4659_, lean_object* v_extensions_4660_, lean_object* v___f_4661_, lean_object* v___f_4662_, lean_object* v_x_4663_, lean_object* v_____s_4664_, lean_object* v___y_4665_){
_start:
{
uint8_t v___x_5391__boxed_4666_; lean_object* v_res_4667_; 
v___x_5391__boxed_4666_ = lean_unbox(v___x_4651_);
v_res_4667_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v___x_5391__boxed_4666_, v_h_4652_, v_responseBodyInstance_4653_, v_handler_4654_, v_config_4655_, v___f_4656_, v_inst_4657_, v_socket_4658_, v_connectionContext_4659_, v_extensions_4660_, v___f_4661_, v___f_4662_, v_x_4663_, v_____s_4664_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4668_, lean_object* v_x_4669_){
_start:
{
if (lean_obj_tag(v_x_4669_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4679_; 
v_a_4671_ = lean_ctor_get(v_x_4669_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_x_4669_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4673_ = v_x_4669_;
v_isShared_4674_ = v_isSharedCheck_4679_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v_x_4669_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4679_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4677_; 
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
return v___x_4677_;
}
}
}
else
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
lean_dec_ref_known(v_x_4669_, 1);
v___x_4680_ = l_IO_Promise_result_x21___redArg(v_a_4668_);
v___x_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
return v___x_4681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4682_, lean_object* v_x_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4682_, v_x_4683_);
lean_dec(v_a_4682_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4686_, lean_object* v___x_4687_, lean_object* v___x_4688_, uint8_t v___x_4689_, lean_object* v_x_4690_){
_start:
{
if (lean_obj_tag(v_x_4690_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4700_; 
lean_dec_ref(v___x_4688_);
lean_dec(v___x_4687_);
lean_dec_ref(v___f_4686_);
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
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4712_; 
v_a_4701_ = lean_ctor_get(v_x_4690_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v_x_4690_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4703_ = v_x_4690_;
v_isShared_4704_ = v_isSharedCheck_4712_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v_x_4690_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4712_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___f_4705_; lean_object* v___x_4706_; lean_object* v___x_4708_; 
lean_inc(v_a_4701_);
v___f_4705_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4705_, 0, v_a_4701_);
lean_inc(v___x_4687_);
v___x_4706_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4686_, v___x_4687_, v_a_4701_, v___x_4688_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 0, v___x_4706_);
v___x_4708_ = v___x_4703_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4706_);
v___x_4708_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
v___x_4710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4687_, v___x_4689_, v___x_4709_, v___f_4705_);
return v___x_4710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4713_, lean_object* v___x_4714_, lean_object* v___x_4715_, lean_object* v___x_4716_, lean_object* v_x_4717_, lean_object* v___y_4718_){
_start:
{
uint8_t v___x_5506__boxed_4719_; lean_object* v_res_4720_; 
v___x_5506__boxed_4719_ = lean_unbox(v___x_4716_);
v_res_4720_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4713_, v___x_4714_, v___x_4715_, v___x_5506__boxed_4719_, v_x_4717_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4721_, lean_object* v_h_4722_, lean_object* v_responseBodyInstance_4723_, lean_object* v_handler_4724_, lean_object* v___f_4725_, lean_object* v_inst_4726_, lean_object* v_socket_4727_, lean_object* v_connectionContext_4728_, lean_object* v_extensions_4729_, lean_object* v___f_4730_, lean_object* v___f_4731_, lean_object* v_machine_4732_, lean_object* v_a_4733_, lean_object* v___x_4734_, lean_object* v___f_4735_, lean_object* v_x_4736_){
_start:
{
if (lean_obj_tag(v_x_4736_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4746_; 
lean_dec_ref(v___f_4735_);
lean_dec(v___x_4734_);
lean_dec_ref(v_a_4733_);
lean_dec_ref(v_machine_4732_);
lean_dec_ref(v___f_4731_);
lean_dec_ref(v___f_4730_);
lean_dec(v_extensions_4729_);
lean_dec_ref(v_connectionContext_4728_);
lean_dec(v_socket_4727_);
lean_dec_ref(v_inst_4726_);
lean_dec_ref(v___f_4725_);
lean_dec(v_handler_4724_);
lean_dec_ref(v_responseBodyInstance_4723_);
lean_dec_ref(v_h_4722_);
lean_dec_ref(v_config_4721_);
v_a_4738_ = lean_ctor_get(v_x_4736_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v_x_4736_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4740_ = v_x_4736_;
v_isShared_4741_ = v_isSharedCheck_4746_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v_x_4736_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4746_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4768_; 
v_a_4747_ = lean_ctor_get(v_x_4736_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_x_4736_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4749_ = v_x_4736_;
v_isShared_4750_ = v_isSharedCheck_4768_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v_x_4736_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4768_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v_keepAliveTimeout_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; lean_object* v___x_4755_; lean_object* v___f_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___f_4760_; lean_object* v___x_4761_; lean_object* v___x_4763_; 
v_keepAliveTimeout_4751_ = lean_ctor_get(v_config_4721_, 5);
lean_inc_n(v_keepAliveTimeout_4751_, 2);
v___x_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4752_, 0, v_keepAliveTimeout_4751_);
v___x_4753_ = lean_box(0);
v___x_4754_ = 0;
v___x_4755_ = lean_box(v___x_4754_);
v___f_4756_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 15, 12);
lean_closure_set(v___f_4756_, 0, v___x_4755_);
lean_closure_set(v___f_4756_, 1, v_h_4722_);
lean_closure_set(v___f_4756_, 2, v_responseBodyInstance_4723_);
lean_closure_set(v___f_4756_, 3, v_handler_4724_);
lean_closure_set(v___f_4756_, 4, v_config_4721_);
lean_closure_set(v___f_4756_, 5, v___f_4725_);
lean_closure_set(v___f_4756_, 6, v_inst_4726_);
lean_closure_set(v___f_4756_, 7, v_socket_4727_);
lean_closure_set(v___f_4756_, 8, v_connectionContext_4728_);
lean_closure_set(v___f_4756_, 9, v_extensions_4729_);
lean_closure_set(v___f_4756_, 10, v___f_4730_);
lean_closure_set(v___f_4756_, 11, v___f_4731_);
v___x_4757_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4757_, 0, v_machine_4732_);
lean_ctor_set(v___x_4757_, 1, v_a_4733_);
lean_ctor_set(v___x_4757_, 2, v___x_4752_);
lean_ctor_set(v___x_4757_, 3, v_keepAliveTimeout_4751_);
lean_ctor_set(v___x_4757_, 4, v___x_4753_);
lean_ctor_set(v___x_4757_, 5, v_a_4747_);
lean_ctor_set(v___x_4757_, 6, v___x_4753_);
lean_ctor_set(v___x_4757_, 7, v___x_4734_);
lean_ctor_set(v___x_4757_, 8, v___x_4753_);
lean_ctor_set_uint8(v___x_4757_, sizeof(void*)*9, v___x_4754_);
lean_ctor_set_uint8(v___x_4757_, sizeof(void*)*9 + 1, v___x_4754_);
v___x_4758_ = lean_unsigned_to_nat(0u);
v___x_4759_ = lean_box(v___x_4754_);
v___f_4760_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4760_, 0, v___f_4756_);
lean_closure_set(v___f_4760_, 1, v___x_4758_);
lean_closure_set(v___f_4760_, 2, v___x_4757_);
lean_closure_set(v___f_4760_, 3, v___x_4759_);
v___x_4761_ = lean_io_promise_new();
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v___x_4761_);
v___x_4763_ = v___x_4749_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4761_);
v___x_4763_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
v___x_4765_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4758_, v___x_4754_, v___x_4764_, v___f_4760_);
v___x_4766_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4758_, v___x_4754_, v___x_4765_, v___f_4735_);
return v___x_4766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4769_ = _args[0];
lean_object* v_h_4770_ = _args[1];
lean_object* v_responseBodyInstance_4771_ = _args[2];
lean_object* v_handler_4772_ = _args[3];
lean_object* v___f_4773_ = _args[4];
lean_object* v_inst_4774_ = _args[5];
lean_object* v_socket_4775_ = _args[6];
lean_object* v_connectionContext_4776_ = _args[7];
lean_object* v_extensions_4777_ = _args[8];
lean_object* v___f_4778_ = _args[9];
lean_object* v___f_4779_ = _args[10];
lean_object* v_machine_4780_ = _args[11];
lean_object* v_a_4781_ = _args[12];
lean_object* v___x_4782_ = _args[13];
lean_object* v___f_4783_ = _args[14];
lean_object* v_x_4784_ = _args[15];
lean_object* v___y_4785_ = _args[16];
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4769_, v_h_4770_, v_responseBodyInstance_4771_, v_handler_4772_, v___f_4773_, v_inst_4774_, v_socket_4775_, v_connectionContext_4776_, v_extensions_4777_, v___f_4778_, v___f_4779_, v_machine_4780_, v_a_4781_, v___x_4782_, v___f_4783_, v_x_4784_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4787_, lean_object* v_h_4788_, lean_object* v_responseBodyInstance_4789_, lean_object* v_handler_4790_, lean_object* v___f_4791_, lean_object* v_inst_4792_, lean_object* v_socket_4793_, lean_object* v_connectionContext_4794_, lean_object* v_extensions_4795_, lean_object* v___f_4796_, lean_object* v___f_4797_, lean_object* v_machine_4798_, lean_object* v___f_4799_, lean_object* v_x_4800_){
_start:
{
if (lean_obj_tag(v_x_4800_) == 0)
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4810_; 
lean_dec_ref(v___f_4799_);
lean_dec_ref(v_machine_4798_);
lean_dec_ref(v___f_4797_);
lean_dec_ref(v___f_4796_);
lean_dec(v_extensions_4795_);
lean_dec_ref(v_connectionContext_4794_);
lean_dec(v_socket_4793_);
lean_dec_ref(v_inst_4792_);
lean_dec_ref(v___f_4791_);
lean_dec(v_handler_4790_);
lean_dec_ref(v_responseBodyInstance_4789_);
lean_dec_ref(v_h_4788_);
lean_dec_ref(v_config_4787_);
v_a_4802_ = lean_ctor_get(v_x_4800_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_x_4800_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4804_ = v_x_4800_;
v_isShared_4805_ = v_isSharedCheck_4810_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v_x_4800_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4810_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4808_; 
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4807_);
return v___x_4808_;
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4825_; 
v_a_4811_ = lean_ctor_get(v_x_4800_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v_x_4800_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4813_ = v_x_4800_;
v_isShared_4814_ = v_isSharedCheck_4825_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v_x_4800_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4825_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___f_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
v___x_4815_ = lean_box(0);
v___f_4816_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4816_, 0, v_config_4787_);
lean_closure_set(v___f_4816_, 1, v_h_4788_);
lean_closure_set(v___f_4816_, 2, v_responseBodyInstance_4789_);
lean_closure_set(v___f_4816_, 3, v_handler_4790_);
lean_closure_set(v___f_4816_, 4, v___f_4791_);
lean_closure_set(v___f_4816_, 5, v_inst_4792_);
lean_closure_set(v___f_4816_, 6, v_socket_4793_);
lean_closure_set(v___f_4816_, 7, v_connectionContext_4794_);
lean_closure_set(v___f_4816_, 8, v_extensions_4795_);
lean_closure_set(v___f_4816_, 9, v___f_4796_);
lean_closure_set(v___f_4816_, 10, v___f_4797_);
lean_closure_set(v___f_4816_, 11, v_machine_4798_);
lean_closure_set(v___f_4816_, 12, v_a_4811_);
lean_closure_set(v___f_4816_, 13, v___x_4815_);
lean_closure_set(v___f_4816_, 14, v___f_4799_);
v___x_4817_ = lean_unsigned_to_nat(0u);
v___x_4818_ = 0;
v___x_4819_ = l_Std_CloseableChannel_new___redArg(v___x_4815_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4819_);
v___x_4821_ = v___x_4813_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
v___x_4823_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4817_, v___x_4818_, v___x_4822_, v___f_4816_);
return v___x_4823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4826_, lean_object* v_h_4827_, lean_object* v_responseBodyInstance_4828_, lean_object* v_handler_4829_, lean_object* v___f_4830_, lean_object* v_inst_4831_, lean_object* v_socket_4832_, lean_object* v_connectionContext_4833_, lean_object* v_extensions_4834_, lean_object* v___f_4835_, lean_object* v___f_4836_, lean_object* v_machine_4837_, lean_object* v___f_4838_, lean_object* v_x_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4826_, v_h_4827_, v_responseBodyInstance_4828_, v_handler_4829_, v___f_4830_, v_inst_4831_, v_socket_4832_, v_connectionContext_4833_, v_extensions_4834_, v___f_4835_, v___f_4836_, v_machine_4837_, v___f_4838_, v_x_4839_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4845_, lean_object* v_h_4846_, lean_object* v_connection_4847_, lean_object* v_config_4848_, lean_object* v_connectionContext_4849_, lean_object* v_handler_4850_){
_start:
{
lean_object* v_responseBodyInstance_4852_; lean_object* v_onFailure_4853_; lean_object* v_socket_4854_; lean_object* v_machine_4855_; lean_object* v_extensions_4856_; lean_object* v___f_4857_; lean_object* v___f_4858_; lean_object* v___f_4859_; lean_object* v___f_4860_; lean_object* v___f_4861_; lean_object* v___f_4862_; lean_object* v___f_4863_; lean_object* v___f_4864_; lean_object* v___f_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v_responseBodyInstance_4852_ = lean_ctor_get(v_h_4846_, 0);
lean_inc_ref_n(v_responseBodyInstance_4852_, 2);
v_onFailure_4853_ = lean_ctor_get(v_h_4846_, 2);
v_socket_4854_ = lean_ctor_get(v_connection_4847_, 0);
lean_inc_n(v_socket_4854_, 2);
v_machine_4855_ = lean_ctor_get(v_connection_4847_, 1);
lean_inc_ref(v_machine_4855_);
v_extensions_4856_ = lean_ctor_get(v_connection_4847_, 2);
lean_inc(v_extensions_4856_);
lean_dec_ref(v_connection_4847_);
v___f_4857_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4858_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4859_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4850_);
lean_inc_ref(v_onFailure_4853_);
v___f_4860_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4860_, 0, v_onFailure_4853_);
lean_closure_set(v___f_4860_, 1, v_handler_4850_);
lean_closure_set(v___f_4860_, 2, v___f_4859_);
v___f_4861_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4845_);
v___f_4862_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4862_, 0, v_inst_4845_);
lean_closure_set(v___f_4862_, 1, v_socket_4854_);
lean_inc_ref(v___f_4862_);
v___f_4863_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4863_, 0, v___f_4862_);
v___f_4864_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4864_, 0, v_responseBodyInstance_4852_);
lean_closure_set(v___f_4864_, 1, v___f_4863_);
lean_closure_set(v___f_4864_, 2, v___f_4862_);
lean_closure_set(v___f_4864_, 3, v___f_4857_);
v___f_4865_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4865_, 0, v_config_4848_);
lean_closure_set(v___f_4865_, 1, v_h_4846_);
lean_closure_set(v___f_4865_, 2, v_responseBodyInstance_4852_);
lean_closure_set(v___f_4865_, 3, v_handler_4850_);
lean_closure_set(v___f_4865_, 4, v___f_4861_);
lean_closure_set(v___f_4865_, 5, v_inst_4845_);
lean_closure_set(v___f_4865_, 6, v_socket_4854_);
lean_closure_set(v___f_4865_, 7, v_connectionContext_4849_);
lean_closure_set(v___f_4865_, 8, v_extensions_4856_);
lean_closure_set(v___f_4865_, 9, v___f_4858_);
lean_closure_set(v___f_4865_, 10, v___f_4860_);
lean_closure_set(v___f_4865_, 11, v_machine_4855_);
lean_closure_set(v___f_4865_, 12, v___f_4864_);
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = 0;
v___x_4868_ = l_Std_Http_Body_mkStream();
v___x_4869_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4866_, v___x_4867_, v___x_4868_, v___f_4865_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4870_, lean_object* v_h_4871_, lean_object* v_connection_4872_, lean_object* v_config_4873_, lean_object* v_connectionContext_4874_, lean_object* v_handler_4875_, lean_object* v_a_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4870_, v_h_4871_, v_connection_4872_, v_config_4873_, v_connectionContext_4874_, v_handler_4875_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4878_, lean_object* v_00_u03c3_4879_, lean_object* v_inst_4880_, lean_object* v_h_4881_, lean_object* v_connection_4882_, lean_object* v_config_4883_, lean_object* v_connectionContext_4884_, lean_object* v_handler_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4880_, v_h_4881_, v_connection_4882_, v_config_4883_, v_connectionContext_4884_, v_handler_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4888_, lean_object* v_00_u03c3_4889_, lean_object* v_inst_4890_, lean_object* v_h_4891_, lean_object* v_connection_4892_, lean_object* v_config_4893_, lean_object* v_connectionContext_4894_, lean_object* v_handler_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4888_, v_00_u03c3_4889_, v_inst_4890_, v_h_4891_, v_connection_4892_, v_config_4893_, v_connectionContext_4894_, v_handler_4895_);
return v_res_4897_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4898_; lean_object* v___x_4899_; 
v___x_4898_ = 0;
v___x_4899_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4898_);
return v___x_4899_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = lean_unsigned_to_nat(4096u);
v___x_4901_ = lean_mk_empty_byte_array(v___x_4900_);
return v___x_4901_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4902_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4903_ = l_ByteArray_mkIterator(v___x_4902_);
return v___x_4903_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4904_ = 0;
v___x_4905_ = lean_unsigned_to_nat(0u);
v___x_4906_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4907_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4908_ = lean_box(0);
v___x_4909_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4909_, 0, v___x_4908_);
lean_ctor_set(v___x_4909_, 1, v___x_4907_);
lean_ctor_set(v___x_4909_, 2, v___x_4906_);
lean_ctor_set(v___x_4909_, 3, v___x_4905_);
lean_ctor_set(v___x_4909_, 4, v___x_4905_);
lean_ctor_set(v___x_4909_, 5, v___x_4905_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*6, v___x_4904_);
return v___x_4909_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4917_; lean_object* v___x_4918_; 
v___x_4917_ = 1;
v___x_4918_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4917_);
return v___x_4918_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4919_ = lean_unsigned_to_nat(0u);
v___x_4920_ = 0;
v___x_4921_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4922_ = lean_box(0);
v___x_4923_ = lean_box(0);
v___x_4924_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4925_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4926_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
lean_ctor_set(v___x_4926_, 1, v___x_4924_);
lean_ctor_set(v___x_4926_, 2, v___x_4923_);
lean_ctor_set(v___x_4926_, 3, v___x_4922_);
lean_ctor_set(v___x_4926_, 4, v___x_4921_);
lean_ctor_set(v___x_4926_, 5, v___x_4919_);
lean_ctor_set_uint8(v___x_4926_, sizeof(void*)*6, v___x_4920_);
lean_ctor_set_uint8(v___x_4926_, sizeof(void*)*6 + 1, v___x_4920_);
lean_ctor_set_uint8(v___x_4926_, sizeof(void*)*6 + 2, v___x_4920_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4927_, lean_object* v_client_4928_, lean_object* v_extensions_4929_, lean_object* v_inst_4930_, lean_object* v_inst_4931_, lean_object* v_handler_4932_, lean_object* v_x_4933_){
_start:
{
if (lean_obj_tag(v_x_4933_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4943_; 
lean_dec(v_handler_4932_);
lean_dec_ref(v_inst_4931_);
lean_dec_ref(v_inst_4930_);
lean_dec(v_extensions_4929_);
lean_dec(v_client_4928_);
lean_dec_ref(v_config_4927_);
v_a_4935_ = lean_ctor_get(v_x_4933_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v_x_4933_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4937_ = v_x_4933_;
v_isShared_4938_ = v_isSharedCheck_4943_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v_x_4933_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4943_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_object* v___x_4941_; 
v___x_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4940_);
return v___x_4941_;
}
}
}
else
{
lean_object* v_a_4944_; uint8_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; uint8_t v_enableKeepAlive_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v_a_4944_ = lean_ctor_get(v_x_4933_, 0);
lean_inc(v_a_4944_);
lean_dec_ref_known(v_x_4933_, 1);
v___x_4945_ = 0;
v___x_4946_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4947_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4948_ = lean_box(0);
v___x_4949_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4950_ = l_Std_Http_Config_toH1Config(v_config_4927_);
v_enableKeepAlive_4951_ = lean_ctor_get_uint8(v___x_4950_, sizeof(void*)*18);
v___x_4952_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4952_, 0, v___x_4946_);
lean_ctor_set(v___x_4952_, 1, v___x_4949_);
lean_ctor_set(v___x_4952_, 2, v___x_4950_);
lean_ctor_set(v___x_4952_, 3, v___x_4947_);
lean_ctor_set(v___x_4952_, 4, v___x_4948_);
lean_ctor_set(v___x_4952_, 5, v___x_4948_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*6, v_enableKeepAlive_4951_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*6 + 1, v___x_4945_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*6 + 2, v___x_4945_);
v___x_4953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4953_, 0, v_client_4928_);
lean_ctor_set(v___x_4953_, 1, v___x_4952_);
lean_ctor_set(v___x_4953_, 2, v_extensions_4929_);
v___x_4954_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4930_, v_inst_4931_, v___x_4953_, v_config_4927_, v_a_4944_, v_handler_4932_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4955_, lean_object* v_client_4956_, lean_object* v_extensions_4957_, lean_object* v_inst_4958_, lean_object* v_inst_4959_, lean_object* v_handler_4960_, lean_object* v_x_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4955_, v_client_4956_, v_extensions_4957_, v_inst_4958_, v_inst_4959_, v_handler_4960_, v_x_4961_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4964_, lean_object* v_inst_4965_, lean_object* v_client_4966_, lean_object* v_handler_4967_, lean_object* v_config_4968_, lean_object* v_extensions_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___f_4972_; lean_object* v___x_4973_; uint8_t v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___f_4972_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4972_, 0, v_config_4968_);
lean_closure_set(v___f_4972_, 1, v_client_4966_);
lean_closure_set(v___f_4972_, 2, v_extensions_4969_);
lean_closure_set(v___f_4972_, 3, v_inst_4964_);
lean_closure_set(v___f_4972_, 4, v_inst_4965_);
lean_closure_set(v___f_4972_, 5, v_handler_4967_);
v___x_4973_ = lean_unsigned_to_nat(0u);
v___x_4974_ = 0;
lean_inc_ref(v_a_4970_);
v___x_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4975_, 0, v_a_4970_);
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
v___x_4977_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4973_, v___x_4974_, v___x_4976_, v___f_4972_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4978_, lean_object* v_inst_4979_, lean_object* v_client_4980_, lean_object* v_handler_4981_, lean_object* v_config_4982_, lean_object* v_extensions_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4978_, v_inst_4979_, v_client_4980_, v_handler_4981_, v_config_4982_, v_extensions_4983_, v_a_4984_);
lean_dec_ref(v_a_4984_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4987_, lean_object* v_00_u03c3_4988_, lean_object* v_inst_4989_, lean_object* v_inst_4990_, lean_object* v_client_4991_, lean_object* v_handler_4992_, lean_object* v_config_4993_, lean_object* v_extensions_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4989_, v_inst_4990_, v_client_4991_, v_handler_4992_, v_config_4993_, v_extensions_4994_, v_a_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4998_, lean_object* v_00_u03c3_4999_, lean_object* v_inst_5000_, lean_object* v_inst_5001_, lean_object* v_client_5002_, lean_object* v_handler_5003_, lean_object* v_config_5004_, lean_object* v_extensions_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Std_Http_Server_serveConnection(v_t_4998_, v_00_u03c3_4999_, v_inst_5000_, v_inst_5001_, v_client_5002_, v_handler_5003_, v_config_5004_, v_extensions_5005_, v_a_5006_);
lean_dec_ref(v_a_5006_);
return v_res_5008_;
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
