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
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
extern lean_object* l_Std_Http_Header_Name_date;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_DateTime_toHTTPDateString(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
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
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__8_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__4_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__5_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__6_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__9_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__7_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12_value;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg(lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_tag_nat(v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg___boxed(lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg(v_x_42_);
lean_dec(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl(lean_object* v_00_u03b2_44_, lean_object* v_x_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_tag_nat(v_x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___boxed(lean_object* v_00_u03b2_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl(v_00_u03b2_47_, v_x_48_);
lean_dec(v_x_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(lean_object* v_t_50_, lean_object* v_k_51_){
_start:
{
switch(lean_obj_tag(v_t_50_))
{
case 0:
{
lean_object* v_x_52_; lean_object* v___x_53_; 
v_x_52_ = lean_ctor_get(v_t_50_, 0);
lean_inc(v_x_52_);
lean_dec_ref_known(v_t_50_, 1);
v___x_53_ = lean_apply_1(v_k_51_, v_x_52_);
return v___x_53_;
}
case 1:
{
lean_object* v_x_54_; lean_object* v___x_55_; 
v_x_54_ = lean_ctor_get(v_t_50_, 0);
lean_inc(v_x_54_);
lean_dec_ref_known(v_t_50_, 1);
v___x_55_ = lean_apply_1(v_k_51_, v_x_54_);
return v___x_55_;
}
case 2:
{
uint8_t v_x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_x_56_ = lean_ctor_get_uint8(v_t_50_, 0);
lean_dec_ref_known(v_t_50_, 0);
v___x_57_ = lean_box(v_x_56_);
v___x_58_ = lean_apply_1(v_k_51_, v___x_57_);
return v___x_58_;
}
case 3:
{
lean_object* v_x_59_; lean_object* v___x_60_; 
v_x_59_ = lean_ctor_get(v_t_50_, 0);
lean_inc_ref(v_x_59_);
lean_dec_ref_known(v_t_50_, 1);
v___x_60_ = lean_apply_1(v_k_51_, v_x_59_);
return v___x_60_;
}
default: 
{
lean_dec(v_t_50_);
return v_k_51_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(lean_object* v_00_u03b2_61_, lean_object* v_motive_62_, lean_object* v_ctorIdx_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_k_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_64_, v_k_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___boxed(lean_object* v_00_u03b2_68_, lean_object* v_motive_69_, lean_object* v_ctorIdx_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_k_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(v_00_u03b2_68_, v_motive_69_, v_ctorIdx_70_, v_t_71_, v_h_72_, v_k_73_);
lean_dec(v_ctorIdx_70_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim___redArg(lean_object* v_t_75_, lean_object* v_bytes_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_75_, v_bytes_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim(lean_object* v_00_u03b2_78_, lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_bytes_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_80_, v_bytes_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim___redArg(lean_object* v_t_84_, lean_object* v_responseBody_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_84_, v_responseBody_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim(lean_object* v_00_u03b2_87_, lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_responseBody_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_89_, v_responseBody_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim___redArg(lean_object* v_t_93_, lean_object* v_bodyInterest_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_93_, v_bodyInterest_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim(lean_object* v_00_u03b2_96_, lean_object* v_motive_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_bodyInterest_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_98_, v_bodyInterest_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim___redArg(lean_object* v_t_102_, lean_object* v_response_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_102_, v_response_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim(lean_object* v_00_u03b2_105_, lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_response_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_107_, v_response_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object* v_t_111_, lean_object* v_timeout_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_111_, v_timeout_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object* v_00_u03b2_114_, lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_timeout_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_116_, v_timeout_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object* v_t_120_, lean_object* v_shutdown_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_120_, v_shutdown_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object* v_00_u03b2_123_, lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_shutdown_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_125_, v_shutdown_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object* v_t_129_, lean_object* v_close_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_129_, v_close_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object* v_00_u03b2_132_, lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_close_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_134_, v_close_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_a_150_ = lean_ctor_get(v_x_146_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_146_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v_x_146_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v_x_146_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; 
v_a_159_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v_x_146_, 1);
if (lean_obj_tag(v_a_159_) == 1)
{
lean_object* v_val_160_; 
v_val_160_ = lean_ctor_get(v_a_159_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v_a_159_, 1);
if (lean_obj_tag(v_val_160_) == 0)
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_161_;
}
else
{
lean_dec(v_val_160_);
goto v___jp_148_;
}
}
else
{
lean_dec(v_a_159_);
goto v___jp_148_;
}
}
v___jp_148_:
{
lean_object* v___x_149_; 
v___x_149_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1));
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_a_171_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
else
{
lean_object* v___x_180_; 
lean_dec_ref_known(v_x_169_, 1);
v___x_180_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_184_, lean_object* v_handler_185_, lean_object* v___f_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_a_189_; lean_object* v_onFailure_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_a_189_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v_x_187_, 1);
v_onFailure_190_ = lean_ctor_get(v_inst_184_, 2);
lean_inc_ref(v_onFailure_190_);
lean_dec_ref(v_inst_184_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = 0;
v___x_193_ = lean_apply_3(v_onFailure_190_, v_handler_185_, v_a_189_, lean_box(0));
v___x_194_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_191_, v___x_192_, v___x_193_, v___f_186_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; 
lean_dec_ref(v___f_186_);
lean_dec(v_handler_185_);
lean_dec_ref(v_inst_184_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_x_187_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_196_, lean_object* v_handler_197_, lean_object* v___f_198_, lean_object* v_x_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_196_, v_handler_197_, v___f_198_, v_x_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_202_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_204_, 0, v_x_202_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_212_, 0, v_x_210_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_215_, lean_object* v___y_216_){
_start:
{
uint8_t v_x_3730__boxed_217_; lean_object* v_res_218_; 
v_x_3730__boxed_217_ = lean_unbox(v_x_215_);
v_res_218_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3730__boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_219_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_x_219_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_227_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_x_227_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v_x_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v_x_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_x_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v___f_247_, lean_object* v_response_248_, lean_object* v___x_249_, lean_object* v___f_250_, lean_object* v_requestBody_251_, lean_object* v___f_252_, lean_object* v_responseBody_253_, lean_object* v_inst_254_, lean_object* v___f_255_, lean_object* v_____r_256_, lean_object* v_selectables_257_){
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
lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = 0;
v___x_263_ = l_Std_Async_Selectable_one___redArg(v_selectables_260_);
v___x_264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_261_, v___x_262_, v___x_263_, v___f_247_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v___f_282_, lean_object* v_response_283_, lean_object* v___x_284_, lean_object* v___f_285_, lean_object* v_requestBody_286_, lean_object* v___f_287_, lean_object* v_responseBody_288_, lean_object* v_inst_289_, lean_object* v___f_290_, lean_object* v_____r_291_, lean_object* v_selectables_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_282_, v_response_283_, v___x_284_, v___f_285_, v_requestBody_286_, v___f_287_, v_responseBody_288_, v_inst_289_, v___f_290_, v_____r_291_, v_selectables_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v_token_295_, lean_object* v___f_296_, lean_object* v_x_297_){
_start:
{
lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = 0;
v___x_301_ = l_Std_CancellationToken_getCancellationReason(v_token_295_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___x_304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_299_, v___x_300_, v___x_303_, v___f_296_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v_token_305_, lean_object* v___f_306_, lean_object* v_x_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v_token_305_, v___f_306_, v_x_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v___f_310_, lean_object* v_selectables_311_, lean_object* v___f_312_, lean_object* v_x_313_){
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v___f_329_, lean_object* v_selectables_330_, lean_object* v___f_331_, lean_object* v_x_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v___f_329_, v_selectables_330_, v___f_331_, v_x_332_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1000000000u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1000u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1000000u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object* v_val_341_, lean_object* v___f_342_, lean_object* v_x_343_){
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
lean_object* v_a_354_; lean_object* v_second_355_; lean_object* v_nano_356_; lean_object* v_second_357_; lean_object* v_nano_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_nanos_363_; lean_object* v___x_364_; lean_object* v_nanos_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_second_368_; lean_object* v_nano_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_millis_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
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
v___x_361_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_362_ = lean_int_mul(v_second_357_, v___x_361_);
v_nanos_363_ = lean_int_add(v___x_362_, v_nano_358_);
lean_dec(v___x_362_);
v___x_364_ = lean_int_mul(v___x_359_, v___x_361_);
lean_dec(v___x_359_);
v_nanos_365_ = lean_int_add(v___x_364_, v___x_360_);
lean_dec(v___x_360_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_add(v_nanos_363_, v_nanos_365_);
lean_dec(v_nanos_365_);
lean_dec(v_nanos_363_);
v___x_367_ = l_Std_Time_Duration_ofNanoseconds(v___x_366_);
lean_dec(v___x_366_);
v_second_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_second_368_);
v_nano_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_nano_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1);
v___x_371_ = lean_int_mul(v_second_368_, v___x_370_);
lean_dec(v_second_368_);
v___x_372_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_373_ = lean_int_ediv(v_nano_369_, v___x_372_);
lean_dec(v_nano_369_);
v_millis_374_ = lean_int_add(v___x_371_, v___x_373_);
lean_dec(v___x_373_);
lean_dec(v___x_371_);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = 0;
v___x_377_ = l_Std_Async_Selector_sleep(v_millis_374_);
lean_dec(v_millis_374_);
v___x_378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_375_, v___x_376_, v___x_377_, v___f_342_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object* v_val_379_, lean_object* v___f_380_, lean_object* v_x_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(v_val_379_, v___f_380_, v_x_381_);
lean_dec_ref(v_val_379_);
return v_res_383_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = l_instInhabitedError;
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_config_397_, lean_object* v_handler_398_, lean_object* v_sources_399_){
_start:
{
uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v_val_405_; lean_object* v_socket_408_; lean_object* v_expect_409_; lean_object* v_response_410_; lean_object* v_responseBody_411_; lean_object* v_requestBody_412_; lean_object* v_timeout_413_; lean_object* v_keepAliveTimeout_414_; lean_object* v_headerTimeout_415_; lean_object* v_connectionContext_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___y_429_; lean_object* v___y_479_; 
v_socket_408_ = lean_ctor_get(v_sources_399_, 0);
lean_inc(v_socket_408_);
v_expect_409_ = lean_ctor_get(v_sources_399_, 1);
lean_inc(v_expect_409_);
v_response_410_ = lean_ctor_get(v_sources_399_, 2);
lean_inc_n(v_response_410_, 2);
v_responseBody_411_ = lean_ctor_get(v_sources_399_, 3);
lean_inc_n(v_responseBody_411_, 2);
v_requestBody_412_ = lean_ctor_get(v_sources_399_, 4);
lean_inc_n(v_requestBody_412_, 2);
v_timeout_413_ = lean_ctor_get(v_sources_399_, 5);
lean_inc(v_timeout_413_);
v_keepAliveTimeout_414_ = lean_ctor_get(v_sources_399_, 6);
lean_inc(v_keepAliveTimeout_414_);
v_headerTimeout_415_ = lean_ctor_get(v_sources_399_, 7);
lean_inc(v_headerTimeout_415_);
v_connectionContext_416_ = lean_ctor_get(v_sources_399_, 8);
lean_inc_ref(v_connectionContext_416_);
lean_dec_ref(v_sources_399_);
v___f_417_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_419_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_419_, 0, v_inst_395_);
lean_closure_set(v___f_419_, 1, v_handler_398_);
lean_closure_set(v___f_419_, 2, v___f_418_);
v___f_420_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_421_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_422_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_423_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_424_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___f_425_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7));
v___x_426_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8);
lean_inc_ref(v_inst_396_);
lean_inc_ref(v___f_419_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 12, 9);
lean_closure_set(v___f_427_, 0, v___f_419_);
lean_closure_set(v___f_427_, 1, v_response_410_);
lean_closure_set(v___f_427_, 2, v___x_426_);
lean_closure_set(v___f_427_, 3, v___f_420_);
lean_closure_set(v___f_427_, 4, v_requestBody_412_);
lean_closure_set(v___f_427_, 5, v___f_421_);
lean_closure_set(v___f_427_, 6, v_responseBody_411_);
lean_closure_set(v___f_427_, 7, v_inst_396_);
lean_closure_set(v___f_427_, 8, v___f_422_);
if (lean_obj_tag(v_expect_409_) == 0)
{
lean_object* v_defaultPayloadBytes_482_; 
v_defaultPayloadBytes_482_ = lean_ctor_get(v_config_397_, 8);
lean_inc(v_defaultPayloadBytes_482_);
v___y_479_ = v_defaultPayloadBytes_482_;
goto v___jp_478_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v_expect_409_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v_expect_409_, 1);
v___y_479_ = v_val_483_;
goto v___jp_478_;
}
v___jp_401_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_val_405_);
v___x_407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_403_, v___y_402_, v___x_406_, v___y_404_);
return v___x_407_;
}
v___jp_428_:
{
lean_object* v_token_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v_selectables_436_; 
v_token_430_ = lean_ctor_get(v_connectionContext_416_, 1);
lean_inc_ref_n(v_token_430_, 2);
lean_dec_ref(v_connectionContext_416_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_431_, 0, v_token_430_);
lean_closure_set(v___f_431_, 1, v___f_417_);
v___x_432_ = l_Std_CancellationToken_selector(v_token_430_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___f_431_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v_selectables_436_ = lean_array_push(v___x_435_, v___x_433_);
if (lean_obj_tag(v_socket_408_) == 1)
{
lean_object* v_val_437_; lean_object* v_recvSelector_438_; uint64_t v_expectedBytes_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_selectables_443_; 
lean_dec_ref(v___f_419_);
lean_dec(v_requestBody_412_);
lean_dec(v_responseBody_411_);
lean_dec(v_response_410_);
lean_dec_ref(v_inst_396_);
v_val_437_ = lean_ctor_get(v_socket_408_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_socket_408_, 1);
v_recvSelector_438_ = lean_ctor_get(v_inst_394_, 2);
lean_inc_ref(v_recvSelector_438_);
lean_dec_ref(v_inst_394_);
v_expectedBytes_439_ = lean_uint64_of_nat(v___y_429_);
lean_dec(v___y_429_);
v___x_440_ = lean_box_uint64(v_expectedBytes_439_);
v___x_441_ = lean_apply_2(v_recvSelector_438_, v_val_437_, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___f_423_);
v_selectables_443_ = lean_array_push(v_selectables_436_, v___x_442_);
if (lean_obj_tag(v_keepAliveTimeout_414_) == 0)
{
if (lean_obj_tag(v_headerTimeout_415_) == 1)
{
lean_object* v_val_444_; lean_object* v___f_445_; lean_object* v___f_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
lean_dec(v_timeout_413_);
v_val_444_ = lean_ctor_get(v_headerTimeout_415_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_headerTimeout_415_, 1);
v___f_445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_445_, 0, v___f_424_);
lean_closure_set(v___f_445_, 1, v_selectables_443_);
lean_closure_set(v___f_445_, 2, v___f_427_);
v___f_446_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_446_, 0, v_val_444_);
lean_closure_set(v___f_446_, 1, v___f_445_);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = 0;
v___x_449_ = lean_get_current_time();
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 1);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v___y_402_ = v___x_448_;
v___y_403_ = v___x_447_;
v___y_404_ = v___f_446_;
v_val_405_ = v___x_455_;
goto v___jp_401_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_449_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_449_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v___y_402_ = v___x_448_;
v___y_403_ = v___x_447_;
v___y_404_ = v___f_446_;
v_val_405_ = v___x_463_;
goto v___jp_401_;
}
}
}
}
else
{
lean_object* v___f_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_headerTimeout_415_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_466_, 0, v___f_424_);
lean_closure_set(v___f_466_, 1, v_selectables_443_);
lean_closure_set(v___f_466_, 2, v___f_427_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = 0;
v___x_469_ = l_Std_Async_Selector_sleep(v_timeout_413_);
lean_dec(v_timeout_413_);
v___x_470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_467_, v___x_468_, v___x_469_, v___f_466_);
return v___x_470_;
}
}
else
{
lean_object* v___f_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref_known(v_keepAliveTimeout_414_, 1);
lean_dec(v_headerTimeout_415_);
v___f_471_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_471_, 0, v___f_425_);
lean_closure_set(v___f_471_, 1, v_selectables_443_);
lean_closure_set(v___f_471_, 2, v___f_427_);
v___x_472_ = 0;
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = l_Std_Async_Selector_sleep(v_timeout_413_);
lean_dec(v_timeout_413_);
v___x_475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_473_, v___x_472_, v___x_474_, v___f_471_);
return v___x_475_;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v___y_429_);
lean_dec_ref(v___f_427_);
lean_dec(v_headerTimeout_415_);
lean_dec(v_keepAliveTimeout_414_);
lean_dec(v_timeout_413_);
lean_dec(v_socket_408_);
lean_dec_ref(v_inst_394_);
v___x_476_ = lean_box(0);
v___x_477_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_419_, v_response_410_, v___x_426_, v___f_420_, v_requestBody_412_, v___f_421_, v_responseBody_411_, v_inst_396_, v___f_422_, v___x_476_, v_selectables_436_);
return v___x_477_;
}
}
v___jp_478_:
{
lean_object* v_maximumRecvSize_480_; uint8_t v___x_481_; 
v_maximumRecvSize_480_ = lean_ctor_get(v_config_397_, 7);
lean_inc(v_maximumRecvSize_480_);
lean_dec_ref(v_config_397_);
v___x_481_ = lean_nat_dec_le(v___y_479_, v_maximumRecvSize_480_);
if (v___x_481_ == 0)
{
lean_dec(v___y_479_);
v___y_429_ = v_maximumRecvSize_480_;
goto v___jp_428_;
}
else
{
lean_dec(v_maximumRecvSize_480_);
v___y_429_ = v___y_479_;
goto v___jp_428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_config_487_, lean_object* v_handler_488_, lean_object* v_sources_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_484_, v_inst_485_, v_inst_486_, v_config_487_, v_handler_488_, v_sources_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_492_, lean_object* v_00_u03c3_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_config_498_, lean_object* v_handler_499_, lean_object* v_sources_500_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_495_, v_inst_496_, v_inst_497_, v_config_498_, v_handler_499_, v_sources_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_503_, lean_object* v_00_u03c3_504_, lean_object* v_00_u03b2_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_config_509_, lean_object* v_handler_510_, lean_object* v_sources_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_503_, v_00_u03c3_504_, v_00_u03b2_505_, v_inst_506_, v_inst_507_, v_inst_508_, v_config_509_, v_handler_510_, v_sources_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___y_518_; uint8_t v___y_519_; 
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_machine_514_);
v_a_524_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v_x_515_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v_x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___y_535_; uint8_t v___x_541_; 
v_a_533_ = lean_ctor_get(v_x_515_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v_x_515_, 1);
v___x_541_ = lean_unbox(v_a_533_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(40);
v___y_535_ = v___x_542_;
goto v___jp_534_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
v___y_535_ = v___x_543_;
goto v___jp_534_;
}
v___jp_534_:
{
uint8_t v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = 0;
lean_inc(v___y_535_);
v___x_537_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_536_, v_machine_514_, v___y_535_);
v___x_538_ = lean_unbox(v_a_533_);
lean_dec(v_a_533_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
v___x_539_ = 1;
v___y_518_ = v___x_537_;
v___y_519_ = v___x_539_;
goto v___jp_517_;
}
else
{
uint8_t v___x_540_; 
v___x_540_ = 0;
v___y_518_ = v___x_537_;
v___y_519_ = v___x_540_;
goto v___jp_517_;
}
}
}
v___jp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_box(v___y_519_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___y_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_544_, lean_object* v_x_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_544_, v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_box(v___y_548_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___y_1377__boxed_555_; lean_object* v_res_556_; 
v___y_1377__boxed_555_ = lean_unbox(v___y_553_);
v_res_556_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1377__boxed_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v_x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_x_557_, 1);
v___x_559_ = lean_task_pure(v_a_558_);
return v___x_559_;
}
else
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v_x_557_, 0);
lean_inc_ref(v_a_560_);
lean_dec_ref_known(v_x_557_, 1);
return v_a_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref_known(v_x_562_, 1);
v___x_564_ = 0;
v___x_565_ = lean_box(0);
v___x_566_ = lean_box(v___x_564_);
v___x_567_ = l_Std_Channel_send___redArg(v_a_561_, v___x_566_);
lean_dec_ref(v___x_567_);
return v___x_565_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_a_568_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v_x_562_, 1);
v___x_569_ = lean_box(0);
v___x_570_ = l_Std_Channel_send___redArg(v_a_561_, v_a_568_);
lean_dec_ref(v___x_570_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_571_, v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(v___x_575_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_581_, lean_object* v_x_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_1421__boxed_584_; lean_object* v_res_585_; 
v___x_1421__boxed_584_ = lean_unbox(v___x_581_);
v_res_585_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1421__boxed_584_, v_x_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_586_, uint8_t v___x_587_, lean_object* v_a_588_, lean_object* v___f_589_, lean_object* v___f_590_, lean_object* v___x_591_, uint8_t v___x_592_, lean_object* v___f_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v___f_593_);
lean_dec(v___x_591_);
lean_dec_ref(v___f_590_);
lean_dec_ref(v___f_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_connectionContext_586_);
v_a_596_ = lean_ctor_get(v_x_594_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v_x_594_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v_x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v_token_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_a_605_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v_x_594_, 1);
v_token_606_ = lean_ctor_get(v_connectionContext_586_, 1);
lean_inc_ref(v_token_606_);
lean_dec_ref(v_connectionContext_586_);
v___x_607_ = lean_box(v___x_587_);
v___x_608_ = l_Std_Channel_recvSelector___redArg(v___x_607_, v_a_588_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___f_589_);
v___x_610_ = l_Std_CancellationToken_selector(v_token_606_);
lean_inc_ref(v___f_590_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___f_590_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_a_605_);
lean_ctor_set(v___x_612_, 1, v___f_590_);
v___x_613_ = lean_unsigned_to_nat(3u);
v___x_614_ = lean_mk_empty_array_with_capacity(v___x_613_);
v___x_615_ = lean_array_push(v___x_614_, v___x_609_);
v___x_616_ = lean_array_push(v___x_615_, v___x_611_);
v___x_617_ = lean_array_push(v___x_616_, v___x_612_);
v___x_618_ = l_Std_Async_Selectable_one___redArg(v___x_617_);
v___x_619_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_591_, v___x_592_, v___x_618_, v___f_593_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_620_, lean_object* v___x_621_, lean_object* v_a_622_, lean_object* v___f_623_, lean_object* v___f_624_, lean_object* v___x_625_, lean_object* v___x_626_, lean_object* v___f_627_, lean_object* v_x_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_1436__boxed_630_; uint8_t v___x_1441__boxed_631_; lean_object* v_res_632_; 
v___x_1436__boxed_630_ = lean_unbox(v___x_621_);
v___x_1441__boxed_631_ = lean_unbox(v___x_626_);
v_res_632_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_620_, v___x_1436__boxed_630_, v_a_622_, v___f_623_, v___f_624_, v___x_625_, v___x_1441__boxed_631_, v___f_627_, v_x_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_633_, lean_object* v___x_634_, uint8_t v___x_635_, lean_object* v___f_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___f_636_);
lean_dec(v___x_634_);
v_a_639_ = lean_ctor_get(v_x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
else
{
lean_object* v_lingeringTimeout_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref_known(v_x_637_, 1);
v_lingeringTimeout_648_ = lean_ctor_get(v_config_633_, 4);
v___x_649_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_648_);
v___x_650_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_634_, v___x_635_, v___x_649_, v___f_636_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v___f_654_, lean_object* v_x_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_1510__boxed_657_; lean_object* v_res_658_; 
v___x_1510__boxed_657_ = lean_unbox(v___x_653_);
v_res_658_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_651_, v___x_652_, v___x_1510__boxed_657_, v___f_654_, v_x_655_);
lean_dec_ref(v_config_651_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_662_, uint8_t v___x_663_, lean_object* v_a_664_, lean_object* v___f_665_, lean_object* v___x_666_, lean_object* v___f_667_, lean_object* v_config_668_, lean_object* v___f_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___f_669_);
lean_dec_ref(v_config_668_);
lean_dec_ref(v___f_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___f_665_);
lean_dec_ref(v_a_664_);
lean_dec_ref(v_connectionContext_662_);
v_a_672_ = lean_ctor_get(v_x_670_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v_x_670_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v_x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_679_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_698_; 
v_a_681_ = lean_ctor_get(v_x_670_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_698_ == 0)
{
v___x_683_ = v_x_670_;
v_isShared_684_ = v_isSharedCheck_698_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v_x_670_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_698_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_685_ = 0;
v___f_686_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_687_ = lean_box(v___x_663_);
v___x_688_ = lean_box(v___x_685_);
lean_inc_n(v___x_666_, 3);
v___f_689_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_689_, 0, v_connectionContext_662_);
lean_closure_set(v___f_689_, 1, v___x_687_);
lean_closure_set(v___f_689_, 2, v_a_664_);
lean_closure_set(v___f_689_, 3, v___f_665_);
lean_closure_set(v___f_689_, 4, v___f_686_);
lean_closure_set(v___f_689_, 5, v___x_666_);
lean_closure_set(v___f_689_, 6, v___x_688_);
lean_closure_set(v___f_689_, 7, v___f_667_);
v___x_690_ = lean_box(v___x_685_);
v___f_691_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_691_, 0, v_config_668_);
lean_closure_set(v___f_691_, 1, v___x_666_);
lean_closure_set(v___f_691_, 2, v___x_690_);
lean_closure_set(v___f_691_, 3, v___f_689_);
v___x_692_ = l_BaseIO_chainTask___redArg(v_a_681_, v___f_669_, v___x_666_, v___x_685_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_692_);
v___x_694_ = v___x_683_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_697_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
v___x_696_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_666_, v___x_685_, v___x_695_, v___f_691_);
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_699_, lean_object* v___x_700_, lean_object* v_a_701_, lean_object* v___f_702_, lean_object* v___x_703_, lean_object* v___f_704_, lean_object* v_config_705_, lean_object* v___f_706_, lean_object* v_x_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___x_1550__boxed_709_; lean_object* v_res_710_; 
v___x_1550__boxed_709_ = lean_unbox(v___x_700_);
v_res_710_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_699_, v___x_1550__boxed_709_, v_a_701_, v___f_702_, v___x_703_, v___f_704_, v_config_705_, v___f_706_, v_x_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_711_, lean_object* v_handler_712_, lean_object* v_head_713_, lean_object* v_connectionContext_714_, uint8_t v___x_715_, lean_object* v___f_716_, lean_object* v___f_717_, lean_object* v_config_718_, lean_object* v___f_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v___f_719_);
lean_dec_ref(v_config_718_);
lean_dec_ref(v___f_717_);
lean_dec_ref(v___f_716_);
lean_dec_ref(v_connectionContext_714_);
lean_dec_ref(v_head_713_);
lean_dec(v_handler_712_);
lean_dec_ref(v_inst_711_);
v_a_722_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v_x_720_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v_x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_751_; 
v_a_731_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_751_ == 0)
{
v___x_733_ = v_x_720_;
v_isShared_734_ = v_isSharedCheck_751_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v_x_720_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_751_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_onContinue_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___f_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v_onContinue_735_ = lean_ctor_get(v_inst_711_, 3);
lean_inc_ref(v_onContinue_735_);
lean_dec_ref(v_inst_711_);
lean_inc(v_a_731_);
v___f_736_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_736_, 0, v_a_731_);
v___x_737_ = lean_apply_2(v_onContinue_735_, v_handler_712_, v_head_713_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_box(v___x_715_);
v___f_740_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_740_, 0, v_connectionContext_714_);
lean_closure_set(v___f_740_, 1, v___x_739_);
lean_closure_set(v___f_740_, 2, v_a_731_);
lean_closure_set(v___f_740_, 3, v___f_716_);
lean_closure_set(v___f_740_, 4, v___x_738_);
lean_closure_set(v___f_740_, 5, v___f_717_);
lean_closure_set(v___f_740_, 6, v_config_718_);
lean_closure_set(v___f_740_, 7, v___f_736_);
v___x_741_ = 0;
v___x_742_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_742_, 0, lean_box(0));
lean_closure_set(v___x_742_, 1, v___x_737_);
v___x_743_ = lean_io_as_task(v___x_742_, v___x_738_);
v___x_744_ = 1;
v___x_745_ = lean_task_bind(v___x_743_, v___f_719_, v___x_738_, v___x_744_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_745_);
v___x_747_ = v___x_733_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_750_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_738_, v___x_741_, v___x_748_, v___f_740_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_752_, lean_object* v_handler_753_, lean_object* v_head_754_, lean_object* v_connectionContext_755_, lean_object* v___x_756_, lean_object* v___f_757_, lean_object* v___f_758_, lean_object* v_config_759_, lean_object* v___f_760_, lean_object* v_x_761_, lean_object* v___y_762_){
_start:
{
uint8_t v___x_1633__boxed_763_; lean_object* v_res_764_; 
v___x_1633__boxed_763_ = lean_unbox(v___x_756_);
v_res_764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_752_, v_handler_753_, v_head_754_, v_connectionContext_755_, v___x_1633__boxed_763_, v___f_757_, v___f_758_, v_config_759_, v___f_760_, v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_767_, lean_object* v_handler_768_, lean_object* v_machine_769_, lean_object* v_head_770_, lean_object* v_config_771_, lean_object* v_connectionContext_772_){
_start:
{
lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___f_774_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_774_, 0, v_machine_769_);
v___f_775_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_776_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_777_ = 0;
v___x_778_ = lean_box(v___x_777_);
v___f_779_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_779_, 0, v_inst_767_);
lean_closure_set(v___f_779_, 1, v_handler_768_);
lean_closure_set(v___f_779_, 2, v_head_770_);
lean_closure_set(v___f_779_, 3, v_connectionContext_772_);
lean_closure_set(v___f_779_, 4, v___x_778_);
lean_closure_set(v___f_779_, 5, v___f_775_);
lean_closure_set(v___f_779_, 6, v___f_774_);
lean_closure_set(v___f_779_, 7, v_config_771_);
lean_closure_set(v___f_779_, 8, v___f_776_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = l_Std_CloseableChannel_new___redArg(v___x_780_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_781_, v___x_777_, v___x_784_, v___f_779_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_786_, lean_object* v_handler_787_, lean_object* v_machine_788_, lean_object* v_head_789_, lean_object* v_config_790_, lean_object* v_connectionContext_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_786_, v_handler_787_, v_machine_788_, v_head_789_, v_config_790_, v_connectionContext_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_794_, lean_object* v_inst_795_, lean_object* v_handler_796_, lean_object* v_machine_797_, lean_object* v_head_798_, lean_object* v_config_799_, lean_object* v_connectionContext_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_795_, v_handler_796_, v_machine_797_, v_head_798_, v_config_799_, v_connectionContext_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_803_, lean_object* v_inst_804_, lean_object* v_handler_805_, lean_object* v_machine_806_, lean_object* v_head_807_, lean_object* v_config_808_, lean_object* v_connectionContext_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_803_, v_inst_804_, v_handler_805_, v_machine_806_, v_head_807_, v_config_808_, v_connectionContext_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_nat_to_int(v_a_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Rat_ofInt(v_a_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_tz_816_, lean_object* v_a_817_, lean_object* v___x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_offset_820_; lean_object* v_second_821_; lean_object* v_nano_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_nanos_826_; lean_object* v___x_827_; lean_object* v_nanos_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_offset_820_ = lean_ctor_get(v_tz_816_, 0);
v_second_821_ = lean_ctor_get(v_a_817_, 0);
v_nano_822_ = lean_ctor_get(v_a_817_, 1);
v___x_823_ = lean_nat_to_int(v___x_818_);
v___x_824_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_825_ = lean_int_mul(v_second_821_, v___x_824_);
v_nanos_826_ = lean_int_add(v___x_825_, v_nano_822_);
lean_dec(v___x_825_);
v___x_827_ = lean_int_mul(v_offset_820_, v___x_824_);
v_nanos_828_ = lean_int_add(v___x_827_, v___x_823_);
lean_dec(v___x_823_);
lean_dec(v___x_827_);
v___x_829_ = lean_int_add(v_nanos_826_, v_nanos_828_);
lean_dec(v_nanos_828_);
lean_dec(v_nanos_826_);
v___x_830_ = l_Std_Time_Duration_ofNanoseconds(v___x_829_);
lean_dec(v___x_829_);
v___x_831_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_tz_832_, lean_object* v_a_833_, lean_object* v___x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_tz_832_, v_a_833_, v___x_834_, v_x_835_);
lean_dec_ref(v_a_833_);
lean_dec_ref(v_tz_832_);
return v_res_836_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
uint8_t v___x_839_; 
v___x_839_ = 0;
return v___x_839_;
}
else
{
lean_object* v_key_840_; lean_object* v_tail_841_; uint8_t v___x_842_; 
v_key_840_ = lean_ctor_get(v_x_838_, 0);
v_tail_841_ = lean_ctor_get(v_x_838_, 2);
v___x_842_ = lean_string_dec_eq(v_key_840_, v_a_837_);
if (v___x_842_ == 0)
{
v_x_838_ = v_tail_841_;
goto _start;
}
else
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg___boxed(lean_object* v_a_844_, lean_object* v_x_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_844_, v_x_845_);
lean_dec(v_x_845_);
lean_dec_ref(v_a_844_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
return v_x_848_;
}
else
{
lean_object* v_key_850_; lean_object* v_value_851_; lean_object* v_tail_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_875_; 
v_key_850_ = lean_ctor_get(v_x_849_, 0);
v_value_851_ = lean_ctor_get(v_x_849_, 1);
v_tail_852_ = lean_ctor_get(v_x_849_, 2);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_875_ == 0)
{
v___x_854_ = v_x_849_;
v_isShared_855_ = v_isSharedCheck_875_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_tail_852_);
lean_inc(v_value_851_);
lean_inc(v_key_850_);
lean_dec(v_x_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_875_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v_fold_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_856_ = lean_array_get_size(v_x_848_);
v___x_857_ = lean_string_hash(v_key_850_);
v___x_858_ = 32ULL;
v___x_859_ = lean_uint64_shift_right(v___x_857_, v___x_858_);
v_fold_860_ = lean_uint64_xor(v___x_857_, v___x_859_);
v___x_861_ = 16ULL;
v___x_862_ = lean_uint64_shift_right(v_fold_860_, v___x_861_);
v___x_863_ = lean_uint64_xor(v_fold_860_, v___x_862_);
v___x_864_ = lean_uint64_to_usize(v___x_863_);
v___x_865_ = lean_usize_of_nat(v___x_856_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_sub(v___x_865_, v___x_866_);
v___x_868_ = lean_usize_land(v___x_864_, v___x_867_);
v___x_869_ = lean_array_uget_borrowed(v_x_848_, v___x_868_);
lean_inc(v___x_869_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 2, v___x_869_);
v___x_871_ = v___x_854_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_key_850_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_value_851_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v___x_869_);
v___x_871_ = v_reuseFailAlloc_874_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; 
v___x_872_ = lean_array_uset(v_x_848_, v___x_868_, v___x_871_);
v_x_848_ = v___x_872_;
v_x_849_ = v_tail_852_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(lean_object* v_i_876_, lean_object* v_source_877_, lean_object* v_target_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_source_877_);
v___x_880_ = lean_nat_dec_lt(v_i_876_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_source_877_);
lean_dec(v_i_876_);
return v_target_878_;
}
else
{
lean_object* v_es_881_; lean_object* v___x_882_; lean_object* v_source_883_; lean_object* v_target_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_es_881_ = lean_array_fget(v_source_877_, v_i_876_);
v___x_882_ = lean_box(0);
v_source_883_ = lean_array_fset(v_source_877_, v_i_876_, v___x_882_);
v_target_884_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(v_target_878_, v_es_881_);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_add(v_i_876_, v___x_885_);
lean_dec(v_i_876_);
v_i_876_ = v___x_886_;
v_source_877_ = v_source_883_;
v_target_878_ = v_target_884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(lean_object* v_data_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_nbuckets_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_889_ = lean_array_get_size(v_data_888_);
v___x_890_ = lean_unsigned_to_nat(2u);
v_nbuckets_891_ = lean_nat_mul(v___x_889_, v___x_890_);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_box(0);
v___x_894_ = lean_mk_array(v_nbuckets_891_, v___x_893_);
v___x_895_ = lean_array_propagate_mark(v_data_888_, v___x_894_);
v___x_896_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(v___x_892_, v_data_888_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(lean_object* v_i_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_mk_empty_array_with_capacity(v___x_899_);
v___x_901_ = lean_array_push(v___x_900_, v_i_897_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
else
{
lean_object* v_val_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_911_; 
v_val_903_ = lean_ctor_get(v_x_898_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_911_ == 0)
{
v___x_905_ = v_x_898_;
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_val_903_);
lean_dec(v_x_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_array_push(v_val_903_, v_i_897_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_907_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(lean_object* v_i_912_, lean_object* v_a_913_, lean_object* v_x_914_){
_start:
{
if (lean_obj_tag(v_x_914_) == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_val_917_; lean_object* v___x_918_; 
v___x_915_ = lean_box(0);
v___x_916_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(v_i_912_, v___x_915_);
v_val_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_val_917_);
lean_dec(v___x_916_);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v_a_913_);
lean_ctor_set(v___x_918_, 1, v_val_917_);
lean_ctor_set(v___x_918_, 2, v_x_914_);
return v___x_918_;
}
else
{
lean_object* v_key_919_; lean_object* v_value_920_; lean_object* v_tail_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_936_; 
v_key_919_ = lean_ctor_get(v_x_914_, 0);
v_value_920_ = lean_ctor_get(v_x_914_, 1);
v_tail_921_ = lean_ctor_get(v_x_914_, 2);
v_isSharedCheck_936_ = !lean_is_exclusive(v_x_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_923_ = v_x_914_;
v_isShared_924_ = v_isSharedCheck_936_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_tail_921_);
lean_inc(v_value_920_);
lean_inc(v_key_919_);
lean_dec(v_x_914_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_936_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
uint8_t v___x_925_; 
v___x_925_ = lean_string_dec_eq(v_key_919_, v_a_913_);
if (v___x_925_ == 0)
{
lean_object* v_tail_926_; lean_object* v___x_928_; 
v_tail_926_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(v_i_912_, v_a_913_, v_tail_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 2, v_tail_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_key_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_value_920_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_tail_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_val_932_; lean_object* v___x_934_; 
lean_dec(v_key_919_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v_value_920_);
v___x_931_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(v_i_912_, v___x_930_);
v_val_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_val_932_);
lean_dec(v___x_931_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v_val_932_);
lean_ctor_set(v___x_923_, 0, v_a_913_);
v___x_934_ = v___x_923_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_913_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_val_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_tail_921_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_i_937_, lean_object* v_m_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_size_940_; lean_object* v_buckets_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_991_; 
v_size_940_ = lean_ctor_get(v_m_938_, 0);
v_buckets_941_ = lean_ctor_get(v_m_938_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_m_938_);
if (v_isSharedCheck_991_ == 0)
{
v___x_943_ = v_m_938_;
v_isShared_944_ = v_isSharedCheck_991_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_buckets_941_);
lean_inc(v_size_940_);
lean_dec(v_m_938_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_991_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; uint64_t v___x_946_; uint64_t v___x_947_; uint64_t v___x_948_; uint64_t v_fold_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v_bkt_958_; uint8_t v___x_959_; 
v___x_945_ = lean_array_get_size(v_buckets_941_);
v___x_946_ = lean_string_hash(v_a_939_);
v___x_947_ = 32ULL;
v___x_948_ = lean_uint64_shift_right(v___x_946_, v___x_947_);
v_fold_949_ = lean_uint64_xor(v___x_946_, v___x_948_);
v___x_950_ = 16ULL;
v___x_951_ = lean_uint64_shift_right(v_fold_949_, v___x_950_);
v___x_952_ = lean_uint64_xor(v_fold_949_, v___x_951_);
v___x_953_ = lean_uint64_to_usize(v___x_952_);
v___x_954_ = lean_usize_of_nat(v___x_945_);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_sub(v___x_954_, v___x_955_);
v___x_957_ = lean_usize_land(v___x_953_, v___x_956_);
v_bkt_958_ = lean_array_uget_borrowed(v_buckets_941_, v___x_957_);
v___x_959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_939_, v_bkt_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_size_x27_963_; lean_object* v___x_964_; lean_object* v_buckets_x27_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_mk_empty_array_with_capacity(v___x_960_);
v___x_962_ = lean_array_push(v___x_961_, v_i_937_);
v_size_x27_963_ = lean_nat_add(v_size_940_, v___x_960_);
lean_dec(v_size_940_);
lean_inc(v_bkt_958_);
v___x_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_964_, 0, v_a_939_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
lean_ctor_set(v___x_964_, 2, v_bkt_958_);
v_buckets_x27_965_ = lean_array_uset(v_buckets_941_, v___x_957_, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_nat_mul(v_size_x27_963_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(3u);
v___x_969_ = lean_nat_div(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_array_get_size(v_buckets_x27_965_);
v___x_971_ = lean_nat_dec_le(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
if (v___x_971_ == 0)
{
lean_object* v_val_972_; lean_object* v___x_974_; 
v_val_972_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(v_buckets_x27_965_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_val_972_);
lean_ctor_set(v___x_943_, 0, v_size_x27_963_);
v___x_974_ = v___x_943_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_size_x27_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_val_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_977_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_buckets_x27_965_);
lean_ctor_set(v___x_943_, 0, v_size_x27_963_);
v___x_977_ = v___x_943_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_size_x27_963_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_buckets_x27_965_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v___x_979_; lean_object* v_buckets_x27_980_; lean_object* v_bkt_x27_981_; lean_object* v___y_983_; uint8_t v___x_988_; 
lean_inc(v_bkt_958_);
v___x_979_ = lean_box(0);
v_buckets_x27_980_ = lean_array_uset(v_buckets_941_, v___x_957_, v___x_979_);
lean_inc_ref(v_a_939_);
v_bkt_x27_981_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(v_i_937_, v_a_939_, v_bkt_958_);
v___x_988_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_939_, v_bkt_x27_981_);
lean_dec_ref(v_a_939_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_sub(v_size_940_, v___x_989_);
lean_dec(v_size_940_);
v___y_983_ = v___x_990_;
goto v___jp_982_;
}
else
{
v___y_983_ = v_size_940_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_array_uset(v_buckets_x27_980_, v___x_957_, v_bkt_x27_981_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_984_);
lean_ctor_set(v___x_943_, 0, v___y_983_);
v___x_986_ = v___x_943_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___y_983_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_nat_to_int(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2));
v___x_998_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_999_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_998_, v___x_997_, v___x_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_entries_1000_, lean_object* v_indexes_1001_, lean_object* v_status_1002_, uint8_t v_version_1003_, lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1004_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_status_1002_);
lean_dec_ref(v_indexes_1001_);
lean_dec_ref(v_entries_1000_);
v_a_1006_ = lean_ctor_get(v_x_1004_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v_x_1004_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v_x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1038_; 
v_a_1015_ = lean_ctor_get(v_x_1004_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_x_1004_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1017_ = v_x_1004_;
v_isShared_1018_ = v_isSharedCheck_1038_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v_x_1004_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1038_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_tz_1021_; lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_i_1028_; lean_object* v___x_1029_; lean_object* v_entries_1030_; lean_object* v_indexes_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3);
v_tz_1021_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_1020_, v_a_1015_);
lean_inc(v_a_1015_);
lean_inc_ref(v_tz_1021_);
v___f_1022_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1022_, 0, v_tz_1021_);
lean_closure_set(v___f_1022_, 1, v_a_1015_);
lean_closure_set(v___f_1022_, 2, v___x_1019_);
v___x_1023_ = lean_mk_thunk(v___f_1022_);
v___x_1024_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_a_1015_);
lean_ctor_set(v___x_1024_, 2, v___x_1020_);
lean_ctor_set(v___x_1024_, 3, v_tz_1021_);
v___x_1025_ = l_Std_Http_Header_Name_date;
v___x_1026_ = l_Std_Time_DateTime_toHTTPDateString(v___x_1024_);
v___x_1027_ = l_Std_Http_Header_Value_ofString_x21(v___x_1026_);
v_i_1028_ = lean_array_get_size(v_entries_1000_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1025_);
lean_ctor_set(v___x_1029_, 1, v___x_1027_);
v_entries_1030_ = lean_array_push(v_entries_1000_, v___x_1029_);
v_indexes_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_i_1028_, v_indexes_1001_, v___x_1025_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_entries_1030_);
lean_ctor_set(v___x_1032_, 1, v_indexes_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1033_, 0, v_status_1002_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*2, v_version_1003_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1033_);
v___x_1035_ = v___x_1017_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_entries_1039_, lean_object* v_indexes_1040_, lean_object* v_status_1041_, lean_object* v_version_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v_version_boxed_1045_; lean_object* v_res_1046_; 
v_version_boxed_1045_ = lean_unbox(v_version_1042_);
v_res_1046_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_entries_1039_, v_indexes_1040_, v_status_1041_, v_version_boxed_1045_, v_x_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(lean_object* v_m_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_buckets_1049_; lean_object* v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v_fold_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_buckets_1049_ = lean_ctor_get(v_m_1047_, 1);
v___x_1050_ = lean_array_get_size(v_buckets_1049_);
v___x_1051_ = lean_string_hash(v_a_1048_);
v___x_1052_ = 32ULL;
v___x_1053_ = lean_uint64_shift_right(v___x_1051_, v___x_1052_);
v_fold_1054_ = lean_uint64_xor(v___x_1051_, v___x_1053_);
v___x_1055_ = 16ULL;
v___x_1056_ = lean_uint64_shift_right(v_fold_1054_, v___x_1055_);
v___x_1057_ = lean_uint64_xor(v_fold_1054_, v___x_1056_);
v___x_1058_ = lean_uint64_to_usize(v___x_1057_);
v___x_1059_ = lean_usize_of_nat(v___x_1050_);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_sub(v___x_1059_, v___x_1060_);
v___x_1062_ = lean_usize_land(v___x_1058_, v___x_1061_);
v___x_1063_ = lean_array_uget_borrowed(v_buckets_1049_, v___x_1062_);
v___x_1064_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_1048_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg___boxed(lean_object* v_m_1065_, lean_object* v_a_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_m_1065_, v_a_1066_);
lean_dec_ref(v_a_1066_);
lean_dec_ref(v_m_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1069_, lean_object* v_head_1070_){
_start:
{
uint8_t v_generateDate_1075_; 
v_generateDate_1075_ = lean_ctor_get_uint8(v_config_1069_, sizeof(void*)*24 + 1);
if (v_generateDate_1075_ == 0)
{
goto v___jp_1072_;
}
else
{
lean_object* v_headers_1076_; lean_object* v_status_1077_; uint8_t v_version_1078_; lean_object* v_entries_1079_; lean_object* v_indexes_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_headers_1076_ = lean_ctor_get(v_head_1070_, 1);
v_status_1077_ = lean_ctor_get(v_head_1070_, 0);
v_version_1078_ = lean_ctor_get_uint8(v_head_1070_, sizeof(void*)*2);
v_entries_1079_ = lean_ctor_get(v_headers_1076_, 0);
v_indexes_1080_ = lean_ctor_get(v_headers_1076_, 1);
v___x_1081_ = l_Std_Http_Header_Name_date;
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_indexes_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v_val_1087_; lean_object* v___x_1090_; 
lean_inc_ref(v_indexes_1080_);
lean_inc_ref(v_entries_1079_);
lean_inc(v_status_1077_);
lean_dec_ref(v_head_1070_);
v___x_1083_ = lean_box(v_version_1078_);
v___f_1084_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1084_, 0, v_entries_1079_);
lean_closure_set(v___f_1084_, 1, v_indexes_1080_);
lean_closure_set(v___f_1084_, 2, v_status_1077_);
lean_closure_set(v___f_1084_, 3, v___x_1083_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_get_current_time();
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 1);
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v_val_1087_ = v___x_1096_;
goto v___jp_1086_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1090_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1090_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v_val_1087_ = v___x_1104_;
goto v___jp_1086_;
}
}
}
v___jp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_val_1087_);
v___x_1089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1085_, v___x_1082_, v___x_1088_, v___f_1084_);
return v___x_1089_;
}
}
else
{
goto v___jp_1072_;
}
}
v___jp_1072_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_head_1070_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1107_, lean_object* v_head_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1107_, v_head_1108_);
lean_dec_ref(v_config_1107_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_nat_to_int(v_a_1111_);
v___x_1113_ = l_Rat_ofInt(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4(lean_object* v_00_u03b2_1114_, lean_object* v_m_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_m_1115_, v_a_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___boxed(lean_object* v_00_u03b2_1118_, lean_object* v_m_1119_, lean_object* v_a_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4(v_00_u03b2_1118_, v_m_1119_, v_a_1120_);
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_m_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3(lean_object* v_00_u03b2_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_1124_, v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1127_, lean_object* v_a_1128_, lean_object* v_x_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3(v_00_u03b2_1127_, v_a_1128_, v_x_1129_);
lean_dec(v_x_1129_);
lean_dec_ref(v_a_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4(lean_object* v_00_u03b2_1132_, lean_object* v_data_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(v_data_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1135_, lean_object* v_i_1136_, lean_object* v_source_1137_, lean_object* v_target_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(v_i_1136_, v_source_1137_, v_target_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(v_x_1141_, v_x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1144_, lean_object* v_____r_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___y_1144_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1151_, lean_object* v_____r_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1151_, v_____r_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1155_, lean_object* v_x_1156_){
_start:
{
if (lean_obj_tag(v_x_1156_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v___f_1155_);
v_a_1158_ = lean_ctor_get(v_x_1156_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1160_ = v_x_1156_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v_x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1168_; 
v_a_1167_ = lean_ctor_get(v_x_1156_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v_x_1156_, 1);
v___x_1168_ = lean_apply_2(v___f_1155_, v_a_1167_, lean_box(0));
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1169_, v_x_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1173_, lean_object* v_body_1174_, lean_object* v___f_1175_, lean_object* v___f_1176_, lean_object* v_x_1177_){
_start:
{
if (lean_obj_tag(v_x_1177_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v___f_1176_);
lean_dec_ref(v___f_1175_);
lean_dec(v_body_1174_);
lean_dec_ref(v_close_1173_);
v_a_1179_ = lean_ctor_get(v_x_1177_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_x_1177_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1181_ = v_x_1177_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v_x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1188_; uint8_t v___x_1189_; 
v_a_1188_ = lean_ctor_get(v_x_1177_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v_x_1177_, 1);
v___x_1189_ = lean_unbox(v_a_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v___f_1176_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_apply_2(v_close_1173_, v_body_1174_, lean_box(0));
v___x_1192_ = lean_unbox(v_a_1188_);
lean_dec(v_a_1188_);
v___x_1193_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1190_, v___x_1192_, v___x_1191_, v___f_1175_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_a_1188_);
lean_dec_ref(v___f_1175_);
lean_dec(v_body_1174_);
lean_dec_ref(v_close_1173_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_apply_2(v___f_1176_, v___x_1194_, lean_box(0));
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1196_, lean_object* v_body_1197_, lean_object* v___f_1198_, lean_object* v___f_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1196_, v_body_1197_, v___f_1198_, v___f_1199_, v_x_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1203_, uint8_t v___x_1204_, lean_object* v___f_1205_, lean_object* v___f_1206_, lean_object* v_x1_1207_, lean_object* v_x2_1208_){
_start:
{
lean_object* v_fst_1209_; uint8_t v___x_1210_; 
v_fst_1209_ = lean_ctor_get(v_x2_1208_, 0);
lean_inc(v_fst_1209_);
v___x_1210_ = lean_string_dec_eq(v___x_1203_, v_fst_1209_);
if (v___x_1210_ == 0)
{
if (v___x_1204_ == 0)
{
lean_dec(v_fst_1209_);
lean_dec_ref(v_x2_1208_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v___f_1205_);
return v_x1_1207_;
}
else
{
lean_object* v_entries_1211_; lean_object* v_indexes_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1223_; 
v_entries_1211_ = lean_ctor_get(v_x1_1207_, 0);
v_indexes_1212_ = lean_ctor_get(v_x1_1207_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x1_1207_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1214_ = v_x1_1207_;
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_indexes_1212_);
lean_inc(v_entries_1211_);
lean_dec(v_x1_1207_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_i_1216_; lean_object* v_f_1217_; lean_object* v_entries_1218_; lean_object* v_indexes_1219_; lean_object* v___x_1221_; 
v_i_1216_ = lean_array_get_size(v_entries_1211_);
v_f_1217_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0), 2, 1);
lean_closure_set(v_f_1217_, 0, v_i_1216_);
v_entries_1218_ = lean_array_push(v_entries_1211_, v_x2_1208_);
v_indexes_1219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1205_, v___f_1206_, v_indexes_1212_, v_fst_1209_, v_f_1217_);
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
else
{
lean_dec(v_fst_1209_);
lean_dec_ref(v_x2_1208_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v___f_1205_);
return v_x1_1207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v___f_1226_, lean_object* v___f_1227_, lean_object* v_x1_1228_, lean_object* v_x2_1229_){
_start:
{
uint8_t v___x_2240__boxed_1230_; lean_object* v_res_1231_; 
v___x_2240__boxed_1230_ = lean_unbox(v___x_1225_);
v_res_1231_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1224_, v___x_2240__boxed_1230_, v___f_1226_, v___f_1227_, v_x1_1228_, v_x2_1229_);
lean_dec_ref(v___x_1224_);
return v_res_1231_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1254_, lean_object* v_body_1255_, lean_object* v_close_1256_, lean_object* v_isClosed_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___y_1261_; uint8_t v_omitBody_1262_; lean_object* v___y_1275_; lean_object* v___y_1310_; uint8_t v___y_1314_; uint8_t v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; 
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_isClosed_1257_);
lean_dec_ref(v_close_1256_);
lean_dec(v_body_1255_);
lean_dec_ref(v___y_1254_);
v_a_1318_ = lean_ctor_get(v_x_1258_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1320_ = v_x_1258_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v_x_1258_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
}
else
{
lean_object* v_writer_1327_; lean_object* v_a_1328_; lean_object* v_reader_1329_; lean_object* v_config_1330_; lean_object* v_events_1331_; lean_object* v_error_1332_; lean_object* v_instant_1333_; uint8_t v_keepAlive_1334_; uint8_t v_forcedFlush_1335_; uint8_t v_pullBodyStalled_1336_; lean_object* v_userData_1337_; lean_object* v_outputData_1338_; lean_object* v_state_1339_; lean_object* v_knownSize_1340_; lean_object* v_messageHead_1341_; uint8_t v_sentMessage_1342_; uint8_t v_userClosedBody_1343_; uint8_t v_omitBody_1344_; lean_object* v_userDataBytes_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1448_; 
v_writer_1327_ = lean_ctor_get(v___y_1254_, 1);
lean_inc_ref(v_writer_1327_);
v_a_1328_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v_x_1258_, 1);
v_reader_1329_ = lean_ctor_get(v___y_1254_, 0);
v_config_1330_ = lean_ctor_get(v___y_1254_, 2);
v_events_1331_ = lean_ctor_get(v___y_1254_, 3);
v_error_1332_ = lean_ctor_get(v___y_1254_, 4);
v_instant_1333_ = lean_ctor_get(v___y_1254_, 5);
v_keepAlive_1334_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*6);
v_forcedFlush_1335_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1336_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*6 + 2);
v_userData_1337_ = lean_ctor_get(v_writer_1327_, 0);
v_outputData_1338_ = lean_ctor_get(v_writer_1327_, 1);
v_state_1339_ = lean_ctor_get(v_writer_1327_, 2);
v_knownSize_1340_ = lean_ctor_get(v_writer_1327_, 3);
v_messageHead_1341_ = lean_ctor_get(v_writer_1327_, 4);
v_sentMessage_1342_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6);
v_userClosedBody_1343_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6 + 1);
v_omitBody_1344_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6 + 2);
v_userDataBytes_1345_ = lean_ctor_get(v_writer_1327_, 5);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_writer_1327_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1347_ = v_writer_1327_;
v_isShared_1348_ = v_isSharedCheck_1448_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_userDataBytes_1345_);
lean_inc(v_messageHead_1341_);
lean_inc(v_knownSize_1340_);
lean_inc(v_state_1339_);
lean_inc(v_outputData_1338_);
lean_inc(v_userData_1337_);
lean_dec(v_writer_1327_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1448_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; uint8_t v___y_1373_; uint8_t v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; uint8_t v___x_1398_; uint8_t v___y_1400_; uint8_t v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1403_; uint8_t v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1427_; uint8_t v___y_1428_; uint8_t v___y_1431_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1398_ = 0;
v___x_1446_ = lean_box(1);
v___x_1447_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1339_, v___x_1446_);
if (v___x_1447_ == 0)
{
v___y_1431_ = v___x_1447_;
goto v___jp_1430_;
}
else
{
if (v_sentMessage_1342_ == 0)
{
v___y_1431_ = v___x_1447_;
goto v___jp_1430_;
}
else
{
lean_del_object(v___x_1347_);
lean_dec(v_userDataBytes_1345_);
lean_dec(v_messageHead_1341_);
lean_dec(v_knownSize_1340_);
lean_dec(v_state_1339_);
lean_dec_ref(v_outputData_1338_);
lean_dec_ref(v_userData_1337_);
lean_dec(v_a_1328_);
v___y_1261_ = v___y_1254_;
v_omitBody_1262_ = v_omitBody_1344_;
goto v___jp_1260_;
}
}
v___jp_1349_:
{
lean_object* v_message_1352_; lean_object* v___x_2029__overap_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v_message_1352_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1350_, v_a_1328_, v___y_1351_);
v___x_2029__overap_1353_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1350_);
v___x_1354_ = lean_apply_2(v___x_2029__overap_1353_, v_outputData_1338_, v_message_1352_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1354_);
v___x_1356_ = v___x_1347_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_userData_1337_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_state_1339_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_knownSize_1340_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_messageHead_1341_);
lean_ctor_set(v_reuseFailAlloc_1358_, 5, v_userDataBytes_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*6, v_sentMessage_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*6 + 1, v_userClosedBody_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*6 + 2, v_omitBody_1344_);
v___x_1356_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1357_, 0, v_reader_1329_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
lean_ctor_set(v___x_1357_, 2, v_config_1330_);
lean_ctor_set(v___x_1357_, 3, v_events_1331_);
lean_ctor_set(v___x_1357_, 4, v_error_1332_);
lean_ctor_set(v___x_1357_, 5, v_instant_1333_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*6, v_keepAlive_1334_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*6 + 1, v_forcedFlush_1335_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*6 + 2, v_pullBodyStalled_1336_);
v___y_1261_ = v___x_1357_;
v_omitBody_1262_ = v_omitBody_1344_;
goto v___jp_1260_;
}
}
v___jp_1359_:
{
lean_object* v_entries_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_entries_1363_ = lean_ctor_get(v___y_1360_, 0);
lean_inc_ref(v_entries_1363_);
lean_dec_ref(v___y_1360_);
v___x_1364_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_array_get_size(v_entries_1363_);
v___x_1367_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_1368_ = lean_nat_dec_lt(v___x_1365_, v___x_1366_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v_entries_1363_);
lean_dec_ref(v___y_1361_);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___x_1364_;
goto v___jp_1349_;
}
else
{
size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1366_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1367_, v___y_1361_, v_entries_1363_, v___x_1369_, v___x_1370_, v___x_1364_);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___x_1371_;
goto v___jp_1349_;
}
}
v___jp_1372_:
{
lean_object* v___x_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; uint8_t v___x_1382_; 
v___x_1377_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1378_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1379_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1380_ = lean_box(v___y_1373_);
v___f_1381_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1381_, 0, v___x_1377_);
lean_closure_set(v___f_1381_, 1, v___x_1380_);
lean_closure_set(v___f_1381_, 2, v___f_1378_);
lean_closure_set(v___f_1381_, 3, v___f_1379_);
v___x_1382_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1378_, v___f_1379_, v___x_1377_, v___y_1376_);
if (v___x_1382_ == 0)
{
if (v___y_1374_ == 0)
{
v___y_1360_ = v___y_1376_;
v___y_1361_ = v___f_1381_;
v___y_1362_ = v___y_1375_;
goto v___jp_1359_;
}
else
{
lean_dec_ref(v___f_1381_);
v___y_1350_ = v___y_1375_;
v___y_1351_ = v___y_1376_;
goto v___jp_1349_;
}
}
else
{
v___y_1360_ = v___y_1376_;
v___y_1361_ = v___f_1381_;
v___y_1362_ = v___y_1375_;
goto v___jp_1359_;
}
}
v___jp_1383_:
{
lean_object* v_entries_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_entries_1389_ = lean_ctor_get(v___y_1385_, 0);
lean_inc_ref(v_entries_1389_);
lean_dec_ref(v___y_1385_);
v___x_1390_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_array_get_size(v_entries_1389_);
v___x_1393_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_1394_ = lean_nat_dec_lt(v___x_1391_, v___x_1392_);
if (v___x_1394_ == 0)
{
lean_dec_ref(v_entries_1389_);
lean_dec_ref(v___y_1387_);
v___y_1373_ = v___y_1384_;
v___y_1374_ = v___y_1386_;
v___y_1375_ = v___y_1388_;
v___y_1376_ = v___x_1390_;
goto v___jp_1372_;
}
else
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = lean_usize_of_nat(v___x_1392_);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1393_, v___y_1387_, v_entries_1389_, v___x_1395_, v___x_1396_, v___x_1390_);
v___y_1373_ = v___y_1384_;
v___y_1374_ = v___y_1386_;
v___y_1375_ = v___y_1388_;
v___y_1376_ = v___x_1397_;
goto v___jp_1372_;
}
}
v___jp_1399_:
{
lean_object* v_headerSize_1406_; lean_object* v_machine_1407_; lean_object* v_machine_1408_; lean_object* v_reader_1409_; lean_object* v_state_1410_; 
v_headerSize_1406_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1404_, v_a_1328_, v___y_1401_);
v_machine_1407_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1398_, v___y_1403_, v_headerSize_1406_, v___y_1405_);
v_machine_1408_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1398_, v_machine_1407_, v_a_1328_);
lean_dec(v_a_1328_);
v_reader_1409_ = lean_ctor_get(v_machine_1408_, 0);
v_state_1410_ = lean_ctor_get(v_reader_1409_, 0);
if (lean_obj_tag(v_state_1410_) == 7)
{
v___y_1314_ = v___y_1401_;
v___y_1315_ = v___y_1400_;
v___y_1316_ = v_machine_1408_;
v___y_1317_ = v___y_1402_;
goto v___jp_1313_;
}
else
{
v___y_1314_ = v___y_1401_;
v___y_1315_ = v___y_1400_;
v___y_1316_ = v_machine_1408_;
v___y_1317_ = v___y_1401_;
goto v___jp_1313_;
}
}
v___jp_1411_:
{
uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v_indexes_1417_; lean_object* v___x_1418_; lean_object* v_machine_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; uint8_t v___x_1423_; 
v___x_1415_ = 1;
v___x_1416_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1415_, v_a_1328_);
v_indexes_1417_ = lean_ctor_get(v___x_1416_, 1);
lean_inc_ref(v_indexes_1417_);
lean_dec_ref(v___x_1416_);
lean_inc(v_a_1328_);
v___x_1418_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1418_, 0, v_userData_1337_);
lean_ctor_set(v___x_1418_, 1, v_outputData_1338_);
lean_ctor_set(v___x_1418_, 2, v_state_1339_);
lean_ctor_set(v___x_1418_, 3, v_knownSize_1340_);
lean_ctor_set(v___x_1418_, 4, v_a_1328_);
lean_ctor_set(v___x_1418_, 5, v_userDataBytes_1345_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*6, v___y_1413_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*6 + 1, v_userClosedBody_1343_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*6 + 2, v_omitBody_1344_);
v_machine_1419_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1419_, 0, v_reader_1329_);
lean_ctor_set(v_machine_1419_, 1, v___x_1418_);
lean_ctor_set(v_machine_1419_, 2, v_config_1330_);
lean_ctor_set(v_machine_1419_, 3, v_events_1331_);
lean_ctor_set(v_machine_1419_, 4, v_error_1332_);
lean_ctor_set(v_machine_1419_, 5, v_instant_1333_);
lean_ctor_set_uint8(v_machine_1419_, sizeof(void*)*6, v_keepAlive_1334_);
lean_ctor_set_uint8(v_machine_1419_, sizeof(void*)*6 + 1, v_forcedFlush_1335_);
lean_ctor_set_uint8(v_machine_1419_, sizeof(void*)*6 + 2, v_pullBodyStalled_1336_);
v___x_1420_ = l_Std_Http_Header_Name_contentLength;
v___f_1421_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1422_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1423_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1421_, v___f_1422_, v_indexes_1417_, v___x_1420_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1421_, v___f_1422_, v_indexes_1417_, v___x_1424_);
lean_dec_ref(v_indexes_1417_);
v___y_1400_ = v___y_1414_;
v___y_1401_ = v___y_1412_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v_machine_1419_;
v___y_1404_ = v___x_1415_;
v___y_1405_ = v___x_1425_;
goto v___jp_1399_;
}
else
{
lean_dec_ref(v_indexes_1417_);
v___y_1400_ = v___y_1414_;
v___y_1401_ = v___y_1412_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v_machine_1419_;
v___y_1404_ = v___x_1415_;
v___y_1405_ = v___x_1423_;
goto v___jp_1399_;
}
}
v___jp_1426_:
{
lean_object* v_state_1429_; 
v_state_1429_ = lean_ctor_get(v_reader_1329_, 0);
if (lean_obj_tag(v_state_1429_) == 7)
{
v___y_1412_ = v___y_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___y_1427_;
goto v___jp_1411_;
}
else
{
v___y_1412_ = v___y_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___y_1428_;
goto v___jp_1411_;
}
}
v___jp_1430_:
{
if (v___y_1431_ == 0)
{
lean_del_object(v___x_1347_);
lean_dec(v_userDataBytes_1345_);
lean_dec(v_messageHead_1341_);
lean_dec(v_knownSize_1340_);
lean_dec(v_state_1339_);
lean_dec_ref(v_outputData_1338_);
lean_dec_ref(v_userData_1337_);
lean_dec(v_a_1328_);
v___y_1261_ = v___y_1254_;
v_omitBody_1262_ = v_omitBody_1344_;
goto v___jp_1260_;
}
else
{
lean_object* v_status_1432_; uint16_t v___x_1433_; uint16_t v___x_1434_; uint8_t v___x_1435_; 
lean_inc(v_instant_1333_);
lean_inc(v_error_1332_);
lean_inc_ref(v_events_1331_);
lean_inc_ref(v_config_1330_);
lean_inc_ref(v_reader_1329_);
lean_dec_ref(v___y_1254_);
v_status_1432_ = lean_ctor_get(v_a_1328_, 0);
v___x_1433_ = 100;
v___x_1434_ = l_Std_Http_Status_toCode(v_status_1432_);
v___x_1435_ = lean_uint16_dec_le(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_del_object(v___x_1347_);
lean_dec(v_messageHead_1341_);
v___y_1427_ = v___y_1431_;
v___y_1428_ = v___x_1435_;
goto v___jp_1426_;
}
else
{
uint16_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = 200;
v___x_1437_ = lean_uint16_dec_lt(v___x_1434_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_del_object(v___x_1347_);
lean_dec(v_messageHead_1341_);
v___y_1427_ = v___y_1431_;
v___y_1428_ = v___x_1437_;
goto v___jp_1426_;
}
else
{
uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___f_1444_; uint8_t v___x_1445_; 
v___x_1438_ = 1;
v___x_1439_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1438_, v_a_1328_);
v___x_1440_ = l_Std_Http_Header_Name_contentLength;
v___f_1441_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1442_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1443_ = lean_box(v___x_1437_);
v___f_1444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1444_, 0, v___x_1440_);
lean_closure_set(v___f_1444_, 1, v___x_1443_);
lean_closure_set(v___f_1444_, 2, v___f_1441_);
lean_closure_set(v___f_1444_, 3, v___f_1442_);
v___x_1445_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1441_, v___f_1442_, v___x_1440_, v___x_1439_);
if (v___x_1445_ == 0)
{
if (v___x_1437_ == 0)
{
v___y_1384_ = v___x_1437_;
v___y_1385_ = v___x_1439_;
v___y_1386_ = v___x_1437_;
v___y_1387_ = v___f_1444_;
v___y_1388_ = v___x_1438_;
goto v___jp_1383_;
}
else
{
lean_dec_ref(v___f_1444_);
v___y_1373_ = v___x_1437_;
v___y_1374_ = v___x_1437_;
v___y_1375_ = v___x_1438_;
v___y_1376_ = v___x_1439_;
goto v___jp_1372_;
}
}
else
{
v___y_1384_ = v___x_1437_;
v___y_1385_ = v___x_1439_;
v___y_1386_ = v___x_1437_;
v___y_1387_ = v___f_1444_;
v___y_1388_ = v___x_1438_;
goto v___jp_1383_;
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
lean_dec_ref(v_isClosed_1257_);
lean_dec_ref(v_close_1256_);
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
lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___f_1267_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1267_, 0, v___y_1261_);
lean_inc_ref(v___f_1267_);
v___f_1268_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1268_, 0, v___f_1267_);
lean_inc(v_body_1255_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1269_, 0, v_close_1256_);
lean_closure_set(v___f_1269_, 1, v_body_1255_);
lean_closure_set(v___f_1269_, 2, v___f_1268_);
lean_closure_set(v___f_1269_, 3, v___f_1267_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = 0;
v___x_1272_ = lean_apply_2(v_isClosed_1257_, v_body_1255_, lean_box(0));
v___x_1273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1270_, v___x_1271_, v___x_1272_, v___f_1269_);
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
lean_object* v_writer_1311_; uint8_t v_omitBody_1312_; 
v_writer_1311_ = lean_ctor_get(v___y_1310_, 1);
v_omitBody_1312_ = lean_ctor_get_uint8(v_writer_1311_, sizeof(void*)*6 + 2);
v___y_1261_ = v___y_1310_;
v_omitBody_1262_ = v_omitBody_1312_;
goto v___jp_1260_;
}
v___jp_1313_:
{
if (v___y_1317_ == 0)
{
v___y_1275_ = v___y_1316_;
goto v___jp_1274_;
}
else
{
if (v___y_1315_ == 0)
{
v___y_1310_ = v___y_1316_;
goto v___jp_1309_;
}
else
{
if (v___y_1314_ == 0)
{
v___y_1275_ = v___y_1316_;
goto v___jp_1274_;
}
else
{
v___y_1310_ = v___y_1316_;
goto v___jp_1309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1449_, lean_object* v_body_1450_, lean_object* v_close_1451_, lean_object* v_isClosed_1452_, lean_object* v_x_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1449_, v_body_1450_, v_close_1451_, v_isClosed_1452_, v_x_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_body_1456_, lean_object* v_close_1457_, lean_object* v_isClosed_1458_, lean_object* v_config_1459_, lean_object* v_line_1460_, lean_object* v_machine_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___y_1465_; 
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v_machine_1461_);
lean_dec_ref(v_line_1460_);
lean_dec_ref(v_isClosed_1458_);
lean_dec_ref(v_close_1457_);
lean_dec(v_body_1456_);
v_a_1471_ = lean_ctor_get(v_x_1462_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1473_ = v_x_1462_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v_x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1480_; 
v_a_1480_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v_x_1462_, 1);
if (lean_obj_tag(v_a_1480_) == 1)
{
lean_object* v_writer_1481_; lean_object* v_reader_1482_; lean_object* v_config_1483_; lean_object* v_events_1484_; lean_object* v_error_1485_; lean_object* v_instant_1486_; uint8_t v_keepAlive_1487_; uint8_t v_forcedFlush_1488_; uint8_t v_pullBodyStalled_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1512_; 
v_writer_1481_ = lean_ctor_get(v_machine_1461_, 1);
v_reader_1482_ = lean_ctor_get(v_machine_1461_, 0);
v_config_1483_ = lean_ctor_get(v_machine_1461_, 2);
v_events_1484_ = lean_ctor_get(v_machine_1461_, 3);
v_error_1485_ = lean_ctor_get(v_machine_1461_, 4);
v_instant_1486_ = lean_ctor_get(v_machine_1461_, 5);
v_keepAlive_1487_ = lean_ctor_get_uint8(v_machine_1461_, sizeof(void*)*6);
v_forcedFlush_1488_ = lean_ctor_get_uint8(v_machine_1461_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1489_ = lean_ctor_get_uint8(v_machine_1461_, sizeof(void*)*6 + 2);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_machine_1461_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1491_ = v_machine_1461_;
v_isShared_1492_ = v_isSharedCheck_1512_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_instant_1486_);
lean_inc(v_error_1485_);
lean_inc(v_events_1484_);
lean_inc(v_config_1483_);
lean_inc(v_writer_1481_);
lean_inc(v_reader_1482_);
lean_dec(v_machine_1461_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1512_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_userData_1493_; lean_object* v_outputData_1494_; lean_object* v_state_1495_; lean_object* v_messageHead_1496_; uint8_t v_sentMessage_1497_; uint8_t v_userClosedBody_1498_; uint8_t v_omitBody_1499_; lean_object* v_userDataBytes_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1510_; 
v_userData_1493_ = lean_ctor_get(v_writer_1481_, 0);
v_outputData_1494_ = lean_ctor_get(v_writer_1481_, 1);
v_state_1495_ = lean_ctor_get(v_writer_1481_, 2);
v_messageHead_1496_ = lean_ctor_get(v_writer_1481_, 4);
v_sentMessage_1497_ = lean_ctor_get_uint8(v_writer_1481_, sizeof(void*)*6);
v_userClosedBody_1498_ = lean_ctor_get_uint8(v_writer_1481_, sizeof(void*)*6 + 1);
v_omitBody_1499_ = lean_ctor_get_uint8(v_writer_1481_, sizeof(void*)*6 + 2);
v_userDataBytes_1500_ = lean_ctor_get(v_writer_1481_, 5);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_writer_1481_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_writer_1481_, 3);
lean_dec(v_unused_1511_);
v___x_1502_ = v_writer_1481_;
v_isShared_1503_ = v_isSharedCheck_1510_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_userDataBytes_1500_);
lean_inc(v_messageHead_1496_);
lean_inc(v_state_1495_);
lean_inc(v_outputData_1494_);
lean_inc(v_userData_1493_);
lean_dec(v_writer_1481_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1510_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 3, v_a_1480_);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_userData_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_outputData_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_state_1495_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_a_1480_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_messageHead_1496_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_userDataBytes_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*6, v_sentMessage_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*6 + 1, v_userClosedBody_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*6 + 2, v_omitBody_1499_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1505_);
v___x_1507_ = v___x_1491_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_reader_1482_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_config_1483_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_events_1484_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_error_1485_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_instant_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*6, v_keepAlive_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*6 + 1, v_forcedFlush_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*6 + 2, v_pullBodyStalled_1489_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v___y_1465_ = v___x_1507_;
goto v___jp_1464_;
}
}
}
}
}
else
{
lean_dec(v_a_1480_);
v___y_1465_ = v_machine_1461_;
goto v___jp_1464_;
}
}
v___jp_1464_:
{
lean_object* v___f_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___f_1466_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1466_, 0, v___y_1465_);
lean_closure_set(v___f_1466_, 1, v_body_1456_);
lean_closure_set(v___f_1466_, 2, v_close_1457_);
lean_closure_set(v___f_1466_, 3, v_isClosed_1458_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = 0;
v___x_1469_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1459_, v_line_1460_);
v___x_1470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1467_, v___x_1468_, v___x_1469_, v___f_1466_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_body_1513_, lean_object* v_close_1514_, lean_object* v_isClosed_1515_, lean_object* v_config_1516_, lean_object* v_line_1517_, lean_object* v_machine_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_body_1513_, v_close_1514_, v_isClosed_1515_, v_config_1516_, v_line_1517_, v_machine_1518_, v_x_1519_);
lean_dec_ref(v_config_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1522_, lean_object* v_config_1523_, lean_object* v_machine_1524_, lean_object* v_res_1525_){
_start:
{
lean_object* v_close_1527_; lean_object* v_isClosed_1528_; lean_object* v_getKnownSize_1529_; lean_object* v_line_1530_; lean_object* v_body_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_close_1527_ = lean_ctor_get(v_inst_1522_, 1);
lean_inc_ref(v_close_1527_);
v_isClosed_1528_ = lean_ctor_get(v_inst_1522_, 2);
lean_inc_ref(v_isClosed_1528_);
v_getKnownSize_1529_ = lean_ctor_get(v_inst_1522_, 5);
lean_inc_ref(v_getKnownSize_1529_);
lean_dec_ref(v_inst_1522_);
v_line_1530_ = lean_ctor_get(v_res_1525_, 0);
lean_inc_ref(v_line_1530_);
v_body_1531_ = lean_ctor_get(v_res_1525_, 1);
lean_inc_n(v_body_1531_, 2);
lean_dec_ref(v_res_1525_);
v___f_1532_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1532_, 0, v_body_1531_);
lean_closure_set(v___f_1532_, 1, v_close_1527_);
lean_closure_set(v___f_1532_, 2, v_isClosed_1528_);
lean_closure_set(v___f_1532_, 3, v_config_1523_);
lean_closure_set(v___f_1532_, 4, v_line_1530_);
lean_closure_set(v___f_1532_, 5, v_machine_1524_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = 0;
v___x_1535_ = lean_apply_2(v_getKnownSize_1529_, v_body_1531_, lean_box(0));
v___x_1536_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1533_, v___x_1534_, v___x_1535_, v___f_1532_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1537_, lean_object* v_config_1538_, lean_object* v_machine_1539_, lean_object* v_res_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1537_, v_config_1538_, v_machine_1539_, v_res_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1543_, lean_object* v_inst_1544_, lean_object* v_config_1545_, lean_object* v_machine_1546_, lean_object* v_res_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1544_, v_config_1545_, v_machine_1546_, v_res_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1550_, lean_object* v_inst_1551_, lean_object* v_config_1552_, lean_object* v_machine_1553_, lean_object* v_res_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1550_, v_inst_1551_, v_config_1552_, v_machine_1553_, v_res_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v_closed_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_closed_1560_ = lean_ctor_get_uint8(v_____do__lift_1557_, sizeof(void*)*6);
v___x_1561_ = lean_box(v_closed_1560_);
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v_____do__lift_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1568_, lean_object* v_x_1569_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v___x_1568_);
v_a_1571_ = lean_ctor_get(v_x_1569_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1573_ = v_x_1569_;
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v_x_1569_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
}
}
else
{
lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1588_; 
v_isSharedCheck_1588_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v_x_1569_, 0);
lean_dec(v_unused_1589_);
v___x_1581_ = v_x_1569_;
v_isShared_1582_ = v_isSharedCheck_1588_;
goto v_resetjp_1580_;
}
else
{
lean_dec(v_x_1569_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1588_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1568_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1590_, lean_object* v_x_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1590_, v_x_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v_pendingProducer_1602_; lean_object* v_pendingConsumer_1603_; lean_object* v_interestWaiter_1604_; uint8_t v_closed_1605_; lean_object* v_pendingIncompleteChunk_1606_; lean_object* v_closeError_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1616_; 
v___x_1601_ = lean_st_ref_take(v___y_1599_);
v_pendingProducer_1602_ = lean_ctor_get(v___x_1601_, 0);
v_pendingConsumer_1603_ = lean_ctor_get(v___x_1601_, 1);
v_interestWaiter_1604_ = lean_ctor_get(v___x_1601_, 2);
v_closed_1605_ = lean_ctor_get_uint8(v___x_1601_, sizeof(void*)*6);
v_pendingIncompleteChunk_1606_ = lean_ctor_get(v___x_1601_, 4);
v_closeError_1607_ = lean_ctor_get(v___x_1601_, 5);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v___x_1601_, 3);
lean_dec(v_unused_1617_);
v___x_1609_ = v___x_1601_;
v_isShared_1610_ = v_isSharedCheck_1616_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_closeError_1607_);
lean_inc(v_pendingIncompleteChunk_1606_);
lean_inc(v_interestWaiter_1604_);
lean_inc(v_pendingConsumer_1603_);
lean_inc(v_pendingProducer_1602_);
lean_dec(v___x_1601_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1616_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v___x_1598_);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_pendingProducer_1602_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_pendingConsumer_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_interestWaiter_1604_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_pendingIncompleteChunk_1606_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v_closeError_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*6, v_closed_1605_);
v___x_1612_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_st_ref_put(v___y_1599_, v___x_1612_);
v___x_1614_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1618_, v___y_1619_);
lean_dec(v___y_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1622_, lean_object* v_requestStream_1623_, lean_object* v_keepAliveTimeout_1624_, lean_object* v_currentTimeout_1625_, lean_object* v_headerTimeout_1626_, lean_object* v_response_1627_, lean_object* v_respStream_1628_, lean_object* v_expectData_1629_, uint8_t v_handlerDispatched_1630_, lean_object* v_____r_1631_){
_start:
{
uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1633_ = 0;
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1635_, 0, v_machine_1622_);
lean_ctor_set(v___x_1635_, 1, v_requestStream_1623_);
lean_ctor_set(v___x_1635_, 2, v_keepAliveTimeout_1624_);
lean_ctor_set(v___x_1635_, 3, v_currentTimeout_1625_);
lean_ctor_set(v___x_1635_, 4, v_headerTimeout_1626_);
lean_ctor_set(v___x_1635_, 5, v_response_1627_);
lean_ctor_set(v___x_1635_, 6, v_respStream_1628_);
lean_ctor_set(v___x_1635_, 7, v_expectData_1629_);
lean_ctor_set(v___x_1635_, 8, v___x_1634_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*9, v___x_1633_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*9 + 1, v_handlerDispatched_1630_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1639_, lean_object* v_requestStream_1640_, lean_object* v_keepAliveTimeout_1641_, lean_object* v_currentTimeout_1642_, lean_object* v_headerTimeout_1643_, lean_object* v_response_1644_, lean_object* v_respStream_1645_, lean_object* v_expectData_1646_, lean_object* v_handlerDispatched_1647_, lean_object* v_____r_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v_handlerDispatched_boxed_1650_; lean_object* v_res_1651_; 
v_handlerDispatched_boxed_1650_ = lean_unbox(v_handlerDispatched_1647_);
v_res_1651_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1639_, v_requestStream_1640_, v_keepAliveTimeout_1641_, v_currentTimeout_1642_, v_headerTimeout_1643_, v_response_1644_, v_respStream_1645_, v_expectData_1646_, v_handlerDispatched_boxed_1650_, v_____r_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1652_, lean_object* v_x_1653_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v___f_1652_);
v_a_1655_ = lean_ctor_get(v_x_1653_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1657_ = v_x_1653_;
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v_x_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v_x_1653_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v_x_1653_, 1);
v___x_1665_ = lean_apply_2(v___f_1652_, v_a_1664_, lean_box(0));
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1666_, lean_object* v_x_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1666_, v_x_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1670_, lean_object* v___f_1671_, lean_object* v___f_1672_, lean_object* v_x_1673_){
_start:
{
if (lean_obj_tag(v_x_1673_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v___f_1672_);
lean_dec_ref(v___f_1671_);
lean_dec_ref(v_requestStream_1670_);
v_a_1675_ = lean_ctor_get(v_x_1673_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1673_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_x_1673_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v_x_1673_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
else
{
lean_object* v_a_1684_; uint8_t v___x_1685_; 
v_a_1684_ = lean_ctor_get(v_x_1673_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v_x_1673_, 1);
v___x_1685_ = lean_unbox(v_a_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; 
lean_dec_ref(v___f_1672_);
v___x_1686_ = lean_unsigned_to_nat(0u);
v___x_1687_ = l_Std_Http_Body_Stream_close(v_requestStream_1670_);
v___x_1688_ = lean_unbox(v_a_1684_);
lean_dec(v_a_1684_);
v___x_1689_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1686_, v___x_1688_, v___x_1687_, v___f_1671_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_a_1684_);
lean_dec_ref(v___f_1671_);
lean_dec_ref(v_requestStream_1670_);
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_apply_2(v___f_1672_, v___x_1690_, lean_box(0));
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1692_, lean_object* v___f_1693_, lean_object* v___f_1694_, lean_object* v_x_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1692_, v___f_1693_, v___f_1694_, v_x_1695_);
return v_res_1697_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1698_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_1699_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; 
v___x_1705_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1706_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1707_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1707_, 0, v___f_1706_);
lean_closure_set(v___f_1707_, 1, v___x_1705_);
return v___f_1707_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; 
v___x_1716_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1717_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1718_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1718_, 0, v___f_1717_);
lean_closure_set(v___f_1718_, 1, v___x_1716_);
return v___f_1718_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1719_; lean_object* v___x_1720_; 
v___f_1719_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1720_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1720_, 0, lean_box(0));
lean_closure_set(v___x_1720_, 1, lean_box(0));
lean_closure_set(v___x_1720_, 2, lean_box(0));
lean_closure_set(v___x_1720_, 3, v___f_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1721_, lean_object* v___f_1722_, lean_object* v_x_1723_){
_start:
{
if (lean_obj_tag(v_x_1723_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v___f_1722_);
lean_dec_ref(v___y_1721_);
v_a_1725_ = lean_ctor_get(v_x_1723_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1723_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v_x_1723_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v_x_1723_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
else
{
lean_object* v_machine_1734_; lean_object* v_requestStream_1735_; lean_object* v_keepAliveTimeout_1736_; lean_object* v_currentTimeout_1737_; lean_object* v_headerTimeout_1738_; lean_object* v_response_1739_; lean_object* v_respStream_1740_; lean_object* v_expectData_1741_; uint8_t v_handlerDispatched_1742_; lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; lean_object* v___f_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_4870__overap_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec_ref_known(v_x_1723_, 1);
v_machine_1734_ = lean_ctor_get(v___y_1721_, 0);
lean_inc_ref(v_machine_1734_);
v_requestStream_1735_ = lean_ctor_get(v___y_1721_, 1);
lean_inc_ref_n(v_requestStream_1735_, 3);
v_keepAliveTimeout_1736_ = lean_ctor_get(v___y_1721_, 2);
lean_inc(v_keepAliveTimeout_1736_);
v_currentTimeout_1737_ = lean_ctor_get(v___y_1721_, 3);
lean_inc(v_currentTimeout_1737_);
v_headerTimeout_1738_ = lean_ctor_get(v___y_1721_, 4);
lean_inc(v_headerTimeout_1738_);
v_response_1739_ = lean_ctor_get(v___y_1721_, 5);
lean_inc_ref(v_response_1739_);
v_respStream_1740_ = lean_ctor_get(v___y_1721_, 6);
lean_inc(v_respStream_1740_);
v_expectData_1741_ = lean_ctor_get(v___y_1721_, 7);
lean_inc(v_expectData_1741_);
v_handlerDispatched_1742_ = lean_ctor_get_uint8(v___y_1721_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1721_);
v___x_1743_ = lean_box(v_handlerDispatched_1742_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1744_, 0, v_machine_1734_);
lean_closure_set(v___f_1744_, 1, v_requestStream_1735_);
lean_closure_set(v___f_1744_, 2, v_keepAliveTimeout_1736_);
lean_closure_set(v___f_1744_, 3, v_currentTimeout_1737_);
lean_closure_set(v___f_1744_, 4, v_headerTimeout_1738_);
lean_closure_set(v___f_1744_, 5, v_response_1739_);
lean_closure_set(v___f_1744_, 6, v_respStream_1740_);
lean_closure_set(v___f_1744_, 7, v_expectData_1741_);
lean_closure_set(v___f_1744_, 8, v___x_1743_);
lean_inc_ref(v___f_1744_);
v___f_1745_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1745_, 0, v___f_1744_);
v___f_1746_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1746_, 0, v_requestStream_1735_);
lean_closure_set(v___f_1746_, 1, v___f_1745_);
lean_closure_set(v___f_1746_, 2, v___f_1744_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = 0;
v___x_1749_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1750_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1751_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1752_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1753_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1753_, 0, lean_box(0));
lean_closure_set(v___x_1753_, 1, lean_box(0));
lean_closure_set(v___x_1753_, 2, v___x_1749_);
lean_closure_set(v___x_1753_, 3, lean_box(0));
lean_closure_set(v___x_1753_, 4, lean_box(0));
lean_closure_set(v___x_1753_, 5, v___x_1752_);
lean_closure_set(v___x_1753_, 6, v___f_1722_);
v___x_4870__overap_1754_ = l_Std_Mutex_atomically___redArg(v___x_1749_, v___f_1750_, v___f_1751_, v_requestStream_1735_, v___x_1753_);
v___x_1755_ = lean_apply_1(v___x_4870__overap_1754_, lean_box(0));
v___x_1756_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1747_, v___x_1748_, v___x_1755_, v___f_1746_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1757_, lean_object* v___f_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1757_, v___f_1758_, v_x_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1762_, lean_object* v_x_1763_){
_start:
{
if (lean_obj_tag(v_x_1763_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___y_1762_);
v_a_1765_ = lean_ctor_get(v_x_1763_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_x_1763_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1767_ = v_x_1763_;
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v_x_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1765_);
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
else
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1782_; 
v_isSharedCheck_1782_ = !lean_is_exclusive(v_x_1763_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v_x_1763_, 0);
lean_dec(v_unused_1783_);
v___x_1775_ = v_x_1763_;
v_isShared_1776_ = v_isSharedCheck_1782_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v_x_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1782_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___y_1762_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1784_, lean_object* v_x_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1784_, v_x_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1788_, lean_object* v___f_1789_, lean_object* v___y_1790_, lean_object* v_x_1791_){
_start:
{
if (lean_obj_tag(v_x_1791_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___f_1789_);
lean_dec_ref(v_requestStream_1788_);
v_a_1793_ = lean_ctor_get(v_x_1791_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_x_1791_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1795_ = v_x_1791_;
v_isShared_1796_ = v_isSharedCheck_1801_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v_x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1801_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1816_; 
v_a_1802_ = lean_ctor_get(v_x_1791_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_x_1791_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1804_ = v_x_1791_;
v_isShared_1805_ = v_isSharedCheck_1816_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v_x_1791_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1816_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_unbox(v_a_1802_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1804_);
lean_dec_ref(v___y_1790_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = l_Std_Http_Body_Stream_close(v_requestStream_1788_);
v___x_1809_ = lean_unbox(v_a_1802_);
lean_dec(v_a_1802_);
v___x_1810_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1807_, v___x_1809_, v___x_1808_, v___f_1789_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec(v_a_1802_);
lean_dec_ref(v___f_1789_);
lean_dec_ref(v_requestStream_1788_);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___y_1790_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1811_);
v___x_1813_ = v___x_1804_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1817_, lean_object* v___f_1818_, lean_object* v___y_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1817_, v___f_1818_, v___y_1819_, v_x_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1823_, lean_object* v_machine_1824_, lean_object* v_a_1825_, uint8_t v_requiresData_1826_, lean_object* v_expectData_1827_, lean_object* v_pendingHead_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1829_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_pendingHead_1828_);
lean_dec(v_expectData_1827_);
lean_dec_ref(v_a_1825_);
lean_dec_ref(v_machine_1824_);
v_a_1831_ = lean_ctor_get(v_x_1829_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1833_ = v_x_1829_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v_x_1829_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1831_);
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
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1854_; 
v_a_1840_ = lean_ctor_get(v_x_1829_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1842_ = v_x_1829_;
v_isShared_1843_ = v_isSharedCheck_1854_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v_x_1829_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1854_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_keepAliveTimeout_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v_keepAliveTimeout_1844_ = lean_ctor_get(v_config_1823_, 5);
lean_inc_n(v_keepAliveTimeout_1844_, 2);
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_keepAliveTimeout_1844_);
v___x_1846_ = lean_box(0);
v___x_1847_ = 0;
v___x_1848_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1848_, 0, v_machine_1824_);
lean_ctor_set(v___x_1848_, 1, v_a_1825_);
lean_ctor_set(v___x_1848_, 2, v___x_1845_);
lean_ctor_set(v___x_1848_, 3, v_keepAliveTimeout_1844_);
lean_ctor_set(v___x_1848_, 4, v___x_1846_);
lean_ctor_set(v___x_1848_, 5, v_a_1840_);
lean_ctor_set(v___x_1848_, 6, v___x_1846_);
lean_ctor_set(v___x_1848_, 7, v_expectData_1827_);
lean_ctor_set(v___x_1848_, 8, v_pendingHead_1828_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*9, v_requiresData_1826_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*9 + 1, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1849_);
v___x_1851_ = v___x_1842_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1855_, lean_object* v_machine_1856_, lean_object* v_a_1857_, lean_object* v_requiresData_1858_, lean_object* v_expectData_1859_, lean_object* v_pendingHead_1860_, lean_object* v_x_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_requiresData_boxed_1863_; lean_object* v_res_1864_; 
v_requiresData_boxed_1863_ = lean_unbox(v_requiresData_1858_);
v_res_1864_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1855_, v_machine_1856_, v_a_1857_, v_requiresData_boxed_1863_, v_expectData_1859_, v_pendingHead_1860_, v_x_1861_);
lean_dec_ref(v_config_1855_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1865_, lean_object* v_machine_1866_, uint8_t v_requiresData_1867_, lean_object* v_expectData_1868_, lean_object* v_pendingHead_1869_, lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_pendingHead_1869_);
lean_dec(v_expectData_1868_);
lean_dec_ref(v_machine_1866_);
lean_dec_ref(v_config_1865_);
v_a_1872_ = lean_ctor_get(v_x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v_x_1870_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1896_; 
v_a_1881_ = lean_ctor_get(v_x_1870_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1883_ = v_x_1870_;
v_isShared_1884_ = v_isSharedCheck_1896_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v_x_1870_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1896_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1885_ = lean_box(v_requiresData_1867_);
v___f_1886_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1886_, 0, v_config_1865_);
lean_closure_set(v___f_1886_, 1, v_machine_1866_);
lean_closure_set(v___f_1886_, 2, v_a_1881_);
lean_closure_set(v___f_1886_, 3, v___x_1885_);
lean_closure_set(v___f_1886_, 4, v_expectData_1868_);
lean_closure_set(v___f_1886_, 5, v_pendingHead_1869_);
v___x_1887_ = lean_box(0);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = 0;
v___x_1890_ = l_Std_CloseableChannel_new___redArg(v___x_1887_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1890_);
v___x_1892_ = v___x_1883_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
v___x_1894_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1888_, v___x_1889_, v___x_1893_, v___f_1886_);
return v___x_1894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1897_, lean_object* v_machine_1898_, lean_object* v_requiresData_1899_, lean_object* v_expectData_1900_, lean_object* v_pendingHead_1901_, lean_object* v_x_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v_requiresData_boxed_1904_; lean_object* v_res_1905_; 
v_requiresData_boxed_1904_ = lean_unbox(v_requiresData_1899_);
v_res_1905_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1897_, v_machine_1898_, v_requiresData_boxed_1904_, v_expectData_1900_, v_pendingHead_1901_, v_x_1902_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1906_, lean_object* v_____r_1907_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = 0;
v___x_1911_ = l_Std_Http_Body_mkStream();
v___x_1912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1909_, v___x_1910_, v___x_1911_, v___f_1906_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1913_, lean_object* v_____r_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1913_, v_____r_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1917_, lean_object* v_val_1918_, lean_object* v___f_1919_, lean_object* v___f_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v___f_1920_);
lean_dec_ref(v___f_1919_);
lean_dec(v_val_1918_);
lean_dec_ref(v_close_1917_);
v_a_1923_ = lean_ctor_get(v_x_1921_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1925_ = v_x_1921_;
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v_x_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1932_; uint8_t v___x_1933_; 
v_a_1932_ = lean_ctor_get(v_x_1921_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v_x_1921_, 1);
v___x_1933_ = lean_unbox(v_a_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; 
lean_dec_ref(v___f_1920_);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_apply_2(v_close_1917_, v_val_1918_, lean_box(0));
v___x_1936_ = lean_unbox(v_a_1932_);
lean_dec(v_a_1932_);
v___x_1937_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1934_, v___x_1936_, v___x_1935_, v___f_1919_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v_a_1932_);
lean_dec_ref(v___f_1919_);
lean_dec(v_val_1918_);
lean_dec_ref(v_close_1917_);
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_apply_2(v___f_1920_, v___x_1938_, lean_box(0));
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1940_, lean_object* v_val_1941_, lean_object* v___f_1942_, lean_object* v___f_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1940_, v_val_1941_, v___f_1942_, v___f_1943_, v_x_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1947_, lean_object* v_inst_1948_, lean_object* v___f_1949_, lean_object* v___f_1950_, lean_object* v_____r_1951_){
_start:
{
if (lean_obj_tag(v_respStream_1947_) == 1)
{
lean_object* v_val_1953_; lean_object* v_close_1954_; lean_object* v_isClosed_1955_; lean_object* v___f_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_val_1953_ = lean_ctor_get(v_respStream_1947_, 0);
lean_inc_n(v_val_1953_, 2);
lean_dec_ref_known(v_respStream_1947_, 1);
v_close_1954_ = lean_ctor_get(v_inst_1948_, 1);
lean_inc_ref(v_close_1954_);
v_isClosed_1955_ = lean_ctor_get(v_inst_1948_, 2);
lean_inc_ref(v_isClosed_1955_);
lean_dec_ref(v_inst_1948_);
v___f_1956_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1956_, 0, v_close_1954_);
lean_closure_set(v___f_1956_, 1, v_val_1953_);
lean_closure_set(v___f_1956_, 2, v___f_1949_);
lean_closure_set(v___f_1956_, 3, v___f_1950_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = 0;
v___x_1959_ = lean_apply_2(v_isClosed_1955_, v_val_1953_, lean_box(0));
v___x_1960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1957_, v___x_1958_, v___x_1959_, v___f_1956_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec_ref(v___f_1949_);
lean_dec_ref(v_inst_1948_);
lean_dec(v_respStream_1947_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_apply_2(v___f_1950_, v___x_1961_, lean_box(0));
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1963_, lean_object* v_inst_1964_, lean_object* v___f_1965_, lean_object* v___f_1966_, lean_object* v_____r_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1963_, v_inst_1964_, v___f_1965_, v___f_1966_, v_____r_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1970_, lean_object* v_keepAliveTimeout_1971_, lean_object* v_currentTimeout_1972_, lean_object* v_headerTimeout_1973_, lean_object* v_response_1974_, lean_object* v_respStream_1975_, uint8_t v_requiresData_1976_, lean_object* v_expectData_1977_, uint8_t v_handlerDispatched_1978_, lean_object* v_pendingHead_1979_, lean_object* v_x_1980_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_pendingHead_1979_);
lean_dec(v_expectData_1977_);
lean_dec(v_respStream_1975_);
lean_dec_ref(v_response_1974_);
lean_dec(v_headerTimeout_1973_);
lean_dec(v_currentTimeout_1972_);
lean_dec(v_keepAliveTimeout_1971_);
lean_dec_ref(v_requestStream_1970_);
v_a_1982_ = lean_ctor_get(v_x_1980_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_x_1980_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v_x_1980_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v_x_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2012_; 
v_a_1991_ = lean_ctor_get(v_x_1980_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_x_1980_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1993_ = v_x_1980_;
v_isShared_1994_ = v_isSharedCheck_2012_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v_x_1980_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2012_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_snd_1995_; uint8_t v___x_1996_; 
v_snd_1995_ = lean_ctor_get(v_a_1991_, 1);
v___x_1996_ = lean_unbox(v_snd_1995_);
if (v___x_1996_ == 0)
{
lean_object* v_fst_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v_fst_1997_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_fst_1997_);
lean_dec(v_a_1991_);
v___x_1998_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1998_, 0, v_fst_1997_);
lean_ctor_set(v___x_1998_, 1, v_requestStream_1970_);
lean_ctor_set(v___x_1998_, 2, v_keepAliveTimeout_1971_);
lean_ctor_set(v___x_1998_, 3, v_currentTimeout_1972_);
lean_ctor_set(v___x_1998_, 4, v_headerTimeout_1973_);
lean_ctor_set(v___x_1998_, 5, v_response_1974_);
lean_ctor_set(v___x_1998_, 6, v_respStream_1975_);
lean_ctor_set(v___x_1998_, 7, v_expectData_1977_);
lean_ctor_set(v___x_1998_, 8, v_pendingHead_1979_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*9, v_requiresData_1976_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*9 + 1, v_handlerDispatched_1978_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1999_);
v___x_2001_ = v___x_1993_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
else
{
lean_object* v_fst_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec(v_pendingHead_1979_);
v_fst_2004_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_fst_2004_);
lean_dec(v_a_1991_);
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2006_, 0, v_fst_2004_);
lean_ctor_set(v___x_2006_, 1, v_requestStream_1970_);
lean_ctor_set(v___x_2006_, 2, v_keepAliveTimeout_1971_);
lean_ctor_set(v___x_2006_, 3, v_currentTimeout_1972_);
lean_ctor_set(v___x_2006_, 4, v_headerTimeout_1973_);
lean_ctor_set(v___x_2006_, 5, v_response_1974_);
lean_ctor_set(v___x_2006_, 6, v_respStream_1975_);
lean_ctor_set(v___x_2006_, 7, v_expectData_1977_);
lean_ctor_set(v___x_2006_, 8, v___x_2005_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*9, v_requiresData_1976_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*9 + 1, v_handlerDispatched_1978_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2007_);
v___x_2009_ = v___x_1993_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2013_, lean_object* v_keepAliveTimeout_2014_, lean_object* v_currentTimeout_2015_, lean_object* v_headerTimeout_2016_, lean_object* v_response_2017_, lean_object* v_respStream_2018_, lean_object* v_requiresData_2019_, lean_object* v_expectData_2020_, lean_object* v_handlerDispatched_2021_, lean_object* v_pendingHead_2022_, lean_object* v_x_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v_requiresData_boxed_2025_; uint8_t v_handlerDispatched_boxed_2026_; lean_object* v_res_2027_; 
v_requiresData_boxed_2025_ = lean_unbox(v_requiresData_2019_);
v_handlerDispatched_boxed_2026_ = lean_unbox(v_handlerDispatched_2021_);
v_res_2027_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2013_, v_keepAliveTimeout_2014_, v_currentTimeout_2015_, v_headerTimeout_2016_, v_response_2017_, v_respStream_2018_, v_requiresData_boxed_2025_, v_expectData_2020_, v_handlerDispatched_boxed_2026_, v_pendingHead_2022_, v_x_2023_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2040_, lean_object* v_inst_2041_, lean_object* v___f_2042_, lean_object* v_handler_2043_, lean_object* v___f_2044_, lean_object* v_inst_2045_, lean_object* v___f_2046_, lean_object* v_connectionContext_2047_, lean_object* v_a_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_){
_start:
{
switch(lean_obj_tag(v_a_2048_))
{
case 0:
{
lean_object* v_head_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_connectionContext_2047_);
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec_ref(v___f_2044_);
lean_dec(v_handler_2043_);
lean_dec_ref(v___f_2042_);
lean_dec_ref(v_inst_2041_);
v_head_2052_ = lean_ctor_get(v_a_2048_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_a_2048_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2054_ = v_a_2048_;
v_isShared_2055_ = v_isSharedCheck_2095_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_head_2052_);
lean_dec(v_a_2048_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2095_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_machine_2056_; lean_object* v_requestStream_2057_; lean_object* v_response_2058_; lean_object* v_respStream_2059_; uint8_t v_requiresData_2060_; lean_object* v_expectData_2061_; uint8_t v_handlerDispatched_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2090_; 
v_machine_2056_ = lean_ctor_get(v___y_2050_, 0);
v_requestStream_2057_ = lean_ctor_get(v___y_2050_, 1);
v_response_2058_ = lean_ctor_get(v___y_2050_, 5);
v_respStream_2059_ = lean_ctor_get(v___y_2050_, 6);
v_requiresData_2060_ = lean_ctor_get_uint8(v___y_2050_, sizeof(void*)*9);
v_expectData_2061_ = lean_ctor_get(v___y_2050_, 7);
v_handlerDispatched_2062_ = lean_ctor_get_uint8(v___y_2050_, sizeof(void*)*9 + 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___y_2050_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; 
v_unused_2091_ = lean_ctor_get(v___y_2050_, 8);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v___y_2050_, 4);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v___y_2050_, 3);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v___y_2050_, 2);
lean_dec(v_unused_2094_);
v___x_2064_ = v___y_2050_;
v_isShared_2065_ = v_isSharedCheck_2090_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_expectData_2061_);
lean_inc(v_respStream_2059_);
lean_inc(v_response_2058_);
lean_inc(v_requestStream_2057_);
lean_inc(v_machine_2056_);
lean_dec(v___y_2050_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2090_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_lingeringTimeout_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v_lingeringTimeout_2066_ = lean_ctor_get(v_config_2040_, 4);
lean_inc(v_lingeringTimeout_2066_);
lean_dec_ref(v_config_2040_);
v___x_2067_ = lean_box(0);
lean_inc(v_head_2052_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set_tag(v___x_2054_, 1);
v___x_2069_ = v___x_2054_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_head_2052_);
v___x_2069_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
lean_inc_ref(v_requestStream_2057_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 8, v___x_2069_);
lean_ctor_set(v___x_2064_, 4, v___x_2067_);
lean_ctor_set(v___x_2064_, 3, v_lingeringTimeout_2066_);
lean_ctor_set(v___x_2064_, 2, v___x_2067_);
v___x_2071_ = v___x_2064_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_machine_2056_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_requestStream_2057_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_lingeringTimeout_2066_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2088_, 5, v_response_2058_);
lean_ctor_set(v_reuseFailAlloc_2088_, 6, v_respStream_2059_);
lean_ctor_set(v_reuseFailAlloc_2088_, 7, v_expectData_2061_);
lean_ctor_set(v_reuseFailAlloc_2088_, 8, v___x_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*9, v_requiresData_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*9 + 1, v_handlerDispatched_2062_);
v___x_2071_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
uint8_t v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = 0;
v___x_2073_ = 1;
v___x_2074_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2072_, v_head_2052_, v___x_2073_);
lean_dec(v_head_2052_);
if (lean_obj_tag(v___x_2074_) == 1)
{
lean_object* v___f_2075_; lean_object* v___f_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___x_5061__overap_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___f_2075_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2075_, 0, v___x_2071_);
v___f_2076_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2076_, 0, v___x_2074_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = 0;
v___x_2079_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2080_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2081_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_2082_ = l_Std_Mutex_atomically___redArg(v___x_2079_, v___f_2080_, v___f_2081_, v_requestStream_2057_, v___f_2076_);
v___x_2083_ = lean_apply_1(v___x_5061__overap_2082_, lean_box(0));
v___x_2084_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2077_, v___x_2078_, v___x_2083_, v___f_2075_);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v___x_2074_);
lean_dec_ref(v_requestStream_2057_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2071_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_connectionContext_2047_);
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec_ref(v___f_2044_);
lean_dec(v_handler_2043_);
lean_dec_ref(v___f_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_config_2040_);
v_size_2096_ = lean_ctor_get(v_a_2048_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_a_2048_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2098_ = v_a_2048_;
v_isShared_2099_ = v_isSharedCheck_2123_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_size_2096_);
lean_dec(v_a_2048_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2123_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_machine_2100_; lean_object* v_requestStream_2101_; lean_object* v_keepAliveTimeout_2102_; lean_object* v_currentTimeout_2103_; lean_object* v_headerTimeout_2104_; lean_object* v_response_2105_; lean_object* v_respStream_2106_; uint8_t v_handlerDispatched_2107_; lean_object* v_pendingHead_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2121_; 
v_machine_2100_ = lean_ctor_get(v___y_2050_, 0);
v_requestStream_2101_ = lean_ctor_get(v___y_2050_, 1);
v_keepAliveTimeout_2102_ = lean_ctor_get(v___y_2050_, 2);
v_currentTimeout_2103_ = lean_ctor_get(v___y_2050_, 3);
v_headerTimeout_2104_ = lean_ctor_get(v___y_2050_, 4);
v_response_2105_ = lean_ctor_get(v___y_2050_, 5);
v_respStream_2106_ = lean_ctor_get(v___y_2050_, 6);
v_handlerDispatched_2107_ = lean_ctor_get_uint8(v___y_2050_, sizeof(void*)*9 + 1);
v_pendingHead_2108_ = lean_ctor_get(v___y_2050_, 8);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___y_2050_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v___y_2050_, 7);
lean_dec(v_unused_2122_);
v___x_2110_ = v___y_2050_;
v_isShared_2111_ = v_isSharedCheck_2121_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_pendingHead_2108_);
lean_inc(v_respStream_2106_);
lean_inc(v_response_2105_);
lean_inc(v_headerTimeout_2104_);
lean_inc(v_currentTimeout_2103_);
lean_inc(v_keepAliveTimeout_2102_);
lean_inc(v_requestStream_2101_);
lean_inc(v_machine_2100_);
lean_dec(v___y_2050_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2121_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
uint8_t v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = 1;
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 7, v_size_2096_);
v___x_2114_ = v___x_2110_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_machine_2100_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_requestStream_2101_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_keepAliveTimeout_2102_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_currentTimeout_2103_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_headerTimeout_2104_);
lean_ctor_set(v_reuseFailAlloc_2120_, 5, v_response_2105_);
lean_ctor_set(v_reuseFailAlloc_2120_, 6, v_respStream_2106_);
lean_ctor_set(v_reuseFailAlloc_2120_, 7, v_size_2096_);
lean_ctor_set(v_reuseFailAlloc_2120_, 8, v_pendingHead_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*9 + 1, v_handlerDispatched_2107_);
v___x_2114_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*9, v___x_2112_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2114_);
v___x_2116_ = v___x_2098_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2124_; lean_object* v_onFailure_2125_; lean_object* v___f_2126_; lean_object* v___y_2128_; 
lean_dec_ref(v_connectionContext_2047_);
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec_ref(v___f_2044_);
lean_dec_ref(v_config_2040_);
v_err_2124_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_err_2124_);
lean_dec_ref_known(v_a_2048_, 1);
v_onFailure_2125_ = lean_ctor_get(v_inst_2041_, 2);
lean_inc_ref(v_onFailure_2125_);
lean_dec_ref(v_inst_2041_);
v___f_2126_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2126_, 0, v___y_2050_);
lean_closure_set(v___f_2126_, 1, v___f_2042_);
switch(lean_obj_tag(v_err_2124_))
{
case 0:
{
lean_object* v___x_2134_; 
v___x_2134_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2128_ = v___x_2134_;
goto v___jp_2127_;
}
case 1:
{
lean_object* v___x_2135_; 
v___x_2135_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2128_ = v___x_2135_;
goto v___jp_2127_;
}
case 2:
{
lean_object* v___x_2136_; 
v___x_2136_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2128_ = v___x_2136_;
goto v___jp_2127_;
}
case 3:
{
lean_object* v___x_2137_; 
v___x_2137_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2128_ = v___x_2137_;
goto v___jp_2127_;
}
case 4:
{
lean_object* v___x_2138_; 
v___x_2138_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2128_ = v___x_2138_;
goto v___jp_2127_;
}
case 5:
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2128_ = v___x_2139_;
goto v___jp_2127_;
}
case 6:
{
lean_object* v___x_2140_; 
v___x_2140_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2128_ = v___x_2140_;
goto v___jp_2127_;
}
case 7:
{
lean_object* v___x_2141_; 
v___x_2141_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2128_ = v___x_2141_;
goto v___jp_2127_;
}
case 8:
{
lean_object* v___x_2142_; 
v___x_2142_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2128_ = v___x_2142_;
goto v___jp_2127_;
}
case 9:
{
lean_object* v___x_2143_; 
v___x_2143_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2128_ = v___x_2143_;
goto v___jp_2127_;
}
case 10:
{
lean_object* v___x_2144_; 
v___x_2144_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2128_ = v___x_2144_;
goto v___jp_2127_;
}
default: 
{
lean_object* v_message_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_message_2145_ = lean_ctor_get(v_err_2124_, 0);
lean_inc_ref(v_message_2145_);
lean_dec_ref_known(v_err_2124_, 1);
v___x_2146_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2147_ = lean_string_append(v___x_2146_, v_message_2145_);
lean_dec_ref(v_message_2145_);
v___y_2128_ = v___x_2147_;
goto v___jp_2127_;
}
}
v___jp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2129_ = lean_mk_io_user_error(v___y_2128_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = 0;
v___x_2132_ = lean_apply_3(v_onFailure_2125_, v_handler_2043_, v___x_2129_, lean_box(0));
v___x_2133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2130_, v___x_2131_, v___x_2132_, v___f_2126_);
return v___x_2133_;
}
}
case 4:
{
lean_object* v_requestStream_2148_; lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_5118__overap_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v_connectionContext_2047_);
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec(v_handler_2043_);
lean_dec_ref(v___f_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_config_2040_);
v_requestStream_2148_ = lean_ctor_get(v___y_2050_, 1);
lean_inc_ref_n(v_requestStream_2148_, 2);
lean_inc_ref(v___y_2050_);
v___f_2149_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2149_, 0, v___y_2050_);
v___f_2150_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2150_, 0, v_requestStream_2148_);
lean_closure_set(v___f_2150_, 1, v___f_2149_);
lean_closure_set(v___f_2150_, 2, v___y_2050_);
v___x_2151_ = lean_unsigned_to_nat(0u);
v___x_2152_ = 0;
v___x_2153_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2154_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2155_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2156_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2157_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2157_, 0, lean_box(0));
lean_closure_set(v___x_2157_, 1, lean_box(0));
lean_closure_set(v___x_2157_, 2, v___x_2153_);
lean_closure_set(v___x_2157_, 3, lean_box(0));
lean_closure_set(v___x_2157_, 4, lean_box(0));
lean_closure_set(v___x_2157_, 5, v___x_2156_);
lean_closure_set(v___x_2157_, 6, v___f_2044_);
v___x_5118__overap_2158_ = l_Std_Mutex_atomically___redArg(v___x_2153_, v___f_2154_, v___f_2155_, v_requestStream_2148_, v___x_2157_);
v___x_2159_ = lean_apply_1(v___x_5118__overap_2158_, lean_box(0));
v___x_2160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2151_, v___x_2152_, v___x_2159_, v___f_2150_);
return v___x_2160_;
}
case 6:
{
lean_object* v_machine_2161_; lean_object* v_requestStream_2162_; lean_object* v_respStream_2163_; uint8_t v_requiresData_2164_; lean_object* v_expectData_2165_; lean_object* v_pendingHead_2166_; lean_object* v___x_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; lean_object* v___f_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_5143__overap_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v_connectionContext_2047_);
lean_dec_ref(v___f_2044_);
lean_dec(v_handler_2043_);
lean_dec_ref(v___f_2042_);
lean_dec_ref(v_inst_2041_);
v_machine_2161_ = lean_ctor_get(v___y_2050_, 0);
lean_inc_ref(v_machine_2161_);
v_requestStream_2162_ = lean_ctor_get(v___y_2050_, 1);
lean_inc_ref_n(v_requestStream_2162_, 2);
v_respStream_2163_ = lean_ctor_get(v___y_2050_, 6);
lean_inc(v_respStream_2163_);
v_requiresData_2164_ = lean_ctor_get_uint8(v___y_2050_, sizeof(void*)*9);
v_expectData_2165_ = lean_ctor_get(v___y_2050_, 7);
lean_inc(v_expectData_2165_);
v_pendingHead_2166_ = lean_ctor_get(v___y_2050_, 8);
lean_inc(v_pendingHead_2166_);
lean_dec_ref(v___y_2050_);
v___x_2167_ = lean_box(v_requiresData_2164_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2168_, 0, v_config_2040_);
lean_closure_set(v___f_2168_, 1, v_machine_2161_);
lean_closure_set(v___f_2168_, 2, v___x_2167_);
lean_closure_set(v___f_2168_, 3, v_expectData_2165_);
lean_closure_set(v___f_2168_, 4, v_pendingHead_2166_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2169_, 0, v___f_2168_);
lean_inc_ref(v___f_2169_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2170_, 0, v___f_2169_);
v___f_2171_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2171_, 0, v_respStream_2163_);
lean_closure_set(v___f_2171_, 1, v_inst_2045_);
lean_closure_set(v___f_2171_, 2, v___f_2170_);
lean_closure_set(v___f_2171_, 3, v___f_2169_);
lean_inc_ref(v___f_2171_);
v___f_2172_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2172_, 0, v___f_2171_);
v___f_2173_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2173_, 0, v_requestStream_2162_);
lean_closure_set(v___f_2173_, 1, v___f_2172_);
lean_closure_set(v___f_2173_, 2, v___f_2171_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = 0;
v___x_2176_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2177_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2178_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2179_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2180_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2180_, 0, lean_box(0));
lean_closure_set(v___x_2180_, 1, lean_box(0));
lean_closure_set(v___x_2180_, 2, v___x_2176_);
lean_closure_set(v___x_2180_, 3, lean_box(0));
lean_closure_set(v___x_2180_, 4, lean_box(0));
lean_closure_set(v___x_2180_, 5, v___x_2179_);
lean_closure_set(v___x_2180_, 6, v___f_2046_);
v___x_5143__overap_2181_ = l_Std_Mutex_atomically___redArg(v___x_2176_, v___f_2177_, v___f_2178_, v_requestStream_2162_, v___x_2180_);
v___x_2182_ = lean_apply_1(v___x_5143__overap_2181_, lean_box(0));
v___x_2183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2174_, v___x_2175_, v___x_2182_, v___f_2173_);
return v___x_2183_;
}
case 7:
{
lean_object* v_pendingHead_2184_; 
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec_ref(v___f_2044_);
lean_dec_ref(v___f_2042_);
v_pendingHead_2184_ = lean_ctor_get(v___y_2050_, 8);
if (lean_obj_tag(v_pendingHead_2184_) == 1)
{
lean_object* v_machine_2185_; lean_object* v_requestStream_2186_; lean_object* v_keepAliveTimeout_2187_; lean_object* v_currentTimeout_2188_; lean_object* v_headerTimeout_2189_; lean_object* v_response_2190_; lean_object* v_respStream_2191_; uint8_t v_requiresData_2192_; lean_object* v_expectData_2193_; uint8_t v_handlerDispatched_2194_; lean_object* v_val_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_inc_ref(v_pendingHead_2184_);
v_machine_2185_ = lean_ctor_get(v___y_2050_, 0);
lean_inc_ref(v_machine_2185_);
v_requestStream_2186_ = lean_ctor_get(v___y_2050_, 1);
lean_inc_ref(v_requestStream_2186_);
v_keepAliveTimeout_2187_ = lean_ctor_get(v___y_2050_, 2);
lean_inc(v_keepAliveTimeout_2187_);
v_currentTimeout_2188_ = lean_ctor_get(v___y_2050_, 3);
lean_inc(v_currentTimeout_2188_);
v_headerTimeout_2189_ = lean_ctor_get(v___y_2050_, 4);
lean_inc(v_headerTimeout_2189_);
v_response_2190_ = lean_ctor_get(v___y_2050_, 5);
lean_inc_ref(v_response_2190_);
v_respStream_2191_ = lean_ctor_get(v___y_2050_, 6);
lean_inc(v_respStream_2191_);
v_requiresData_2192_ = lean_ctor_get_uint8(v___y_2050_, sizeof(void*)*9);
v_expectData_2193_ = lean_ctor_get(v___y_2050_, 7);
lean_inc(v_expectData_2193_);
v_handlerDispatched_2194_ = lean_ctor_get_uint8(v___y_2050_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2050_);
v_val_2195_ = lean_ctor_get(v_pendingHead_2184_, 0);
lean_inc(v_val_2195_);
v___x_2196_ = lean_box(v_requiresData_2192_);
v___x_2197_ = lean_box(v_handlerDispatched_2194_);
v___f_2198_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2198_, 0, v_requestStream_2186_);
lean_closure_set(v___f_2198_, 1, v_keepAliveTimeout_2187_);
lean_closure_set(v___f_2198_, 2, v_currentTimeout_2188_);
lean_closure_set(v___f_2198_, 3, v_headerTimeout_2189_);
lean_closure_set(v___f_2198_, 4, v_response_2190_);
lean_closure_set(v___f_2198_, 5, v_respStream_2191_);
lean_closure_set(v___f_2198_, 6, v___x_2196_);
lean_closure_set(v___f_2198_, 7, v_expectData_2193_);
lean_closure_set(v___f_2198_, 8, v___x_2197_);
lean_closure_set(v___f_2198_, 9, v_pendingHead_2184_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = 0;
v___x_2201_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2041_, v_handler_2043_, v_machine_2185_, v_val_2195_, v_config_2040_, v_connectionContext_2047_);
v___x_2202_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2199_, v___x_2200_, v___x_2201_, v___f_2198_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref(v_connectionContext_2047_);
lean_dec(v_handler_2043_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_config_2040_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___y_2050_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
default: 
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v_a_2048_);
lean_dec_ref(v_connectionContext_2047_);
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec_ref(v___f_2044_);
lean_dec(v_handler_2043_);
lean_dec_ref(v___f_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec_ref(v_config_2040_);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___y_2050_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2209_, lean_object* v_inst_2210_, lean_object* v___f_2211_, lean_object* v_handler_2212_, lean_object* v___f_2213_, lean_object* v_inst_2214_, lean_object* v___f_2215_, lean_object* v_connectionContext_2216_, lean_object* v_a_2217_, lean_object* v_x_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2209_, v_inst_2210_, v___f_2211_, v_handler_2212_, v___f_2213_, v_inst_2214_, v___f_2215_, v_connectionContext_2216_, v_a_2217_, v_x_2218_, v___y_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_x_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_handler_2232_, lean_object* v_config_2233_, lean_object* v_connectionContext_2234_, lean_object* v_events_2235_, lean_object* v_state_2236_){
_start:
{
lean_object* v___f_2238_; lean_object* v___f_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_4072__overap_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___f_2238_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2239_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2239_, 0, v_config_2233_);
lean_closure_set(v___f_2239_, 1, v_inst_2230_);
lean_closure_set(v___f_2239_, 2, v___f_2238_);
lean_closure_set(v___f_2239_, 3, v_handler_2232_);
lean_closure_set(v___f_2239_, 4, v___f_2238_);
lean_closure_set(v___f_2239_, 5, v_inst_2231_);
lean_closure_set(v___f_2239_, 6, v___f_2238_);
lean_closure_set(v___f_2239_, 7, v_connectionContext_2234_);
v___f_2240_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2241_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2242_ = lean_array_size(v_events_2235_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = 0;
v___x_4072__overap_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2241_, v_events_2235_, v___f_2239_, v_sz_2242_, v___x_2243_, v_state_2236_);
v___x_2247_ = lean_apply_1(v___x_4072__overap_2246_, lean_box(0));
v___x_2248_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2244_, v___x_2245_, v___x_2247_, v___f_2240_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_handler_2251_, lean_object* v_config_2252_, lean_object* v_connectionContext_2253_, lean_object* v_events_2254_, lean_object* v_state_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2249_, v_inst_2250_, v_handler_2251_, v_config_2252_, v_connectionContext_2253_, v_events_2254_, v_state_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2258_, lean_object* v_00_u03b2_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_handler_2262_, lean_object* v_config_2263_, lean_object* v_connectionContext_2264_, lean_object* v_events_2265_, lean_object* v_state_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2260_, v_inst_2261_, v_handler_2262_, v_config_2263_, v_connectionContext_2264_, v_events_2265_, v_state_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2269_, lean_object* v_00_u03b2_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_handler_2273_, lean_object* v_config_2274_, lean_object* v_connectionContext_2275_, lean_object* v_events_2276_, lean_object* v_state_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2269_, v_00_u03b2_2270_, v_inst_2271_, v_inst_2272_, v_handler_2273_, v_config_2274_, v_connectionContext_2275_, v_events_2276_, v_state_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2280_){
_start:
{
if (lean_obj_tag(v_x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; 
v_a_2281_ = lean_ctor_get(v_x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v_x_2280_, 1);
v___x_2282_ = lean_task_pure(v_a_2281_);
return v___x_2282_;
}
else
{
lean_object* v_a_2283_; 
v_a_2283_ = lean_ctor_get(v_x_2280_, 0);
lean_inc_ref(v_a_2283_);
lean_dec_ref_known(v_x_2280_, 1);
return v_a_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2284_, lean_object* v_requestStream_2285_, lean_object* v_keepAliveTimeout_2286_, lean_object* v_currentTimeout_2287_, lean_object* v_headerTimeout_2288_, lean_object* v_response_2289_, lean_object* v_respStream_2290_, uint8_t v_requiresData_2291_, lean_object* v_expectData_2292_, lean_object* v_x_2293_){
_start:
{
if (lean_obj_tag(v_x_2293_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_expectData_2292_);
lean_dec(v_respStream_2290_);
lean_dec_ref(v_response_2289_);
lean_dec(v_headerTimeout_2288_);
lean_dec(v_currentTimeout_2287_);
lean_dec(v_keepAliveTimeout_2286_);
lean_dec_ref(v_requestStream_2285_);
lean_dec_ref(v_machine_2284_);
v_a_2295_ = lean_ctor_get(v_x_2293_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_x_2293_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2297_ = v_x_2293_;
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v_x_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
else
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2314_; 
v_isSharedCheck_2314_ = !lean_is_exclusive(v_x_2293_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_x_2293_, 0);
lean_dec(v_unused_2315_);
v___x_2305_ = v_x_2293_;
v_isShared_2306_ = v_isSharedCheck_2314_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v_x_2293_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2314_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
uint8_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2307_ = 1;
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2309_, 0, v_machine_2284_);
lean_ctor_set(v___x_2309_, 1, v_requestStream_2285_);
lean_ctor_set(v___x_2309_, 2, v_keepAliveTimeout_2286_);
lean_ctor_set(v___x_2309_, 3, v_currentTimeout_2287_);
lean_ctor_set(v___x_2309_, 4, v_headerTimeout_2288_);
lean_ctor_set(v___x_2309_, 5, v_response_2289_);
lean_ctor_set(v___x_2309_, 6, v_respStream_2290_);
lean_ctor_set(v___x_2309_, 7, v_expectData_2292_);
lean_ctor_set(v___x_2309_, 8, v___x_2308_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*9, v_requiresData_2291_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*9 + 1, v___x_2307_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2309_);
v___x_2311_ = v___x_2305_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2316_, lean_object* v_requestStream_2317_, lean_object* v_keepAliveTimeout_2318_, lean_object* v_currentTimeout_2319_, lean_object* v_headerTimeout_2320_, lean_object* v_response_2321_, lean_object* v_respStream_2322_, lean_object* v_requiresData_2323_, lean_object* v_expectData_2324_, lean_object* v_x_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_requiresData_boxed_2327_; lean_object* v_res_2328_; 
v_requiresData_boxed_2327_ = lean_unbox(v_requiresData_2323_);
v_res_2328_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2316_, v_requestStream_2317_, v_keepAliveTimeout_2318_, v_currentTimeout_2319_, v_headerTimeout_2320_, v_response_2321_, v_respStream_2322_, v_requiresData_boxed_2327_, v_expectData_2324_, v_x_2325_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2329_, lean_object* v_response_2330_, lean_object* v___x_2331_, lean_object* v___f_2332_, lean_object* v_x_2333_){
_start:
{
if (lean_obj_tag(v_x_2333_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___f_2332_);
lean_dec(v___x_2331_);
lean_dec_ref(v_response_2330_);
lean_dec_ref(v_toFunctor_2329_);
v_a_2335_ = lean_ctor_get(v_x_2333_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_x_2333_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2337_ = v_x_2333_;
v_isShared_2338_ = v_isSharedCheck_2343_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v_x_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2343_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2358_; 
v_a_2344_ = lean_ctor_get(v_x_2333_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_x_2333_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2346_ = v_x_2333_;
v_isShared_2347_ = v_isSharedCheck_2358_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v_x_2333_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2358_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2348_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2348_, 0, lean_box(0));
lean_closure_set(v___x_2348_, 1, lean_box(0));
lean_closure_set(v___x_2348_, 2, v_toFunctor_2329_);
v___x_2349_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2349_, 0, lean_box(0));
lean_closure_set(v___x_2349_, 1, v_response_2330_);
v___x_2350_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2350_, 0, lean_box(0));
lean_closure_set(v___x_2350_, 1, lean_box(0));
lean_closure_set(v___x_2350_, 2, lean_box(0));
lean_closure_set(v___x_2350_, 3, v___x_2348_);
lean_closure_set(v___x_2350_, 4, v___x_2349_);
v___x_2351_ = 0;
lean_inc(v___x_2331_);
v___x_2352_ = l_BaseIO_chainTask___redArg(v_a_2344_, v___x_2350_, v___x_2331_, v___x_2351_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2352_);
v___x_2354_ = v___x_2346_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
v___x_2356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2331_, v___x_2351_, v___x_2355_, v___f_2332_);
return v___x_2356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2359_, lean_object* v_response_2360_, lean_object* v___x_2361_, lean_object* v___f_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2359_, v_response_2360_, v___x_2361_, v___f_2362_, v_x_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2367_, lean_object* v_handler_2368_, lean_object* v_extensions_2369_, lean_object* v_connectionContext_2370_, lean_object* v_state_2371_){
_start:
{
lean_object* v___x_2373_; lean_object* v_toApplicative_2374_; lean_object* v_pendingHead_2375_; 
v___x_2373_ = l_instMonadBaseIO;
v_toApplicative_2374_ = lean_ctor_get(v___x_2373_, 0);
v_pendingHead_2375_ = lean_ctor_get(v_state_2371_, 8);
lean_inc(v_pendingHead_2375_);
if (lean_obj_tag(v_pendingHead_2375_) == 1)
{
lean_object* v_toFunctor_2376_; lean_object* v_machine_2377_; lean_object* v_requestStream_2378_; lean_object* v_keepAliveTimeout_2379_; lean_object* v_currentTimeout_2380_; lean_object* v_headerTimeout_2381_; lean_object* v_response_2382_; lean_object* v_respStream_2383_; uint8_t v_requiresData_2384_; lean_object* v_expectData_2385_; lean_object* v_val_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2408_; 
v_toFunctor_2376_ = lean_ctor_get(v_toApplicative_2374_, 0);
v_machine_2377_ = lean_ctor_get(v_state_2371_, 0);
lean_inc_ref(v_machine_2377_);
v_requestStream_2378_ = lean_ctor_get(v_state_2371_, 1);
lean_inc_ref(v_requestStream_2378_);
v_keepAliveTimeout_2379_ = lean_ctor_get(v_state_2371_, 2);
lean_inc(v_keepAliveTimeout_2379_);
v_currentTimeout_2380_ = lean_ctor_get(v_state_2371_, 3);
lean_inc(v_currentTimeout_2380_);
v_headerTimeout_2381_ = lean_ctor_get(v_state_2371_, 4);
lean_inc(v_headerTimeout_2381_);
v_response_2382_ = lean_ctor_get(v_state_2371_, 5);
lean_inc_ref(v_response_2382_);
v_respStream_2383_ = lean_ctor_get(v_state_2371_, 6);
lean_inc(v_respStream_2383_);
v_requiresData_2384_ = lean_ctor_get_uint8(v_state_2371_, sizeof(void*)*9);
v_expectData_2385_ = lean_ctor_get(v_state_2371_, 7);
lean_inc(v_expectData_2385_);
lean_dec_ref(v_state_2371_);
v_val_2386_ = lean_ctor_get(v_pendingHead_2375_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_pendingHead_2375_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2388_ = v_pendingHead_2375_;
v_isShared_2389_ = v_isSharedCheck_2408_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_val_2386_);
lean_dec(v_pendingHead_2375_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2408_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_onRequest_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v_onRequest_2390_ = lean_ctor_get(v_inst_2367_, 1);
lean_inc_ref(v_onRequest_2390_);
lean_dec_ref(v_inst_2367_);
v___f_2391_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2392_ = lean_box(v_requiresData_2384_);
lean_inc_ref(v_response_2382_);
lean_inc_ref(v_requestStream_2378_);
v___f_2393_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2393_, 0, v_machine_2377_);
lean_closure_set(v___f_2393_, 1, v_requestStream_2378_);
lean_closure_set(v___f_2393_, 2, v_keepAliveTimeout_2379_);
lean_closure_set(v___f_2393_, 3, v_currentTimeout_2380_);
lean_closure_set(v___f_2393_, 4, v_headerTimeout_2381_);
lean_closure_set(v___f_2393_, 5, v_response_2382_);
lean_closure_set(v___f_2393_, 6, v_respStream_2383_);
lean_closure_set(v___f_2393_, 7, v___x_2392_);
lean_closure_set(v___f_2393_, 8, v_expectData_2385_);
v___x_2394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2394_, 0, v_val_2386_);
lean_ctor_set(v___x_2394_, 1, v_requestStream_2378_);
lean_ctor_set(v___x_2394_, 2, v_extensions_2369_);
v___x_2395_ = lean_apply_3(v_onRequest_2390_, v_handler_2368_, v___x_2394_, v_connectionContext_2370_);
v___x_2396_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2376_);
v___f_2397_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2397_, 0, v_toFunctor_2376_);
lean_closure_set(v___f_2397_, 1, v_response_2382_);
lean_closure_set(v___f_2397_, 2, v___x_2396_);
lean_closure_set(v___f_2397_, 3, v___f_2393_);
v___x_2398_ = 0;
v___x_2399_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2399_, 0, lean_box(0));
lean_closure_set(v___x_2399_, 1, v___x_2395_);
v___x_2400_ = lean_io_as_task(v___x_2399_, v___x_2396_);
v___x_2401_ = 1;
v___x_2402_ = lean_task_bind(v___x_2400_, v___f_2391_, v___x_2396_, v___x_2401_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2402_);
v___x_2404_ = v___x_2388_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
v___x_2406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2396_, v___x_2398_, v___x_2405_, v___f_2397_);
return v___x_2406_;
}
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v_pendingHead_2375_);
lean_dec_ref(v_connectionContext_2370_);
lean_dec(v_extensions_2369_);
lean_dec(v_handler_2368_);
lean_dec_ref(v_inst_2367_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_state_2371_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2411_, lean_object* v_handler_2412_, lean_object* v_extensions_2413_, lean_object* v_connectionContext_2414_, lean_object* v_state_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2411_, v_handler_2412_, v_extensions_2413_, v_connectionContext_2414_, v_state_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2418_, lean_object* v_inst_2419_, lean_object* v_handler_2420_, lean_object* v_extensions_2421_, lean_object* v_connectionContext_2422_, lean_object* v_state_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2419_, v_handler_2420_, v_extensions_2421_, v_connectionContext_2422_, v_state_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2426_, lean_object* v_inst_2427_, lean_object* v_handler_2428_, lean_object* v_extensions_2429_, lean_object* v_connectionContext_2430_, lean_object* v_state_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2426_, v_inst_2427_, v_handler_2428_, v_extensions_2429_, v_connectionContext_2430_, v_state_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2434_, lean_object* v_____r_2435_){
_start:
{
lean_object* v_writer_2437_; lean_object* v_reader_2438_; lean_object* v_config_2439_; lean_object* v_events_2440_; lean_object* v_error_2441_; lean_object* v_instant_2442_; uint8_t v_keepAlive_2443_; uint8_t v_forcedFlush_2444_; uint8_t v_pullBodyStalled_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2472_; 
v_writer_2437_ = lean_ctor_get(v_machine_2434_, 1);
v_reader_2438_ = lean_ctor_get(v_machine_2434_, 0);
v_config_2439_ = lean_ctor_get(v_machine_2434_, 2);
v_events_2440_ = lean_ctor_get(v_machine_2434_, 3);
v_error_2441_ = lean_ctor_get(v_machine_2434_, 4);
v_instant_2442_ = lean_ctor_get(v_machine_2434_, 5);
v_keepAlive_2443_ = lean_ctor_get_uint8(v_machine_2434_, sizeof(void*)*6);
v_forcedFlush_2444_ = lean_ctor_get_uint8(v_machine_2434_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2445_ = lean_ctor_get_uint8(v_machine_2434_, sizeof(void*)*6 + 2);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_machine_2434_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2447_ = v_machine_2434_;
v_isShared_2448_ = v_isSharedCheck_2472_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_instant_2442_);
lean_inc(v_error_2441_);
lean_inc(v_events_2440_);
lean_inc(v_config_2439_);
lean_inc(v_writer_2437_);
lean_inc(v_reader_2438_);
lean_dec(v_machine_2434_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2472_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v_userData_2449_; lean_object* v_outputData_2450_; lean_object* v_state_2451_; lean_object* v_knownSize_2452_; lean_object* v_messageHead_2453_; uint8_t v_sentMessage_2454_; uint8_t v_omitBody_2455_; lean_object* v_userDataBytes_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2471_; 
v_userData_2449_ = lean_ctor_get(v_writer_2437_, 0);
v_outputData_2450_ = lean_ctor_get(v_writer_2437_, 1);
v_state_2451_ = lean_ctor_get(v_writer_2437_, 2);
v_knownSize_2452_ = lean_ctor_get(v_writer_2437_, 3);
v_messageHead_2453_ = lean_ctor_get(v_writer_2437_, 4);
v_sentMessage_2454_ = lean_ctor_get_uint8(v_writer_2437_, sizeof(void*)*6);
v_omitBody_2455_ = lean_ctor_get_uint8(v_writer_2437_, sizeof(void*)*6 + 2);
v_userDataBytes_2456_ = lean_ctor_get(v_writer_2437_, 5);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_writer_2437_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2458_ = v_writer_2437_;
v_isShared_2459_ = v_isSharedCheck_2471_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_userDataBytes_2456_);
lean_inc(v_messageHead_2453_);
lean_inc(v_knownSize_2452_);
lean_inc(v_state_2451_);
lean_inc(v_outputData_2450_);
lean_inc(v_userData_2449_);
lean_dec(v_writer_2437_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2471_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
uint8_t v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = 1;
if (v_isShared_2459_ == 0)
{
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_userData_2449_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_outputData_2450_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_state_2451_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_knownSize_2452_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_messageHead_2453_);
lean_ctor_set(v_reuseFailAlloc_2470_, 5, v_userDataBytes_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*6, v_sentMessage_2454_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*6 + 2, v_omitBody_2455_);
v___x_2462_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2464_; 
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*6 + 1, v___x_2460_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v___x_2462_);
v___x_2464_ = v___x_2447_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_reader_2438_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_config_2439_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_events_2440_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_error_2441_);
lean_ctor_set(v_reuseFailAlloc_2469_, 5, v_instant_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2469_, sizeof(void*)*6, v_keepAlive_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2469_, sizeof(void*)*6 + 1, v_forcedFlush_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2469_, sizeof(void*)*6 + 2, v_pullBodyStalled_2445_);
v___x_2464_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2473_, lean_object* v_____r_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2473_, v_____r_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2477_, lean_object* v_x2_2478_){
_start:
{
lean_object* v_data_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_data_2479_ = lean_ctor_get(v_x2_2478_, 0);
v___x_2480_ = lean_byte_array_size(v_data_2479_);
v___x_2481_ = lean_nat_add(v_x1_2477_, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2482_, lean_object* v_x2_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2482_, v_x2_2483_);
lean_dec_ref(v_x2_2483_);
lean_dec(v_x1_2482_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2485_, lean_object* v_machine_2486_, lean_object* v_isClosed_2487_, lean_object* v___f_2488_, lean_object* v___f_2489_, lean_object* v_x_2490_){
_start:
{
lean_object* v___y_2493_; 
if (lean_obj_tag(v_x_2490_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2506_; 
lean_dec_ref(v___f_2489_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v_isClosed_2487_);
lean_dec_ref(v_machine_2486_);
lean_dec(v_body_2485_);
v_a_2498_ = lean_ctor_get(v_x_2490_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_x_2490_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2500_ = v_x_2490_;
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v_x_2490_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2570_; 
v_a_2507_ = lean_ctor_get(v_x_2490_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_x_2490_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2509_ = v_x_2490_;
v_isShared_2510_ = v_isSharedCheck_2570_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v_x_2490_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2570_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
if (lean_obj_tag(v_a_2507_) == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
lean_dec_ref(v___f_2489_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v_isClosed_2487_);
v___x_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_body_2485_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_machine_2486_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2512_);
v___x_2514_ = v___x_2509_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
return v___x_2515_;
}
}
else
{
lean_object* v_val_2517_; 
lean_del_object(v___x_2509_);
v_val_2517_ = lean_ctor_get(v_a_2507_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v_a_2507_, 1);
if (lean_obj_tag(v_val_2517_) == 0)
{
lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v___f_2489_);
lean_dec_ref(v_machine_2486_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = 0;
v___x_2520_ = lean_apply_2(v_isClosed_2487_, v_body_2485_, lean_box(0));
v___x_2521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2518_, v___x_2519_, v___x_2520_, v___f_2488_);
return v___x_2521_;
}
else
{
lean_object* v_val_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
lean_dec_ref(v___f_2488_);
lean_dec_ref(v_isClosed_2487_);
v_val_2522_ = lean_ctor_get(v_val_2517_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v_val_2517_, 1);
v___x_2523_ = lean_unsigned_to_nat(1u);
v___x_2524_ = lean_mk_empty_array_with_capacity(v___x_2523_);
v___x_2525_ = lean_array_push(v___x_2524_, v_val_2522_);
v___x_2526_ = lean_array_get_size(v___x_2525_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_nat_dec_eq(v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v_reader_2529_; lean_object* v_writer_2530_; lean_object* v_config_2531_; lean_object* v_events_2532_; lean_object* v_error_2533_; lean_object* v_instant_2534_; uint8_t v_keepAlive_2535_; uint8_t v_forcedFlush_2536_; uint8_t v_pullBodyStalled_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2569_; 
v_reader_2529_ = lean_ctor_get(v_machine_2486_, 0);
v_writer_2530_ = lean_ctor_get(v_machine_2486_, 1);
v_config_2531_ = lean_ctor_get(v_machine_2486_, 2);
v_events_2532_ = lean_ctor_get(v_machine_2486_, 3);
v_error_2533_ = lean_ctor_get(v_machine_2486_, 4);
v_instant_2534_ = lean_ctor_get(v_machine_2486_, 5);
v_keepAlive_2535_ = lean_ctor_get_uint8(v_machine_2486_, sizeof(void*)*6);
v_forcedFlush_2536_ = lean_ctor_get_uint8(v_machine_2486_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2537_ = lean_ctor_get_uint8(v_machine_2486_, sizeof(void*)*6 + 2);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_machine_2486_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2539_ = v_machine_2486_;
v_isShared_2540_ = v_isSharedCheck_2569_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_instant_2534_);
lean_inc(v_error_2533_);
lean_inc(v_events_2532_);
lean_inc(v_config_2531_);
lean_inc(v_writer_2530_);
lean_inc(v_reader_2529_);
lean_dec(v_machine_2486_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2569_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___y_2542_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_2565_ = lean_nat_dec_lt(v___x_2527_, v___x_2526_);
if (v___x_2565_ == 0)
{
lean_dec_ref(v___f_2489_);
v___y_2542_ = v___x_2527_;
goto v___jp_2541_;
}
else
{
size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = lean_usize_of_nat(v___x_2526_);
lean_inc_ref(v___x_2525_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2564_, v___f_2489_, v___x_2525_, v___x_2566_, v___x_2567_, v___x_2527_);
v___y_2542_ = v___x_2568_;
goto v___jp_2541_;
}
v___jp_2541_:
{
lean_object* v_userData_2543_; lean_object* v_outputData_2544_; lean_object* v_state_2545_; lean_object* v_knownSize_2546_; lean_object* v_messageHead_2547_; uint8_t v_sentMessage_2548_; uint8_t v_userClosedBody_2549_; uint8_t v_omitBody_2550_; lean_object* v_userDataBytes_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2563_; 
v_userData_2543_ = lean_ctor_get(v_writer_2530_, 0);
v_outputData_2544_ = lean_ctor_get(v_writer_2530_, 1);
v_state_2545_ = lean_ctor_get(v_writer_2530_, 2);
v_knownSize_2546_ = lean_ctor_get(v_writer_2530_, 3);
v_messageHead_2547_ = lean_ctor_get(v_writer_2530_, 4);
v_sentMessage_2548_ = lean_ctor_get_uint8(v_writer_2530_, sizeof(void*)*6);
v_userClosedBody_2549_ = lean_ctor_get_uint8(v_writer_2530_, sizeof(void*)*6 + 1);
v_omitBody_2550_ = lean_ctor_get_uint8(v_writer_2530_, sizeof(void*)*6 + 2);
v_userDataBytes_2551_ = lean_ctor_get(v_writer_2530_, 5);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_writer_2530_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2553_ = v_writer_2530_;
v_isShared_2554_ = v_isSharedCheck_2563_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_userDataBytes_2551_);
lean_inc(v_messageHead_2547_);
lean_inc(v_knownSize_2546_);
lean_inc(v_state_2545_);
lean_inc(v_outputData_2544_);
lean_inc(v_userData_2543_);
lean_dec(v_writer_2530_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2563_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2555_ = l_Array_append___redArg(v_userData_2543_, v___x_2525_);
lean_dec_ref(v___x_2525_);
v___x_2556_ = lean_nat_add(v_userDataBytes_2551_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec(v_userDataBytes_2551_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 5, v___x_2556_);
lean_ctor_set(v___x_2553_, 0, v___x_2555_);
v___x_2558_ = v___x_2553_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_outputData_2544_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_state_2545_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_knownSize_2546_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_messageHead_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v___x_2556_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*6, v_sentMessage_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*6 + 1, v_userClosedBody_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*6 + 2, v_omitBody_2550_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2558_);
v___x_2560_ = v___x_2539_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_reader_2529_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_config_2531_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_events_2532_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_error_2533_);
lean_ctor_set(v_reuseFailAlloc_2561_, 5, v_instant_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*6, v_keepAlive_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*6 + 1, v_forcedFlush_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*6 + 2, v_pullBodyStalled_2537_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v___y_2493_ = v___x_2560_;
goto v___jp_2492_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___f_2489_);
v___y_2493_ = v_machine_2486_;
goto v___jp_2492_;
}
}
}
}
}
v___jp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_body_2485_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2571_, lean_object* v_machine_2572_, lean_object* v_isClosed_2573_, lean_object* v___f_2574_, lean_object* v___f_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2571_, v_machine_2572_, v_isClosed_2573_, v___f_2574_, v___f_2575_, v_x_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2580_, lean_object* v_machine_2581_, lean_object* v_body_2582_){
_start:
{
lean_object* v_close_2584_; lean_object* v_isClosed_2585_; lean_object* v_tryRecv_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___f_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_close_2584_ = lean_ctor_get(v_inst_2580_, 1);
lean_inc_ref(v_close_2584_);
v_isClosed_2585_ = lean_ctor_get(v_inst_2580_, 2);
lean_inc_ref(v_isClosed_2585_);
v_tryRecv_2586_ = lean_ctor_get(v_inst_2580_, 4);
lean_inc_ref(v_tryRecv_2586_);
lean_dec_ref(v_inst_2580_);
lean_inc_ref(v_machine_2581_);
v___f_2587_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2587_, 0, v_machine_2581_);
lean_inc_ref(v___f_2587_);
v___f_2588_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2588_, 0, v___f_2587_);
lean_inc_n(v_body_2582_, 2);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2589_, 0, v_close_2584_);
lean_closure_set(v___f_2589_, 1, v_body_2582_);
lean_closure_set(v___f_2589_, 2, v___f_2588_);
lean_closure_set(v___f_2589_, 3, v___f_2587_);
v___f_2590_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2591_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2591_, 0, v_body_2582_);
lean_closure_set(v___f_2591_, 1, v_machine_2581_);
lean_closure_set(v___f_2591_, 2, v_isClosed_2585_);
lean_closure_set(v___f_2591_, 3, v___f_2589_);
lean_closure_set(v___f_2591_, 4, v___f_2590_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = 0;
v___x_2594_ = lean_apply_2(v_tryRecv_2586_, v_body_2582_, lean_box(0));
v___x_2595_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2592_, v___x_2593_, v___x_2594_, v___f_2591_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2596_, lean_object* v_machine_2597_, lean_object* v_body_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2596_, v_machine_2597_, v_body_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2601_, lean_object* v_inst_2602_, lean_object* v_machine_2603_, lean_object* v_body_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2602_, v_machine_2603_, v_body_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2607_, lean_object* v_inst_2608_, lean_object* v_machine_2609_, lean_object* v_body_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2607_, v_inst_2608_, v_machine_2609_, v_body_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2619_, lean_object* v_____r_2620_, lean_object* v_st_2621_){
_start:
{
lean_object* v_machine_2623_; lean_object* v_requestStream_2624_; lean_object* v_keepAliveTimeout_2625_; lean_object* v_currentTimeout_2626_; lean_object* v_headerTimeout_2627_; lean_object* v_response_2628_; lean_object* v_respStream_2629_; uint8_t v_requiresData_2630_; lean_object* v_expectData_2631_; uint8_t v_handlerDispatched_2632_; lean_object* v_pendingHead_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2715_; 
v_machine_2623_ = lean_ctor_get(v_st_2621_, 0);
v_requestStream_2624_ = lean_ctor_get(v_st_2621_, 1);
v_keepAliveTimeout_2625_ = lean_ctor_get(v_st_2621_, 2);
v_currentTimeout_2626_ = lean_ctor_get(v_st_2621_, 3);
v_headerTimeout_2627_ = lean_ctor_get(v_st_2621_, 4);
v_response_2628_ = lean_ctor_get(v_st_2621_, 5);
v_respStream_2629_ = lean_ctor_get(v_st_2621_, 6);
v_requiresData_2630_ = lean_ctor_get_uint8(v_st_2621_, sizeof(void*)*9);
v_expectData_2631_ = lean_ctor_get(v_st_2621_, 7);
v_handlerDispatched_2632_ = lean_ctor_get_uint8(v_st_2621_, sizeof(void*)*9 + 1);
v_pendingHead_2633_ = lean_ctor_get(v_st_2621_, 8);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_st_2621_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2635_ = v_st_2621_;
v_isShared_2636_ = v_isSharedCheck_2715_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_pendingHead_2633_);
lean_inc(v_expectData_2631_);
lean_inc(v_respStream_2629_);
lean_inc(v_response_2628_);
lean_inc(v_headerTimeout_2627_);
lean_inc(v_currentTimeout_2626_);
lean_inc(v_keepAliveTimeout_2625_);
lean_inc(v_requestStream_2624_);
lean_inc(v_machine_2623_);
lean_dec(v_st_2621_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2715_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___y_2638_; lean_object* v_reader_2647_; lean_object* v_state_2648_; 
v_reader_2647_ = lean_ctor_get(v_machine_2623_, 0);
lean_inc_ref(v_reader_2647_);
v_state_2648_ = lean_ctor_get(v_reader_2647_, 0);
lean_inc(v_state_2648_);
if (lean_obj_tag(v_state_2648_) == 6)
{
lean_dec_ref(v_reader_2647_);
lean_dec_ref(v_val_2619_);
v___y_2638_ = v_machine_2623_;
goto v___jp_2637_;
}
else
{
if (lean_obj_tag(v_state_2648_) == 7)
{
lean_dec_ref_known(v_state_2648_, 1);
lean_dec_ref(v_reader_2647_);
lean_dec_ref(v_val_2619_);
v___y_2638_ = v_machine_2623_;
goto v___jp_2637_;
}
else
{
lean_object* v_input_2649_; lean_object* v_writer_2650_; lean_object* v_config_2651_; lean_object* v_events_2652_; lean_object* v_error_2653_; lean_object* v_instant_2654_; uint8_t v_keepAlive_2655_; uint8_t v_forcedFlush_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2713_; 
v_input_2649_ = lean_ctor_get(v_reader_2647_, 1);
lean_inc_ref(v_input_2649_);
v_writer_2650_ = lean_ctor_get(v_machine_2623_, 1);
v_config_2651_ = lean_ctor_get(v_machine_2623_, 2);
v_events_2652_ = lean_ctor_get(v_machine_2623_, 3);
v_error_2653_ = lean_ctor_get(v_machine_2623_, 4);
v_instant_2654_ = lean_ctor_get(v_machine_2623_, 5);
v_keepAlive_2655_ = lean_ctor_get_uint8(v_machine_2623_, sizeof(void*)*6);
v_forcedFlush_2656_ = lean_ctor_get_uint8(v_machine_2623_, sizeof(void*)*6 + 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_machine_2623_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; 
v_unused_2714_ = lean_ctor_get(v_machine_2623_, 0);
lean_dec(v_unused_2714_);
v___x_2658_ = v_machine_2623_;
v_isShared_2659_ = v_isSharedCheck_2713_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_instant_2654_);
lean_inc(v_error_2653_);
lean_inc(v_events_2652_);
lean_inc(v_config_2651_);
lean_inc(v_writer_2650_);
lean_dec(v_machine_2623_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2713_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_messageHead_2660_; lean_object* v_messageCount_2661_; lean_object* v_bodyBytesRead_2662_; lean_object* v_headerBytesRead_2663_; uint8_t v_noMoreInput_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2710_; 
v_messageHead_2660_ = lean_ctor_get(v_reader_2647_, 2);
v_messageCount_2661_ = lean_ctor_get(v_reader_2647_, 3);
v_bodyBytesRead_2662_ = lean_ctor_get(v_reader_2647_, 4);
v_headerBytesRead_2663_ = lean_ctor_get(v_reader_2647_, 5);
v_noMoreInput_2664_ = lean_ctor_get_uint8(v_reader_2647_, sizeof(void*)*6);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_reader_2647_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2711_ = lean_ctor_get(v_reader_2647_, 1);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_reader_2647_, 0);
lean_dec(v_unused_2712_);
v___x_2666_ = v_reader_2647_;
v_isShared_2667_ = v_isSharedCheck_2710_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_headerBytesRead_2663_);
lean_inc(v_bodyBytesRead_2662_);
lean_inc(v_messageCount_2661_);
lean_inc(v_messageHead_2660_);
lean_dec(v_reader_2647_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2710_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_array_2668_; lean_object* v_idx_2669_; uint8_t v___x_2670_; lean_object* v___y_2672_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_array_2668_ = lean_ctor_get(v_input_2649_, 0);
lean_inc_ref(v_array_2668_);
v_idx_2669_ = lean_ctor_get(v_input_2649_, 1);
lean_inc(v_idx_2669_);
lean_dec_ref(v_input_2649_);
v___x_2670_ = 0;
v___x_2701_ = lean_byte_array_size(v_array_2668_);
v___x_2702_ = lean_nat_dec_le(v___x_2701_, v_idx_2669_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2703_ = l_ByteArray_extract(v_array_2668_, v_idx_2669_, v___x_2701_);
lean_dec_ref(v_array_2668_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_byte_array_size(v___x_2703_);
v___x_2706_ = lean_byte_array_size(v_val_2619_);
v___x_2707_ = lean_byte_array_copy_slice(v_val_2619_, v___x_2704_, v___x_2703_, v___x_2705_, v___x_2706_, v___x_2702_);
lean_dec_ref(v_val_2619_);
v___x_2708_ = l_ByteArray_mkIterator(v___x_2707_);
v___y_2672_ = v___x_2708_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_idx_2669_);
lean_dec_ref(v_array_2668_);
v___x_2709_ = l_ByteArray_mkIterator(v_val_2619_);
v___y_2672_ = v___x_2709_;
goto v___jp_2671_;
}
v___jp_2671_:
{
lean_object* v_maxHeaderBytes_2673_; lean_object* v_maxStartLineLength_2674_; lean_object* v_maxChunkLineLength_2675_; lean_object* v_maxBodySize_2676_; lean_object* v_array_2677_; lean_object* v_idx_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_maxHeaderBytes_2673_ = lean_ctor_get(v_config_2651_, 2);
v_maxStartLineLength_2674_ = lean_ctor_get(v_config_2651_, 5);
v_maxChunkLineLength_2675_ = lean_ctor_get(v_config_2651_, 13);
v_maxBodySize_2676_ = lean_ctor_get(v_config_2651_, 15);
v_array_2677_ = lean_ctor_get(v___y_2672_, 0);
v_idx_2678_ = lean_ctor_get(v___y_2672_, 1);
v___x_2679_ = lean_nat_add(v_maxBodySize_2676_, v_maxHeaderBytes_2673_);
v___x_2680_ = lean_nat_add(v___x_2679_, v_maxStartLineLength_2674_);
lean_dec(v___x_2679_);
v___x_2681_ = lean_nat_add(v___x_2680_, v_maxChunkLineLength_2675_);
lean_dec(v___x_2680_);
v___x_2682_ = lean_byte_array_size(v_array_2677_);
v___x_2683_ = lean_nat_sub(v___x_2682_, v_idx_2678_);
v___x_2684_ = lean_nat_dec_lt(v___x_2681_, v___x_2683_);
lean_dec(v___x_2683_);
lean_dec(v___x_2681_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2686_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___y_2672_);
v___x_2686_ = v___x_2666_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_state_2648_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___y_2672_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_messageHead_2660_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_messageCount_2661_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_bodyBytesRead_2662_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v_headerBytesRead_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2690_, sizeof(void*)*6, v_noMoreInput_2664_);
v___x_2686_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v_machine_2688_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2686_);
v_machine_2688_ = v___x_2658_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_writer_2650_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v_config_2651_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v_events_2652_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v_error_2653_);
lean_ctor_set(v_reuseFailAlloc_2689_, 5, v_instant_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2689_, sizeof(void*)*6, v_keepAlive_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2689_, sizeof(void*)*6 + 1, v_forcedFlush_2656_);
v_machine_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_ctor_set_uint8(v_machine_2688_, sizeof(void*)*6 + 2, v___x_2670_);
v___y_2638_ = v_machine_2688_;
goto v___jp_2637_;
}
}
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec(v_error_2653_);
lean_dec(v_state_2648_);
v___x_2691_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2692_ = lean_array_push(v_events_2652_, v___x_2691_);
v___x_2693_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___y_2672_);
lean_ctor_set(v___x_2666_, 0, v___x_2693_);
v___x_2695_ = v___x_2666_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___y_2672_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_messageHead_2660_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_messageCount_2661_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_bodyBytesRead_2662_);
lean_ctor_set(v_reuseFailAlloc_2700_, 5, v_headerBytesRead_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, sizeof(void*)*6, v_noMoreInput_2664_);
v___x_2695_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 4, v___x_2696_);
lean_ctor_set(v___x_2658_, 3, v___x_2692_);
lean_ctor_set(v___x_2658_, 0, v___x_2695_);
v___x_2698_ = v___x_2658_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_writer_2650_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_config_2651_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2699_, 5, v_instant_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2699_, sizeof(void*)*6, v_keepAlive_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2699_, sizeof(void*)*6 + 1, v_forcedFlush_2656_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*6 + 2, v___x_2670_);
v___y_2638_ = v___x_2698_;
goto v___jp_2637_;
}
}
}
}
}
}
}
}
v___jp_2637_:
{
lean_object* v___x_2640_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___y_2638_);
v___x_2640_ = v___x_2635_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___y_2638_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_requestStream_2624_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_keepAliveTimeout_2625_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_currentTimeout_2626_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v_headerTimeout_2627_);
lean_ctor_set(v_reuseFailAlloc_2646_, 5, v_response_2628_);
lean_ctor_set(v_reuseFailAlloc_2646_, 6, v_respStream_2629_);
lean_ctor_set(v_reuseFailAlloc_2646_, 7, v_expectData_2631_);
lean_ctor_set(v_reuseFailAlloc_2646_, 8, v_pendingHead_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*9, v_requiresData_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*9 + 1, v_handlerDispatched_2632_);
v___x_2640_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2641_ = 0;
v___x_2642_ = lean_box(v___x_2641_);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2640_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
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
lean_object* v___x_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_6684__overap_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
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
v___x_6684__overap_2972_ = l_Std_Mutex_atomically___redArg(v___x_2967_, v___f_2968_, v___f_2969_, v_requestStream_2950_, v___x_2971_);
v___x_2973_ = lean_apply_1(v___x_6684__overap_2972_, lean_box(0));
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
uint8_t v_requiresData_boxed_3129_; uint8_t v___x_7494__boxed_3130_; lean_object* v_res_3131_; 
v_requiresData_boxed_3129_ = lean_unbox(v_requiresData_3123_);
v___x_7494__boxed_3130_ = lean_unbox(v___x_3125_);
v_res_3131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3118_, v_keepAliveTimeout_3119_, v_currentTimeout_3120_, v_headerTimeout_3121_, v_response_3122_, v_requiresData_boxed_3129_, v_expectData_3124_, v___x_7494__boxed_3130_, v_pendingHead_3126_, v_____x_3127_);
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
uint8_t v___x_7562__boxed_3185_; lean_object* v_res_3186_; 
v___x_7562__boxed_3185_ = lean_unbox(v___x_3182_);
v_res_3186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7562__boxed_3185_, v_x_3183_);
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
uint8_t v___x_7630__boxed_3218_; lean_object* v_res_3219_; 
v___x_7630__boxed_3218_ = lean_unbox(v___x_3214_);
v_res_3219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3213_, v___x_7630__boxed_3218_, v_fst_3215_, v_x_3216_);
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
uint8_t v___x_7688__boxed_3238_; lean_object* v_res_3239_; 
v___x_7688__boxed_3238_ = lean_unbox(v___x_3234_);
v_res_3239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3232_, v_handler_3233_, v___x_7688__boxed_3238_, v___f_3235_, v_x_3236_);
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
uint8_t v___x_7713__boxed_3303_; uint8_t v___x_7715__boxed_3304_; lean_object* v_res_3305_; 
v___x_7713__boxed_3303_ = lean_unbox(v___x_3293_);
v___x_7715__boxed_3304_ = lean_unbox(v___x_3295_);
v_res_3305_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_7713__boxed_3303_, v___f_3294_, v___x_7715__boxed_3304_, v_inst_3296_, v_handler_3297_, v_inst_3298_, v___f_3299_, v___f_3300_, v_x_3301_);
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
v___x_3576_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3770_, uint8_t v_handlerDispatched_3771_, lean_object* v_keepAliveTimeout_3772_, lean_object* v_headerTimeout_3773_, lean_object* v_expectData_3774_, lean_object* v_respStream_3775_, lean_object* v_currentTimeout_3776_, lean_object* v_response_3777_, lean_object* v_socket_3778_, uint8_t v_requiresData_3779_, uint8_t v_sentMessage_3780_, lean_object* v_reader_3781_, uint8_t v_requestBodyInterested_3782_, lean_object* v_requestBody_3783_){
_start:
{
lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3797_; 
if (v_requiresData_3779_ == 0)
{
if (v_handlerDispatched_3771_ == 0)
{
goto v___jp_3800_;
}
else
{
if (lean_obj_tag(v_respStream_3775_) == 0)
{
if (v_sentMessage_3780_ == 0)
{
lean_object* v_state_3804_; 
v_state_3804_ = lean_ctor_get(v_reader_3781_, 0);
if (lean_obj_tag(v_state_3804_) == 2)
{
if (v_requestBodyInterested_3782_ == 0)
{
lean_dec(v_socket_3778_);
goto v___jp_3802_;
}
else
{
goto v___jp_3800_;
}
}
else
{
lean_dec(v_socket_3778_);
goto v___jp_3802_;
}
}
else
{
goto v___jp_3800_;
}
}
else
{
goto v___jp_3800_;
}
}
}
else
{
goto v___jp_3800_;
}
v___jp_3785_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3793_, 0, v___y_3787_);
lean_ctor_set(v___x_3793_, 1, v___y_3789_);
lean_ctor_set(v___x_3793_, 2, v___y_3792_);
lean_ctor_set(v___x_3793_, 3, v___y_3790_);
lean_ctor_set(v___x_3793_, 4, v_requestBody_3783_);
lean_ctor_set(v___x_3793_, 5, v___y_3791_);
lean_ctor_set(v___x_3793_, 6, v___y_3786_);
lean_ctor_set(v___x_3793_, 7, v___y_3788_);
lean_ctor_set(v___x_3793_, 8, v_connectionContext_3770_);
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
return v___x_3795_;
}
v___jp_3796_:
{
if (v_handlerDispatched_3771_ == 0)
{
lean_object* v___x_3798_; 
lean_dec_ref(v_response_3777_);
v___x_3798_ = lean_box(0);
v___y_3786_ = v_keepAliveTimeout_3772_;
v___y_3787_ = v___y_3797_;
v___y_3788_ = v_headerTimeout_3773_;
v___y_3789_ = v_expectData_3774_;
v___y_3790_ = v_respStream_3775_;
v___y_3791_ = v_currentTimeout_3776_;
v___y_3792_ = v___x_3798_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_response_3777_);
v___y_3786_ = v_keepAliveTimeout_3772_;
v___y_3787_ = v___y_3797_;
v___y_3788_ = v_headerTimeout_3773_;
v___y_3789_ = v_expectData_3774_;
v___y_3790_ = v_respStream_3775_;
v___y_3791_ = v_currentTimeout_3776_;
v___y_3792_ = v___x_3799_;
goto v___jp_3785_;
}
}
v___jp_3800_:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3801_, 0, v_socket_3778_);
v___y_3797_ = v___x_3801_;
goto v___jp_3796_;
}
v___jp_3802_:
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_box(0);
v___y_3797_ = v___x_3803_;
goto v___jp_3796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3805_, lean_object* v_handlerDispatched_3806_, lean_object* v_keepAliveTimeout_3807_, lean_object* v_headerTimeout_3808_, lean_object* v_expectData_3809_, lean_object* v_respStream_3810_, lean_object* v_currentTimeout_3811_, lean_object* v_response_3812_, lean_object* v_socket_3813_, lean_object* v_requiresData_3814_, lean_object* v_sentMessage_3815_, lean_object* v_reader_3816_, lean_object* v_requestBodyInterested_3817_, lean_object* v_requestBody_3818_, lean_object* v___y_3819_){
_start:
{
uint8_t v_handlerDispatched_boxed_3820_; uint8_t v_requiresData_boxed_3821_; uint8_t v_sentMessage_boxed_3822_; uint8_t v_requestBodyInterested_boxed_3823_; lean_object* v_res_3824_; 
v_handlerDispatched_boxed_3820_ = lean_unbox(v_handlerDispatched_3806_);
v_requiresData_boxed_3821_ = lean_unbox(v_requiresData_3814_);
v_sentMessage_boxed_3822_ = lean_unbox(v_sentMessage_3815_);
v_requestBodyInterested_boxed_3823_ = lean_unbox(v_requestBodyInterested_3817_);
v_res_3824_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3805_, v_handlerDispatched_boxed_3820_, v_keepAliveTimeout_3807_, v_headerTimeout_3808_, v_expectData_3809_, v_respStream_3810_, v_currentTimeout_3811_, v_response_3812_, v_socket_3813_, v_requiresData_boxed_3821_, v_sentMessage_boxed_3822_, v_reader_3816_, v_requestBodyInterested_boxed_3823_, v_requestBody_3818_);
lean_dec_ref(v_reader_3816_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3825_, lean_object* v_x_3826_){
_start:
{
if (lean_obj_tag(v_x_3826_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v___f_3825_);
v_a_3828_ = lean_ctor_get(v_x_3826_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_x_3826_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3830_ = v_x_3826_;
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v_x_3826_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3838_; 
v_a_3837_ = lean_ctor_get(v_x_3826_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v_x_3826_, 1);
v___x_3838_ = lean_apply_2(v___f_3825_, v_a_3837_, lean_box(0));
return v___x_3838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3839_, lean_object* v_x_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3839_, v_x_3840_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3847_, uint8_t v_handlerDispatched_3848_, lean_object* v_keepAliveTimeout_3849_, lean_object* v_headerTimeout_3850_, lean_object* v_expectData_3851_, lean_object* v_respStream_3852_, lean_object* v_currentTimeout_3853_, lean_object* v_response_3854_, lean_object* v_socket_3855_, uint8_t v_requiresData_3856_, uint8_t v_sentMessage_3857_, lean_object* v_reader_3858_, uint8_t v_pullBodyStalled_3859_, uint8_t v_requestBodyOpen_3860_, lean_object* v_requestStream_3861_, uint8_t v_requestBodyInterested_3862_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___f_3868_; lean_object* v___f_3869_; uint8_t v___y_3871_; 
v___x_3864_ = lean_box(v_handlerDispatched_3848_);
v___x_3865_ = lean_box(v_requiresData_3856_);
v___x_3866_ = lean_box(v_sentMessage_3857_);
v___x_3867_ = lean_box(v_requestBodyInterested_3862_);
lean_inc_ref(v_reader_3858_);
v___f_3868_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3868_, 0, v_connectionContext_3847_);
lean_closure_set(v___f_3868_, 1, v___x_3864_);
lean_closure_set(v___f_3868_, 2, v_keepAliveTimeout_3849_);
lean_closure_set(v___f_3868_, 3, v_headerTimeout_3850_);
lean_closure_set(v___f_3868_, 4, v_expectData_3851_);
lean_closure_set(v___f_3868_, 5, v_respStream_3852_);
lean_closure_set(v___f_3868_, 6, v_currentTimeout_3853_);
lean_closure_set(v___f_3868_, 7, v_response_3854_);
lean_closure_set(v___f_3868_, 8, v_socket_3855_);
lean_closure_set(v___f_3868_, 9, v___x_3865_);
lean_closure_set(v___f_3868_, 10, v___x_3866_);
lean_closure_set(v___f_3868_, 11, v_reader_3858_);
lean_closure_set(v___f_3868_, 12, v___x_3867_);
v___f_3869_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3869_, 0, v___f_3868_);
if (v_sentMessage_3857_ == 0)
{
lean_object* v_state_3875_; 
v_state_3875_ = lean_ctor_get(v_reader_3858_, 0);
lean_inc(v_state_3875_);
lean_dec_ref(v_reader_3858_);
if (lean_obj_tag(v_state_3875_) == 2)
{
lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3886_; 
v_isSharedCheck_3886_ = !lean_is_exclusive(v_state_3875_);
if (v_isSharedCheck_3886_ == 0)
{
lean_object* v_unused_3887_; 
v_unused_3887_ = lean_ctor_get(v_state_3875_, 0);
lean_dec(v_unused_3887_);
v___x_3877_ = v_state_3875_;
v_isShared_3878_ = v_isSharedCheck_3886_;
goto v_resetjp_3876_;
}
else
{
lean_dec(v_state_3875_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3886_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
if (v_pullBodyStalled_3859_ == 0)
{
if (v_requestBodyOpen_3860_ == 0)
{
lean_del_object(v___x_3877_);
lean_dec_ref(v_requestStream_3861_);
v___y_3871_ = v_requestBodyOpen_3860_;
goto v___jp_3870_;
}
else
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 1);
lean_ctor_set(v___x_3877_, 0, v_requestStream_3861_);
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_requestStream_3861_);
v___x_3880_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3880_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
v___x_3884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3881_, v_pullBodyStalled_3859_, v___x_3883_, v___f_3869_);
return v___x_3884_;
}
}
}
else
{
lean_del_object(v___x_3877_);
lean_dec_ref(v_requestStream_3861_);
v___y_3871_ = v_sentMessage_3857_;
goto v___jp_3870_;
}
}
}
else
{
lean_dec(v_state_3875_);
lean_dec_ref(v_requestStream_3861_);
v___y_3871_ = v_sentMessage_3857_;
goto v___jp_3870_;
}
}
else
{
uint8_t v___x_3888_; 
lean_dec_ref(v_requestStream_3861_);
lean_dec_ref(v_reader_3858_);
v___x_3888_ = 0;
v___y_3871_ = v___x_3888_;
goto v___jp_3870_;
}
v___jp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = lean_unsigned_to_nat(0u);
v___x_3873_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3874_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3872_, v___y_3871_, v___x_3873_, v___f_3869_);
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3889_ = _args[0];
lean_object* v_handlerDispatched_3890_ = _args[1];
lean_object* v_keepAliveTimeout_3891_ = _args[2];
lean_object* v_headerTimeout_3892_ = _args[3];
lean_object* v_expectData_3893_ = _args[4];
lean_object* v_respStream_3894_ = _args[5];
lean_object* v_currentTimeout_3895_ = _args[6];
lean_object* v_response_3896_ = _args[7];
lean_object* v_socket_3897_ = _args[8];
lean_object* v_requiresData_3898_ = _args[9];
lean_object* v_sentMessage_3899_ = _args[10];
lean_object* v_reader_3900_ = _args[11];
lean_object* v_pullBodyStalled_3901_ = _args[12];
lean_object* v_requestBodyOpen_3902_ = _args[13];
lean_object* v_requestStream_3903_ = _args[14];
lean_object* v_requestBodyInterested_3904_ = _args[15];
lean_object* v___y_3905_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3906_; uint8_t v_requiresData_boxed_3907_; uint8_t v_sentMessage_boxed_3908_; uint8_t v_pullBodyStalled_boxed_3909_; uint8_t v_requestBodyOpen_boxed_3910_; uint8_t v_requestBodyInterested_boxed_3911_; lean_object* v_res_3912_; 
v_handlerDispatched_boxed_3906_ = lean_unbox(v_handlerDispatched_3890_);
v_requiresData_boxed_3907_ = lean_unbox(v_requiresData_3898_);
v_sentMessage_boxed_3908_ = lean_unbox(v_sentMessage_3899_);
v_pullBodyStalled_boxed_3909_ = lean_unbox(v_pullBodyStalled_3901_);
v_requestBodyOpen_boxed_3910_ = lean_unbox(v_requestBodyOpen_3902_);
v_requestBodyInterested_boxed_3911_ = lean_unbox(v_requestBodyInterested_3904_);
v_res_3912_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3889_, v_handlerDispatched_boxed_3906_, v_keepAliveTimeout_3891_, v_headerTimeout_3892_, v_expectData_3893_, v_respStream_3894_, v_currentTimeout_3895_, v_response_3896_, v_socket_3897_, v_requiresData_boxed_3907_, v_sentMessage_boxed_3908_, v_reader_3900_, v_pullBodyStalled_boxed_3909_, v_requestBodyOpen_boxed_3910_, v_requestStream_3903_, v_requestBodyInterested_boxed_3911_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3913_, lean_object* v_x_3914_){
_start:
{
if (lean_obj_tag(v_x_3914_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref(v___f_3913_);
v_a_3916_ = lean_ctor_get(v_x_3914_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_x_3914_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v_x_3914_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v_x_3914_);
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
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v_x_3914_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v_x_3914_, 1);
v___x_3926_ = lean_apply_2(v___f_3913_, v_a_3925_, lean_box(0));
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3927_, lean_object* v_x_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3927_, v_x_3928_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3931_, uint8_t v_handlerDispatched_3932_, lean_object* v_keepAliveTimeout_3933_, lean_object* v_headerTimeout_3934_, lean_object* v_expectData_3935_, lean_object* v_respStream_3936_, lean_object* v_currentTimeout_3937_, lean_object* v_response_3938_, lean_object* v_socket_3939_, uint8_t v_requiresData_3940_, uint8_t v_sentMessage_3941_, lean_object* v_reader_3942_, uint8_t v_pullBodyStalled_3943_, lean_object* v_requestStream_3944_, uint8_t v_requestBodyOpen_3945_){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___f_3952_; lean_object* v___f_3953_; uint8_t v___y_3955_; 
v___x_3947_ = lean_box(v_handlerDispatched_3932_);
v___x_3948_ = lean_box(v_requiresData_3940_);
v___x_3949_ = lean_box(v_sentMessage_3941_);
v___x_3950_ = lean_box(v_pullBodyStalled_3943_);
v___x_3951_ = lean_box(v_requestBodyOpen_3945_);
lean_inc_ref(v_requestStream_3944_);
lean_inc_ref(v_reader_3942_);
v___f_3952_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3952_, 0, v_connectionContext_3931_);
lean_closure_set(v___f_3952_, 1, v___x_3947_);
lean_closure_set(v___f_3952_, 2, v_keepAliveTimeout_3933_);
lean_closure_set(v___f_3952_, 3, v_headerTimeout_3934_);
lean_closure_set(v___f_3952_, 4, v_expectData_3935_);
lean_closure_set(v___f_3952_, 5, v_respStream_3936_);
lean_closure_set(v___f_3952_, 6, v_currentTimeout_3937_);
lean_closure_set(v___f_3952_, 7, v_response_3938_);
lean_closure_set(v___f_3952_, 8, v_socket_3939_);
lean_closure_set(v___f_3952_, 9, v___x_3948_);
lean_closure_set(v___f_3952_, 10, v___x_3949_);
lean_closure_set(v___f_3952_, 11, v_reader_3942_);
lean_closure_set(v___f_3952_, 12, v___x_3950_);
lean_closure_set(v___f_3952_, 13, v___x_3951_);
lean_closure_set(v___f_3952_, 14, v_requestStream_3944_);
v___f_3953_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3953_, 0, v___f_3952_);
if (v_sentMessage_3941_ == 0)
{
lean_object* v_state_3961_; 
v_state_3961_ = lean_ctor_get(v_reader_3942_, 0);
lean_inc(v_state_3961_);
lean_dec_ref(v_reader_3942_);
if (lean_obj_tag(v_state_3961_) == 2)
{
lean_dec_ref_known(v_state_3961_, 1);
if (v_requestBodyOpen_3945_ == 0)
{
lean_dec_ref(v_requestStream_3944_);
v___y_3955_ = v_requestBodyOpen_3945_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_unsigned_to_nat(0u);
v___x_3963_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3944_);
v___x_3964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3962_, v_sentMessage_3941_, v___x_3963_, v___f_3953_);
return v___x_3964_;
}
}
else
{
lean_dec(v_state_3961_);
lean_dec_ref(v_requestStream_3944_);
v___y_3955_ = v_sentMessage_3941_;
goto v___jp_3954_;
}
}
else
{
uint8_t v___x_3965_; 
lean_dec_ref(v_requestStream_3944_);
lean_dec_ref(v_reader_3942_);
v___x_3965_ = 0;
v___y_3955_ = v___x_3965_;
goto v___jp_3954_;
}
v___jp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_3957_ = lean_box(v___y_3955_);
v___x_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
v___x_3960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3956_, v___y_3955_, v___x_3959_, v___f_3953_);
return v___x_3960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3966_, lean_object* v_handlerDispatched_3967_, lean_object* v_keepAliveTimeout_3968_, lean_object* v_headerTimeout_3969_, lean_object* v_expectData_3970_, lean_object* v_respStream_3971_, lean_object* v_currentTimeout_3972_, lean_object* v_response_3973_, lean_object* v_socket_3974_, lean_object* v_requiresData_3975_, lean_object* v_sentMessage_3976_, lean_object* v_reader_3977_, lean_object* v_pullBodyStalled_3978_, lean_object* v_requestStream_3979_, lean_object* v_requestBodyOpen_3980_, lean_object* v___y_3981_){
_start:
{
uint8_t v_handlerDispatched_boxed_3982_; uint8_t v_requiresData_boxed_3983_; uint8_t v_sentMessage_boxed_3984_; uint8_t v_pullBodyStalled_boxed_3985_; uint8_t v_requestBodyOpen_boxed_3986_; lean_object* v_res_3987_; 
v_handlerDispatched_boxed_3982_ = lean_unbox(v_handlerDispatched_3967_);
v_requiresData_boxed_3983_ = lean_unbox(v_requiresData_3975_);
v_sentMessage_boxed_3984_ = lean_unbox(v_sentMessage_3976_);
v_pullBodyStalled_boxed_3985_ = lean_unbox(v_pullBodyStalled_3978_);
v_requestBodyOpen_boxed_3986_ = lean_unbox(v_requestBodyOpen_3980_);
v_res_3987_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3966_, v_handlerDispatched_boxed_3982_, v_keepAliveTimeout_3968_, v_headerTimeout_3969_, v_expectData_3970_, v_respStream_3971_, v_currentTimeout_3972_, v_response_3973_, v_socket_3974_, v_requiresData_boxed_3983_, v_sentMessage_boxed_3984_, v_reader_3977_, v_pullBodyStalled_boxed_3985_, v_requestStream_3979_, v_requestBodyOpen_boxed_3986_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3988_, lean_object* v___f_3989_, uint8_t v___x_3990_, lean_object* v_x_3991_){
_start:
{
uint8_t v___y_3994_; 
if (lean_obj_tag(v_x_3991_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v___f_3989_);
v_a_4000_ = lean_ctor_get(v_x_3991_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_x_3991_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4002_ = v_x_3991_;
v_isShared_4003_ = v_isSharedCheck_4008_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v_x_3991_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4008_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
}
else
{
lean_object* v_a_4009_; uint8_t v___x_4010_; 
v_a_4009_ = lean_ctor_get(v_x_3991_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v_x_3991_, 1);
v___x_4010_ = lean_unbox(v_a_4009_);
lean_dec(v_a_4009_);
if (v___x_4010_ == 0)
{
v___y_3994_ = v___x_3990_;
goto v___jp_3993_;
}
else
{
v___y_3994_ = v_sentMessage_3988_;
goto v___jp_3993_;
}
}
v___jp_3993_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3995_ = lean_unsigned_to_nat(0u);
v___x_3996_ = lean_box(v___y_3994_);
v___x_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
v___x_3999_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3995_, v_sentMessage_3988_, v___x_3998_, v___f_3989_);
return v___x_3999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4011_, lean_object* v___f_4012_, lean_object* v___x_4013_, lean_object* v_x_4014_, lean_object* v___y_4015_){
_start:
{
uint8_t v_sentMessage_boxed_4016_; uint8_t v___x_2892__boxed_4017_; lean_object* v_res_4018_; 
v_sentMessage_boxed_4016_ = lean_unbox(v_sentMessage_4011_);
v___x_2892__boxed_4017_ = lean_unbox(v___x_4013_);
v_res_4018_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4016_, v___f_4012_, v___x_2892__boxed_4017_, v_x_4014_);
return v_res_4018_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___f_4019_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4020_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4021_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4022_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4022_, 0, lean_box(0));
lean_closure_set(v___x_4022_, 1, lean_box(0));
lean_closure_set(v___x_4022_, 2, v___x_4021_);
lean_closure_set(v___x_4022_, 3, lean_box(0));
lean_closure_set(v___x_4022_, 4, lean_box(0));
lean_closure_set(v___x_4022_, 5, v___x_4020_);
lean_closure_set(v___x_4022_, 6, v___f_4019_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4023_, lean_object* v_connectionContext_4024_, lean_object* v_state_4025_){
_start:
{
lean_object* v_machine_4027_; lean_object* v_writer_4028_; lean_object* v_requestStream_4029_; lean_object* v_keepAliveTimeout_4030_; lean_object* v_currentTimeout_4031_; lean_object* v_headerTimeout_4032_; lean_object* v_response_4033_; lean_object* v_respStream_4034_; uint8_t v_requiresData_4035_; lean_object* v_expectData_4036_; uint8_t v_handlerDispatched_4037_; lean_object* v_reader_4038_; uint8_t v_pullBodyStalled_4039_; uint8_t v_sentMessage_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___f_4045_; lean_object* v___f_4046_; uint8_t v___y_4048_; 
v_machine_4027_ = lean_ctor_get(v_state_4025_, 0);
lean_inc_ref(v_machine_4027_);
v_writer_4028_ = lean_ctor_get(v_machine_4027_, 1);
lean_inc_ref(v_writer_4028_);
v_requestStream_4029_ = lean_ctor_get(v_state_4025_, 1);
lean_inc_ref_n(v_requestStream_4029_, 2);
v_keepAliveTimeout_4030_ = lean_ctor_get(v_state_4025_, 2);
lean_inc(v_keepAliveTimeout_4030_);
v_currentTimeout_4031_ = lean_ctor_get(v_state_4025_, 3);
lean_inc(v_currentTimeout_4031_);
v_headerTimeout_4032_ = lean_ctor_get(v_state_4025_, 4);
lean_inc(v_headerTimeout_4032_);
v_response_4033_ = lean_ctor_get(v_state_4025_, 5);
lean_inc_ref(v_response_4033_);
v_respStream_4034_ = lean_ctor_get(v_state_4025_, 6);
lean_inc(v_respStream_4034_);
v_requiresData_4035_ = lean_ctor_get_uint8(v_state_4025_, sizeof(void*)*9);
v_expectData_4036_ = lean_ctor_get(v_state_4025_, 7);
lean_inc(v_expectData_4036_);
v_handlerDispatched_4037_ = lean_ctor_get_uint8(v_state_4025_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4025_);
v_reader_4038_ = lean_ctor_get(v_machine_4027_, 0);
lean_inc_ref_n(v_reader_4038_, 2);
v_pullBodyStalled_4039_ = lean_ctor_get_uint8(v_machine_4027_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4027_);
v_sentMessage_4040_ = lean_ctor_get_uint8(v_writer_4028_, sizeof(void*)*6);
lean_dec_ref(v_writer_4028_);
v___x_4041_ = lean_box(v_handlerDispatched_4037_);
v___x_4042_ = lean_box(v_requiresData_4035_);
v___x_4043_ = lean_box(v_sentMessage_4040_);
v___x_4044_ = lean_box(v_pullBodyStalled_4039_);
v___f_4045_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4045_, 0, v_connectionContext_4024_);
lean_closure_set(v___f_4045_, 1, v___x_4041_);
lean_closure_set(v___f_4045_, 2, v_keepAliveTimeout_4030_);
lean_closure_set(v___f_4045_, 3, v_headerTimeout_4032_);
lean_closure_set(v___f_4045_, 4, v_expectData_4036_);
lean_closure_set(v___f_4045_, 5, v_respStream_4034_);
lean_closure_set(v___f_4045_, 6, v_currentTimeout_4031_);
lean_closure_set(v___f_4045_, 7, v_response_4033_);
lean_closure_set(v___f_4045_, 8, v_socket_4023_);
lean_closure_set(v___f_4045_, 9, v___x_4042_);
lean_closure_set(v___f_4045_, 10, v___x_4043_);
lean_closure_set(v___f_4045_, 11, v_reader_4038_);
lean_closure_set(v___f_4045_, 12, v___x_4044_);
lean_closure_set(v___f_4045_, 13, v_requestStream_4029_);
v___f_4046_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4046_, 0, v___f_4045_);
if (v_sentMessage_4040_ == 0)
{
lean_object* v_state_4054_; 
v_state_4054_ = lean_ctor_get(v_reader_4038_, 0);
lean_inc(v_state_4054_);
lean_dec_ref(v_reader_4038_);
if (lean_obj_tag(v_state_4054_) == 2)
{
uint8_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___f_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___f_4061_; lean_object* v___f_4062_; lean_object* v___x_4063_; lean_object* v___x_2542__overap_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_dec_ref_known(v_state_4054_, 1);
v___x_4055_ = 1;
v___x_4056_ = lean_box(v_sentMessage_4040_);
v___x_4057_ = lean_box(v___x_4055_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4058_, 0, v___x_4056_);
lean_closure_set(v___f_4058_, 1, v___f_4046_);
lean_closure_set(v___f_4058_, 2, v___x_4057_);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4061_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4062_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4063_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2542__overap_4064_ = l_Std_Mutex_atomically___redArg(v___x_4060_, v___f_4061_, v___f_4062_, v_requestStream_4029_, v___x_4063_);
v___x_4065_ = lean_apply_1(v___x_2542__overap_4064_, lean_box(0));
v___x_4066_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4059_, v_sentMessage_4040_, v___x_4065_, v___f_4058_);
return v___x_4066_;
}
else
{
lean_dec(v_state_4054_);
lean_dec_ref(v_requestStream_4029_);
v___y_4048_ = v_sentMessage_4040_;
goto v___jp_4047_;
}
}
else
{
uint8_t v___x_4067_; 
lean_dec_ref(v_reader_4038_);
lean_dec_ref(v_requestStream_4029_);
v___x_4067_ = 0;
v___y_4048_ = v___x_4067_;
goto v___jp_4047_;
}
v___jp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_box(v___y_4048_);
v___x_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
v___x_4053_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4049_, v___y_4048_, v___x_4052_, v___f_4046_);
return v___x_4053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4068_, lean_object* v_connectionContext_4069_, lean_object* v_state_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4068_, v_connectionContext_4069_, v_state_4070_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4073_, lean_object* v_00_u03b2_4074_, lean_object* v_inst_4075_, lean_object* v_socket_4076_, lean_object* v_connectionContext_4077_, lean_object* v_state_4078_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4076_, v_connectionContext_4077_, v_state_4078_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4081_, lean_object* v_00_u03b2_4082_, lean_object* v_inst_4083_, lean_object* v_socket_4084_, lean_object* v_connectionContext_4085_, lean_object* v_state_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4081_, v_00_u03b2_4082_, v_inst_4083_, v_socket_4084_, v_connectionContext_4085_, v_state_4086_);
lean_dec_ref(v_inst_4083_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4089_){
_start:
{
if (lean_obj_tag(v_x_4089_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4099_; 
v_a_4091_ = lean_ctor_get(v_x_4089_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v_x_4089_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4093_ = v_x_4089_;
v_isShared_4094_ = v_isSharedCheck_4099_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v_x_4089_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4099_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
return v___x_4097_;
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4109_; 
v_a_4100_ = lean_ctor_get(v_x_4089_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_x_4089_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4102_ = v_x_4089_;
v_isShared_4103_ = v_isSharedCheck_4109_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v_x_4089_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4109_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4104_; lean_object* v___x_4106_; 
v___x_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_a_4100_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4104_);
v___x_4106_ = v___x_4102_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4104_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4117_){
_start:
{
if (lean_obj_tag(v_x_4117_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4127_; 
v_a_4119_ = lean_ctor_get(v_x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4121_ = v_x_4117_;
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v_x_4117_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
}
}
else
{
lean_object* v___x_4128_; 
lean_dec_ref_known(v_x_4117_, 1);
v___x_4128_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_4128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4129_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_4132_, lean_object* v_handler_4133_, lean_object* v___f_4134_, lean_object* v_x_4135_){
_start:
{
if (lean_obj_tag(v_x_4135_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_a_4137_ = lean_ctor_get(v_x_4135_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v_x_4135_, 1);
v___x_4138_ = lean_unsigned_to_nat(0u);
v___x_4139_ = 0;
v___x_4140_ = lean_apply_3(v_onFailure_4132_, v_handler_4133_, v_a_4137_, lean_box(0));
v___x_4141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4138_, v___x_4139_, v___x_4140_, v___f_4134_);
return v___x_4141_;
}
else
{
lean_object* v___x_4142_; 
lean_dec_ref(v___f_4134_);
lean_dec(v_handler_4133_);
lean_dec_ref(v_onFailure_4132_);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_x_4135_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_4143_, lean_object* v_handler_4144_, lean_object* v___f_4145_, lean_object* v_x_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_4143_, v_handler_4144_, v___f_4145_, v_x_4146_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4149_){
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
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4178_; 
v_a_4160_ = lean_ctor_get(v_x_4149_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v_x_4149_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4162_ = v_x_4149_;
v_isShared_4163_ = v_isSharedCheck_4178_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v_x_4149_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4178_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v_snd_4164_; uint8_t v___x_4165_; 
v_snd_4164_ = lean_ctor_get(v_a_4160_, 1);
v___x_4165_ = lean_unbox(v_snd_4164_);
if (v___x_4165_ == 0)
{
lean_object* v_fst_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v_fst_4166_ = lean_ctor_get(v_a_4160_, 0);
lean_inc(v_fst_4166_);
lean_dec(v_a_4160_);
v___x_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4167_, 0, v_fst_4166_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4167_);
v___x_4169_ = v___x_4162_;
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
else
{
lean_object* v_fst_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v_fst_4172_ = lean_ctor_get(v_a_4160_, 0);
lean_inc(v_fst_4172_);
lean_dec(v_a_4160_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_fst_4172_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4173_);
v___x_4175_ = v___x_4162_;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4182_, lean_object* v_socket_4183_, lean_object* v_____r_4184_){
_start:
{
lean_object* v_val_4187_; lean_object* v_close_4189_; lean_object* v___x_4190_; 
v_close_4189_ = lean_ctor_get(v_inst_4182_, 3);
lean_inc_ref(v_close_4189_);
lean_dec_ref(v_inst_4182_);
v___x_4190_ = lean_apply_2(v_close_4189_, v_socket_4183_, lean_box(0));
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 1);
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
v_val_4187_ = v___x_4196_;
goto v___jp_4186_;
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4190_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4190_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
lean_ctor_set_tag(v___x_4201_, 0);
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
v_val_4187_ = v___x_4204_;
goto v___jp_4186_;
}
}
}
v___jp_4186_:
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v_val_4187_);
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4207_, lean_object* v_socket_4208_, lean_object* v_____r_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4207_, v_socket_4208_, v_____r_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4212_, lean_object* v_x_4213_){
_start:
{
if (lean_obj_tag(v_x_4213_) == 0)
{
lean_object* v___x_4215_; 
lean_dec_ref(v___f_4212_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_x_4213_);
return v___x_4215_;
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4217_; 
v_a_4216_ = lean_ctor_get(v_x_4213_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v_x_4213_, 1);
v___x_4217_ = lean_apply_2(v___f_4212_, v_a_4216_, lean_box(0));
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4218_, lean_object* v_x_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4218_, v_x_4219_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4222_, lean_object* v_val_4223_, lean_object* v___f_4224_, lean_object* v___f_4225_, lean_object* v_x_4226_){
_start:
{
if (lean_obj_tag(v_x_4226_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v___f_4225_);
lean_dec_ref(v___f_4224_);
lean_dec(v_val_4223_);
lean_dec_ref(v_close_4222_);
v_a_4228_ = lean_ctor_get(v_x_4226_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_x_4226_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4230_ = v_x_4226_;
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v_x_4226_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
return v___x_4234_;
}
}
}
else
{
lean_object* v_a_4237_; uint8_t v___x_4238_; 
v_a_4237_ = lean_ctor_get(v_x_4226_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v_x_4226_, 1);
v___x_4238_ = lean_unbox(v_a_4237_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; lean_object* v___x_4242_; 
lean_dec_ref(v___f_4225_);
v___x_4239_ = lean_unsigned_to_nat(0u);
v___x_4240_ = lean_apply_2(v_close_4222_, v_val_4223_, lean_box(0));
v___x_4241_ = lean_unbox(v_a_4237_);
lean_dec(v_a_4237_);
v___x_4242_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4239_, v___x_4241_, v___x_4240_, v___f_4224_);
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
lean_dec(v_a_4237_);
lean_dec_ref(v___f_4224_);
lean_dec(v_val_4223_);
lean_dec_ref(v_close_4222_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_apply_2(v___f_4225_, v___x_4243_, lean_box(0));
return v___x_4244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4245_, lean_object* v_val_4246_, lean_object* v___f_4247_, lean_object* v___f_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4245_, v_val_4246_, v___f_4247_, v___f_4248_, v_x_4249_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4252_, lean_object* v_responseBodyInstance_4253_, lean_object* v___f_4254_, lean_object* v___f_4255_, lean_object* v_____r_4256_){
_start:
{
if (lean_obj_tag(v_respStream_4252_) == 1)
{
lean_object* v_val_4258_; lean_object* v_close_4259_; lean_object* v_isClosed_4260_; lean_object* v___f_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_val_4258_ = lean_ctor_get(v_respStream_4252_, 0);
lean_inc_n(v_val_4258_, 2);
lean_dec_ref_known(v_respStream_4252_, 1);
v_close_4259_ = lean_ctor_get(v_responseBodyInstance_4253_, 1);
lean_inc_ref(v_close_4259_);
v_isClosed_4260_ = lean_ctor_get(v_responseBodyInstance_4253_, 2);
lean_inc_ref(v_isClosed_4260_);
lean_dec_ref(v_responseBodyInstance_4253_);
v___f_4261_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4261_, 0, v_close_4259_);
lean_closure_set(v___f_4261_, 1, v_val_4258_);
lean_closure_set(v___f_4261_, 2, v___f_4254_);
lean_closure_set(v___f_4261_, 3, v___f_4255_);
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = 0;
v___x_4264_ = lean_apply_2(v_isClosed_4260_, v_val_4258_, lean_box(0));
v___x_4265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4262_, v___x_4263_, v___x_4264_, v___f_4261_);
return v___x_4265_;
}
else
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec_ref(v___f_4254_);
lean_dec_ref(v_responseBodyInstance_4253_);
lean_dec(v_respStream_4252_);
v___x_4266_ = lean_box(0);
v___x_4267_ = lean_apply_2(v___f_4255_, v___x_4266_, lean_box(0));
return v___x_4267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4268_, lean_object* v_responseBodyInstance_4269_, lean_object* v___f_4270_, lean_object* v___f_4271_, lean_object* v_____r_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4268_, v_responseBodyInstance_4269_, v___f_4270_, v___f_4271_, v_____r_4272_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4275_, lean_object* v___f_4276_, lean_object* v___f_4277_, lean_object* v_x_4278_){
_start:
{
if (lean_obj_tag(v_x_4278_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v___f_4277_);
lean_dec_ref(v___f_4276_);
lean_dec_ref(v_requestStream_4275_);
v_a_4280_ = lean_ctor_get(v_x_4278_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_x_4278_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4282_ = v_x_4278_;
v_isShared_4283_ = v_isSharedCheck_4288_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v_x_4278_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4288_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
return v___x_4286_;
}
}
}
else
{
lean_object* v_a_4289_; uint8_t v___x_4290_; 
v_a_4289_ = lean_ctor_get(v_x_4278_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v_x_4278_, 1);
v___x_4290_ = lean_unbox(v_a_4289_);
if (v___x_4290_ == 0)
{
lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; 
lean_dec_ref(v___f_4277_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = l_Std_Http_Body_Stream_close(v_requestStream_4275_);
v___x_4293_ = lean_unbox(v_a_4289_);
lean_dec(v_a_4289_);
v___x_4294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4291_, v___x_4293_, v___x_4292_, v___f_4276_);
return v___x_4294_;
}
else
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
lean_dec(v_a_4289_);
lean_dec_ref(v___f_4276_);
lean_dec_ref(v_requestStream_4275_);
v___x_4295_ = lean_box(0);
v___x_4296_ = lean_apply_2(v___f_4277_, v___x_4295_, lean_box(0));
return v___x_4296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4297_, lean_object* v___f_4298_, lean_object* v___f_4299_, lean_object* v_x_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4297_, v___f_4298_, v___f_4299_, v_x_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4303_, lean_object* v___f_4304_, lean_object* v___f_4305_, lean_object* v___f_4306_, lean_object* v_x_4307_){
_start:
{
if (lean_obj_tag(v_x_4307_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4317_; 
lean_dec_ref(v___f_4306_);
lean_dec_ref(v___f_4305_);
lean_dec_ref(v___f_4304_);
lean_dec_ref(v_responseBodyInstance_4303_);
v_a_4309_ = lean_ctor_get(v_x_4307_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_x_4307_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4311_ = v_x_4307_;
v_isShared_4312_ = v_isSharedCheck_4317_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v_x_4307_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4317_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
lean_object* v___x_4315_; 
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v_requestStream_4319_; lean_object* v_respStream_4320_; lean_object* v___f_4321_; lean_object* v___f_4322_; lean_object* v___f_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4542__overap_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_a_4318_ = lean_ctor_get(v_x_4307_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v_x_4307_, 1);
v_requestStream_4319_ = lean_ctor_get(v_a_4318_, 1);
lean_inc_ref_n(v_requestStream_4319_, 2);
v_respStream_4320_ = lean_ctor_get(v_a_4318_, 6);
lean_inc(v_respStream_4320_);
lean_dec(v_a_4318_);
v___f_4321_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4321_, 0, v_respStream_4320_);
lean_closure_set(v___f_4321_, 1, v_responseBodyInstance_4303_);
lean_closure_set(v___f_4321_, 2, v___f_4304_);
lean_closure_set(v___f_4321_, 3, v___f_4305_);
lean_inc_ref(v___f_4321_);
v___f_4322_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4322_, 0, v___f_4321_);
v___f_4323_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4323_, 0, v_requestStream_4319_);
lean_closure_set(v___f_4323_, 1, v___f_4322_);
lean_closure_set(v___f_4323_, 2, v___f_4321_);
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = 0;
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
lean_closure_set(v___x_4330_, 6, v___f_4306_);
v___x_4542__overap_4331_ = l_Std_Mutex_atomically___redArg(v___x_4326_, v___f_4327_, v___f_4328_, v_requestStream_4319_, v___x_4330_);
v___x_4332_ = lean_apply_1(v___x_4542__overap_4331_, lean_box(0));
v___x_4333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4324_, v___x_4325_, v___x_4332_, v___f_4323_);
return v___x_4333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4334_, lean_object* v___f_4335_, lean_object* v___f_4336_, lean_object* v___f_4337_, lean_object* v_x_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4334_, v___f_4335_, v___f_4336_, v___f_4337_, v_x_4338_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4341_, lean_object* v_responseBodyInstance_4342_, lean_object* v_handler_4343_, lean_object* v_config_4344_, lean_object* v___x_4345_, uint8_t v___x_4346_, lean_object* v___f_4347_, lean_object* v_x_4348_){
_start:
{
if (lean_obj_tag(v_x_4348_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4358_; 
lean_dec_ref(v___f_4347_);
lean_dec_ref(v___x_4345_);
lean_dec_ref(v_config_4344_);
lean_dec(v_handler_4343_);
lean_dec_ref(v_responseBodyInstance_4342_);
lean_dec_ref(v_h_4341_);
v_a_4350_ = lean_ctor_get(v_x_4348_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v_x_4348_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4352_ = v_x_4348_;
v_isShared_4353_ = v_isSharedCheck_4358_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v_x_4348_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4358_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4355_);
return v___x_4356_;
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_a_4359_ = lean_ctor_get(v_x_4348_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v_x_4348_, 1);
v___x_4360_ = lean_unsigned_to_nat(0u);
v___x_4361_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4341_, v_responseBodyInstance_4342_, v_handler_4343_, v_config_4344_, v_a_4359_, v___x_4345_);
v___x_4362_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4360_, v___x_4346_, v___x_4361_, v___f_4347_);
return v___x_4362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4363_, lean_object* v_responseBodyInstance_4364_, lean_object* v_handler_4365_, lean_object* v_config_4366_, lean_object* v___x_4367_, lean_object* v___x_4368_, lean_object* v___f_4369_, lean_object* v_x_4370_, lean_object* v___y_4371_){
_start:
{
uint8_t v___x_5208__boxed_4372_; lean_object* v_res_4373_; 
v___x_5208__boxed_4372_ = lean_unbox(v___x_4368_);
v_res_4373_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4363_, v_responseBodyInstance_4364_, v_handler_4365_, v_config_4366_, v___x_4367_, v___x_5208__boxed_4372_, v___f_4369_, v_x_4370_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4374_, lean_object* v_h_4375_, lean_object* v_responseBodyInstance_4376_, lean_object* v_config_4377_, lean_object* v_handler_4378_, uint8_t v___x_4379_, lean_object* v___f_4380_, lean_object* v_x_4381_){
_start:
{
if (lean_obj_tag(v_x_4381_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4391_; 
lean_dec_ref(v___f_4380_);
lean_dec(v_handler_4378_);
lean_dec_ref(v_config_4377_);
lean_dec_ref(v_responseBodyInstance_4376_);
lean_dec_ref(v_h_4375_);
lean_dec_ref(v_inst_4374_);
v_a_4383_ = lean_ctor_get(v_x_4381_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_x_4381_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4385_ = v_x_4381_;
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v_x_4381_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; 
v___x_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
return v___x_4389_;
}
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_a_4392_ = lean_ctor_get(v_x_4381_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v_x_4381_, 1);
v___x_4393_ = lean_unsigned_to_nat(0u);
v___x_4394_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4374_, v_h_4375_, v_responseBodyInstance_4376_, v_config_4377_, v_handler_4378_, v_a_4392_);
v___x_4395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4393_, v___x_4379_, v___x_4394_, v___f_4380_);
return v___x_4395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4396_, lean_object* v_h_4397_, lean_object* v_responseBodyInstance_4398_, lean_object* v_config_4399_, lean_object* v_handler_4400_, lean_object* v___x_4401_, lean_object* v___f_4402_, lean_object* v_x_4403_, lean_object* v___y_4404_){
_start:
{
uint8_t v___x_5249__boxed_4405_; lean_object* v_res_4406_; 
v___x_5249__boxed_4405_ = lean_unbox(v___x_4401_);
v_res_4406_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4396_, v_h_4397_, v_responseBodyInstance_4398_, v_config_4399_, v_handler_4400_, v___x_5249__boxed_4405_, v___f_4402_, v_x_4403_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4407_, lean_object* v_h_4408_, lean_object* v_responseBodyInstance_4409_, lean_object* v_handler_4410_, lean_object* v_config_4411_, lean_object* v___f_4412_, lean_object* v_inst_4413_, lean_object* v_socket_4414_, lean_object* v_connectionContext_4415_, lean_object* v_x_4416_){
_start:
{
if (lean_obj_tag(v_x_4416_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v_connectionContext_4415_);
lean_dec(v_socket_4414_);
lean_dec_ref(v_inst_4413_);
lean_dec_ref(v___f_4412_);
lean_dec_ref(v_config_4411_);
lean_dec(v_handler_4410_);
lean_dec_ref(v_responseBodyInstance_4409_);
lean_dec_ref(v_h_4408_);
v_a_4418_ = lean_ctor_get(v_x_4416_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_x_4416_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4420_ = v_x_4416_;
v_isShared_4421_ = v_isSharedCheck_4426_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v_x_4416_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4426_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; 
v___x_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
return v___x_4424_;
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4461_; 
v_a_4427_ = lean_ctor_get(v_x_4416_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_x_4416_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4429_ = v_x_4416_;
v_isShared_4430_ = v_isSharedCheck_4461_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v_x_4416_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4461_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v_machine_4437_; lean_object* v_requestStream_4438_; lean_object* v_keepAliveTimeout_4439_; lean_object* v_currentTimeout_4440_; lean_object* v_headerTimeout_4441_; lean_object* v_response_4442_; lean_object* v_respStream_4443_; uint8_t v_requiresData_4444_; lean_object* v_expectData_4445_; uint8_t v_handlerDispatched_4446_; lean_object* v_pendingHead_4447_; 
v_machine_4437_ = lean_ctor_get(v_a_4427_, 0);
v_requestStream_4438_ = lean_ctor_get(v_a_4427_, 1);
v_keepAliveTimeout_4439_ = lean_ctor_get(v_a_4427_, 2);
v_currentTimeout_4440_ = lean_ctor_get(v_a_4427_, 3);
v_headerTimeout_4441_ = lean_ctor_get(v_a_4427_, 4);
v_response_4442_ = lean_ctor_get(v_a_4427_, 5);
v_respStream_4443_ = lean_ctor_get(v_a_4427_, 6);
v_requiresData_4444_ = lean_ctor_get_uint8(v_a_4427_, sizeof(void*)*9);
v_expectData_4445_ = lean_ctor_get(v_a_4427_, 7);
v_handlerDispatched_4446_ = lean_ctor_get_uint8(v_a_4427_, sizeof(void*)*9 + 1);
v_pendingHead_4447_ = lean_ctor_get(v_a_4427_, 8);
if (v_requiresData_4444_ == 0)
{
if (v_handlerDispatched_4446_ == 0)
{
if (lean_obj_tag(v_respStream_4443_) == 0)
{
lean_object* v_writer_4457_; uint8_t v_sentMessage_4458_; 
v_writer_4457_ = lean_ctor_get(v_machine_4437_, 1);
v_sentMessage_4458_ = lean_ctor_get_uint8(v_writer_4457_, sizeof(void*)*6);
if (v_sentMessage_4458_ == 0)
{
lean_object* v_reader_4459_; lean_object* v_state_4460_; 
v_reader_4459_ = lean_ctor_get(v_machine_4437_, 0);
v_state_4460_ = lean_ctor_get(v_reader_4459_, 0);
if (lean_obj_tag(v_state_4460_) == 2)
{
lean_inc(v_respStream_4443_);
lean_inc(v_pendingHead_4447_);
lean_inc(v_expectData_4445_);
lean_inc_ref(v_response_4442_);
lean_inc(v_headerTimeout_4441_);
lean_inc(v_currentTimeout_4440_);
lean_inc(v_keepAliveTimeout_4439_);
lean_inc_ref(v_requestStream_4438_);
lean_inc_ref(v_machine_4437_);
lean_del_object(v___x_4429_);
lean_dec(v_a_4427_);
goto v___jp_4448_;
}
else
{
lean_dec_ref(v_connectionContext_4415_);
lean_dec(v_socket_4414_);
lean_dec_ref(v_inst_4413_);
lean_dec_ref(v___f_4412_);
lean_dec_ref(v_config_4411_);
lean_dec(v_handler_4410_);
lean_dec_ref(v_responseBodyInstance_4409_);
lean_dec_ref(v_h_4408_);
goto v___jp_4431_;
}
}
else
{
lean_dec_ref(v_connectionContext_4415_);
lean_dec(v_socket_4414_);
lean_dec_ref(v_inst_4413_);
lean_dec_ref(v___f_4412_);
lean_dec_ref(v_config_4411_);
lean_dec(v_handler_4410_);
lean_dec_ref(v_responseBodyInstance_4409_);
lean_dec_ref(v_h_4408_);
goto v___jp_4431_;
}
}
else
{
lean_inc_ref(v_respStream_4443_);
lean_inc(v_pendingHead_4447_);
lean_inc(v_expectData_4445_);
lean_inc_ref(v_response_4442_);
lean_inc(v_headerTimeout_4441_);
lean_inc(v_currentTimeout_4440_);
lean_inc(v_keepAliveTimeout_4439_);
lean_inc_ref(v_requestStream_4438_);
lean_inc_ref(v_machine_4437_);
lean_del_object(v___x_4429_);
lean_dec(v_a_4427_);
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
lean_del_object(v___x_4429_);
lean_dec(v_a_4427_);
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
lean_del_object(v___x_4429_);
lean_dec(v_a_4427_);
goto v___jp_4448_;
}
v___jp_4431_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4432_, 0, v_a_4427_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4432_);
v___x_4434_ = v___x_4429_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
v___jp_4448_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___f_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
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
lean_ctor_set_uint8(v___x_4449_, sizeof(void*)*9, v___x_4407_);
lean_ctor_set_uint8(v___x_4449_, sizeof(void*)*9 + 1, v_handlerDispatched_4446_);
v___x_4450_ = lean_box(v___x_4407_);
lean_inc_ref(v___x_4449_);
lean_inc_ref(v_config_4411_);
lean_inc(v_handler_4410_);
lean_inc_ref(v_responseBodyInstance_4409_);
lean_inc_ref(v_h_4408_);
v___f_4451_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4451_, 0, v_h_4408_);
lean_closure_set(v___f_4451_, 1, v_responseBodyInstance_4409_);
lean_closure_set(v___f_4451_, 2, v_handler_4410_);
lean_closure_set(v___f_4451_, 3, v_config_4411_);
lean_closure_set(v___f_4451_, 4, v___x_4449_);
lean_closure_set(v___f_4451_, 5, v___x_4450_);
lean_closure_set(v___f_4451_, 6, v___f_4412_);
v___x_4452_ = lean_box(v___x_4407_);
v___f_4453_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4453_, 0, v_inst_4413_);
lean_closure_set(v___f_4453_, 1, v_h_4408_);
lean_closure_set(v___f_4453_, 2, v_responseBodyInstance_4409_);
lean_closure_set(v___f_4453_, 3, v_config_4411_);
lean_closure_set(v___f_4453_, 4, v_handler_4410_);
lean_closure_set(v___f_4453_, 5, v___x_4452_);
lean_closure_set(v___f_4453_, 6, v___f_4451_);
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4455_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4414_, v_connectionContext_4415_, v___x_4449_);
v___x_4456_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4454_, v___x_4407_, v___x_4455_, v___f_4453_);
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4462_, lean_object* v_h_4463_, lean_object* v_responseBodyInstance_4464_, lean_object* v_handler_4465_, lean_object* v_config_4466_, lean_object* v___f_4467_, lean_object* v_inst_4468_, lean_object* v_socket_4469_, lean_object* v_connectionContext_4470_, lean_object* v_x_4471_, lean_object* v___y_4472_){
_start:
{
uint8_t v___x_5289__boxed_4473_; lean_object* v_res_4474_; 
v___x_5289__boxed_4473_ = lean_unbox(v___x_4462_);
v_res_4474_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5289__boxed_4473_, v_h_4463_, v_responseBodyInstance_4464_, v_handler_4465_, v_config_4466_, v___f_4467_, v_inst_4468_, v_socket_4469_, v_connectionContext_4470_, v_x_4471_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4475_, lean_object* v_handler_4476_, lean_object* v_extensions_4477_, lean_object* v_connectionContext_4478_, uint8_t v___x_4479_, lean_object* v___f_4480_, lean_object* v_x_4481_){
_start:
{
if (lean_obj_tag(v_x_4481_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v___f_4480_);
lean_dec_ref(v_connectionContext_4478_);
lean_dec(v_extensions_4477_);
lean_dec(v_handler_4476_);
lean_dec_ref(v_h_4475_);
v_a_4483_ = lean_ctor_get(v_x_4481_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_x_4481_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4485_ = v_x_4481_;
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v_x_4481_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4489_; 
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
return v___x_4489_;
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v_a_4492_ = lean_ctor_get(v_x_4481_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v_x_4481_, 1);
v___x_4493_ = lean_unsigned_to_nat(0u);
v___x_4494_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4475_, v_handler_4476_, v_extensions_4477_, v_connectionContext_4478_, v_a_4492_);
v___x_4495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4493_, v___x_4479_, v___x_4494_, v___f_4480_);
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4496_, lean_object* v_handler_4497_, lean_object* v_extensions_4498_, lean_object* v_connectionContext_4499_, lean_object* v___x_4500_, lean_object* v___f_4501_, lean_object* v_x_4502_, lean_object* v___y_4503_){
_start:
{
uint8_t v___x_5364__boxed_4504_; lean_object* v_res_4505_; 
v___x_5364__boxed_4504_ = lean_unbox(v___x_4500_);
v_res_4505_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4496_, v_handler_4497_, v_extensions_4498_, v_connectionContext_4499_, v___x_5364__boxed_4504_, v___f_4501_, v_x_4502_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4506_, lean_object* v_responseBodyInstance_4507_, lean_object* v_handler_4508_, lean_object* v_config_4509_, lean_object* v_connectionContext_4510_, lean_object* v_events_4511_, lean_object* v___x_4512_, uint8_t v___x_4513_, lean_object* v___f_4514_, lean_object* v_____r_4515_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4506_, v_responseBodyInstance_4507_, v_handler_4508_, v_config_4509_, v_connectionContext_4510_, v_events_4511_, v___x_4512_);
v___x_4519_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4517_, v___x_4513_, v___x_4518_, v___f_4514_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4520_, lean_object* v_responseBodyInstance_4521_, lean_object* v_handler_4522_, lean_object* v_config_4523_, lean_object* v_connectionContext_4524_, lean_object* v_events_4525_, lean_object* v___x_4526_, lean_object* v___x_4527_, lean_object* v___f_4528_, lean_object* v_____r_4529_, lean_object* v___y_4530_){
_start:
{
uint8_t v___x_5403__boxed_4531_; lean_object* v_res_4532_; 
v___x_5403__boxed_4531_ = lean_unbox(v___x_4527_);
v_res_4532_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4520_, v_responseBodyInstance_4521_, v_handler_4522_, v_config_4523_, v_connectionContext_4524_, v_events_4525_, v___x_4526_, v___x_5403__boxed_4531_, v___f_4528_, v_____r_4529_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4533_, lean_object* v___f_4534_, lean_object* v_x_4535_){
_start:
{
if (lean_obj_tag(v_x_4535_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v___f_4534_);
lean_dec_ref(v___x_4533_);
v_a_4537_ = lean_ctor_get(v_x_4535_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_x_4535_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4539_ = v_x_4535_;
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v_x_4535_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4557_; 
v_a_4546_ = lean_ctor_get(v_x_4535_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v_x_4535_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4548_ = v_x_4535_;
v_isShared_4549_ = v_isSharedCheck_4557_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v_x_4535_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4557_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
if (lean_obj_tag(v_a_4546_) == 0)
{
lean_object* v___x_4550_; lean_object* v___x_4552_; 
lean_dec_ref(v___f_4534_);
v___x_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4533_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v___x_4550_);
v___x_4552_ = v___x_4548_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4550_);
v___x_4552_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4553_; 
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
}
else
{
lean_object* v_val_4555_; lean_object* v___x_4556_; 
lean_del_object(v___x_4548_);
lean_dec_ref(v___x_4533_);
v_val_4555_ = lean_ctor_get(v_a_4546_, 0);
lean_inc(v_val_4555_);
lean_dec_ref_known(v_a_4546_, 1);
v___x_4556_ = lean_apply_2(v___f_4534_, v_val_4555_, lean_box(0));
return v___x_4556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4558_, lean_object* v___f_4559_, lean_object* v_x_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4558_, v___f_4559_, v_x_4560_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4563_, lean_object* v_responseBodyInstance_4564_, lean_object* v_handler_4565_, lean_object* v_config_4566_, lean_object* v_connectionContext_4567_, uint8_t v___x_4568_, lean_object* v___f_4569_, lean_object* v_inst_4570_, lean_object* v_socket_4571_, lean_object* v___f_4572_, lean_object* v___f_4573_, lean_object* v_x_4574_, lean_object* v_____s_4575_){
_start:
{
lean_object* v_machine_4577_; lean_object* v_reader_4578_; lean_object* v_requestStream_4579_; lean_object* v_keepAliveTimeout_4580_; lean_object* v_currentTimeout_4581_; lean_object* v_headerTimeout_4582_; lean_object* v_response_4583_; lean_object* v_respStream_4584_; uint8_t v_requiresData_4585_; lean_object* v_expectData_4586_; uint8_t v_handlerDispatched_4587_; lean_object* v_pendingHead_4588_; lean_object* v_writer_4589_; lean_object* v_state_4590_; uint8_t v___x_4591_; 
v_machine_4577_ = lean_ctor_get(v_____s_4575_, 0);
v_reader_4578_ = lean_ctor_get(v_machine_4577_, 0);
v_requestStream_4579_ = lean_ctor_get(v_____s_4575_, 1);
v_keepAliveTimeout_4580_ = lean_ctor_get(v_____s_4575_, 2);
v_currentTimeout_4581_ = lean_ctor_get(v_____s_4575_, 3);
v_headerTimeout_4582_ = lean_ctor_get(v_____s_4575_, 4);
v_response_4583_ = lean_ctor_get(v_____s_4575_, 5);
v_respStream_4584_ = lean_ctor_get(v_____s_4575_, 6);
v_requiresData_4585_ = lean_ctor_get_uint8(v_____s_4575_, sizeof(void*)*9);
v_expectData_4586_ = lean_ctor_get(v_____s_4575_, 7);
v_handlerDispatched_4587_ = lean_ctor_get_uint8(v_____s_4575_, sizeof(void*)*9 + 1);
v_pendingHead_4588_ = lean_ctor_get(v_____s_4575_, 8);
v_writer_4589_ = lean_ctor_get(v_machine_4577_, 1);
v_state_4590_ = lean_ctor_get(v_reader_4578_, 0);
v___x_4591_ = 0;
if (lean_obj_tag(v_state_4590_) == 6)
{
lean_object* v_state_4613_; 
v_state_4613_ = lean_ctor_get(v_writer_4589_, 2);
if (lean_obj_tag(v_state_4613_) == 7)
{
lean_object* v_outputData_4614_; lean_object* v_size_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; 
v_outputData_4614_ = lean_ctor_get(v_writer_4589_, 1);
v_size_4615_ = lean_ctor_get(v_outputData_4614_, 1);
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = lean_nat_dec_eq(v_size_4615_, v___x_4616_);
if (v___x_4617_ == 0)
{
lean_inc(v_pendingHead_4588_);
lean_inc(v_expectData_4586_);
lean_inc(v_respStream_4584_);
lean_inc_ref(v_response_4583_);
lean_inc(v_headerTimeout_4582_);
lean_inc(v_currentTimeout_4581_);
lean_inc(v_keepAliveTimeout_4580_);
lean_inc_ref(v_requestStream_4579_);
lean_inc_ref(v_machine_4577_);
lean_dec_ref(v_____s_4575_);
goto v___jp_4592_;
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_dec_ref(v___f_4573_);
lean_dec_ref(v___f_4572_);
lean_dec(v_socket_4571_);
lean_dec_ref(v_inst_4570_);
lean_dec_ref(v___f_4569_);
lean_dec_ref(v_connectionContext_4567_);
lean_dec_ref(v_config_4566_);
lean_dec(v_handler_4565_);
lean_dec_ref(v_responseBodyInstance_4564_);
lean_dec_ref(v_h_4563_);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v_____s_4575_);
v___x_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
return v___x_4620_;
}
}
else
{
lean_inc(v_pendingHead_4588_);
lean_inc(v_expectData_4586_);
lean_inc(v_respStream_4584_);
lean_inc_ref(v_response_4583_);
lean_inc(v_headerTimeout_4582_);
lean_inc(v_currentTimeout_4581_);
lean_inc(v_keepAliveTimeout_4580_);
lean_inc_ref(v_requestStream_4579_);
lean_inc_ref(v_machine_4577_);
lean_dec_ref(v_____s_4575_);
goto v___jp_4592_;
}
}
else
{
lean_inc(v_pendingHead_4588_);
lean_inc(v_expectData_4586_);
lean_inc(v_respStream_4584_);
lean_inc_ref(v_response_4583_);
lean_inc(v_headerTimeout_4582_);
lean_inc(v_currentTimeout_4581_);
lean_inc(v_keepAliveTimeout_4580_);
lean_inc_ref(v_requestStream_4579_);
lean_inc_ref(v_machine_4577_);
lean_dec_ref(v_____s_4575_);
goto v___jp_4592_;
}
v___jp_4592_:
{
lean_object* v___x_4593_; lean_object* v_snd_4594_; lean_object* v_output_4595_; lean_object* v_fst_4596_; lean_object* v_events_4597_; lean_object* v_data_4598_; lean_object* v_size_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___f_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4593_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4591_, v_machine_4577_);
v_snd_4594_ = lean_ctor_get(v___x_4593_, 1);
lean_inc(v_snd_4594_);
v_output_4595_ = lean_ctor_get(v_snd_4594_, 1);
lean_inc_ref(v_output_4595_);
v_fst_4596_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_fst_4596_);
lean_dec_ref(v___x_4593_);
v_events_4597_ = lean_ctor_get(v_snd_4594_, 0);
lean_inc_ref_n(v_events_4597_, 2);
lean_dec(v_snd_4594_);
v_data_4598_ = lean_ctor_get(v_output_4595_, 0);
lean_inc_ref(v_data_4598_);
v_size_4599_ = lean_ctor_get(v_output_4595_, 1);
lean_inc(v_size_4599_);
lean_dec_ref(v_output_4595_);
v___x_4600_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4600_, 0, v_fst_4596_);
lean_ctor_set(v___x_4600_, 1, v_requestStream_4579_);
lean_ctor_set(v___x_4600_, 2, v_keepAliveTimeout_4580_);
lean_ctor_set(v___x_4600_, 3, v_currentTimeout_4581_);
lean_ctor_set(v___x_4600_, 4, v_headerTimeout_4582_);
lean_ctor_set(v___x_4600_, 5, v_response_4583_);
lean_ctor_set(v___x_4600_, 6, v_respStream_4584_);
lean_ctor_set(v___x_4600_, 7, v_expectData_4586_);
lean_ctor_set(v___x_4600_, 8, v_pendingHead_4588_);
lean_ctor_set_uint8(v___x_4600_, sizeof(void*)*9, v_requiresData_4585_);
lean_ctor_set_uint8(v___x_4600_, sizeof(void*)*9 + 1, v_handlerDispatched_4587_);
v___x_4601_ = lean_box(v___x_4568_);
lean_inc_ref(v___f_4569_);
lean_inc_ref(v___x_4600_);
lean_inc_ref(v_connectionContext_4567_);
lean_inc_ref(v_config_4566_);
lean_inc(v_handler_4565_);
lean_inc_ref(v_responseBodyInstance_4564_);
lean_inc_ref(v_h_4563_);
v___f_4602_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4602_, 0, v_h_4563_);
lean_closure_set(v___f_4602_, 1, v_responseBodyInstance_4564_);
lean_closure_set(v___f_4602_, 2, v_handler_4565_);
lean_closure_set(v___f_4602_, 3, v_config_4566_);
lean_closure_set(v___f_4602_, 4, v_connectionContext_4567_);
lean_closure_set(v___f_4602_, 5, v_events_4597_);
lean_closure_set(v___f_4602_, 6, v___x_4600_);
lean_closure_set(v___f_4602_, 7, v___x_4601_);
lean_closure_set(v___f_4602_, 8, v___f_4569_);
v___x_4603_ = lean_unsigned_to_nat(0u);
v___x_4604_ = lean_nat_dec_lt(v___x_4603_, v_size_4599_);
lean_dec(v_size_4599_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
lean_dec_ref(v___f_4602_);
lean_dec_ref(v_data_4598_);
lean_dec_ref(v___f_4573_);
lean_dec_ref(v___f_4572_);
lean_dec(v_socket_4571_);
lean_dec_ref(v_inst_4570_);
v___x_4605_ = lean_box(0);
v___x_4606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4563_, v_responseBodyInstance_4564_, v_handler_4565_, v_config_4566_, v_connectionContext_4567_, v_events_4597_, v___x_4600_, v___x_4568_, v___f_4569_, v___x_4605_);
return v___x_4606_;
}
else
{
lean_object* v_sendAll_4607_; lean_object* v___f_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
lean_dec_ref(v_events_4597_);
lean_dec_ref(v___f_4569_);
lean_dec_ref(v_connectionContext_4567_);
lean_dec_ref(v_config_4566_);
lean_dec(v_handler_4565_);
lean_dec_ref(v_responseBodyInstance_4564_);
lean_dec_ref(v_h_4563_);
v_sendAll_4607_ = lean_ctor_get(v_inst_4570_, 1);
lean_inc_ref(v_sendAll_4607_);
lean_dec_ref(v_inst_4570_);
v___f_4608_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4608_, 0, v___x_4600_);
lean_closure_set(v___f_4608_, 1, v___f_4602_);
v___x_4609_ = lean_apply_3(v_sendAll_4607_, v_socket_4571_, v_data_4598_, lean_box(0));
v___x_4610_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4603_, v___x_4568_, v___x_4609_, v___f_4572_);
v___x_4611_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4603_, v___x_4568_, v___x_4610_, v___f_4573_);
v___x_4612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4603_, v___x_4568_, v___x_4611_, v___f_4608_);
return v___x_4612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4621_, lean_object* v_responseBodyInstance_4622_, lean_object* v_handler_4623_, lean_object* v_config_4624_, lean_object* v_connectionContext_4625_, lean_object* v___x_4626_, lean_object* v___f_4627_, lean_object* v_inst_4628_, lean_object* v_socket_4629_, lean_object* v___f_4630_, lean_object* v___f_4631_, lean_object* v_x_4632_, lean_object* v_____s_4633_, lean_object* v___y_4634_){
_start:
{
uint8_t v___x_5477__boxed_4635_; lean_object* v_res_4636_; 
v___x_5477__boxed_4635_ = lean_unbox(v___x_4626_);
v_res_4636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4621_, v_responseBodyInstance_4622_, v_handler_4623_, v_config_4624_, v_connectionContext_4625_, v___x_5477__boxed_4635_, v___f_4627_, v_inst_4628_, v_socket_4629_, v___f_4630_, v___f_4631_, v_x_4632_, v_____s_4633_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4637_, lean_object* v_x_4638_){
_start:
{
if (lean_obj_tag(v_x_4638_) == 0)
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4648_; 
v_a_4640_ = lean_ctor_get(v_x_4638_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v_x_4638_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4642_ = v_x_4638_;
v_isShared_4643_ = v_isSharedCheck_4648_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v_x_4638_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4648_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
lean_object* v___x_4646_; 
v___x_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
return v___x_4646_;
}
}
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
lean_dec_ref_known(v_x_4638_, 1);
v___x_4649_ = l_IO_Promise_result_x21___redArg(v_a_4637_);
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4651_, lean_object* v_x_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4651_, v_x_4652_);
lean_dec(v_a_4651_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4655_, lean_object* v___x_4656_, lean_object* v___x_4657_, uint8_t v___x_4658_, lean_object* v_x_4659_){
_start:
{
if (lean_obj_tag(v_x_4659_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4669_; 
lean_dec_ref(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec_ref(v___f_4655_);
v_a_4661_ = lean_ctor_get(v_x_4659_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v_x_4659_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4663_ = v_x_4659_;
v_isShared_4664_ = v_isSharedCheck_4669_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v_x_4659_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4669_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4667_; 
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
return v___x_4667_;
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4681_; 
v_a_4670_ = lean_ctor_get(v_x_4659_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_x_4659_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4672_ = v_x_4659_;
v_isShared_4673_ = v_isSharedCheck_4681_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v_x_4659_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4681_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___f_4674_; lean_object* v___x_4675_; lean_object* v___x_4677_; 
lean_inc(v_a_4670_);
v___f_4674_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4674_, 0, v_a_4670_);
lean_inc(v___x_4656_);
v___x_4675_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4655_, v___x_4656_, v_a_4670_, v___x_4657_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 0, v___x_4675_);
v___x_4677_ = v___x_4672_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4675_);
v___x_4677_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
v___x_4679_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4656_, v___x_4658_, v___x_4678_, v___f_4674_);
return v___x_4679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4682_, lean_object* v___x_4683_, lean_object* v___x_4684_, lean_object* v___x_4685_, lean_object* v_x_4686_, lean_object* v___y_4687_){
_start:
{
uint8_t v___x_5580__boxed_4688_; lean_object* v_res_4689_; 
v___x_5580__boxed_4688_ = lean_unbox(v___x_4685_);
v_res_4689_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4682_, v___x_4683_, v___x_4684_, v___x_5580__boxed_4688_, v_x_4686_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4690_, lean_object* v_h_4691_, lean_object* v_responseBodyInstance_4692_, lean_object* v_handler_4693_, lean_object* v___f_4694_, lean_object* v_inst_4695_, lean_object* v_socket_4696_, lean_object* v_connectionContext_4697_, lean_object* v_extensions_4698_, lean_object* v___f_4699_, lean_object* v___f_4700_, lean_object* v_machine_4701_, lean_object* v_a_4702_, lean_object* v___x_4703_, lean_object* v___f_4704_, lean_object* v_x_4705_){
_start:
{
if (lean_obj_tag(v_x_4705_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4715_; 
lean_dec_ref(v___f_4704_);
lean_dec(v___x_4703_);
lean_dec_ref(v_a_4702_);
lean_dec_ref(v_machine_4701_);
lean_dec_ref(v___f_4700_);
lean_dec_ref(v___f_4699_);
lean_dec(v_extensions_4698_);
lean_dec_ref(v_connectionContext_4697_);
lean_dec(v_socket_4696_);
lean_dec_ref(v_inst_4695_);
lean_dec_ref(v___f_4694_);
lean_dec(v_handler_4693_);
lean_dec_ref(v_responseBodyInstance_4692_);
lean_dec_ref(v_h_4691_);
lean_dec_ref(v_config_4690_);
v_a_4707_ = lean_ctor_get(v_x_4705_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_x_4705_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4709_ = v_x_4705_;
v_isShared_4710_ = v_isSharedCheck_4715_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v_x_4705_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4715_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; 
v___x_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4712_);
return v___x_4713_;
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4741_; 
v_a_4716_ = lean_ctor_get(v_x_4705_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_x_4705_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4718_ = v_x_4705_;
v_isShared_4719_ = v_isSharedCheck_4741_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v_x_4705_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4741_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v_keepAliveTimeout_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___f_4725_; lean_object* v___x_4726_; lean_object* v___f_4727_; lean_object* v___x_4728_; lean_object* v___f_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___f_4733_; lean_object* v___x_4734_; lean_object* v___x_4736_; 
v_keepAliveTimeout_4720_ = lean_ctor_get(v_config_4690_, 5);
lean_inc_n(v_keepAliveTimeout_4720_, 2);
v___x_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4721_, 0, v_keepAliveTimeout_4720_);
v___x_4722_ = lean_box(0);
v___x_4723_ = 0;
v___x_4724_ = lean_box(v___x_4723_);
lean_inc_ref_n(v_connectionContext_4697_, 2);
lean_inc(v_socket_4696_);
lean_inc_ref(v_inst_4695_);
lean_inc_ref(v_config_4690_);
lean_inc_n(v_handler_4693_, 2);
lean_inc_ref(v_responseBodyInstance_4692_);
lean_inc_ref_n(v_h_4691_, 2);
v___f_4725_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4725_, 0, v___x_4724_);
lean_closure_set(v___f_4725_, 1, v_h_4691_);
lean_closure_set(v___f_4725_, 2, v_responseBodyInstance_4692_);
lean_closure_set(v___f_4725_, 3, v_handler_4693_);
lean_closure_set(v___f_4725_, 4, v_config_4690_);
lean_closure_set(v___f_4725_, 5, v___f_4694_);
lean_closure_set(v___f_4725_, 6, v_inst_4695_);
lean_closure_set(v___f_4725_, 7, v_socket_4696_);
lean_closure_set(v___f_4725_, 8, v_connectionContext_4697_);
v___x_4726_ = lean_box(v___x_4723_);
v___f_4727_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4727_, 0, v_h_4691_);
lean_closure_set(v___f_4727_, 1, v_handler_4693_);
lean_closure_set(v___f_4727_, 2, v_extensions_4698_);
lean_closure_set(v___f_4727_, 3, v_connectionContext_4697_);
lean_closure_set(v___f_4727_, 4, v___x_4726_);
lean_closure_set(v___f_4727_, 5, v___f_4725_);
v___x_4728_ = lean_box(v___x_4723_);
v___f_4729_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4729_, 0, v_h_4691_);
lean_closure_set(v___f_4729_, 1, v_responseBodyInstance_4692_);
lean_closure_set(v___f_4729_, 2, v_handler_4693_);
lean_closure_set(v___f_4729_, 3, v_config_4690_);
lean_closure_set(v___f_4729_, 4, v_connectionContext_4697_);
lean_closure_set(v___f_4729_, 5, v___x_4728_);
lean_closure_set(v___f_4729_, 6, v___f_4727_);
lean_closure_set(v___f_4729_, 7, v_inst_4695_);
lean_closure_set(v___f_4729_, 8, v_socket_4696_);
lean_closure_set(v___f_4729_, 9, v___f_4699_);
lean_closure_set(v___f_4729_, 10, v___f_4700_);
v___x_4730_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4730_, 0, v_machine_4701_);
lean_ctor_set(v___x_4730_, 1, v_a_4702_);
lean_ctor_set(v___x_4730_, 2, v___x_4721_);
lean_ctor_set(v___x_4730_, 3, v_keepAliveTimeout_4720_);
lean_ctor_set(v___x_4730_, 4, v___x_4722_);
lean_ctor_set(v___x_4730_, 5, v_a_4716_);
lean_ctor_set(v___x_4730_, 6, v___x_4722_);
lean_ctor_set(v___x_4730_, 7, v___x_4703_);
lean_ctor_set(v___x_4730_, 8, v___x_4722_);
lean_ctor_set_uint8(v___x_4730_, sizeof(void*)*9, v___x_4723_);
lean_ctor_set_uint8(v___x_4730_, sizeof(void*)*9 + 1, v___x_4723_);
v___x_4731_ = lean_unsigned_to_nat(0u);
v___x_4732_ = lean_box(v___x_4723_);
v___f_4733_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4733_, 0, v___f_4729_);
lean_closure_set(v___f_4733_, 1, v___x_4731_);
lean_closure_set(v___f_4733_, 2, v___x_4730_);
lean_closure_set(v___f_4733_, 3, v___x_4732_);
v___x_4734_ = lean_io_promise_new();
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 0, v___x_4734_);
v___x_4736_ = v___x_4718_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4734_);
v___x_4736_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
v___x_4738_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4731_, v___x_4723_, v___x_4737_, v___f_4733_);
v___x_4739_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4731_, v___x_4723_, v___x_4738_, v___f_4704_);
return v___x_4739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4742_ = _args[0];
lean_object* v_h_4743_ = _args[1];
lean_object* v_responseBodyInstance_4744_ = _args[2];
lean_object* v_handler_4745_ = _args[3];
lean_object* v___f_4746_ = _args[4];
lean_object* v_inst_4747_ = _args[5];
lean_object* v_socket_4748_ = _args[6];
lean_object* v_connectionContext_4749_ = _args[7];
lean_object* v_extensions_4750_ = _args[8];
lean_object* v___f_4751_ = _args[9];
lean_object* v___f_4752_ = _args[10];
lean_object* v_machine_4753_ = _args[11];
lean_object* v_a_4754_ = _args[12];
lean_object* v___x_4755_ = _args[13];
lean_object* v___f_4756_ = _args[14];
lean_object* v_x_4757_ = _args[15];
lean_object* v___y_4758_ = _args[16];
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4742_, v_h_4743_, v_responseBodyInstance_4744_, v_handler_4745_, v___f_4746_, v_inst_4747_, v_socket_4748_, v_connectionContext_4749_, v_extensions_4750_, v___f_4751_, v___f_4752_, v_machine_4753_, v_a_4754_, v___x_4755_, v___f_4756_, v_x_4757_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4760_, lean_object* v_h_4761_, lean_object* v_responseBodyInstance_4762_, lean_object* v_handler_4763_, lean_object* v___f_4764_, lean_object* v_inst_4765_, lean_object* v_socket_4766_, lean_object* v_connectionContext_4767_, lean_object* v_extensions_4768_, lean_object* v___f_4769_, lean_object* v___f_4770_, lean_object* v_machine_4771_, lean_object* v___f_4772_, lean_object* v_x_4773_){
_start:
{
if (lean_obj_tag(v_x_4773_) == 0)
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4783_; 
lean_dec_ref(v___f_4772_);
lean_dec_ref(v_machine_4771_);
lean_dec_ref(v___f_4770_);
lean_dec_ref(v___f_4769_);
lean_dec(v_extensions_4768_);
lean_dec_ref(v_connectionContext_4767_);
lean_dec(v_socket_4766_);
lean_dec_ref(v_inst_4765_);
lean_dec_ref(v___f_4764_);
lean_dec(v_handler_4763_);
lean_dec_ref(v_responseBodyInstance_4762_);
lean_dec_ref(v_h_4761_);
lean_dec_ref(v_config_4760_);
v_a_4775_ = lean_ctor_get(v_x_4773_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_x_4773_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4777_ = v_x_4773_;
v_isShared_4778_ = v_isSharedCheck_4783_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v_x_4773_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4783_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4781_; 
v___x_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
return v___x_4781_;
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4798_; 
v_a_4784_ = lean_ctor_get(v_x_4773_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_x_4773_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4786_ = v_x_4773_;
v_isShared_4787_ = v_isSharedCheck_4798_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v_x_4773_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4798_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v___f_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4788_ = lean_box(0);
v___f_4789_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4789_, 0, v_config_4760_);
lean_closure_set(v___f_4789_, 1, v_h_4761_);
lean_closure_set(v___f_4789_, 2, v_responseBodyInstance_4762_);
lean_closure_set(v___f_4789_, 3, v_handler_4763_);
lean_closure_set(v___f_4789_, 4, v___f_4764_);
lean_closure_set(v___f_4789_, 5, v_inst_4765_);
lean_closure_set(v___f_4789_, 6, v_socket_4766_);
lean_closure_set(v___f_4789_, 7, v_connectionContext_4767_);
lean_closure_set(v___f_4789_, 8, v_extensions_4768_);
lean_closure_set(v___f_4789_, 9, v___f_4769_);
lean_closure_set(v___f_4789_, 10, v___f_4770_);
lean_closure_set(v___f_4789_, 11, v_machine_4771_);
lean_closure_set(v___f_4789_, 12, v_a_4784_);
lean_closure_set(v___f_4789_, 13, v___x_4788_);
lean_closure_set(v___f_4789_, 14, v___f_4772_);
v___x_4790_ = lean_unsigned_to_nat(0u);
v___x_4791_ = 0;
v___x_4792_ = l_Std_CloseableChannel_new___redArg(v___x_4788_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v___x_4792_);
v___x_4794_ = v___x_4786_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4792_);
v___x_4794_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
v___x_4796_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4790_, v___x_4791_, v___x_4795_, v___f_4789_);
return v___x_4796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4799_, lean_object* v_h_4800_, lean_object* v_responseBodyInstance_4801_, lean_object* v_handler_4802_, lean_object* v___f_4803_, lean_object* v_inst_4804_, lean_object* v_socket_4805_, lean_object* v_connectionContext_4806_, lean_object* v_extensions_4807_, lean_object* v___f_4808_, lean_object* v___f_4809_, lean_object* v_machine_4810_, lean_object* v___f_4811_, lean_object* v_x_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4799_, v_h_4800_, v_responseBodyInstance_4801_, v_handler_4802_, v___f_4803_, v_inst_4804_, v_socket_4805_, v_connectionContext_4806_, v_extensions_4807_, v___f_4808_, v___f_4809_, v_machine_4810_, v___f_4811_, v_x_4812_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4818_, lean_object* v_h_4819_, lean_object* v_connection_4820_, lean_object* v_config_4821_, lean_object* v_connectionContext_4822_, lean_object* v_handler_4823_){
_start:
{
lean_object* v_responseBodyInstance_4825_; lean_object* v_onFailure_4826_; lean_object* v_socket_4827_; lean_object* v_machine_4828_; lean_object* v_extensions_4829_; lean_object* v___f_4830_; lean_object* v___f_4831_; lean_object* v___f_4832_; lean_object* v___f_4833_; lean_object* v___f_4834_; lean_object* v___f_4835_; lean_object* v___f_4836_; lean_object* v___f_4837_; lean_object* v___f_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v_responseBodyInstance_4825_ = lean_ctor_get(v_h_4819_, 0);
lean_inc_ref_n(v_responseBodyInstance_4825_, 2);
v_onFailure_4826_ = lean_ctor_get(v_h_4819_, 2);
v_socket_4827_ = lean_ctor_get(v_connection_4820_, 0);
lean_inc_n(v_socket_4827_, 2);
v_machine_4828_ = lean_ctor_get(v_connection_4820_, 1);
lean_inc_ref(v_machine_4828_);
v_extensions_4829_ = lean_ctor_get(v_connection_4820_, 2);
lean_inc(v_extensions_4829_);
lean_dec_ref(v_connection_4820_);
v___f_4830_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4831_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4832_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4823_);
lean_inc_ref(v_onFailure_4826_);
v___f_4833_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4833_, 0, v_onFailure_4826_);
lean_closure_set(v___f_4833_, 1, v_handler_4823_);
lean_closure_set(v___f_4833_, 2, v___f_4832_);
v___f_4834_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4818_);
v___f_4835_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4835_, 0, v_inst_4818_);
lean_closure_set(v___f_4835_, 1, v_socket_4827_);
lean_inc_ref(v___f_4835_);
v___f_4836_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4836_, 0, v___f_4835_);
v___f_4837_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4837_, 0, v_responseBodyInstance_4825_);
lean_closure_set(v___f_4837_, 1, v___f_4836_);
lean_closure_set(v___f_4837_, 2, v___f_4835_);
lean_closure_set(v___f_4837_, 3, v___f_4830_);
v___f_4838_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4838_, 0, v_config_4821_);
lean_closure_set(v___f_4838_, 1, v_h_4819_);
lean_closure_set(v___f_4838_, 2, v_responseBodyInstance_4825_);
lean_closure_set(v___f_4838_, 3, v_handler_4823_);
lean_closure_set(v___f_4838_, 4, v___f_4834_);
lean_closure_set(v___f_4838_, 5, v_inst_4818_);
lean_closure_set(v___f_4838_, 6, v_socket_4827_);
lean_closure_set(v___f_4838_, 7, v_connectionContext_4822_);
lean_closure_set(v___f_4838_, 8, v_extensions_4829_);
lean_closure_set(v___f_4838_, 9, v___f_4831_);
lean_closure_set(v___f_4838_, 10, v___f_4833_);
lean_closure_set(v___f_4838_, 11, v_machine_4828_);
lean_closure_set(v___f_4838_, 12, v___f_4837_);
v___x_4839_ = lean_unsigned_to_nat(0u);
v___x_4840_ = 0;
v___x_4841_ = l_Std_Http_Body_mkStream();
v___x_4842_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4839_, v___x_4840_, v___x_4841_, v___f_4838_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4843_, lean_object* v_h_4844_, lean_object* v_connection_4845_, lean_object* v_config_4846_, lean_object* v_connectionContext_4847_, lean_object* v_handler_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4843_, v_h_4844_, v_connection_4845_, v_config_4846_, v_connectionContext_4847_, v_handler_4848_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4851_, lean_object* v_00_u03c3_4852_, lean_object* v_inst_4853_, lean_object* v_h_4854_, lean_object* v_connection_4855_, lean_object* v_config_4856_, lean_object* v_connectionContext_4857_, lean_object* v_handler_4858_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4853_, v_h_4854_, v_connection_4855_, v_config_4856_, v_connectionContext_4857_, v_handler_4858_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4861_, lean_object* v_00_u03c3_4862_, lean_object* v_inst_4863_, lean_object* v_h_4864_, lean_object* v_connection_4865_, lean_object* v_config_4866_, lean_object* v_connectionContext_4867_, lean_object* v_handler_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4861_, v_00_u03c3_4862_, v_inst_4863_, v_h_4864_, v_connection_4865_, v_config_4866_, v_connectionContext_4867_, v_handler_4868_);
return v_res_4870_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = 0;
v___x_4872_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4871_);
return v___x_4872_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_unsigned_to_nat(4096u);
v___x_4874_ = lean_mk_empty_byte_array(v___x_4873_);
return v___x_4874_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4876_ = l_ByteArray_mkIterator(v___x_4875_);
return v___x_4876_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4877_ = 0;
v___x_4878_ = lean_unsigned_to_nat(0u);
v___x_4879_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4880_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4881_ = lean_box(0);
v___x_4882_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
lean_ctor_set(v___x_4882_, 1, v___x_4880_);
lean_ctor_set(v___x_4882_, 2, v___x_4879_);
lean_ctor_set(v___x_4882_, 3, v___x_4878_);
lean_ctor_set(v___x_4882_, 4, v___x_4878_);
lean_ctor_set(v___x_4882_, 5, v___x_4878_);
lean_ctor_set_uint8(v___x_4882_, sizeof(void*)*6, v___x_4877_);
return v___x_4882_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = 1;
v___x_4891_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4890_);
return v___x_4891_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4892_; uint8_t v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = 0;
v___x_4894_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4895_ = lean_box(0);
v___x_4896_ = lean_box(0);
v___x_4897_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4898_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4899_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
lean_ctor_set(v___x_4899_, 1, v___x_4897_);
lean_ctor_set(v___x_4899_, 2, v___x_4896_);
lean_ctor_set(v___x_4899_, 3, v___x_4895_);
lean_ctor_set(v___x_4899_, 4, v___x_4894_);
lean_ctor_set(v___x_4899_, 5, v___x_4892_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*6, v___x_4893_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*6 + 1, v___x_4893_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*6 + 2, v___x_4893_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4900_, lean_object* v_client_4901_, lean_object* v_extensions_4902_, lean_object* v_inst_4903_, lean_object* v_inst_4904_, lean_object* v_handler_4905_, lean_object* v_x_4906_){
_start:
{
if (lean_obj_tag(v_x_4906_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4916_; 
lean_dec(v_handler_4905_);
lean_dec_ref(v_inst_4904_);
lean_dec_ref(v_inst_4903_);
lean_dec(v_extensions_4902_);
lean_dec(v_client_4901_);
lean_dec_ref(v_config_4900_);
v_a_4908_ = lean_ctor_get(v_x_4906_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v_x_4906_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4910_ = v_x_4906_;
v_isShared_4911_ = v_isSharedCheck_4916_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v_x_4906_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4916_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4913_; 
if (v_isShared_4911_ == 0)
{
v___x_4913_ = v___x_4910_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4908_);
v___x_4913_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
lean_object* v___x_4914_; 
v___x_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4913_);
return v___x_4914_;
}
}
}
else
{
lean_object* v_a_4917_; uint8_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; uint8_t v_enableKeepAlive_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_a_4917_ = lean_ctor_get(v_x_4906_, 0);
lean_inc(v_a_4917_);
lean_dec_ref_known(v_x_4906_, 1);
v___x_4918_ = 0;
v___x_4919_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4920_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4921_ = lean_box(0);
v___x_4922_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4923_ = l_Std_Http_Config_toH1Config(v_config_4900_);
v_enableKeepAlive_4924_ = lean_ctor_get_uint8(v___x_4923_, sizeof(void*)*18);
v___x_4925_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4925_, 0, v___x_4919_);
lean_ctor_set(v___x_4925_, 1, v___x_4922_);
lean_ctor_set(v___x_4925_, 2, v___x_4923_);
lean_ctor_set(v___x_4925_, 3, v___x_4920_);
lean_ctor_set(v___x_4925_, 4, v___x_4921_);
lean_ctor_set(v___x_4925_, 5, v___x_4921_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*6, v_enableKeepAlive_4924_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*6 + 1, v___x_4918_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*6 + 2, v___x_4918_);
v___x_4926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4926_, 0, v_client_4901_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
lean_ctor_set(v___x_4926_, 2, v_extensions_4902_);
v___x_4927_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4903_, v_inst_4904_, v___x_4926_, v_config_4900_, v_a_4917_, v_handler_4905_);
return v___x_4927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4928_, lean_object* v_client_4929_, lean_object* v_extensions_4930_, lean_object* v_inst_4931_, lean_object* v_inst_4932_, lean_object* v_handler_4933_, lean_object* v_x_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4928_, v_client_4929_, v_extensions_4930_, v_inst_4931_, v_inst_4932_, v_handler_4933_, v_x_4934_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4937_, lean_object* v_inst_4938_, lean_object* v_client_4939_, lean_object* v_handler_4940_, lean_object* v_config_4941_, lean_object* v_extensions_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v___f_4945_; lean_object* v___x_4946_; uint8_t v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___f_4945_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4945_, 0, v_config_4941_);
lean_closure_set(v___f_4945_, 1, v_client_4939_);
lean_closure_set(v___f_4945_, 2, v_extensions_4942_);
lean_closure_set(v___f_4945_, 3, v_inst_4937_);
lean_closure_set(v___f_4945_, 4, v_inst_4938_);
lean_closure_set(v___f_4945_, 5, v_handler_4940_);
v___x_4946_ = lean_unsigned_to_nat(0u);
v___x_4947_ = 0;
lean_inc_ref(v_a_4943_);
v___x_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4948_, 0, v_a_4943_);
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
v___x_4950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4946_, v___x_4947_, v___x_4949_, v___f_4945_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4951_, lean_object* v_inst_4952_, lean_object* v_client_4953_, lean_object* v_handler_4954_, lean_object* v_config_4955_, lean_object* v_extensions_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4951_, v_inst_4952_, v_client_4953_, v_handler_4954_, v_config_4955_, v_extensions_4956_, v_a_4957_);
lean_dec_ref(v_a_4957_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4960_, lean_object* v_00_u03c3_4961_, lean_object* v_inst_4962_, lean_object* v_inst_4963_, lean_object* v_client_4964_, lean_object* v_handler_4965_, lean_object* v_config_4966_, lean_object* v_extensions_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4962_, v_inst_4963_, v_client_4964_, v_handler_4965_, v_config_4966_, v_extensions_4967_, v_a_4968_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4971_, lean_object* v_00_u03c3_4972_, lean_object* v_inst_4973_, lean_object* v_inst_4974_, lean_object* v_client_4975_, lean_object* v_handler_4976_, lean_object* v_config_4977_, lean_object* v_extensions_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l_Std_Http_Server_serveConnection(v_t_4971_, v_00_u03c3_4972_, v_inst_4973_, v_inst_4974_, v_client_4975_, v_handler_4976_, v_config_4977_, v_extensions_4978_, v_a_4979_);
lean_dec_ref(v_a_4979_);
return v_res_4981_;
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
