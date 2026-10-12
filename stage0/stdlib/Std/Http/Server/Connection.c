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
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_146_){
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
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_146_ = stack[0].m_obj;
lean_object* v_res_162_;
v_res_162_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_146_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_163_);
return v_res_165_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_180_; 
v_a_172_ = lean_ctor_get(v_x_170_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_170_);
if (v_isSharedCheck_180_ == 0)
{
v___x_174_ = v_x_170_;
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v_x_170_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
else
{
lean_object* v___x_181_; 
lean_dec_ref_known(v_x_170_, 1);
v___x_181_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_181_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_170_ = stack[0].m_obj;
lean_object* v_res_182_;
v_res_182_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_170_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_183_);
return v_res_185_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_186_, lean_object* v_handler_187_, lean_object* v___f_188_, lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v_a_191_; lean_object* v_onFailure_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_a_191_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v_x_189_, 1);
v_onFailure_192_ = lean_ctor_get(v_inst_186_, 2);
lean_inc_ref(v_onFailure_192_);
lean_dec_ref(v_inst_186_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = 0;
v___x_195_ = lean_apply_3(v_onFailure_192_, v_handler_187_, v_a_191_, lean_box(0));
v___x_196_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_193_, v___x_194_, v___x_195_, v___f_188_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
lean_dec_ref(v___f_188_);
lean_dec(v_handler_187_);
lean_dec_ref(v_inst_186_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_x_189_);
return v___x_197_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_186_ = stack[0].m_obj;
lean_object* v_handler_187_ = stack[1].m_obj;
lean_object* v___f_188_ = stack[2].m_obj;
lean_object* v_x_189_ = stack[3].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_186_, v_handler_187_, v___f_188_, v_x_189_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_199_, lean_object* v_handler_200_, lean_object* v___f_201_, lean_object* v_x_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_199_, v_handler_200_, v___f_201_, v_x_202_);
return v_res_204_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_207_, 0, v_x_205_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_205_ = stack[0].m_obj;
lean_object* v_res_210_;
v_res_210_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_205_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_211_);
return v_res_213_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_216_, 0, v_x_214_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_214_ = stack[0].m_num;
lean_object* v_res_219_;
v_res_219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_214_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_220_, lean_object* v___y_221_){
_start:
{
uint8_t v_x_3795__boxed_222_; lean_object* v_res_223_; 
v_x_3795__boxed_222_ = lean_unbox(v_x_220_);
v_res_223_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3795__boxed_222_);
return v_res_223_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_224_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_x_224_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_224_ = stack[0].m_obj;
lean_object* v_res_229_;
v_res_229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_224_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_230_);
return v_res_232_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_233_){
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
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_233_ = stack[0].m_obj;
lean_object* v_res_238_;
v_res_238_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_233_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_239_);
return v_res_241_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_244_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_242_ = stack[0].m_obj;
lean_object* v_res_245_;
v_res_245_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_246_);
return v_res_248_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v_x_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_251_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_249_ = stack[0].m_obj;
lean_object* v_res_252_;
v_res_252_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_x_249_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v_x_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_x_253_);
return v_res_255_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v___f_256_, lean_object* v_response_257_, lean_object* v___x_258_, lean_object* v___f_259_, lean_object* v_requestBody_260_, lean_object* v___f_261_, lean_object* v_responseBody_262_, lean_object* v_inst_263_, lean_object* v___f_264_, lean_object* v_____r_265_, lean_object* v_selectables_266_){
_start:
{
lean_object* v_selectables_269_; lean_object* v_selectables_275_; lean_object* v_selectables_281_; 
if (lean_obj_tag(v_responseBody_262_) == 1)
{
lean_object* v_val_286_; lean_object* v_recvSelector_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_selectables_290_; 
v_val_286_ = lean_ctor_get(v_responseBody_262_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v_responseBody_262_, 1);
v_recvSelector_287_ = lean_ctor_get(v_inst_263_, 3);
lean_inc_ref(v_recvSelector_287_);
lean_dec_ref(v_inst_263_);
v___x_288_ = lean_apply_1(v_recvSelector_287_, v_val_286_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___f_264_);
v_selectables_290_ = lean_array_push(v_selectables_266_, v___x_289_);
v_selectables_281_ = v_selectables_290_;
goto v___jp_280_;
}
else
{
lean_dec_ref(v___f_264_);
lean_dec_ref(v_inst_263_);
lean_dec(v_responseBody_262_);
v_selectables_281_ = v_selectables_266_;
goto v___jp_280_;
}
v___jp_268_:
{
lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = 0;
v___x_272_ = l_Std_Async_Selectable_one___redArg(v_selectables_269_);
v___x_273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_270_, v___x_271_, v___x_272_, v___f_256_);
return v___x_273_;
}
v___jp_274_:
{
if (lean_obj_tag(v_response_257_) == 1)
{
lean_object* v_val_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_selectables_279_; 
v_val_276_ = lean_ctor_get(v_response_257_, 0);
lean_inc(v_val_276_);
lean_dec_ref_known(v_response_257_, 1);
v___x_277_ = l_Std_Channel_recvSelector___redArg(v___x_258_, v_val_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___f_259_);
v_selectables_279_ = lean_array_push(v_selectables_275_, v___x_278_);
v_selectables_269_ = v_selectables_279_;
goto v___jp_268_;
}
else
{
lean_dec_ref(v___f_259_);
lean_dec_ref(v___x_258_);
lean_dec(v_response_257_);
v_selectables_269_ = v_selectables_275_;
goto v___jp_268_;
}
}
v___jp_280_:
{
if (lean_obj_tag(v_requestBody_260_) == 1)
{
lean_object* v_val_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_selectables_285_; 
v_val_282_ = lean_ctor_get(v_requestBody_260_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v_requestBody_260_, 1);
v___x_283_ = l_Std_Http_Body_Stream_interestSelector(v_val_282_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___f_261_);
v_selectables_285_ = lean_array_push(v_selectables_281_, v___x_284_);
v_selectables_275_ = v_selectables_285_;
goto v___jp_274_;
}
else
{
lean_dec_ref(v___f_261_);
lean_dec(v_requestBody_260_);
v_selectables_275_ = v_selectables_281_;
goto v___jp_274_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_256_ = stack[0].m_obj;
lean_object* v_response_257_ = stack[1].m_obj;
lean_object* v___x_258_ = stack[2].m_obj;
lean_object* v___f_259_ = stack[3].m_obj;
lean_object* v_requestBody_260_ = stack[4].m_obj;
lean_object* v___f_261_ = stack[5].m_obj;
lean_object* v_responseBody_262_ = stack[6].m_obj;
lean_object* v_inst_263_ = stack[7].m_obj;
lean_object* v___f_264_ = stack[8].m_obj;
lean_object* v_____r_265_ = stack[9].m_obj;
lean_object* v_selectables_266_ = stack[10].m_obj;
lean_object* v_res_291_;
v_res_291_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_256_, v_response_257_, v___x_258_, v___f_259_, v_requestBody_260_, v___f_261_, v_responseBody_262_, v_inst_263_, v___f_264_, v_____r_265_, v_selectables_266_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v___f_292_, lean_object* v_response_293_, lean_object* v___x_294_, lean_object* v___f_295_, lean_object* v_requestBody_296_, lean_object* v___f_297_, lean_object* v_responseBody_298_, lean_object* v_inst_299_, lean_object* v___f_300_, lean_object* v_____r_301_, lean_object* v_selectables_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_292_, v_response_293_, v___x_294_, v___f_295_, v_requestBody_296_, v___f_297_, v_responseBody_298_, v_inst_299_, v___f_300_, v_____r_301_, v_selectables_302_);
return v_res_304_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v_token_305_, lean_object* v___f_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = 0;
v___x_311_ = l_Std_CancellationToken_getCancellationReason(v_token_305_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_309_, v___x_310_, v___x_313_, v___f_306_);
return v___x_314_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_305_ = stack[0].m_obj;
lean_object* v___f_306_ = stack[1].m_obj;
lean_object* v_x_307_ = stack[2].m_obj;
lean_object* v_res_315_;
v_res_315_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v_token_305_, v___f_306_, v_x_307_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v_token_316_, lean_object* v___f_317_, lean_object* v_x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v_token_316_, v___f_317_, v_x_318_);
return v_res_320_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v___f_321_, lean_object* v_selectables_322_, lean_object* v___f_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v___f_323_);
lean_dec_ref(v_selectables_322_);
lean_dec_ref(v___f_321_);
v_a_326_ = lean_ctor_get(v_x_324_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v_x_324_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v_x_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_333_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_335_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v_x_324_, 1);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_335_);
lean_ctor_set(v___x_336_, 1, v___f_321_);
v___x_337_ = lean_array_push(v_selectables_322_, v___x_336_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_apply_3(v___f_323_, v___x_338_, v___x_337_, lean_box(0));
return v___x_339_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_321_ = stack[0].m_obj;
lean_object* v_selectables_322_ = stack[1].m_obj;
lean_object* v___f_323_ = stack[2].m_obj;
lean_object* v_x_324_ = stack[3].m_obj;
lean_object* v_res_340_;
v_res_340_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v___f_321_, v_selectables_322_, v___f_323_, v_x_324_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v___f_341_, lean_object* v_selectables_342_, lean_object* v___f_343_, lean_object* v_x_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v___f_341_, v_selectables_342_, v___f_343_, v_x_344_);
return v_res_346_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1000000000u);
v___x_348_ = lean_nat_to_int(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(1000u);
v___x_350_ = lean_nat_to_int(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1000000u);
v___x_352_ = lean_nat_to_int(v___x_351_);
return v___x_352_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object* v_val_353_, lean_object* v___f_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v___f_354_);
v_a_357_ = lean_ctor_get(v_x_355_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_355_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v_x_355_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v_x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v_second_367_; lean_object* v_nano_368_; lean_object* v_second_369_; lean_object* v_nano_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_nanos_375_; lean_object* v___x_376_; lean_object* v_nanos_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_second_380_; lean_object* v_nano_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_millis_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_a_366_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v_x_355_, 1);
v_second_367_ = lean_ctor_get(v_a_366_, 0);
lean_inc(v_second_367_);
v_nano_368_ = lean_ctor_get(v_a_366_, 1);
lean_inc(v_nano_368_);
lean_dec(v_a_366_);
v_second_369_ = lean_ctor_get(v_val_353_, 0);
v_nano_370_ = lean_ctor_get(v_val_353_, 1);
v___x_371_ = lean_int_neg(v_second_367_);
lean_dec(v_second_367_);
v___x_372_ = lean_int_neg(v_nano_368_);
lean_dec(v_nano_368_);
v___x_373_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_374_ = lean_int_mul(v_second_369_, v___x_373_);
v_nanos_375_ = lean_int_add(v___x_374_, v_nano_370_);
lean_dec(v___x_374_);
v___x_376_ = lean_int_mul(v___x_371_, v___x_373_);
lean_dec(v___x_371_);
v_nanos_377_ = lean_int_add(v___x_376_, v___x_372_);
lean_dec(v___x_372_);
lean_dec(v___x_376_);
v___x_378_ = lean_int_add(v_nanos_375_, v_nanos_377_);
lean_dec(v_nanos_377_);
lean_dec(v_nanos_375_);
v___x_379_ = l_Std_Time_Duration_ofNanoseconds(v___x_378_);
lean_dec(v___x_378_);
v_second_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_second_380_);
v_nano_381_ = lean_ctor_get(v___x_379_, 1);
lean_inc(v_nano_381_);
lean_dec_ref(v___x_379_);
v___x_382_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1);
v___x_383_ = lean_int_mul(v_second_380_, v___x_382_);
lean_dec(v_second_380_);
v___x_384_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_385_ = lean_int_ediv(v_nano_381_, v___x_384_);
lean_dec(v_nano_381_);
v_millis_386_ = lean_int_add(v___x_383_, v___x_385_);
lean_dec(v___x_385_);
lean_dec(v___x_383_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = 0;
v___x_389_ = l_Std_Async_Selector_sleep(v_millis_386_);
lean_dec(v_millis_386_);
v___x_390_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_387_, v___x_388_, v___x_389_, v___f_354_);
return v___x_390_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_353_ = stack[0].m_obj;
lean_object* v___f_354_ = stack[1].m_obj;
lean_object* v_x_355_ = stack[2].m_obj;
lean_object* v_res_391_;
v_res_391_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(v_val_353_, v___f_354_, v_x_355_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object* v_val_392_, lean_object* v___f_393_, lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(v_val_392_, v___f_393_, v_x_394_);
lean_dec_ref(v_val_392_);
return v_res_396_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = l_instInhabitedError;
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_config_410_, lean_object* v_handler_411_, lean_object* v_sources_412_){
_start:
{
uint8_t v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v_val_418_; lean_object* v_socket_421_; lean_object* v_expect_422_; lean_object* v_response_423_; lean_object* v_responseBody_424_; lean_object* v_requestBody_425_; lean_object* v_timeout_426_; lean_object* v_keepAliveTimeout_427_; lean_object* v_headerTimeout_428_; lean_object* v_connectionContext_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___f_440_; lean_object* v___y_442_; lean_object* v___y_492_; 
v_socket_421_ = lean_ctor_get(v_sources_412_, 0);
lean_inc(v_socket_421_);
v_expect_422_ = lean_ctor_get(v_sources_412_, 1);
lean_inc(v_expect_422_);
v_response_423_ = lean_ctor_get(v_sources_412_, 2);
lean_inc_n(v_response_423_, 2);
v_responseBody_424_ = lean_ctor_get(v_sources_412_, 3);
lean_inc_n(v_responseBody_424_, 2);
v_requestBody_425_ = lean_ctor_get(v_sources_412_, 4);
lean_inc_n(v_requestBody_425_, 2);
v_timeout_426_ = lean_ctor_get(v_sources_412_, 5);
lean_inc(v_timeout_426_);
v_keepAliveTimeout_427_ = lean_ctor_get(v_sources_412_, 6);
lean_inc(v_keepAliveTimeout_427_);
v_headerTimeout_428_ = lean_ctor_get(v_sources_412_, 7);
lean_inc(v_headerTimeout_428_);
v_connectionContext_429_ = lean_ctor_get(v_sources_412_, 8);
lean_inc_ref(v_connectionContext_429_);
lean_dec_ref(v_sources_412_);
v___f_430_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_431_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_432_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_432_, 0, v_inst_408_);
lean_closure_set(v___f_432_, 1, v_handler_411_);
lean_closure_set(v___f_432_, 2, v___f_431_);
v___f_433_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_434_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_435_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_436_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_437_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___f_438_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7));
v___x_439_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8);
lean_inc_ref(v_inst_409_);
lean_inc_ref(v___f_432_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 12, 9);
lean_closure_set(v___f_440_, 0, v___f_432_);
lean_closure_set(v___f_440_, 1, v_response_423_);
lean_closure_set(v___f_440_, 2, v___x_439_);
lean_closure_set(v___f_440_, 3, v___f_433_);
lean_closure_set(v___f_440_, 4, v_requestBody_425_);
lean_closure_set(v___f_440_, 5, v___f_434_);
lean_closure_set(v___f_440_, 6, v_responseBody_424_);
lean_closure_set(v___f_440_, 7, v_inst_409_);
lean_closure_set(v___f_440_, 8, v___f_435_);
if (lean_obj_tag(v_expect_422_) == 0)
{
lean_object* v_defaultPayloadBytes_495_; 
v_defaultPayloadBytes_495_ = lean_ctor_get(v_config_410_, 8);
lean_inc(v_defaultPayloadBytes_495_);
v___y_492_ = v_defaultPayloadBytes_495_;
goto v___jp_491_;
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v_expect_422_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v_expect_422_, 1);
v___y_492_ = v_val_496_;
goto v___jp_491_;
}
v___jp_414_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_val_418_);
v___x_420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_416_, v___y_415_, v___x_419_, v___y_417_);
return v___x_420_;
}
v___jp_441_:
{
lean_object* v_token_443_; lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_selectables_449_; 
v_token_443_ = lean_ctor_get(v_connectionContext_429_, 1);
lean_inc_ref_n(v_token_443_, 2);
lean_dec_ref(v_connectionContext_429_);
v___f_444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_444_, 0, v_token_443_);
lean_closure_set(v___f_444_, 1, v___f_430_);
v___x_445_ = l_Std_CancellationToken_selector(v_token_443_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___f_444_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_mk_empty_array_with_capacity(v___x_447_);
v_selectables_449_ = lean_array_push(v___x_448_, v___x_446_);
if (lean_obj_tag(v_socket_421_) == 1)
{
lean_object* v_val_450_; lean_object* v_recvSelector_451_; uint64_t v_expectedBytes_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_selectables_456_; 
lean_dec_ref(v___f_432_);
lean_dec(v_requestBody_425_);
lean_dec(v_responseBody_424_);
lean_dec(v_response_423_);
lean_dec_ref(v_inst_409_);
v_val_450_ = lean_ctor_get(v_socket_421_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v_socket_421_, 1);
v_recvSelector_451_ = lean_ctor_get(v_inst_407_, 2);
lean_inc_ref(v_recvSelector_451_);
lean_dec_ref(v_inst_407_);
v_expectedBytes_452_ = lean_uint64_of_nat(v___y_442_);
lean_dec(v___y_442_);
v___x_453_ = lean_box_uint64(v_expectedBytes_452_);
v___x_454_ = lean_apply_2(v_recvSelector_451_, v_val_450_, v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___f_436_);
v_selectables_456_ = lean_array_push(v_selectables_449_, v___x_455_);
if (lean_obj_tag(v_keepAliveTimeout_427_) == 0)
{
if (lean_obj_tag(v_headerTimeout_428_) == 1)
{
lean_object* v_val_457_; lean_object* v___f_458_; lean_object* v___f_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
lean_dec(v_timeout_426_);
v_val_457_ = lean_ctor_get(v_headerTimeout_428_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v_headerTimeout_428_, 1);
v___f_458_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_458_, 0, v___f_437_);
lean_closure_set(v___f_458_, 1, v_selectables_456_);
lean_closure_set(v___f_458_, 2, v___f_440_);
v___f_459_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_459_, 0, v_val_457_);
lean_closure_set(v___f_459_, 1, v___f_458_);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = 0;
v___x_462_ = lean_get_current_time();
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 1);
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v___y_415_ = v___x_461_;
v___y_416_ = v___x_460_;
v___y_417_ = v___f_459_;
v_val_418_ = v___x_468_;
goto v___jp_414_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 0);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
v___y_415_ = v___x_461_;
v___y_416_ = v___x_460_;
v___y_417_ = v___f_459_;
v_val_418_ = v___x_476_;
goto v___jp_414_;
}
}
}
}
else
{
lean_object* v___f_479_; lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_headerTimeout_428_);
v___f_479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_479_, 0, v___f_437_);
lean_closure_set(v___f_479_, 1, v_selectables_456_);
lean_closure_set(v___f_479_, 2, v___f_440_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = 0;
v___x_482_ = l_Std_Async_Selector_sleep(v_timeout_426_);
lean_dec(v_timeout_426_);
v___x_483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_480_, v___x_481_, v___x_482_, v___f_479_);
return v___x_483_;
}
}
else
{
lean_object* v___f_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref_known(v_keepAliveTimeout_427_, 1);
lean_dec(v_headerTimeout_428_);
v___f_484_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_484_, 0, v___f_438_);
lean_closure_set(v___f_484_, 1, v_selectables_456_);
lean_closure_set(v___f_484_, 2, v___f_440_);
v___x_485_ = 0;
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = l_Std_Async_Selector_sleep(v_timeout_426_);
lean_dec(v_timeout_426_);
v___x_488_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_486_, v___x_485_, v___x_487_, v___f_484_);
return v___x_488_;
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v___y_442_);
lean_dec_ref(v___f_440_);
lean_dec(v_headerTimeout_428_);
lean_dec(v_keepAliveTimeout_427_);
lean_dec(v_timeout_426_);
lean_dec(v_socket_421_);
lean_dec_ref(v_inst_407_);
v___x_489_ = lean_box(0);
v___x_490_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_432_, v_response_423_, v___x_439_, v___f_433_, v_requestBody_425_, v___f_434_, v_responseBody_424_, v_inst_409_, v___f_435_, v___x_489_, v_selectables_449_);
return v___x_490_;
}
}
v___jp_491_:
{
lean_object* v_maximumRecvSize_493_; uint8_t v___x_494_; 
v_maximumRecvSize_493_ = lean_ctor_get(v_config_410_, 7);
lean_inc(v_maximumRecvSize_493_);
lean_dec_ref(v_config_410_);
v___x_494_ = lean_nat_dec_le(v___y_492_, v_maximumRecvSize_493_);
if (v___x_494_ == 0)
{
lean_dec(v___y_492_);
v___y_442_ = v_maximumRecvSize_493_;
goto v___jp_441_;
}
else
{
lean_dec(v_maximumRecvSize_493_);
v___y_442_ = v___y_492_;
goto v___jp_441_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_407_ = stack[0].m_obj;
lean_object* v_inst_408_ = stack[1].m_obj;
lean_object* v_inst_409_ = stack[2].m_obj;
lean_object* v_config_410_ = stack[3].m_obj;
lean_object* v_handler_411_ = stack[4].m_obj;
lean_object* v_sources_412_ = stack[5].m_obj;
lean_object* v_res_497_;
v_res_497_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_407_, v_inst_408_, v_inst_409_, v_config_410_, v_handler_411_, v_sources_412_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_config_501_, lean_object* v_handler_502_, lean_object* v_sources_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_498_, v_inst_499_, v_inst_500_, v_config_501_, v_handler_502_, v_sources_503_);
return v_res_505_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_506_, lean_object* v_00_u03c3_507_, lean_object* v_00_u03b2_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_config_512_, lean_object* v_handler_513_, lean_object* v_sources_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_509_, v_inst_510_, v_inst_511_, v_config_512_, v_handler_513_, v_sources_514_);
return v___x_516_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_509_ = stack[3].m_obj;
lean_object* v_inst_510_ = stack[4].m_obj;
lean_object* v_inst_511_ = stack[5].m_obj;
lean_object* v_config_512_ = stack[6].m_obj;
lean_object* v_handler_513_ = stack[7].m_obj;
lean_object* v_sources_514_ = stack[8].m_obj;
lean_object* v_res_517_;
v_res_517_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_box(0), lean_box(0), lean_box(0), v_inst_509_, v_inst_510_, v_inst_511_, v_config_512_, v_handler_513_, v_sources_514_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03c3_519_, lean_object* v_00_u03b2_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_config_524_, lean_object* v_handler_525_, lean_object* v_sources_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_518_, v_00_u03c3_519_, v_00_u03b2_520_, v_inst_521_, v_inst_522_, v_inst_523_, v_config_524_, v_handler_525_, v_sources_526_);
return v_res_528_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___y_533_; uint8_t v___y_534_; 
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_machine_529_);
v_a_539_ = lean_ctor_get(v_x_530_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v_x_530_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v_x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___y_550_; uint8_t v___x_556_; 
v_a_548_ = lean_ctor_get(v_x_530_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v_x_530_, 1);
v___x_556_ = lean_unbox(v_a_548_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_box(40);
v___y_550_ = v___x_557_;
goto v___jp_549_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
v___y_550_ = v___x_558_;
goto v___jp_549_;
}
v___jp_549_:
{
uint8_t v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = 0;
lean_inc(v___y_550_);
v___x_552_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_551_, v_machine_529_, v___y_550_);
v___x_553_ = lean_unbox(v_a_548_);
lean_dec(v_a_548_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = 1;
v___y_533_ = v___x_552_;
v___y_534_ = v___x_554_;
goto v___jp_532_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = 0;
v___y_533_ = v___x_552_;
v___y_534_ = v___x_555_;
goto v___jp_532_;
}
}
}
v___jp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = lean_box(v___y_534_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_machine_529_ = stack[0].m_obj;
lean_object* v_x_530_ = stack[1].m_obj;
lean_object* v_res_559_;
v_res_559_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_529_, v_x_530_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_560_, lean_object* v_x_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_560_, v_x_561_);
return v_res_563_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_box(v___y_564_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_564_ = stack[0].m_num;
lean_object* v_res_569_;
v_res_569_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_564_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___y_1408__boxed_572_; lean_object* v_res_573_; 
v___y_1408__boxed_572_ = lean_unbox(v___y_570_);
v_res_573_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1408__boxed_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v_x_574_, 1);
v___x_576_ = lean_task_pure(v_a_575_);
return v___x_576_;
}
else
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v_x_574_, 0);
lean_inc_ref(v_a_577_);
lean_dec_ref_known(v_x_574_, 1);
return v_a_577_;
}
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref_known(v_x_579_, 1);
v___x_581_ = 0;
v___x_582_ = lean_box(0);
v___x_583_ = lean_box(v___x_581_);
v___x_584_ = l_Std_Channel_send___redArg(v_a_578_, v___x_583_);
lean_dec_ref(v___x_584_);
return v___x_582_;
}
else
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_585_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v_x_579_, 1);
v___x_586_ = lean_box(0);
v___x_587_ = l_Std_Channel_send___redArg(v_a_578_, v_a_585_);
lean_dec_ref(v___x_587_);
return v___x_586_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_578_ = stack[0].m_obj;
lean_object* v_x_579_ = stack[1].m_obj;
lean_object* v_res_588_;
v_res_588_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_578_, v_x_579_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_589_, lean_object* v_x_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_589_, v_x_590_);
return v_res_592_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_box(v___x_593_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_593_ = stack[0].m_num;
lean_object* v_x_594_ = stack[1].m_obj;
lean_object* v_res_599_;
v_res_599_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_593_, v_x_594_);
stack->m_obj
 = v_res_599_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_600_, lean_object* v_x_601_, lean_object* v___y_602_){
_start:
{
uint8_t v___x_1476__boxed_603_; lean_object* v_res_604_; 
v___x_1476__boxed_603_ = lean_unbox(v___x_600_);
v_res_604_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1476__boxed_603_, v_x_601_);
return v_res_604_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_605_, uint8_t v___x_606_, lean_object* v_a_607_, lean_object* v___f_608_, lean_object* v___f_609_, lean_object* v___x_610_, uint8_t v___x_611_, lean_object* v___f_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v___f_612_);
lean_dec(v___x_610_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v_a_607_);
lean_dec_ref(v_connectionContext_605_);
v_a_615_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v_x_613_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v_x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v_token_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_a_624_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v_x_613_, 1);
v_token_625_ = lean_ctor_get(v_connectionContext_605_, 1);
lean_inc_ref(v_token_625_);
lean_dec_ref(v_connectionContext_605_);
v___x_626_ = lean_box(v___x_606_);
v___x_627_ = l_Std_Channel_recvSelector___redArg(v___x_626_, v_a_607_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___f_608_);
v___x_629_ = l_Std_CancellationToken_selector(v_token_625_);
lean_inc_ref(v___f_609_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___f_609_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_a_624_);
lean_ctor_set(v___x_631_, 1, v___f_609_);
v___x_632_ = lean_unsigned_to_nat(3u);
v___x_633_ = lean_mk_empty_array_with_capacity(v___x_632_);
v___x_634_ = lean_array_push(v___x_633_, v___x_628_);
v___x_635_ = lean_array_push(v___x_634_, v___x_630_);
v___x_636_ = lean_array_push(v___x_635_, v___x_631_);
v___x_637_ = l_Std_Async_Selectable_one___redArg(v___x_636_);
v___x_638_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_610_, v___x_611_, v___x_637_, v___f_612_);
return v___x_638_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_connectionContext_605_ = stack[0].m_obj;
uint8_t v___x_606_ = stack[1].m_num;
lean_object* v_a_607_ = stack[2].m_obj;
lean_object* v___f_608_ = stack[3].m_obj;
lean_object* v___f_609_ = stack[4].m_obj;
lean_object* v___x_610_ = stack[5].m_obj;
uint8_t v___x_611_ = stack[6].m_num;
lean_object* v___f_612_ = stack[7].m_obj;
lean_object* v_x_613_ = stack[8].m_obj;
lean_object* v_res_639_;
v_res_639_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_605_, v___x_606_, v_a_607_, v___f_608_, v___f_609_, v___x_610_, v___x_611_, v___f_612_, v_x_613_);
stack->m_obj
 = v_res_639_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_640_, lean_object* v___x_641_, lean_object* v_a_642_, lean_object* v___f_643_, lean_object* v___f_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___f_647_, lean_object* v_x_648_, lean_object* v___y_649_){
_start:
{
uint8_t v___x_1500__boxed_650_; uint8_t v___x_1505__boxed_651_; lean_object* v_res_652_; 
v___x_1500__boxed_650_ = lean_unbox(v___x_641_);
v___x_1505__boxed_651_ = lean_unbox(v___x_646_);
v_res_652_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_640_, v___x_1500__boxed_650_, v_a_642_, v___f_643_, v___f_644_, v___x_645_, v___x_1505__boxed_651_, v___f_647_, v_x_648_);
return v_res_652_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_653_, lean_object* v___x_654_, uint8_t v___x_655_, lean_object* v___f_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v___f_656_);
lean_dec(v___x_654_);
v_a_659_ = lean_ctor_get(v_x_657_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v_x_657_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v_x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
else
{
lean_object* v_lingeringTimeout_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref_known(v_x_657_, 1);
v_lingeringTimeout_668_ = lean_ctor_get(v_config_653_, 4);
v___x_669_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_668_);
v___x_670_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_654_, v___x_655_, v___x_669_, v___f_656_);
return v___x_670_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_653_ = stack[0].m_obj;
lean_object* v___x_654_ = stack[1].m_obj;
uint8_t v___x_655_ = stack[2].m_num;
lean_object* v___f_656_ = stack[3].m_obj;
lean_object* v_x_657_ = stack[4].m_obj;
lean_object* v_res_671_;
v_res_671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_653_, v___x_654_, v___x_655_, v___f_656_, v_x_657_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v___f_675_, lean_object* v_x_676_, lean_object* v___y_677_){
_start:
{
uint8_t v___x_1615__boxed_678_; lean_object* v_res_679_; 
v___x_1615__boxed_678_ = lean_unbox(v___x_674_);
v_res_679_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_672_, v___x_673_, v___x_1615__boxed_678_, v___f_675_, v_x_676_);
lean_dec_ref(v_config_672_);
return v_res_679_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_683_, uint8_t v___x_684_, lean_object* v_a_685_, lean_object* v___f_686_, lean_object* v___x_687_, lean_object* v___f_688_, lean_object* v_config_689_, lean_object* v___f_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v___f_690_);
lean_dec_ref(v_config_689_);
lean_dec_ref(v___f_688_);
lean_dec(v___x_687_);
lean_dec_ref(v___f_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_connectionContext_683_);
v_a_693_ = lean_ctor_get(v_x_691_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v_x_691_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v_x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_719_; 
v_a_702_ = lean_ctor_get(v_x_691_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_719_ == 0)
{
v___x_704_ = v_x_691_;
v_isShared_705_ = v_isSharedCheck_719_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v_x_691_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_719_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v___x_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_706_ = 0;
v___f_707_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_708_ = lean_box(v___x_684_);
v___x_709_ = lean_box(v___x_706_);
lean_inc_n(v___x_687_, 3);
v___f_710_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_710_, 0, v_connectionContext_683_);
lean_closure_set(v___f_710_, 1, v___x_708_);
lean_closure_set(v___f_710_, 2, v_a_685_);
lean_closure_set(v___f_710_, 3, v___f_686_);
lean_closure_set(v___f_710_, 4, v___f_707_);
lean_closure_set(v___f_710_, 5, v___x_687_);
lean_closure_set(v___f_710_, 6, v___x_709_);
lean_closure_set(v___f_710_, 7, v___f_688_);
v___x_711_ = lean_box(v___x_706_);
v___f_712_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_712_, 0, v_config_689_);
lean_closure_set(v___f_712_, 1, v___x_687_);
lean_closure_set(v___f_712_, 2, v___x_711_);
lean_closure_set(v___f_712_, 3, v___f_710_);
v___x_713_ = l_BaseIO_chainTask___redArg(v_a_702_, v___f_690_, v___x_687_, v___x_706_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_713_);
v___x_715_ = v___x_704_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_718_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_687_, v___x_706_, v___x_716_, v___f_712_);
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_connectionContext_683_ = stack[0].m_obj;
uint8_t v___x_684_ = stack[1].m_num;
lean_object* v_a_685_ = stack[2].m_obj;
lean_object* v___f_686_ = stack[3].m_obj;
lean_object* v___x_687_ = stack[4].m_obj;
lean_object* v___f_688_ = stack[5].m_obj;
lean_object* v_config_689_ = stack[6].m_obj;
lean_object* v___f_690_ = stack[7].m_obj;
lean_object* v_x_691_ = stack[8].m_obj;
lean_object* v_res_720_;
v_res_720_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_683_, v___x_684_, v_a_685_, v___f_686_, v___x_687_, v___f_688_, v_config_689_, v___f_690_, v_x_691_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_721_, lean_object* v___x_722_, lean_object* v_a_723_, lean_object* v___f_724_, lean_object* v___x_725_, lean_object* v___f_726_, lean_object* v_config_727_, lean_object* v___f_728_, lean_object* v_x_729_, lean_object* v___y_730_){
_start:
{
uint8_t v___x_1676__boxed_731_; lean_object* v_res_732_; 
v___x_1676__boxed_731_ = lean_unbox(v___x_722_);
v_res_732_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_721_, v___x_1676__boxed_731_, v_a_723_, v___f_724_, v___x_725_, v___f_726_, v_config_727_, v___f_728_, v_x_729_);
return v_res_732_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_733_, lean_object* v_handler_734_, lean_object* v_head_735_, lean_object* v_connectionContext_736_, uint8_t v___x_737_, lean_object* v___f_738_, lean_object* v___f_739_, lean_object* v_config_740_, lean_object* v___f_741_, lean_object* v_x_742_){
_start:
{
if (lean_obj_tag(v_x_742_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v___f_741_);
lean_dec_ref(v_config_740_);
lean_dec_ref(v___f_739_);
lean_dec_ref(v___f_738_);
lean_dec_ref(v_connectionContext_736_);
lean_dec_ref(v_head_735_);
lean_dec(v_handler_734_);
lean_dec_ref(v_inst_733_);
v_a_744_ = lean_ctor_get(v_x_742_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_742_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v_x_742_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v_x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_773_; 
v_a_753_ = lean_ctor_get(v_x_742_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_742_);
if (v_isSharedCheck_773_ == 0)
{
v___x_755_ = v_x_742_;
v_isShared_756_ = v_isSharedCheck_773_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v_x_742_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_773_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_onContinue_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___f_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v_onContinue_757_ = lean_ctor_get(v_inst_733_, 3);
lean_inc_ref(v_onContinue_757_);
lean_dec_ref(v_inst_733_);
lean_inc(v_a_753_);
v___f_758_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_758_, 0, v_a_753_);
v___x_759_ = lean_apply_2(v_onContinue_757_, v_handler_734_, v_head_735_);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_box(v___x_737_);
v___f_762_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_762_, 0, v_connectionContext_736_);
lean_closure_set(v___f_762_, 1, v___x_761_);
lean_closure_set(v___f_762_, 2, v_a_753_);
lean_closure_set(v___f_762_, 3, v___f_738_);
lean_closure_set(v___f_762_, 4, v___x_760_);
lean_closure_set(v___f_762_, 5, v___f_739_);
lean_closure_set(v___f_762_, 6, v_config_740_);
lean_closure_set(v___f_762_, 7, v___f_758_);
v___x_763_ = 0;
v___x_764_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_764_, 0, lean_box(0));
lean_closure_set(v___x_764_, 1, v___x_759_);
v___x_765_ = lean_io_as_task(v___x_764_, v___x_760_);
v___x_766_ = 1;
v___x_767_ = lean_task_bind(v___x_765_, v___f_741_, v___x_760_, v___x_766_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_767_);
v___x_769_ = v___x_755_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_772_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
v___x_771_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_760_, v___x_763_, v___x_770_, v___f_762_);
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_733_ = stack[0].m_obj;
lean_object* v_handler_734_ = stack[1].m_obj;
lean_object* v_head_735_ = stack[2].m_obj;
lean_object* v_connectionContext_736_ = stack[3].m_obj;
uint8_t v___x_737_ = stack[4].m_num;
lean_object* v___f_738_ = stack[5].m_obj;
lean_object* v___f_739_ = stack[6].m_obj;
lean_object* v_config_740_ = stack[7].m_obj;
lean_object* v___f_741_ = stack[8].m_obj;
lean_object* v_x_742_ = stack[9].m_obj;
lean_object* v_res_774_;
v_res_774_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_733_, v_handler_734_, v_head_735_, v_connectionContext_736_, v___x_737_, v___f_738_, v___f_739_, v_config_740_, v___f_741_, v_x_742_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_775_, lean_object* v_handler_776_, lean_object* v_head_777_, lean_object* v_connectionContext_778_, lean_object* v___x_779_, lean_object* v___f_780_, lean_object* v___f_781_, lean_object* v_config_782_, lean_object* v___f_783_, lean_object* v_x_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_1805__boxed_786_; lean_object* v_res_787_; 
v___x_1805__boxed_786_ = lean_unbox(v___x_779_);
v_res_787_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_775_, v_handler_776_, v_head_777_, v_connectionContext_778_, v___x_1805__boxed_786_, v___f_780_, v___f_781_, v_config_782_, v___f_783_, v_x_784_);
return v_res_787_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_790_, lean_object* v_handler_791_, lean_object* v_machine_792_, lean_object* v_head_793_, lean_object* v_config_794_, lean_object* v_connectionContext_795_){
_start:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___f_797_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_797_, 0, v_machine_792_);
v___f_798_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_799_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_800_ = 0;
v___x_801_ = lean_box(v___x_800_);
v___f_802_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_802_, 0, v_inst_790_);
lean_closure_set(v___f_802_, 1, v_handler_791_);
lean_closure_set(v___f_802_, 2, v_head_793_);
lean_closure_set(v___f_802_, 3, v_connectionContext_795_);
lean_closure_set(v___f_802_, 4, v___x_801_);
lean_closure_set(v___f_802_, 5, v___f_798_);
lean_closure_set(v___f_802_, 6, v___f_797_);
lean_closure_set(v___f_802_, 7, v_config_794_);
lean_closure_set(v___f_802_, 8, v___f_799_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = l_Std_CloseableChannel_new___redArg(v___x_803_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_804_, v___x_800_, v___x_807_, v___f_802_);
return v___x_808_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_790_ = stack[0].m_obj;
lean_object* v_handler_791_ = stack[1].m_obj;
lean_object* v_machine_792_ = stack[2].m_obj;
lean_object* v_head_793_ = stack[3].m_obj;
lean_object* v_config_794_ = stack[4].m_obj;
lean_object* v_connectionContext_795_ = stack[5].m_obj;
lean_object* v_res_809_;
v_res_809_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_790_, v_handler_791_, v_machine_792_, v_head_793_, v_config_794_, v_connectionContext_795_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_810_, lean_object* v_handler_811_, lean_object* v_machine_812_, lean_object* v_head_813_, lean_object* v_config_814_, lean_object* v_connectionContext_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_810_, v_handler_811_, v_machine_812_, v_head_813_, v_config_814_, v_connectionContext_815_);
return v_res_817_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_818_, lean_object* v_inst_819_, lean_object* v_handler_820_, lean_object* v_machine_821_, lean_object* v_head_822_, lean_object* v_config_823_, lean_object* v_connectionContext_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_819_, v_handler_820_, v_machine_821_, v_head_822_, v_config_823_, v_connectionContext_824_);
return v___x_826_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_819_ = stack[1].m_obj;
lean_object* v_handler_820_ = stack[2].m_obj;
lean_object* v_machine_821_ = stack[3].m_obj;
lean_object* v_head_822_ = stack[4].m_obj;
lean_object* v_config_823_ = stack[5].m_obj;
lean_object* v_connectionContext_824_ = stack[6].m_obj;
lean_object* v_res_827_;
v_res_827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_box(0), v_inst_819_, v_handler_820_, v_machine_821_, v_head_822_, v_config_823_, v_connectionContext_824_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_828_, lean_object* v_inst_829_, lean_object* v_handler_830_, lean_object* v_machine_831_, lean_object* v_head_832_, lean_object* v_config_833_, lean_object* v_connectionContext_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_828_, v_inst_829_, v_handler_830_, v_machine_831_, v_head_832_, v_config_833_, v_connectionContext_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_nat_to_int(v_a_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Rat_ofInt(v_a_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_tz_841_, lean_object* v_a_842_, lean_object* v___x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v_offset_845_; lean_object* v_second_846_; lean_object* v_nano_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_nanos_851_; lean_object* v___x_852_; lean_object* v_nanos_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_offset_845_ = lean_ctor_get(v_tz_841_, 0);
v_second_846_ = lean_ctor_get(v_a_842_, 0);
v_nano_847_ = lean_ctor_get(v_a_842_, 1);
v___x_848_ = lean_nat_to_int(v___x_843_);
v___x_849_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_850_ = lean_int_mul(v_second_846_, v___x_849_);
v_nanos_851_ = lean_int_add(v___x_850_, v_nano_847_);
lean_dec(v___x_850_);
v___x_852_ = lean_int_mul(v_offset_845_, v___x_849_);
v_nanos_853_ = lean_int_add(v___x_852_, v___x_848_);
lean_dec(v___x_848_);
lean_dec(v___x_852_);
v___x_854_ = lean_int_add(v_nanos_851_, v_nanos_853_);
lean_dec(v_nanos_853_);
lean_dec(v_nanos_851_);
v___x_855_ = l_Std_Time_Duration_ofNanoseconds(v___x_854_);
lean_dec(v___x_854_);
v___x_856_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_tz_857_, lean_object* v_a_858_, lean_object* v___x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_tz_857_, v_a_858_, v___x_859_, v_x_860_);
lean_dec_ref(v_a_858_);
lean_dec_ref(v_tz_857_);
return v_res_861_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
uint8_t v___x_864_; 
v___x_864_ = 0;
return v___x_864_;
}
else
{
lean_object* v_key_865_; lean_object* v_tail_866_; uint8_t v___x_867_; 
v_key_865_ = lean_ctor_get(v_x_863_, 0);
v_tail_866_ = lean_ctor_get(v_x_863_, 2);
v___x_867_ = lean_string_dec_eq(v_key_865_, v_a_862_);
if (v___x_867_ == 0)
{
v_x_863_ = v_tail_866_;
goto _start;
}
else
{
return v___x_867_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_862_ = stack[0].m_obj;
lean_object* v_x_863_ = stack[1].m_obj;
uint8_t v_res_869_;
v_res_869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_862_, v_x_863_);
stack->m_num = v_res_869_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg___boxed(lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec_ref(v_a_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
return v_x_874_;
}
else
{
lean_object* v_key_876_; lean_object* v_value_877_; lean_object* v_tail_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_901_; 
v_key_876_ = lean_ctor_get(v_x_875_, 0);
v_value_877_ = lean_ctor_get(v_x_875_, 1);
v_tail_878_ = lean_ctor_get(v_x_875_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_901_ == 0)
{
v___x_880_ = v_x_875_;
v_isShared_881_ = v_isSharedCheck_901_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_tail_878_);
lean_inc(v_value_877_);
lean_inc(v_key_876_);
lean_dec(v_x_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_901_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v_fold_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_882_ = lean_array_get_size(v_x_874_);
v___x_883_ = lean_string_hash(v_key_876_);
v___x_884_ = 32ULL;
v___x_885_ = lean_uint64_shift_right(v___x_883_, v___x_884_);
v_fold_886_ = lean_uint64_xor(v___x_883_, v___x_885_);
v___x_887_ = 16ULL;
v___x_888_ = lean_uint64_shift_right(v_fold_886_, v___x_887_);
v___x_889_ = lean_uint64_xor(v_fold_886_, v___x_888_);
v___x_890_ = lean_uint64_to_usize(v___x_889_);
v___x_891_ = lean_usize_of_nat(v___x_882_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_sub(v___x_891_, v___x_892_);
v___x_894_ = lean_usize_land(v___x_890_, v___x_893_);
v___x_895_ = lean_array_uget_borrowed(v_x_874_, v___x_894_);
lean_inc(v___x_895_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v___x_895_);
v___x_897_ = v___x_880_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_key_876_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_value_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v___x_895_);
v___x_897_ = v_reuseFailAlloc_900_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; 
v___x_898_ = lean_array_uset(v_x_874_, v___x_894_, v___x_897_);
v_x_874_ = v___x_898_;
v_x_875_ = v_tail_878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(lean_object* v_i_902_, lean_object* v_source_903_, lean_object* v_target_904_){
_start:
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_array_get_size(v_source_903_);
v___x_906_ = lean_nat_dec_lt(v_i_902_, v___x_905_);
if (v___x_906_ == 0)
{
lean_dec_ref(v_source_903_);
lean_dec(v_i_902_);
return v_target_904_;
}
else
{
lean_object* v_es_907_; lean_object* v___x_908_; lean_object* v_source_909_; lean_object* v_target_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_es_907_ = lean_array_fget(v_source_903_, v_i_902_);
v___x_908_ = lean_box(0);
v_source_909_ = lean_array_fset(v_source_903_, v_i_902_, v___x_908_);
v_target_910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(v_target_904_, v_es_907_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_902_, v___x_911_);
lean_dec(v_i_902_);
v_i_902_ = v___x_912_;
v_source_903_ = v_source_909_;
v_target_904_ = v_target_910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(lean_object* v_data_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_nbuckets_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_915_ = lean_array_get_size(v_data_914_);
v___x_916_ = lean_unsigned_to_nat(2u);
v_nbuckets_917_ = lean_nat_mul(v___x_915_, v___x_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_box(0);
v___x_920_ = lean_mk_array(v_nbuckets_917_, v___x_919_);
v___x_921_ = lean_array_propagate_mark(v_data_914_, v___x_920_);
v___x_922_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(v___x_918_, v_data_914_, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(lean_object* v_i_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_mk_empty_array_with_capacity(v___x_925_);
v___x_927_ = lean_array_push(v___x_926_, v_i_923_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
else
{
lean_object* v_val_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
v_val_929_ = lean_ctor_get(v_x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_931_ = v_x_924_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_val_929_);
lean_dec(v_x_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_array_push(v_val_929_, v_i_923_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(lean_object* v_i_938_, lean_object* v_a_939_, lean_object* v_x_940_){
_start:
{
if (lean_obj_tag(v_x_940_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_val_943_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(v_i_938_, v___x_941_);
v_val_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_val_943_);
lean_dec(v___x_942_);
v___x_944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_944_, 0, v_a_939_);
lean_ctor_set(v___x_944_, 1, v_val_943_);
lean_ctor_set(v___x_944_, 2, v_x_940_);
return v___x_944_;
}
else
{
lean_object* v_key_945_; lean_object* v_value_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_962_; 
v_key_945_ = lean_ctor_get(v_x_940_, 0);
v_value_946_ = lean_ctor_get(v_x_940_, 1);
v_tail_947_ = lean_ctor_get(v_x_940_, 2);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_962_ == 0)
{
v___x_949_ = v_x_940_;
v_isShared_950_ = v_isSharedCheck_962_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_inc(v_value_946_);
lean_inc(v_key_945_);
lean_dec(v_x_940_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_962_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
uint8_t v___x_951_; 
v___x_951_ = lean_string_dec_eq(v_key_945_, v_a_939_);
if (v___x_951_ == 0)
{
lean_object* v_tail_952_; lean_object* v___x_954_; 
v_tail_952_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(v_i_938_, v_a_939_, v_tail_947_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v_tail_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_key_945_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_value_946_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_tail_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_val_958_; lean_object* v___x_960_; 
lean_dec(v_key_945_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_value_946_);
v___x_957_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0(v_i_938_, v___x_956_);
v_val_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_val_958_);
lean_dec(v___x_957_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_val_958_);
lean_ctor_set(v___x_949_, 0, v_a_939_);
v___x_960_ = v___x_949_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_939_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_val_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_tail_947_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_i_963_, lean_object* v_m_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_size_966_; lean_object* v_buckets_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1017_; 
v_size_966_ = lean_ctor_get(v_m_964_, 0);
v_buckets_967_ = lean_ctor_get(v_m_964_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_m_964_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_969_ = v_m_964_;
v_isShared_970_ = v_isSharedCheck_1017_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_buckets_967_);
lean_inc(v_size_966_);
lean_dec(v_m_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1017_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; uint64_t v_fold_975_; uint64_t v___x_976_; uint64_t v___x_977_; uint64_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v___x_983_; lean_object* v_bkt_984_; uint8_t v___x_985_; 
v___x_971_ = lean_array_get_size(v_buckets_967_);
v___x_972_ = lean_string_hash(v_a_965_);
v___x_973_ = 32ULL;
v___x_974_ = lean_uint64_shift_right(v___x_972_, v___x_973_);
v_fold_975_ = lean_uint64_xor(v___x_972_, v___x_974_);
v___x_976_ = 16ULL;
v___x_977_ = lean_uint64_shift_right(v_fold_975_, v___x_976_);
v___x_978_ = lean_uint64_xor(v_fold_975_, v___x_977_);
v___x_979_ = lean_uint64_to_usize(v___x_978_);
v___x_980_ = lean_usize_of_nat(v___x_971_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_sub(v___x_980_, v___x_981_);
v___x_983_ = lean_usize_land(v___x_979_, v___x_982_);
v_bkt_984_ = lean_array_uget_borrowed(v_buckets_967_, v___x_983_);
v___x_985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_965_, v_bkt_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_size_x27_989_; lean_object* v___x_990_; lean_object* v_buckets_x27_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_mk_empty_array_with_capacity(v___x_986_);
v___x_988_ = lean_array_push(v___x_987_, v_i_963_);
v_size_x27_989_ = lean_nat_add(v_size_966_, v___x_986_);
lean_dec(v_size_966_);
lean_inc(v_bkt_984_);
v___x_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_990_, 0, v_a_965_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
lean_ctor_set(v___x_990_, 2, v_bkt_984_);
v_buckets_x27_991_ = lean_array_uset(v_buckets_967_, v___x_983_, v___x_990_);
v___x_992_ = lean_unsigned_to_nat(4u);
v___x_993_ = lean_nat_mul(v_size_x27_989_, v___x_992_);
v___x_994_ = lean_unsigned_to_nat(3u);
v___x_995_ = lean_nat_div(v___x_993_, v___x_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_array_get_size(v_buckets_x27_991_);
v___x_997_ = lean_nat_dec_le(v___x_995_, v___x_996_);
lean_dec(v___x_995_);
if (v___x_997_ == 0)
{
lean_object* v_val_998_; lean_object* v___x_1000_; 
v_val_998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(v_buckets_x27_991_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_val_998_);
lean_ctor_set(v___x_969_, 0, v_size_x27_989_);
v___x_1000_ = v___x_969_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_size_x27_989_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_val_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1003_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_buckets_x27_991_);
lean_ctor_set(v___x_969_, 0, v_size_x27_989_);
v___x_1003_ = v___x_969_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_size_x27_989_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_buckets_x27_991_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v_buckets_x27_1006_; lean_object* v_bkt_x27_1007_; lean_object* v___y_1009_; uint8_t v___x_1014_; 
lean_inc(v_bkt_984_);
v___x_1005_ = lean_box(0);
v_buckets_x27_1006_ = lean_array_uset(v_buckets_967_, v___x_983_, v___x_1005_);
lean_inc_ref(v_a_965_);
v_bkt_x27_1007_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5(v_i_963_, v_a_965_, v_bkt_984_);
v___x_1014_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_965_, v_bkt_x27_1007_);
lean_dec_ref(v_a_965_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_sub(v_size_966_, v___x_1015_);
lean_dec(v_size_966_);
v___y_1009_ = v___x_1016_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v_size_966_;
goto v___jp_1008_;
}
v___jp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_array_uset(v_buckets_x27_1006_, v___x_983_, v_bkt_x27_1007_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_1010_);
lean_ctor_set(v___x_969_, 0, v___y_1009_);
v___x_1012_ = v___x_969_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___y_1009_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_nat_to_int(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2));
v___x_1024_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_1025_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_1024_, v___x_1023_, v___x_1023_);
return v___x_1025_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_entries_1026_, lean_object* v_indexes_1027_, lean_object* v_status_1028_, uint8_t v_version_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_status_1028_);
lean_dec_ref(v_indexes_1027_);
lean_dec_ref(v_entries_1026_);
v_a_1032_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v_x_1030_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v_x_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1064_; 
v_a_1041_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1043_ = v_x_1030_;
v_isShared_1044_ = v_isSharedCheck_1064_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v_x_1030_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1064_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_tz_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_i_1054_; lean_object* v___x_1055_; lean_object* v_entries_1056_; lean_object* v_indexes_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3);
v_tz_1047_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_1046_, v_a_1041_);
lean_inc(v_a_1041_);
lean_inc_ref(v_tz_1047_);
v___f_1048_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1048_, 0, v_tz_1047_);
lean_closure_set(v___f_1048_, 1, v_a_1041_);
lean_closure_set(v___f_1048_, 2, v___x_1045_);
v___x_1049_ = lean_mk_thunk(v___f_1048_);
v___x_1050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_1041_);
lean_ctor_set(v___x_1050_, 2, v___x_1046_);
lean_ctor_set(v___x_1050_, 3, v_tz_1047_);
v___x_1051_ = l_Std_Http_Header_Name_date;
v___x_1052_ = l_Std_Time_DateTime_toHTTPDateString(v___x_1050_);
v___x_1053_ = l_Std_Http_Header_Value_ofString_x21(v___x_1052_);
v_i_1054_ = lean_array_get_size(v_entries_1026_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1051_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
v_entries_1056_ = lean_array_push(v_entries_1026_, v___x_1055_);
v_indexes_1057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_i_1054_, v_indexes_1027_, v___x_1051_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_entries_1056_);
lean_ctor_set(v___x_1058_, 1, v_indexes_1057_);
v___x_1059_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1059_, 0, v_status_1028_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*2, v_version_1029_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1059_);
v___x_1061_ = v___x_1043_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_entries_1026_ = stack[0].m_obj;
lean_object* v_indexes_1027_ = stack[1].m_obj;
lean_object* v_status_1028_ = stack[2].m_obj;
uint8_t v_version_1029_ = stack[3].m_num;
lean_object* v_x_1030_ = stack[4].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_entries_1026_, v_indexes_1027_, v_status_1028_, v_version_1029_, v_x_1030_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_entries_1066_, lean_object* v_indexes_1067_, lean_object* v_status_1068_, lean_object* v_version_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v_version_boxed_1072_; lean_object* v_res_1073_; 
v_version_boxed_1072_ = lean_unbox(v_version_1069_);
v_res_1073_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_entries_1066_, v_indexes_1067_, v_status_1068_, v_version_boxed_1072_, v_x_1070_);
return v_res_1073_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(lean_object* v_m_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_buckets_1076_; lean_object* v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v_fold_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_buckets_1076_ = lean_ctor_get(v_m_1074_, 1);
v___x_1077_ = lean_array_get_size(v_buckets_1076_);
v___x_1078_ = lean_string_hash(v_a_1075_);
v___x_1079_ = 32ULL;
v___x_1080_ = lean_uint64_shift_right(v___x_1078_, v___x_1079_);
v_fold_1081_ = lean_uint64_xor(v___x_1078_, v___x_1080_);
v___x_1082_ = 16ULL;
v___x_1083_ = lean_uint64_shift_right(v_fold_1081_, v___x_1082_);
v___x_1084_ = lean_uint64_xor(v_fold_1081_, v___x_1083_);
v___x_1085_ = lean_uint64_to_usize(v___x_1084_);
v___x_1086_ = lean_usize_of_nat(v___x_1077_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_sub(v___x_1086_, v___x_1087_);
v___x_1089_ = lean_usize_land(v___x_1085_, v___x_1088_);
v___x_1090_ = lean_array_uget_borrowed(v_buckets_1076_, v___x_1089_);
v___x_1091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_1075_, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1074_ = stack[0].m_obj;
lean_object* v_a_1075_ = stack[1].m_obj;
uint8_t v_res_1092_;
v_res_1092_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_m_1074_, v_a_1075_);
stack->m_num = v_res_1092_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg___boxed(lean_object* v_m_1093_, lean_object* v_a_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_m_1093_, v_a_1094_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_m_1093_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1097_, lean_object* v_head_1098_){
_start:
{
uint8_t v_generateDate_1103_; 
v_generateDate_1103_ = lean_ctor_get_uint8(v_config_1097_, sizeof(void*)*24 + 1);
if (v_generateDate_1103_ == 0)
{
goto v___jp_1100_;
}
else
{
lean_object* v_headers_1104_; lean_object* v_status_1105_; uint8_t v_version_1106_; lean_object* v_entries_1107_; lean_object* v_indexes_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_headers_1104_ = lean_ctor_get(v_head_1098_, 1);
v_status_1105_ = lean_ctor_get(v_head_1098_, 0);
v_version_1106_ = lean_ctor_get_uint8(v_head_1098_, sizeof(void*)*2);
v_entries_1107_ = lean_ctor_get(v_headers_1104_, 0);
v_indexes_1108_ = lean_ctor_get(v_headers_1104_, 1);
v___x_1109_ = l_Std_Http_Header_Name_date;
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_indexes_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v_val_1115_; lean_object* v___x_1118_; 
lean_inc_ref(v_indexes_1108_);
lean_inc_ref(v_entries_1107_);
lean_inc(v_status_1105_);
lean_dec_ref(v_head_1098_);
v___x_1111_ = lean_box(v_version_1106_);
v___f_1112_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1112_, 0, v_entries_1107_);
lean_closure_set(v___f_1112_, 1, v_indexes_1108_);
lean_closure_set(v___f_1112_, 2, v_status_1105_);
lean_closure_set(v___f_1112_, 3, v___x_1111_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_get_current_time();
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 1);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v_val_1115_ = v___x_1124_;
goto v___jp_1114_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v_val_1115_ = v___x_1132_;
goto v___jp_1114_;
}
}
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_val_1115_);
v___x_1117_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1113_, v___x_1110_, v___x_1116_, v___f_1112_);
return v___x_1117_;
}
}
else
{
goto v___jp_1100_;
}
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_head_1098_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1097_ = stack[0].m_obj;
lean_object* v_head_1098_ = stack[1].m_obj;
lean_object* v_res_1135_;
v_res_1135_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1097_, v_head_1098_);
stack->m_obj
 = v_res_1135_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1136_, lean_object* v_head_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1136_, v_head_1137_);
lean_dec_ref(v_config_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_nat_to_int(v_a_1140_);
v___x_1142_ = l_Rat_ofInt(v___x_1141_);
return v___x_1142_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4(lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___redArg(v_m_1144_, v_a_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1144_ = stack[1].m_obj;
lean_object* v_a_1145_ = stack[2].m_obj;
uint8_t v_res_1147_;
v_res_1147_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4(lean_box(0), v_m_1144_, v_a_1145_);
stack->m_num = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4___boxed(lean_object* v_00_u03b2_1148_, lean_object* v_m_1149_, lean_object* v_a_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__4(v_00_u03b2_1148_, v_m_1149_, v_a_1150_);
lean_dec_ref(v_a_1150_);
lean_dec_ref(v_m_1149_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3(lean_object* v_00_u03b2_1153_, lean_object* v_a_1154_, lean_object* v_x_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___redArg(v_a_1154_, v_x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1154_ = stack[1].m_obj;
lean_object* v_x_1155_ = stack[2].m_obj;
uint8_t v_res_1157_;
v_res_1157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3(lean_box(0), v_a_1154_, v_x_1155_);
stack->m_num = v_res_1157_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1158_, lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
uint8_t v_res_1161_; lean_object* v_r_1162_; 
v_res_1161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__3(v_00_u03b2_1158_, v_a_1159_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec_ref(v_a_1159_);
v_r_1162_ = lean_box(v_res_1161_);
return v_r_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4(lean_object* v_00_u03b2_1163_, lean_object* v_data_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4___redArg(v_data_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1166_, lean_object* v_i_1167_, lean_object* v_source_1168_, lean_object* v_target_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5___redArg(v_i_1167_, v_source_1168_, v_target_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__4_spec__5_spec__7___redArg(v_x_1172_, v_x_1173_);
return v___x_1174_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1175_, lean_object* v_____r_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1175_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1175_ = stack[0].m_obj;
lean_object* v_____r_1176_ = stack[1].m_obj;
lean_object* v_res_1182_;
v_res_1182_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1175_, v_____r_1176_);
stack->m_obj
 = v_res_1182_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1183_, lean_object* v_____r_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1183_, v_____r_1184_);
return v_res_1186_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1187_, lean_object* v_x_1188_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v___f_1187_);
v_a_1190_ = lean_ctor_get(v_x_1188_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1188_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v_x_1188_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v_x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1200_; 
v_a_1199_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v_x_1188_, 1);
v___x_1200_ = lean_apply_2(v___f_1187_, v_a_1199_, lean_box(0));
return v___x_1200_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1187_ = stack[0].m_obj;
lean_object* v_x_1188_ = stack[1].m_obj;
lean_object* v_res_1201_;
v_res_1201_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1187_, v_x_1188_);
stack->m_obj
 = v_res_1201_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1202_, v_x_1203_);
return v_res_1205_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1206_, lean_object* v_body_1207_, lean_object* v___f_1208_, lean_object* v___f_1209_, lean_object* v_x_1210_){
_start:
{
if (lean_obj_tag(v_x_1210_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___f_1208_);
lean_dec(v_body_1207_);
lean_dec_ref(v_close_1206_);
v_a_1212_ = lean_ctor_get(v_x_1210_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1210_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1214_ = v_x_1210_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v_x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1221_; uint8_t v___x_1222_; 
v_a_1221_ = lean_ctor_get(v_x_1210_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v_x_1210_, 1);
v___x_1222_ = lean_unbox(v_a_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v___f_1209_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_apply_2(v_close_1206_, v_body_1207_, lean_box(0));
v___x_1225_ = lean_unbox(v_a_1221_);
lean_dec(v_a_1221_);
v___x_1226_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1223_, v___x_1225_, v___x_1224_, v___f_1208_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_a_1221_);
lean_dec_ref(v___f_1208_);
lean_dec(v_body_1207_);
lean_dec_ref(v_close_1206_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_apply_2(v___f_1209_, v___x_1227_, lean_box(0));
return v___x_1228_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_close_1206_ = stack[0].m_obj;
lean_object* v_body_1207_ = stack[1].m_obj;
lean_object* v___f_1208_ = stack[2].m_obj;
lean_object* v___f_1209_ = stack[3].m_obj;
lean_object* v_x_1210_ = stack[4].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1206_, v_body_1207_, v___f_1208_, v___f_1209_, v_x_1210_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1230_, lean_object* v_body_1231_, lean_object* v___f_1232_, lean_object* v___f_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1230_, v_body_1231_, v___f_1232_, v___f_1233_, v_x_1234_);
return v_res_1236_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1237_, uint8_t v___x_1238_, lean_object* v___f_1239_, lean_object* v___f_1240_, lean_object* v_x1_1241_, lean_object* v_x2_1242_){
_start:
{
lean_object* v_fst_1243_; uint8_t v___x_1244_; 
v_fst_1243_ = lean_ctor_get(v_x2_1242_, 0);
lean_inc(v_fst_1243_);
v___x_1244_ = lean_string_dec_eq(v___x_1237_, v_fst_1243_);
if (v___x_1244_ == 0)
{
if (v___x_1238_ == 0)
{
lean_dec(v_fst_1243_);
lean_dec_ref(v_x2_1242_);
lean_dec_ref(v___f_1240_);
lean_dec_ref(v___f_1239_);
return v_x1_1241_;
}
else
{
lean_object* v_entries_1245_; lean_object* v_indexes_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
v_entries_1245_ = lean_ctor_get(v_x1_1241_, 0);
v_indexes_1246_ = lean_ctor_get(v_x1_1241_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x1_1241_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1248_ = v_x1_1241_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_indexes_1246_);
lean_inc(v_entries_1245_);
lean_dec(v_x1_1241_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_i_1250_; lean_object* v_f_1251_; lean_object* v_entries_1252_; lean_object* v_indexes_1253_; lean_object* v___x_1255_; 
v_i_1250_ = lean_array_get_size(v_entries_1245_);
v_f_1251_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0), 2, 1);
lean_closure_set(v_f_1251_, 0, v_i_1250_);
v_entries_1252_ = lean_array_push(v_entries_1245_, v_x2_1242_);
v_indexes_1253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1239_, v___f_1240_, v_indexes_1246_, v_fst_1243_, v_f_1251_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_indexes_1253_);
lean_ctor_set(v___x_1248_, 0, v_entries_1252_);
v___x_1255_ = v___x_1248_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_entries_1252_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_indexes_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_dec(v_fst_1243_);
lean_dec_ref(v_x2_1242_);
lean_dec_ref(v___f_1240_);
lean_dec_ref(v___f_1239_);
return v_x1_1241_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1237_ = stack[0].m_obj;
uint8_t v___x_1238_ = stack[1].m_num;
lean_object* v___f_1239_ = stack[2].m_obj;
lean_object* v___f_1240_ = stack[3].m_obj;
lean_object* v_x1_1241_ = stack[4].m_obj;
lean_object* v_x2_1242_ = stack[5].m_obj;
lean_object* v_res_1258_;
v_res_1258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1237_, v___x_1238_, v___f_1239_, v___f_1240_, v_x1_1241_, v_x2_1242_);
stack->m_obj
 = v_res_1258_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v___f_1261_, lean_object* v___f_1262_, lean_object* v_x1_1263_, lean_object* v_x2_1264_){
_start:
{
uint8_t v___x_2292__boxed_1265_; lean_object* v_res_1266_; 
v___x_2292__boxed_1265_ = lean_unbox(v___x_1260_);
v_res_1266_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1259_, v___x_2292__boxed_1265_, v___f_1261_, v___f_1262_, v_x1_1263_, v_x2_1264_);
lean_dec_ref(v___x_1259_);
return v_res_1266_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_1267_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1289_, lean_object* v_body_1290_, lean_object* v_close_1291_, lean_object* v_isClosed_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___y_1296_; uint8_t v_omitBody_1297_; lean_object* v___y_1310_; lean_object* v___y_1345_; uint8_t v___y_1349_; uint8_t v___y_1350_; lean_object* v___y_1351_; uint8_t v___y_1352_; 
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_isClosed_1292_);
lean_dec_ref(v_close_1291_);
lean_dec(v_body_1290_);
lean_dec_ref(v___y_1289_);
v_a_1353_ = lean_ctor_get(v_x_1293_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v_x_1293_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v_x_1293_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
}
else
{
lean_object* v_writer_1362_; lean_object* v_a_1363_; lean_object* v_reader_1364_; lean_object* v_config_1365_; lean_object* v_events_1366_; lean_object* v_error_1367_; lean_object* v_instant_1368_; uint8_t v_keepAlive_1369_; uint8_t v_forcedFlush_1370_; uint8_t v_pullBodyStalled_1371_; lean_object* v_userData_1372_; lean_object* v_outputData_1373_; lean_object* v_state_1374_; lean_object* v_knownSize_1375_; lean_object* v_messageHead_1376_; uint8_t v_sentMessage_1377_; uint8_t v_userClosedBody_1378_; uint8_t v_omitBody_1379_; lean_object* v_userDataBytes_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1483_; 
v_writer_1362_ = lean_ctor_get(v___y_1289_, 1);
lean_inc_ref(v_writer_1362_);
v_a_1363_ = lean_ctor_get(v_x_1293_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v_x_1293_, 1);
v_reader_1364_ = lean_ctor_get(v___y_1289_, 0);
v_config_1365_ = lean_ctor_get(v___y_1289_, 2);
v_events_1366_ = lean_ctor_get(v___y_1289_, 3);
v_error_1367_ = lean_ctor_get(v___y_1289_, 4);
v_instant_1368_ = lean_ctor_get(v___y_1289_, 5);
v_keepAlive_1369_ = lean_ctor_get_uint8(v___y_1289_, sizeof(void*)*6);
v_forcedFlush_1370_ = lean_ctor_get_uint8(v___y_1289_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1371_ = lean_ctor_get_uint8(v___y_1289_, sizeof(void*)*6 + 2);
v_userData_1372_ = lean_ctor_get(v_writer_1362_, 0);
v_outputData_1373_ = lean_ctor_get(v_writer_1362_, 1);
v_state_1374_ = lean_ctor_get(v_writer_1362_, 2);
v_knownSize_1375_ = lean_ctor_get(v_writer_1362_, 3);
v_messageHead_1376_ = lean_ctor_get(v_writer_1362_, 4);
v_sentMessage_1377_ = lean_ctor_get_uint8(v_writer_1362_, sizeof(void*)*6);
v_userClosedBody_1378_ = lean_ctor_get_uint8(v_writer_1362_, sizeof(void*)*6 + 1);
v_omitBody_1379_ = lean_ctor_get_uint8(v_writer_1362_, sizeof(void*)*6 + 2);
v_userDataBytes_1380_ = lean_ctor_get(v_writer_1362_, 5);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_writer_1362_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1382_ = v_writer_1362_;
v_isShared_1383_ = v_isSharedCheck_1483_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_userDataBytes_1380_);
lean_inc(v_messageHead_1376_);
lean_inc(v_knownSize_1375_);
lean_inc(v_state_1374_);
lean_inc(v_outputData_1373_);
lean_inc(v_userData_1372_);
lean_dec(v_writer_1362_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1483_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
uint8_t v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1408_; uint8_t v___y_1409_; uint8_t v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; uint8_t v___x_1433_; uint8_t v___y_1435_; uint8_t v___y_1436_; uint8_t v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; uint8_t v___y_1440_; uint8_t v___y_1447_; uint8_t v___y_1448_; uint8_t v___y_1449_; uint8_t v___y_1462_; uint8_t v___y_1463_; uint8_t v___y_1466_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1433_ = 0;
v___x_1481_ = lean_box(1);
v___x_1482_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1374_, v___x_1481_);
if (v___x_1482_ == 0)
{
v___y_1466_ = v___x_1482_;
goto v___jp_1465_;
}
else
{
if (v_sentMessage_1377_ == 0)
{
v___y_1466_ = v___x_1482_;
goto v___jp_1465_;
}
else
{
lean_del_object(v___x_1382_);
lean_dec(v_userDataBytes_1380_);
lean_dec(v_messageHead_1376_);
lean_dec(v_knownSize_1375_);
lean_dec(v_state_1374_);
lean_dec_ref(v_outputData_1373_);
lean_dec_ref(v_userData_1372_);
lean_dec(v_a_1363_);
v___y_1296_ = v___y_1289_;
v_omitBody_1297_ = v_omitBody_1379_;
goto v___jp_1295_;
}
}
v___jp_1384_:
{
lean_object* v_message_1387_; lean_object* v___x_2029__overap_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v_message_1387_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1385_, v_a_1363_, v___y_1386_);
v___x_2029__overap_1388_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1385_);
v___x_1389_ = lean_apply_2(v___x_2029__overap_1388_, v_outputData_1373_, v_message_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1389_);
v___x_1391_ = v___x_1382_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_userData_1372_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_state_1374_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_knownSize_1375_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_messageHead_1376_);
lean_ctor_set(v_reuseFailAlloc_1393_, 5, v_userDataBytes_1380_);
lean_ctor_set_uint8(v_reuseFailAlloc_1393_, sizeof(void*)*6, v_sentMessage_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1393_, sizeof(void*)*6 + 1, v_userClosedBody_1378_);
lean_ctor_set_uint8(v_reuseFailAlloc_1393_, sizeof(void*)*6 + 2, v_omitBody_1379_);
v___x_1391_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1392_, 0, v_reader_1364_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
lean_ctor_set(v___x_1392_, 2, v_config_1365_);
lean_ctor_set(v___x_1392_, 3, v_events_1366_);
lean_ctor_set(v___x_1392_, 4, v_error_1367_);
lean_ctor_set(v___x_1392_, 5, v_instant_1368_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*6, v_keepAlive_1369_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*6 + 1, v_forcedFlush_1370_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*6 + 2, v_pullBodyStalled_1371_);
v___y_1296_ = v___x_1392_;
v_omitBody_1297_ = v_omitBody_1379_;
goto v___jp_1295_;
}
}
v___jp_1394_:
{
lean_object* v_entries_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_entries_1398_ = lean_ctor_get(v___y_1395_, 0);
lean_inc_ref(v_entries_1398_);
lean_dec_ref(v___y_1395_);
v___x_1399_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_array_get_size(v_entries_1398_);
v___x_1402_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_1403_ = lean_nat_dec_lt(v___x_1400_, v___x_1401_);
if (v___x_1403_ == 0)
{
lean_dec_ref(v_entries_1398_);
lean_dec_ref(v___y_1396_);
v___y_1385_ = v___y_1397_;
v___y_1386_ = v___x_1399_;
goto v___jp_1384_;
}
else
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1401_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1402_, v___y_1396_, v_entries_1398_, v___x_1404_, v___x_1405_, v___x_1399_);
v___y_1385_ = v___y_1397_;
v___y_1386_ = v___x_1406_;
goto v___jp_1384_;
}
}
v___jp_1407_:
{
lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; uint8_t v___x_1417_; 
v___x_1412_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1413_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1414_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1415_ = lean_box(v___y_1408_);
v___f_1416_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1416_, 0, v___x_1412_);
lean_closure_set(v___f_1416_, 1, v___x_1415_);
lean_closure_set(v___f_1416_, 2, v___f_1413_);
lean_closure_set(v___f_1416_, 3, v___f_1414_);
v___x_1417_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1413_, v___f_1414_, v___x_1412_, v___y_1411_);
if (v___x_1417_ == 0)
{
if (v___y_1409_ == 0)
{
v___y_1395_ = v___y_1411_;
v___y_1396_ = v___f_1416_;
v___y_1397_ = v___y_1410_;
goto v___jp_1394_;
}
else
{
lean_dec_ref(v___f_1416_);
v___y_1385_ = v___y_1410_;
v___y_1386_ = v___y_1411_;
goto v___jp_1384_;
}
}
else
{
v___y_1395_ = v___y_1411_;
v___y_1396_ = v___f_1416_;
v___y_1397_ = v___y_1410_;
goto v___jp_1394_;
}
}
v___jp_1418_:
{
lean_object* v_entries_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_entries_1424_ = lean_ctor_get(v___y_1420_, 0);
lean_inc_ref(v_entries_1424_);
lean_dec_ref(v___y_1420_);
v___x_1425_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_array_get_size(v_entries_1424_);
v___x_1428_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_1429_ = lean_nat_dec_lt(v___x_1426_, v___x_1427_);
if (v___x_1429_ == 0)
{
lean_dec_ref(v_entries_1424_);
lean_dec_ref(v___y_1422_);
v___y_1408_ = v___y_1419_;
v___y_1409_ = v___y_1421_;
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___x_1425_;
goto v___jp_1407_;
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1427_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1428_, v___y_1422_, v_entries_1424_, v___x_1430_, v___x_1431_, v___x_1425_);
v___y_1408_ = v___y_1419_;
v___y_1409_ = v___y_1421_;
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___x_1432_;
goto v___jp_1407_;
}
}
v___jp_1434_:
{
lean_object* v_headerSize_1441_; lean_object* v_machine_1442_; lean_object* v_machine_1443_; lean_object* v_reader_1444_; lean_object* v_state_1445_; 
v_headerSize_1441_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1439_, v_a_1363_, v___y_1436_);
v_machine_1442_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1433_, v___y_1438_, v_headerSize_1441_, v___y_1440_);
v_machine_1443_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1433_, v_machine_1442_, v_a_1363_);
lean_dec(v_a_1363_);
v_reader_1444_ = lean_ctor_get(v_machine_1443_, 0);
v_state_1445_ = lean_ctor_get(v_reader_1444_, 0);
if (lean_obj_tag(v_state_1445_) == 7)
{
v___y_1349_ = v___y_1436_;
v___y_1350_ = v___y_1435_;
v___y_1351_ = v_machine_1443_;
v___y_1352_ = v___y_1437_;
goto v___jp_1348_;
}
else
{
v___y_1349_ = v___y_1436_;
v___y_1350_ = v___y_1435_;
v___y_1351_ = v_machine_1443_;
v___y_1352_ = v___y_1436_;
goto v___jp_1348_;
}
}
v___jp_1446_:
{
uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v_indexes_1452_; lean_object* v___x_1453_; lean_object* v_machine_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; uint8_t v___x_1458_; 
v___x_1450_ = 1;
v___x_1451_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1450_, v_a_1363_);
v_indexes_1452_ = lean_ctor_get(v___x_1451_, 1);
lean_inc_ref(v_indexes_1452_);
lean_dec_ref(v___x_1451_);
lean_inc(v_a_1363_);
v___x_1453_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1453_, 0, v_userData_1372_);
lean_ctor_set(v___x_1453_, 1, v_outputData_1373_);
lean_ctor_set(v___x_1453_, 2, v_state_1374_);
lean_ctor_set(v___x_1453_, 3, v_knownSize_1375_);
lean_ctor_set(v___x_1453_, 4, v_a_1363_);
lean_ctor_set(v___x_1453_, 5, v_userDataBytes_1380_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*6, v___y_1448_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*6 + 1, v_userClosedBody_1378_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*6 + 2, v_omitBody_1379_);
v_machine_1454_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1454_, 0, v_reader_1364_);
lean_ctor_set(v_machine_1454_, 1, v___x_1453_);
lean_ctor_set(v_machine_1454_, 2, v_config_1365_);
lean_ctor_set(v_machine_1454_, 3, v_events_1366_);
lean_ctor_set(v_machine_1454_, 4, v_error_1367_);
lean_ctor_set(v_machine_1454_, 5, v_instant_1368_);
lean_ctor_set_uint8(v_machine_1454_, sizeof(void*)*6, v_keepAlive_1369_);
lean_ctor_set_uint8(v_machine_1454_, sizeof(void*)*6 + 1, v_forcedFlush_1370_);
lean_ctor_set_uint8(v_machine_1454_, sizeof(void*)*6 + 2, v_pullBodyStalled_1371_);
v___x_1455_ = l_Std_Http_Header_Name_contentLength;
v___f_1456_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1457_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1456_, v___f_1457_, v_indexes_1452_, v___x_1455_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1460_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1456_, v___f_1457_, v_indexes_1452_, v___x_1459_);
lean_dec_ref(v_indexes_1452_);
v___y_1435_ = v___y_1449_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___y_1448_;
v___y_1438_ = v_machine_1454_;
v___y_1439_ = v___x_1450_;
v___y_1440_ = v___x_1460_;
goto v___jp_1434_;
}
else
{
lean_dec_ref(v_indexes_1452_);
v___y_1435_ = v___y_1449_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___y_1448_;
v___y_1438_ = v_machine_1454_;
v___y_1439_ = v___x_1450_;
v___y_1440_ = v___x_1458_;
goto v___jp_1434_;
}
}
v___jp_1461_:
{
lean_object* v_state_1464_; 
v_state_1464_ = lean_ctor_get(v_reader_1364_, 0);
if (lean_obj_tag(v_state_1464_) == 7)
{
v___y_1447_ = v___y_1463_;
v___y_1448_ = v___y_1462_;
v___y_1449_ = v___y_1462_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___y_1463_;
v___y_1448_ = v___y_1462_;
v___y_1449_ = v___y_1463_;
goto v___jp_1446_;
}
}
v___jp_1465_:
{
if (v___y_1466_ == 0)
{
lean_del_object(v___x_1382_);
lean_dec(v_userDataBytes_1380_);
lean_dec(v_messageHead_1376_);
lean_dec(v_knownSize_1375_);
lean_dec(v_state_1374_);
lean_dec_ref(v_outputData_1373_);
lean_dec_ref(v_userData_1372_);
lean_dec(v_a_1363_);
v___y_1296_ = v___y_1289_;
v_omitBody_1297_ = v_omitBody_1379_;
goto v___jp_1295_;
}
else
{
lean_object* v_status_1467_; uint16_t v___x_1468_; uint16_t v___x_1469_; uint8_t v___x_1470_; 
lean_inc(v_instant_1368_);
lean_inc(v_error_1367_);
lean_inc_ref(v_events_1366_);
lean_inc_ref(v_config_1365_);
lean_inc_ref(v_reader_1364_);
lean_dec_ref(v___y_1289_);
v_status_1467_ = lean_ctor_get(v_a_1363_, 0);
v___x_1468_ = 100;
v___x_1469_ = l_Std_Http_Status_toCode(v_status_1467_);
v___x_1470_ = lean_uint16_dec_le(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_del_object(v___x_1382_);
lean_dec(v_messageHead_1376_);
v___y_1462_ = v___y_1466_;
v___y_1463_ = v___x_1470_;
goto v___jp_1461_;
}
else
{
uint16_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = 200;
v___x_1472_ = lean_uint16_dec_lt(v___x_1469_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_del_object(v___x_1382_);
lean_dec(v_messageHead_1376_);
v___y_1462_ = v___y_1466_;
v___y_1463_ = v___x_1472_;
goto v___jp_1461_;
}
else
{
uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; uint8_t v___x_1480_; 
v___x_1473_ = 1;
v___x_1474_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1473_, v_a_1363_);
v___x_1475_ = l_Std_Http_Header_Name_contentLength;
v___f_1476_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1477_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1478_ = lean_box(v___x_1472_);
v___f_1479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1479_, 0, v___x_1475_);
lean_closure_set(v___f_1479_, 1, v___x_1478_);
lean_closure_set(v___f_1479_, 2, v___f_1476_);
lean_closure_set(v___f_1479_, 3, v___f_1477_);
v___x_1480_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1476_, v___f_1477_, v___x_1475_, v___x_1474_);
if (v___x_1480_ == 0)
{
if (v___x_1472_ == 0)
{
v___y_1419_ = v___x_1472_;
v___y_1420_ = v___x_1474_;
v___y_1421_ = v___x_1472_;
v___y_1422_ = v___f_1479_;
v___y_1423_ = v___x_1473_;
goto v___jp_1418_;
}
else
{
lean_dec_ref(v___f_1479_);
v___y_1408_ = v___x_1472_;
v___y_1409_ = v___x_1472_;
v___y_1410_ = v___x_1473_;
v___y_1411_ = v___x_1474_;
goto v___jp_1407_;
}
}
else
{
v___y_1419_ = v___x_1472_;
v___y_1420_ = v___x_1474_;
v___y_1421_ = v___x_1472_;
v___y_1422_ = v___f_1479_;
v___y_1423_ = v___x_1473_;
goto v___jp_1418_;
}
}
}
}
}
}
}
v___jp_1295_:
{
if (v_omitBody_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v_isClosed_1292_);
lean_dec_ref(v_close_1291_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_body_1290_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___y_1296_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
else
{
lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___f_1302_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1302_, 0, v___y_1296_);
lean_inc_ref(v___f_1302_);
v___f_1303_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1303_, 0, v___f_1302_);
lean_inc(v_body_1290_);
v___f_1304_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1304_, 0, v_close_1291_);
lean_closure_set(v___f_1304_, 1, v_body_1290_);
lean_closure_set(v___f_1304_, 2, v___f_1303_);
lean_closure_set(v___f_1304_, 3, v___f_1302_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = 0;
v___x_1307_ = lean_apply_2(v_isClosed_1292_, v_body_1290_, lean_box(0));
v___x_1308_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1305_, v___x_1306_, v___x_1307_, v___f_1304_);
return v___x_1308_;
}
}
v___jp_1309_:
{
lean_object* v_writer_1311_; lean_object* v_reader_1312_; lean_object* v_config_1313_; lean_object* v_events_1314_; lean_object* v_error_1315_; lean_object* v_instant_1316_; uint8_t v_keepAlive_1317_; uint8_t v_forcedFlush_1318_; uint8_t v_pullBodyStalled_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1343_; 
v_writer_1311_ = lean_ctor_get(v___y_1310_, 1);
v_reader_1312_ = lean_ctor_get(v___y_1310_, 0);
v_config_1313_ = lean_ctor_get(v___y_1310_, 2);
v_events_1314_ = lean_ctor_get(v___y_1310_, 3);
v_error_1315_ = lean_ctor_get(v___y_1310_, 4);
v_instant_1316_ = lean_ctor_get(v___y_1310_, 5);
v_keepAlive_1317_ = lean_ctor_get_uint8(v___y_1310_, sizeof(void*)*6);
v_forcedFlush_1318_ = lean_ctor_get_uint8(v___y_1310_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1319_ = lean_ctor_get_uint8(v___y_1310_, sizeof(void*)*6 + 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___y_1310_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1321_ = v___y_1310_;
v_isShared_1322_ = v_isSharedCheck_1343_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_instant_1316_);
lean_inc(v_error_1315_);
lean_inc(v_events_1314_);
lean_inc(v_config_1313_);
lean_inc(v_writer_1311_);
lean_inc(v_reader_1312_);
lean_dec(v___y_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1343_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_userData_1323_; lean_object* v_outputData_1324_; lean_object* v_knownSize_1325_; lean_object* v_messageHead_1326_; uint8_t v_sentMessage_1327_; uint8_t v_userClosedBody_1328_; uint8_t v_omitBody_1329_; lean_object* v_userDataBytes_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1341_; 
v_userData_1323_ = lean_ctor_get(v_writer_1311_, 0);
v_outputData_1324_ = lean_ctor_get(v_writer_1311_, 1);
v_knownSize_1325_ = lean_ctor_get(v_writer_1311_, 3);
v_messageHead_1326_ = lean_ctor_get(v_writer_1311_, 4);
v_sentMessage_1327_ = lean_ctor_get_uint8(v_writer_1311_, sizeof(void*)*6);
v_userClosedBody_1328_ = lean_ctor_get_uint8(v_writer_1311_, sizeof(void*)*6 + 1);
v_omitBody_1329_ = lean_ctor_get_uint8(v_writer_1311_, sizeof(void*)*6 + 2);
v_userDataBytes_1330_ = lean_ctor_get(v_writer_1311_, 5);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_writer_1311_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_writer_1311_, 2);
lean_dec(v_unused_1342_);
v___x_1332_ = v_writer_1311_;
v_isShared_1333_ = v_isSharedCheck_1341_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_userDataBytes_1330_);
lean_inc(v_messageHead_1326_);
lean_inc(v_knownSize_1325_);
lean_inc(v_outputData_1324_);
lean_inc(v_userData_1323_);
lean_dec(v_writer_1311_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1341_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_box(2);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 2, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_userData_1323_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_outputData_1324_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_knownSize_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_messageHead_1326_);
lean_ctor_set(v_reuseFailAlloc_1340_, 5, v_userDataBytes_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*6, v_sentMessage_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*6 + 1, v_userClosedBody_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*6 + 2, v_omitBody_1329_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1336_);
v___x_1338_ = v___x_1321_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_reader_1312_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_config_1313_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_events_1314_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_error_1315_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_instant_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*6, v_keepAlive_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*6 + 1, v_forcedFlush_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*6 + 2, v_pullBodyStalled_1319_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
v___y_1296_ = v___x_1338_;
v_omitBody_1297_ = v_omitBody_1329_;
goto v___jp_1295_;
}
}
}
}
}
v___jp_1344_:
{
lean_object* v_writer_1346_; uint8_t v_omitBody_1347_; 
v_writer_1346_ = lean_ctor_get(v___y_1345_, 1);
v_omitBody_1347_ = lean_ctor_get_uint8(v_writer_1346_, sizeof(void*)*6 + 2);
v___y_1296_ = v___y_1345_;
v_omitBody_1297_ = v_omitBody_1347_;
goto v___jp_1295_;
}
v___jp_1348_:
{
if (v___y_1352_ == 0)
{
v___y_1310_ = v___y_1351_;
goto v___jp_1309_;
}
else
{
if (v___y_1350_ == 0)
{
v___y_1345_ = v___y_1351_;
goto v___jp_1344_;
}
else
{
if (v___y_1349_ == 0)
{
v___y_1310_ = v___y_1351_;
goto v___jp_1309_;
}
else
{
v___y_1345_ = v___y_1351_;
goto v___jp_1344_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1289_ = stack[0].m_obj;
lean_object* v_body_1290_ = stack[1].m_obj;
lean_object* v_close_1291_ = stack[2].m_obj;
lean_object* v_isClosed_1292_ = stack[3].m_obj;
lean_object* v_x_1293_ = stack[4].m_obj;
lean_object* v_res_1484_;
v_res_1484_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1289_, v_body_1290_, v_close_1291_, v_isClosed_1292_, v_x_1293_);
stack->m_obj
 = v_res_1484_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1485_, lean_object* v_body_1486_, lean_object* v_close_1487_, lean_object* v_isClosed_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1485_, v_body_1486_, v_close_1487_, v_isClosed_1488_, v_x_1489_);
return v_res_1491_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_body_1492_, lean_object* v_close_1493_, lean_object* v_isClosed_1494_, lean_object* v_config_1495_, lean_object* v_line_1496_, lean_object* v_machine_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v___y_1501_; 
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_machine_1497_);
lean_dec_ref(v_line_1496_);
lean_dec_ref(v_isClosed_1494_);
lean_dec_ref(v_close_1493_);
lean_dec(v_body_1492_);
v_a_1507_ = lean_ctor_get(v_x_1498_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1498_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1509_ = v_x_1498_;
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v_x_1498_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; 
v_a_1516_ = lean_ctor_get(v_x_1498_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v_x_1498_, 1);
if (lean_obj_tag(v_a_1516_) == 1)
{
lean_object* v_writer_1517_; lean_object* v_reader_1518_; lean_object* v_config_1519_; lean_object* v_events_1520_; lean_object* v_error_1521_; lean_object* v_instant_1522_; uint8_t v_keepAlive_1523_; uint8_t v_forcedFlush_1524_; uint8_t v_pullBodyStalled_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1548_; 
v_writer_1517_ = lean_ctor_get(v_machine_1497_, 1);
v_reader_1518_ = lean_ctor_get(v_machine_1497_, 0);
v_config_1519_ = lean_ctor_get(v_machine_1497_, 2);
v_events_1520_ = lean_ctor_get(v_machine_1497_, 3);
v_error_1521_ = lean_ctor_get(v_machine_1497_, 4);
v_instant_1522_ = lean_ctor_get(v_machine_1497_, 5);
v_keepAlive_1523_ = lean_ctor_get_uint8(v_machine_1497_, sizeof(void*)*6);
v_forcedFlush_1524_ = lean_ctor_get_uint8(v_machine_1497_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1525_ = lean_ctor_get_uint8(v_machine_1497_, sizeof(void*)*6 + 2);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_machine_1497_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1527_ = v_machine_1497_;
v_isShared_1528_ = v_isSharedCheck_1548_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_instant_1522_);
lean_inc(v_error_1521_);
lean_inc(v_events_1520_);
lean_inc(v_config_1519_);
lean_inc(v_writer_1517_);
lean_inc(v_reader_1518_);
lean_dec(v_machine_1497_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1548_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_userData_1529_; lean_object* v_outputData_1530_; lean_object* v_state_1531_; lean_object* v_messageHead_1532_; uint8_t v_sentMessage_1533_; uint8_t v_userClosedBody_1534_; uint8_t v_omitBody_1535_; lean_object* v_userDataBytes_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1546_; 
v_userData_1529_ = lean_ctor_get(v_writer_1517_, 0);
v_outputData_1530_ = lean_ctor_get(v_writer_1517_, 1);
v_state_1531_ = lean_ctor_get(v_writer_1517_, 2);
v_messageHead_1532_ = lean_ctor_get(v_writer_1517_, 4);
v_sentMessage_1533_ = lean_ctor_get_uint8(v_writer_1517_, sizeof(void*)*6);
v_userClosedBody_1534_ = lean_ctor_get_uint8(v_writer_1517_, sizeof(void*)*6 + 1);
v_omitBody_1535_ = lean_ctor_get_uint8(v_writer_1517_, sizeof(void*)*6 + 2);
v_userDataBytes_1536_ = lean_ctor_get(v_writer_1517_, 5);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_writer_1517_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_writer_1517_, 3);
lean_dec(v_unused_1547_);
v___x_1538_ = v_writer_1517_;
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_userDataBytes_1536_);
lean_inc(v_messageHead_1532_);
lean_inc(v_state_1531_);
lean_inc(v_outputData_1530_);
lean_inc(v_userData_1529_);
lean_dec(v_writer_1517_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 3, v_a_1516_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_userData_1529_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_outputData_1530_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_state_1531_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_a_1516_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_messageHead_1532_);
lean_ctor_set(v_reuseFailAlloc_1545_, 5, v_userDataBytes_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*6, v_sentMessage_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*6 + 1, v_userClosedBody_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*6 + 2, v_omitBody_1535_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1541_);
v___x_1543_ = v___x_1527_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_reader_1518_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_config_1519_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_events_1520_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_error_1521_);
lean_ctor_set(v_reuseFailAlloc_1544_, 5, v_instant_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1544_, sizeof(void*)*6, v_keepAlive_1523_);
lean_ctor_set_uint8(v_reuseFailAlloc_1544_, sizeof(void*)*6 + 1, v_forcedFlush_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1544_, sizeof(void*)*6 + 2, v_pullBodyStalled_1525_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
v___y_1501_ = v___x_1543_;
goto v___jp_1500_;
}
}
}
}
}
else
{
lean_dec(v_a_1516_);
v___y_1501_ = v_machine_1497_;
goto v___jp_1500_;
}
}
v___jp_1500_:
{
lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___f_1502_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1502_, 0, v___y_1501_);
lean_closure_set(v___f_1502_, 1, v_body_1492_);
lean_closure_set(v___f_1502_, 2, v_close_1493_);
lean_closure_set(v___f_1502_, 3, v_isClosed_1494_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = 0;
v___x_1505_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1495_, v_line_1496_);
v___x_1506_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1503_, v___x_1504_, v___x_1505_, v___f_1502_);
return v___x_1506_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_1492_ = stack[0].m_obj;
lean_object* v_close_1493_ = stack[1].m_obj;
lean_object* v_isClosed_1494_ = stack[2].m_obj;
lean_object* v_config_1495_ = stack[3].m_obj;
lean_object* v_line_1496_ = stack[4].m_obj;
lean_object* v_machine_1497_ = stack[5].m_obj;
lean_object* v_x_1498_ = stack[6].m_obj;
lean_object* v_res_1549_;
v_res_1549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_body_1492_, v_close_1493_, v_isClosed_1494_, v_config_1495_, v_line_1496_, v_machine_1497_, v_x_1498_);
stack->m_obj
 = v_res_1549_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_body_1550_, lean_object* v_close_1551_, lean_object* v_isClosed_1552_, lean_object* v_config_1553_, lean_object* v_line_1554_, lean_object* v_machine_1555_, lean_object* v_x_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_body_1550_, v_close_1551_, v_isClosed_1552_, v_config_1553_, v_line_1554_, v_machine_1555_, v_x_1556_);
lean_dec_ref(v_config_1553_);
return v_res_1558_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1559_, lean_object* v_config_1560_, lean_object* v_machine_1561_, lean_object* v_res_1562_){
_start:
{
lean_object* v_close_1564_; lean_object* v_isClosed_1565_; lean_object* v_getKnownSize_1566_; lean_object* v_line_1567_; lean_object* v_body_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_close_1564_ = lean_ctor_get(v_inst_1559_, 1);
lean_inc_ref(v_close_1564_);
v_isClosed_1565_ = lean_ctor_get(v_inst_1559_, 2);
lean_inc_ref(v_isClosed_1565_);
v_getKnownSize_1566_ = lean_ctor_get(v_inst_1559_, 5);
lean_inc_ref(v_getKnownSize_1566_);
lean_dec_ref(v_inst_1559_);
v_line_1567_ = lean_ctor_get(v_res_1562_, 0);
lean_inc_ref(v_line_1567_);
v_body_1568_ = lean_ctor_get(v_res_1562_, 1);
lean_inc_n(v_body_1568_, 2);
lean_dec_ref(v_res_1562_);
v___f_1569_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1569_, 0, v_body_1568_);
lean_closure_set(v___f_1569_, 1, v_close_1564_);
lean_closure_set(v___f_1569_, 2, v_isClosed_1565_);
lean_closure_set(v___f_1569_, 3, v_config_1560_);
lean_closure_set(v___f_1569_, 4, v_line_1567_);
lean_closure_set(v___f_1569_, 5, v_machine_1561_);
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = 0;
v___x_1572_ = lean_apply_2(v_getKnownSize_1566_, v_body_1568_, lean_box(0));
v___x_1573_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1570_, v___x_1571_, v___x_1572_, v___f_1569_);
return v___x_1573_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1559_ = stack[0].m_obj;
lean_object* v_config_1560_ = stack[1].m_obj;
lean_object* v_machine_1561_ = stack[2].m_obj;
lean_object* v_res_1562_ = stack[3].m_obj;
lean_object* v_res_1574_;
v_res_1574_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1559_, v_config_1560_, v_machine_1561_, v_res_1562_);
stack->m_obj
 = v_res_1574_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1575_, lean_object* v_config_1576_, lean_object* v_machine_1577_, lean_object* v_res_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1575_, v_config_1576_, v_machine_1577_, v_res_1578_);
return v_res_1580_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1581_, lean_object* v_inst_1582_, lean_object* v_config_1583_, lean_object* v_machine_1584_, lean_object* v_res_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1582_, v_config_1583_, v_machine_1584_, v_res_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1582_ = stack[1].m_obj;
lean_object* v_config_1583_ = stack[2].m_obj;
lean_object* v_machine_1584_ = stack[3].m_obj;
lean_object* v_res_1585_ = stack[4].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_box(0), v_inst_1582_, v_config_1583_, v_machine_1584_, v_res_1585_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1589_, lean_object* v_inst_1590_, lean_object* v_config_1591_, lean_object* v_machine_1592_, lean_object* v_res_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1589_, v_inst_1590_, v_config_1591_, v_machine_1592_, v_res_1593_);
return v_res_1595_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v_closed_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_closed_1599_ = lean_ctor_get_uint8(v_____do__lift_1596_, sizeof(void*)*6);
v___x_1600_ = lean_box(v_closed_1599_);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1596_ = stack[0].m_obj;
lean_object* v___y_1597_ = stack[1].m_obj;
lean_object* v_res_1603_;
v_res_1603_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1596_, v___y_1597_);
stack->m_obj
 = v_res_1603_;
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
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1608_, lean_object* v_x_1609_){
_start:
{
if (lean_obj_tag(v_x_1609_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v___x_1608_);
v_a_1611_ = lean_ctor_get(v_x_1609_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_x_1609_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v_x_1609_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v_x_1609_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
}
else
{
lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1628_; 
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1609_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_x_1609_, 0);
lean_dec(v_unused_1629_);
v___x_1621_ = v_x_1609_;
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v_x_1609_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1608_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1608_ = stack[0].m_obj;
lean_object* v_x_1609_ = stack[1].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1608_, v_x_1609_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1631_, v_x_1632_);
return v_res_1634_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; lean_object* v_pendingProducer_1643_; lean_object* v_pendingConsumer_1644_; lean_object* v_interestWaiter_1645_; uint8_t v_closed_1646_; lean_object* v_pendingIncompleteChunk_1647_; lean_object* v_closeError_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1657_; 
v___x_1642_ = lean_st_ref_take(v___y_1640_);
v_pendingProducer_1643_ = lean_ctor_get(v___x_1642_, 0);
v_pendingConsumer_1644_ = lean_ctor_get(v___x_1642_, 1);
v_interestWaiter_1645_ = lean_ctor_get(v___x_1642_, 2);
v_closed_1646_ = lean_ctor_get_uint8(v___x_1642_, sizeof(void*)*6);
v_pendingIncompleteChunk_1647_ = lean_ctor_get(v___x_1642_, 4);
v_closeError_1648_ = lean_ctor_get(v___x_1642_, 5);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v___x_1642_, 3);
lean_dec(v_unused_1658_);
v___x_1650_ = v___x_1642_;
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_closeError_1648_);
lean_inc(v_pendingIncompleteChunk_1647_);
lean_inc(v_interestWaiter_1645_);
lean_inc(v_pendingConsumer_1644_);
lean_inc(v_pendingProducer_1643_);
lean_dec(v___x_1642_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 3, v___x_1639_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_pendingProducer_1643_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_pendingConsumer_1644_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_interestWaiter_1645_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_pendingIncompleteChunk_1647_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_closeError_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, sizeof(void*)*6, v_closed_1646_);
v___x_1653_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_st_ref_put(v___y_1640_, v___x_1653_);
v___x_1655_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1655_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1639_ = stack[0].m_obj;
lean_object* v___y_1640_ = stack[1].m_obj;
lean_object* v_res_1659_;
v_res_1659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1639_, v___y_1640_);
stack->m_obj
 = v_res_1659_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1660_, v___y_1661_);
lean_dec(v___y_1661_);
return v_res_1663_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1664_, lean_object* v_requestStream_1665_, lean_object* v_keepAliveTimeout_1666_, lean_object* v_currentTimeout_1667_, lean_object* v_headerTimeout_1668_, lean_object* v_response_1669_, lean_object* v_respStream_1670_, lean_object* v_expectData_1671_, uint8_t v_handlerDispatched_1672_, lean_object* v_____r_1673_){
_start:
{
uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1675_ = 0;
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1677_, 0, v_machine_1664_);
lean_ctor_set(v___x_1677_, 1, v_requestStream_1665_);
lean_ctor_set(v___x_1677_, 2, v_keepAliveTimeout_1666_);
lean_ctor_set(v___x_1677_, 3, v_currentTimeout_1667_);
lean_ctor_set(v___x_1677_, 4, v_headerTimeout_1668_);
lean_ctor_set(v___x_1677_, 5, v_response_1669_);
lean_ctor_set(v___x_1677_, 6, v_respStream_1670_);
lean_ctor_set(v___x_1677_, 7, v_expectData_1671_);
lean_ctor_set(v___x_1677_, 8, v___x_1676_);
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*9, v___x_1675_);
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*9 + 1, v_handlerDispatched_1672_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_machine_1664_ = stack[0].m_obj;
lean_object* v_requestStream_1665_ = stack[1].m_obj;
lean_object* v_keepAliveTimeout_1666_ = stack[2].m_obj;
lean_object* v_currentTimeout_1667_ = stack[3].m_obj;
lean_object* v_headerTimeout_1668_ = stack[4].m_obj;
lean_object* v_response_1669_ = stack[5].m_obj;
lean_object* v_respStream_1670_ = stack[6].m_obj;
lean_object* v_expectData_1671_ = stack[7].m_obj;
uint8_t v_handlerDispatched_1672_ = stack[8].m_num;
lean_object* v_____r_1673_ = stack[9].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1664_, v_requestStream_1665_, v_keepAliveTimeout_1666_, v_currentTimeout_1667_, v_headerTimeout_1668_, v_response_1669_, v_respStream_1670_, v_expectData_1671_, v_handlerDispatched_1672_, v_____r_1673_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1682_, lean_object* v_requestStream_1683_, lean_object* v_keepAliveTimeout_1684_, lean_object* v_currentTimeout_1685_, lean_object* v_headerTimeout_1686_, lean_object* v_response_1687_, lean_object* v_respStream_1688_, lean_object* v_expectData_1689_, lean_object* v_handlerDispatched_1690_, lean_object* v_____r_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v_handlerDispatched_boxed_1693_; lean_object* v_res_1694_; 
v_handlerDispatched_boxed_1693_ = lean_unbox(v_handlerDispatched_1690_);
v_res_1694_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1682_, v_requestStream_1683_, v_keepAliveTimeout_1684_, v_currentTimeout_1685_, v_headerTimeout_1686_, v_response_1687_, v_respStream_1688_, v_expectData_1689_, v_handlerDispatched_boxed_1693_, v_____r_1691_);
return v_res_1694_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1695_, lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v___f_1695_);
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
lean_object* v_a_1707_; lean_object* v___x_1708_; 
v_a_1707_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v_x_1696_, 1);
v___x_1708_ = lean_apply_2(v___f_1695_, v_a_1707_, lean_box(0));
return v___x_1708_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1695_ = stack[0].m_obj;
lean_object* v_x_1696_ = stack[1].m_obj;
lean_object* v_res_1709_;
v_res_1709_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1695_, v_x_1696_);
stack->m_obj
 = v_res_1709_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1710_, v_x_1711_);
return v_res_1713_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1714_, lean_object* v___f_1715_, lean_object* v___f_1716_, lean_object* v_x_1717_){
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
lean_dec_ref_known(v_x_1717_, 1);
v___x_1729_ = lean_unbox(v_a_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v___f_1716_);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = l_Std_Http_Body_Stream_close(v_requestStream_1714_);
v___x_1732_ = lean_unbox(v_a_1728_);
lean_dec(v_a_1728_);
v___x_1733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1730_, v___x_1732_, v___x_1731_, v___f_1715_);
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
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestStream_1714_ = stack[0].m_obj;
lean_object* v___f_1715_ = stack[1].m_obj;
lean_object* v___f_1716_ = stack[2].m_obj;
lean_object* v_x_1717_ = stack[3].m_obj;
lean_object* v_res_1736_;
v_res_1736_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1714_, v___f_1715_, v___f_1716_, v_x_1717_);
stack->m_obj
 = v_res_1736_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1737_, lean_object* v___f_1738_, lean_object* v___f_1739_, lean_object* v_x_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1737_, v___f_1738_, v___f_1739_, v_x_1740_);
return v_res_1742_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1743_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_1744_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___f_1752_; 
v___x_1750_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1751_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1752_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1752_, 0, v___f_1751_);
lean_closure_set(v___f_1752_, 1, v___x_1750_);
return v___f_1752_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___f_1762_; lean_object* v___f_1763_; 
v___x_1761_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1762_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1763_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1763_, 0, v___f_1762_);
lean_closure_set(v___f_1763_, 1, v___x_1761_);
return v___f_1763_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1764_; lean_object* v___x_1765_; 
v___f_1764_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1765_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1765_, 0, lean_box(0));
lean_closure_set(v___x_1765_, 1, lean_box(0));
lean_closure_set(v___x_1765_, 2, lean_box(0));
lean_closure_set(v___x_1765_, 3, v___f_1764_);
return v___x_1765_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1766_, lean_object* v___f_1767_, lean_object* v_x_1768_){
_start:
{
if (lean_obj_tag(v_x_1768_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___f_1767_);
lean_dec_ref(v___y_1766_);
v_a_1770_ = lean_ctor_get(v_x_1768_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_x_1768_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1772_ = v_x_1768_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v_x_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
}
else
{
lean_object* v_machine_1779_; lean_object* v_requestStream_1780_; lean_object* v_keepAliveTimeout_1781_; lean_object* v_currentTimeout_1782_; lean_object* v_headerTimeout_1783_; lean_object* v_response_1784_; lean_object* v_respStream_1785_; lean_object* v_expectData_1786_; uint8_t v_handlerDispatched_1787_; lean_object* v___x_1788_; lean_object* v___f_1789_; lean_object* v___f_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_4870__overap_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec_ref_known(v_x_1768_, 1);
v_machine_1779_ = lean_ctor_get(v___y_1766_, 0);
lean_inc_ref(v_machine_1779_);
v_requestStream_1780_ = lean_ctor_get(v___y_1766_, 1);
lean_inc_ref_n(v_requestStream_1780_, 3);
v_keepAliveTimeout_1781_ = lean_ctor_get(v___y_1766_, 2);
lean_inc(v_keepAliveTimeout_1781_);
v_currentTimeout_1782_ = lean_ctor_get(v___y_1766_, 3);
lean_inc(v_currentTimeout_1782_);
v_headerTimeout_1783_ = lean_ctor_get(v___y_1766_, 4);
lean_inc(v_headerTimeout_1783_);
v_response_1784_ = lean_ctor_get(v___y_1766_, 5);
lean_inc_ref(v_response_1784_);
v_respStream_1785_ = lean_ctor_get(v___y_1766_, 6);
lean_inc(v_respStream_1785_);
v_expectData_1786_ = lean_ctor_get(v___y_1766_, 7);
lean_inc(v_expectData_1786_);
v_handlerDispatched_1787_ = lean_ctor_get_uint8(v___y_1766_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1766_);
v___x_1788_ = lean_box(v_handlerDispatched_1787_);
v___f_1789_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1789_, 0, v_machine_1779_);
lean_closure_set(v___f_1789_, 1, v_requestStream_1780_);
lean_closure_set(v___f_1789_, 2, v_keepAliveTimeout_1781_);
lean_closure_set(v___f_1789_, 3, v_currentTimeout_1782_);
lean_closure_set(v___f_1789_, 4, v_headerTimeout_1783_);
lean_closure_set(v___f_1789_, 5, v_response_1784_);
lean_closure_set(v___f_1789_, 6, v_respStream_1785_);
lean_closure_set(v___f_1789_, 7, v_expectData_1786_);
lean_closure_set(v___f_1789_, 8, v___x_1788_);
lean_inc_ref(v___f_1789_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1790_, 0, v___f_1789_);
v___f_1791_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1791_, 0, v_requestStream_1780_);
lean_closure_set(v___f_1791_, 1, v___f_1790_);
lean_closure_set(v___f_1791_, 2, v___f_1789_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = 0;
v___x_1794_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1795_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1796_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1797_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1798_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1798_, 0, lean_box(0));
lean_closure_set(v___x_1798_, 1, lean_box(0));
lean_closure_set(v___x_1798_, 2, v___x_1794_);
lean_closure_set(v___x_1798_, 3, lean_box(0));
lean_closure_set(v___x_1798_, 4, lean_box(0));
lean_closure_set(v___x_1798_, 5, v___x_1797_);
lean_closure_set(v___x_1798_, 6, v___f_1767_);
v___x_4870__overap_1799_ = l_Std_Mutex_atomically___redArg(v___x_1794_, v___f_1795_, v___f_1796_, v_requestStream_1780_, v___x_1798_);
v___x_1800_ = lean_apply_1(v___x_4870__overap_1799_, lean_box(0));
v___x_1801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1792_, v___x_1793_, v___x_1800_, v___f_1791_);
return v___x_1801_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1766_ = stack[0].m_obj;
lean_object* v___f_1767_ = stack[1].m_obj;
lean_object* v_x_1768_ = stack[2].m_obj;
lean_object* v_res_1802_;
v_res_1802_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1766_, v___f_1767_, v_x_1768_);
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1803_, lean_object* v___f_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1803_, v___f_1804_, v_x_1805_);
return v_res_1807_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1809_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v___y_1808_);
v_a_1811_ = lean_ctor_get(v_x_1809_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v_x_1809_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v_x_1809_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1811_);
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
else
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1828_; 
v_isSharedCheck_1828_ = !lean_is_exclusive(v_x_1809_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_x_1809_, 0);
lean_dec(v_unused_1829_);
v___x_1821_ = v_x_1809_;
v_isShared_1822_ = v_isSharedCheck_1828_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v_x_1809_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1828_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___y_1808_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1808_ = stack[0].m_obj;
lean_object* v_x_1809_ = stack[1].m_obj;
lean_object* v_res_1830_;
v_res_1830_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1808_, v_x_1809_);
stack->m_obj
 = v_res_1830_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1831_, lean_object* v_x_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1831_, v_x_1832_);
return v_res_1834_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1835_, lean_object* v___f_1836_, lean_object* v___y_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___y_1837_);
lean_dec_ref(v___f_1836_);
lean_dec_ref(v_requestStream_1835_);
v_a_1840_ = lean_ctor_get(v_x_1838_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1842_ = v_x_1838_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v_x_1838_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1840_);
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
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1863_; 
v_a_1849_ = lean_ctor_get(v_x_1838_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1851_ = v_x_1838_;
v_isShared_1852_ = v_isSharedCheck_1863_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v_x_1838_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1863_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_unbox(v_a_1849_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; 
lean_del_object(v___x_1851_);
lean_dec_ref(v___y_1837_);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = l_Std_Http_Body_Stream_close(v_requestStream_1835_);
v___x_1856_ = lean_unbox(v_a_1849_);
lean_dec(v_a_1849_);
v___x_1857_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1854_, v___x_1856_, v___x_1855_, v___f_1836_);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
lean_dec(v_a_1849_);
lean_dec_ref(v___f_1836_);
lean_dec_ref(v_requestStream_1835_);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___y_1837_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1858_);
v___x_1860_ = v___x_1851_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestStream_1835_ = stack[0].m_obj;
lean_object* v___f_1836_ = stack[1].m_obj;
lean_object* v___y_1837_ = stack[2].m_obj;
lean_object* v_x_1838_ = stack[3].m_obj;
lean_object* v_res_1864_;
v_res_1864_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1835_, v___f_1836_, v___y_1837_, v_x_1838_);
stack->m_obj
 = v_res_1864_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1865_, lean_object* v___f_1866_, lean_object* v___y_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1865_, v___f_1866_, v___y_1867_, v_x_1868_);
return v_res_1870_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1871_, lean_object* v_machine_1872_, lean_object* v_a_1873_, uint8_t v_requiresData_1874_, lean_object* v_expectData_1875_, lean_object* v_pendingHead_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_pendingHead_1876_);
lean_dec(v_expectData_1875_);
lean_dec_ref(v_a_1873_);
lean_dec_ref(v_machine_1872_);
v_a_1879_ = lean_ctor_get(v_x_1877_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1881_ = v_x_1877_;
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v_x_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1902_; 
v_a_1888_ = lean_ctor_get(v_x_1877_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1890_ = v_x_1877_;
v_isShared_1891_ = v_isSharedCheck_1902_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v_x_1877_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1902_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_keepAliveTimeout_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v_keepAliveTimeout_1892_ = lean_ctor_get(v_config_1871_, 5);
lean_inc_n(v_keepAliveTimeout_1892_, 2);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_keepAliveTimeout_1892_);
v___x_1894_ = lean_box(0);
v___x_1895_ = 0;
v___x_1896_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1896_, 0, v_machine_1872_);
lean_ctor_set(v___x_1896_, 1, v_a_1873_);
lean_ctor_set(v___x_1896_, 2, v___x_1893_);
lean_ctor_set(v___x_1896_, 3, v_keepAliveTimeout_1892_);
lean_ctor_set(v___x_1896_, 4, v___x_1894_);
lean_ctor_set(v___x_1896_, 5, v_a_1888_);
lean_ctor_set(v___x_1896_, 6, v___x_1894_);
lean_ctor_set(v___x_1896_, 7, v_expectData_1875_);
lean_ctor_set(v___x_1896_, 8, v_pendingHead_1876_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*9, v_requiresData_1874_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*9 + 1, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1897_);
v___x_1899_ = v___x_1890_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1871_ = stack[0].m_obj;
lean_object* v_machine_1872_ = stack[1].m_obj;
lean_object* v_a_1873_ = stack[2].m_obj;
uint8_t v_requiresData_1874_ = stack[3].m_num;
lean_object* v_expectData_1875_ = stack[4].m_obj;
lean_object* v_pendingHead_1876_ = stack[5].m_obj;
lean_object* v_x_1877_ = stack[6].m_obj;
lean_object* v_res_1903_;
v_res_1903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1871_, v_machine_1872_, v_a_1873_, v_requiresData_1874_, v_expectData_1875_, v_pendingHead_1876_, v_x_1877_);
stack->m_obj
 = v_res_1903_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1904_, lean_object* v_machine_1905_, lean_object* v_a_1906_, lean_object* v_requiresData_1907_, lean_object* v_expectData_1908_, lean_object* v_pendingHead_1909_, lean_object* v_x_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v_requiresData_boxed_1912_; lean_object* v_res_1913_; 
v_requiresData_boxed_1912_ = lean_unbox(v_requiresData_1907_);
v_res_1913_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1904_, v_machine_1905_, v_a_1906_, v_requiresData_boxed_1912_, v_expectData_1908_, v_pendingHead_1909_, v_x_1910_);
lean_dec_ref(v_config_1904_);
return v_res_1913_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1914_, lean_object* v_machine_1915_, uint8_t v_requiresData_1916_, lean_object* v_expectData_1917_, lean_object* v_pendingHead_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_pendingHead_1918_);
lean_dec(v_expectData_1917_);
lean_dec_ref(v_machine_1915_);
lean_dec_ref(v_config_1914_);
v_a_1921_ = lean_ctor_get(v_x_1919_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v_x_1919_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v_x_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1945_; 
v_a_1930_ = lean_ctor_get(v_x_1919_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1932_ = v_x_1919_;
v_isShared_1933_ = v_isSharedCheck_1945_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v_x_1919_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1945_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1934_ = lean_box(v_requiresData_1916_);
v___f_1935_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1935_, 0, v_config_1914_);
lean_closure_set(v___f_1935_, 1, v_machine_1915_);
lean_closure_set(v___f_1935_, 2, v_a_1930_);
lean_closure_set(v___f_1935_, 3, v___x_1934_);
lean_closure_set(v___f_1935_, 4, v_expectData_1917_);
lean_closure_set(v___f_1935_, 5, v_pendingHead_1918_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = 0;
v___x_1939_ = l_Std_CloseableChannel_new___redArg(v___x_1936_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1939_);
v___x_1941_ = v___x_1932_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
v___x_1943_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1937_, v___x_1938_, v___x_1942_, v___f_1935_);
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1914_ = stack[0].m_obj;
lean_object* v_machine_1915_ = stack[1].m_obj;
uint8_t v_requiresData_1916_ = stack[2].m_num;
lean_object* v_expectData_1917_ = stack[3].m_obj;
lean_object* v_pendingHead_1918_ = stack[4].m_obj;
lean_object* v_x_1919_ = stack[5].m_obj;
lean_object* v_res_1946_;
v_res_1946_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1914_, v_machine_1915_, v_requiresData_1916_, v_expectData_1917_, v_pendingHead_1918_, v_x_1919_);
stack->m_obj
 = v_res_1946_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1947_, lean_object* v_machine_1948_, lean_object* v_requiresData_1949_, lean_object* v_expectData_1950_, lean_object* v_pendingHead_1951_, lean_object* v_x_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v_requiresData_boxed_1954_; lean_object* v_res_1955_; 
v_requiresData_boxed_1954_ = lean_unbox(v_requiresData_1949_);
v_res_1955_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1947_, v_machine_1948_, v_requiresData_boxed_1954_, v_expectData_1950_, v_pendingHead_1951_, v_x_1952_);
return v_res_1955_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1956_, lean_object* v_____r_1957_){
_start:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = 0;
v___x_1961_ = l_Std_Http_Body_mkStream();
v___x_1962_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1959_, v___x_1960_, v___x_1961_, v___f_1956_);
return v___x_1962_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1956_ = stack[0].m_obj;
lean_object* v_____r_1957_ = stack[1].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1956_, v_____r_1957_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1964_, lean_object* v_____r_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1964_, v_____r_1965_);
return v_res_1967_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1968_, lean_object* v_val_1969_, lean_object* v___f_1970_, lean_object* v___f_1971_, lean_object* v_x_1972_){
_start:
{
if (lean_obj_tag(v_x_1972_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v___f_1971_);
lean_dec_ref(v___f_1970_);
lean_dec(v_val_1969_);
lean_dec_ref(v_close_1968_);
v_a_1974_ = lean_ctor_get(v_x_1972_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_x_1972_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v_x_1972_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v_x_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1983_; uint8_t v___x_1984_; 
v_a_1983_ = lean_ctor_get(v_x_1972_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v_x_1972_, 1);
v___x_1984_ = lean_unbox(v_a_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; 
lean_dec_ref(v___f_1971_);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_apply_2(v_close_1968_, v_val_1969_, lean_box(0));
v___x_1987_ = lean_unbox(v_a_1983_);
lean_dec(v_a_1983_);
v___x_1988_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1985_, v___x_1987_, v___x_1986_, v___f_1970_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v_a_1983_);
lean_dec_ref(v___f_1970_);
lean_dec(v_val_1969_);
lean_dec_ref(v_close_1968_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_apply_2(v___f_1971_, v___x_1989_, lean_box(0));
return v___x_1990_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_close_1968_ = stack[0].m_obj;
lean_object* v_val_1969_ = stack[1].m_obj;
lean_object* v___f_1970_ = stack[2].m_obj;
lean_object* v___f_1971_ = stack[3].m_obj;
lean_object* v_x_1972_ = stack[4].m_obj;
lean_object* v_res_1991_;
v_res_1991_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1968_, v_val_1969_, v___f_1970_, v___f_1971_, v_x_1972_);
stack->m_obj
 = v_res_1991_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1992_, lean_object* v_val_1993_, lean_object* v___f_1994_, lean_object* v___f_1995_, lean_object* v_x_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1992_, v_val_1993_, v___f_1994_, v___f_1995_, v_x_1996_);
return v_res_1998_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1999_, lean_object* v_inst_2000_, lean_object* v___f_2001_, lean_object* v___f_2002_, lean_object* v_____r_2003_){
_start:
{
if (lean_obj_tag(v_respStream_1999_) == 1)
{
lean_object* v_val_2005_; lean_object* v_close_2006_; lean_object* v_isClosed_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_val_2005_ = lean_ctor_get(v_respStream_1999_, 0);
lean_inc_n(v_val_2005_, 2);
lean_dec_ref_known(v_respStream_1999_, 1);
v_close_2006_ = lean_ctor_get(v_inst_2000_, 1);
lean_inc_ref(v_close_2006_);
v_isClosed_2007_ = lean_ctor_get(v_inst_2000_, 2);
lean_inc_ref(v_isClosed_2007_);
lean_dec_ref(v_inst_2000_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_2008_, 0, v_close_2006_);
lean_closure_set(v___f_2008_, 1, v_val_2005_);
lean_closure_set(v___f_2008_, 2, v___f_2001_);
lean_closure_set(v___f_2008_, 3, v___f_2002_);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = 0;
v___x_2011_ = lean_apply_2(v_isClosed_2007_, v_val_2005_, lean_box(0));
v___x_2012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2009_, v___x_2010_, v___x_2011_, v___f_2008_);
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v___f_2001_);
lean_dec_ref(v_inst_2000_);
lean_dec(v_respStream_1999_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_apply_2(v___f_2002_, v___x_2013_, lean_box(0));
return v___x_2014_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_respStream_1999_ = stack[0].m_obj;
lean_object* v_inst_2000_ = stack[1].m_obj;
lean_object* v___f_2001_ = stack[2].m_obj;
lean_object* v___f_2002_ = stack[3].m_obj;
lean_object* v_____r_2003_ = stack[4].m_obj;
lean_object* v_res_2015_;
v_res_2015_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1999_, v_inst_2000_, v___f_2001_, v___f_2002_, v_____r_2003_);
stack->m_obj
 = v_res_2015_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_2016_, lean_object* v_inst_2017_, lean_object* v___f_2018_, lean_object* v___f_2019_, lean_object* v_____r_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_2016_, v_inst_2017_, v___f_2018_, v___f_2019_, v_____r_2020_);
return v_res_2022_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_2023_, lean_object* v_keepAliveTimeout_2024_, lean_object* v_currentTimeout_2025_, lean_object* v_headerTimeout_2026_, lean_object* v_response_2027_, lean_object* v_respStream_2028_, uint8_t v_requiresData_2029_, lean_object* v_expectData_2030_, uint8_t v_handlerDispatched_2031_, lean_object* v_pendingHead_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_pendingHead_2032_);
lean_dec(v_expectData_2030_);
lean_dec(v_respStream_2028_);
lean_dec_ref(v_response_2027_);
lean_dec(v_headerTimeout_2026_);
lean_dec(v_currentTimeout_2025_);
lean_dec(v_keepAliveTimeout_2024_);
lean_dec_ref(v_requestStream_2023_);
v_a_2035_ = lean_ctor_get(v_x_2033_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2037_ = v_x_2033_;
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v_x_2033_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2035_);
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
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2065_; 
v_a_2044_ = lean_ctor_get(v_x_2033_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2046_ = v_x_2033_;
v_isShared_2047_ = v_isSharedCheck_2065_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v_x_2033_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2065_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_snd_2048_; uint8_t v___x_2049_; 
v_snd_2048_ = lean_ctor_get(v_a_2044_, 1);
v___x_2049_ = lean_unbox(v_snd_2048_);
if (v___x_2049_ == 0)
{
lean_object* v_fst_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v_fst_2050_ = lean_ctor_get(v_a_2044_, 0);
lean_inc(v_fst_2050_);
lean_dec(v_a_2044_);
v___x_2051_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2051_, 0, v_fst_2050_);
lean_ctor_set(v___x_2051_, 1, v_requestStream_2023_);
lean_ctor_set(v___x_2051_, 2, v_keepAliveTimeout_2024_);
lean_ctor_set(v___x_2051_, 3, v_currentTimeout_2025_);
lean_ctor_set(v___x_2051_, 4, v_headerTimeout_2026_);
lean_ctor_set(v___x_2051_, 5, v_response_2027_);
lean_ctor_set(v___x_2051_, 6, v_respStream_2028_);
lean_ctor_set(v___x_2051_, 7, v_expectData_2030_);
lean_ctor_set(v___x_2051_, 8, v_pendingHead_2032_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*9, v_requiresData_2029_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*9 + 1, v_handlerDispatched_2031_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2052_);
v___x_2054_ = v___x_2046_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
else
{
lean_object* v_fst_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec(v_pendingHead_2032_);
v_fst_2057_ = lean_ctor_get(v_a_2044_, 0);
lean_inc(v_fst_2057_);
lean_dec(v_a_2044_);
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2059_, 0, v_fst_2057_);
lean_ctor_set(v___x_2059_, 1, v_requestStream_2023_);
lean_ctor_set(v___x_2059_, 2, v_keepAliveTimeout_2024_);
lean_ctor_set(v___x_2059_, 3, v_currentTimeout_2025_);
lean_ctor_set(v___x_2059_, 4, v_headerTimeout_2026_);
lean_ctor_set(v___x_2059_, 5, v_response_2027_);
lean_ctor_set(v___x_2059_, 6, v_respStream_2028_);
lean_ctor_set(v___x_2059_, 7, v_expectData_2030_);
lean_ctor_set(v___x_2059_, 8, v___x_2058_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*9, v_requiresData_2029_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*9 + 1, v_handlerDispatched_2031_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2060_);
v___x_2062_ = v___x_2046_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestStream_2023_ = stack[0].m_obj;
lean_object* v_keepAliveTimeout_2024_ = stack[1].m_obj;
lean_object* v_currentTimeout_2025_ = stack[2].m_obj;
lean_object* v_headerTimeout_2026_ = stack[3].m_obj;
lean_object* v_response_2027_ = stack[4].m_obj;
lean_object* v_respStream_2028_ = stack[5].m_obj;
uint8_t v_requiresData_2029_ = stack[6].m_num;
lean_object* v_expectData_2030_ = stack[7].m_obj;
uint8_t v_handlerDispatched_2031_ = stack[8].m_num;
lean_object* v_pendingHead_2032_ = stack[9].m_obj;
lean_object* v_x_2033_ = stack[10].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2023_, v_keepAliveTimeout_2024_, v_currentTimeout_2025_, v_headerTimeout_2026_, v_response_2027_, v_respStream_2028_, v_requiresData_2029_, v_expectData_2030_, v_handlerDispatched_2031_, v_pendingHead_2032_, v_x_2033_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2067_, lean_object* v_keepAliveTimeout_2068_, lean_object* v_currentTimeout_2069_, lean_object* v_headerTimeout_2070_, lean_object* v_response_2071_, lean_object* v_respStream_2072_, lean_object* v_requiresData_2073_, lean_object* v_expectData_2074_, lean_object* v_handlerDispatched_2075_, lean_object* v_pendingHead_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_requiresData_boxed_2079_; uint8_t v_handlerDispatched_boxed_2080_; lean_object* v_res_2081_; 
v_requiresData_boxed_2079_ = lean_unbox(v_requiresData_2073_);
v_handlerDispatched_boxed_2080_ = lean_unbox(v_handlerDispatched_2075_);
v_res_2081_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2067_, v_keepAliveTimeout_2068_, v_currentTimeout_2069_, v_headerTimeout_2070_, v_response_2071_, v_respStream_2072_, v_requiresData_boxed_2079_, v_expectData_2074_, v_handlerDispatched_boxed_2080_, v_pendingHead_2076_, v_x_2077_);
return v_res_2081_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2094_, lean_object* v_inst_2095_, lean_object* v___f_2096_, lean_object* v_handler_2097_, lean_object* v___f_2098_, lean_object* v_inst_2099_, lean_object* v___f_2100_, lean_object* v_connectionContext_2101_, lean_object* v_a_2102_, lean_object* v_x_2103_, lean_object* v___y_2104_){
_start:
{
switch(lean_obj_tag(v_a_2102_))
{
case 0:
{
lean_object* v_head_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_connectionContext_2101_);
lean_dec_ref(v___f_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec_ref(v___f_2098_);
lean_dec(v_handler_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v_inst_2095_);
v_head_2106_ = lean_ctor_get(v_a_2102_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_a_2102_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2108_ = v_a_2102_;
v_isShared_2109_ = v_isSharedCheck_2149_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_head_2106_);
lean_dec(v_a_2102_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2149_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_machine_2110_; lean_object* v_requestStream_2111_; lean_object* v_response_2112_; lean_object* v_respStream_2113_; uint8_t v_requiresData_2114_; lean_object* v_expectData_2115_; uint8_t v_handlerDispatched_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2144_; 
v_machine_2110_ = lean_ctor_get(v___y_2104_, 0);
v_requestStream_2111_ = lean_ctor_get(v___y_2104_, 1);
v_response_2112_ = lean_ctor_get(v___y_2104_, 5);
v_respStream_2113_ = lean_ctor_get(v___y_2104_, 6);
v_requiresData_2114_ = lean_ctor_get_uint8(v___y_2104_, sizeof(void*)*9);
v_expectData_2115_ = lean_ctor_get(v___y_2104_, 7);
v_handlerDispatched_2116_ = lean_ctor_get_uint8(v___y_2104_, sizeof(void*)*9 + 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___y_2104_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; 
v_unused_2145_ = lean_ctor_get(v___y_2104_, 8);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v___y_2104_, 4);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v___y_2104_, 3);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v___y_2104_, 2);
lean_dec(v_unused_2148_);
v___x_2118_ = v___y_2104_;
v_isShared_2119_ = v_isSharedCheck_2144_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_expectData_2115_);
lean_inc(v_respStream_2113_);
lean_inc(v_response_2112_);
lean_inc(v_requestStream_2111_);
lean_inc(v_machine_2110_);
lean_dec(v___y_2104_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2144_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_lingeringTimeout_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v_lingeringTimeout_2120_ = lean_ctor_get(v_config_2094_, 4);
lean_inc(v_lingeringTimeout_2120_);
lean_dec_ref(v_config_2094_);
v___x_2121_ = lean_box(0);
lean_inc(v_head_2106_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 1);
v___x_2123_ = v___x_2108_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_head_2106_);
v___x_2123_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
lean_inc_ref(v_requestStream_2111_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 8, v___x_2123_);
lean_ctor_set(v___x_2118_, 4, v___x_2121_);
lean_ctor_set(v___x_2118_, 3, v_lingeringTimeout_2120_);
lean_ctor_set(v___x_2118_, 2, v___x_2121_);
v___x_2125_ = v___x_2118_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_machine_2110_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_requestStream_2111_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v_lingeringTimeout_2120_);
lean_ctor_set(v_reuseFailAlloc_2142_, 4, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2142_, 5, v_response_2112_);
lean_ctor_set(v_reuseFailAlloc_2142_, 6, v_respStream_2113_);
lean_ctor_set(v_reuseFailAlloc_2142_, 7, v_expectData_2115_);
lean_ctor_set(v_reuseFailAlloc_2142_, 8, v___x_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2142_, sizeof(void*)*9, v_requiresData_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2142_, sizeof(void*)*9 + 1, v_handlerDispatched_2116_);
v___x_2125_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
uint8_t v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = 0;
v___x_2127_ = 1;
v___x_2128_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2126_, v_head_2106_, v___x_2127_);
lean_dec(v_head_2106_);
if (lean_obj_tag(v___x_2128_) == 1)
{
lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; lean_object* v___x_5061__overap_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___f_2129_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2129_, 0, v___x_2125_);
v___f_2130_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2130_, 0, v___x_2128_);
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = 0;
v___x_2133_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2134_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2135_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_2136_ = l_Std_Mutex_atomically___redArg(v___x_2133_, v___f_2134_, v___f_2135_, v_requestStream_2111_, v___f_2130_);
v___x_2137_ = lean_apply_1(v___x_5061__overap_2136_, lean_box(0));
v___x_2138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2131_, v___x_2132_, v___x_2137_, v___f_2129_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec(v___x_2128_);
lean_dec_ref(v_requestStream_2111_);
v___x_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2125_);
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
}
case 1:
{
lean_object* v_size_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_connectionContext_2101_);
lean_dec_ref(v___f_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec_ref(v___f_2098_);
lean_dec(v_handler_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v_inst_2095_);
lean_dec_ref(v_config_2094_);
v_size_2150_ = lean_ctor_get(v_a_2102_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_a_2102_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2152_ = v_a_2102_;
v_isShared_2153_ = v_isSharedCheck_2177_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_size_2150_);
lean_dec(v_a_2102_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2177_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_machine_2154_; lean_object* v_requestStream_2155_; lean_object* v_keepAliveTimeout_2156_; lean_object* v_currentTimeout_2157_; lean_object* v_headerTimeout_2158_; lean_object* v_response_2159_; lean_object* v_respStream_2160_; uint8_t v_handlerDispatched_2161_; lean_object* v_pendingHead_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2175_; 
v_machine_2154_ = lean_ctor_get(v___y_2104_, 0);
v_requestStream_2155_ = lean_ctor_get(v___y_2104_, 1);
v_keepAliveTimeout_2156_ = lean_ctor_get(v___y_2104_, 2);
v_currentTimeout_2157_ = lean_ctor_get(v___y_2104_, 3);
v_headerTimeout_2158_ = lean_ctor_get(v___y_2104_, 4);
v_response_2159_ = lean_ctor_get(v___y_2104_, 5);
v_respStream_2160_ = lean_ctor_get(v___y_2104_, 6);
v_handlerDispatched_2161_ = lean_ctor_get_uint8(v___y_2104_, sizeof(void*)*9 + 1);
v_pendingHead_2162_ = lean_ctor_get(v___y_2104_, 8);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___y_2104_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; 
v_unused_2176_ = lean_ctor_get(v___y_2104_, 7);
lean_dec(v_unused_2176_);
v___x_2164_ = v___y_2104_;
v_isShared_2165_ = v_isSharedCheck_2175_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_pendingHead_2162_);
lean_inc(v_respStream_2160_);
lean_inc(v_response_2159_);
lean_inc(v_headerTimeout_2158_);
lean_inc(v_currentTimeout_2157_);
lean_inc(v_keepAliveTimeout_2156_);
lean_inc(v_requestStream_2155_);
lean_inc(v_machine_2154_);
lean_dec(v___y_2104_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2175_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint8_t v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = 1;
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 7, v_size_2150_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_machine_2154_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_requestStream_2155_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_keepAliveTimeout_2156_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_currentTimeout_2157_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_headerTimeout_2158_);
lean_ctor_set(v_reuseFailAlloc_2174_, 5, v_response_2159_);
lean_ctor_set(v_reuseFailAlloc_2174_, 6, v_respStream_2160_);
lean_ctor_set(v_reuseFailAlloc_2174_, 7, v_size_2150_);
lean_ctor_set(v_reuseFailAlloc_2174_, 8, v_pendingHead_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*9 + 1, v_handlerDispatched_2161_);
v___x_2168_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*9, v___x_2166_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2168_);
v___x_2170_ = v___x_2152_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2178_; lean_object* v_onFailure_2179_; lean_object* v___f_2180_; lean_object* v___y_2182_; 
lean_dec_ref(v_connectionContext_2101_);
lean_dec_ref(v___f_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec_ref(v___f_2098_);
lean_dec_ref(v_config_2094_);
v_err_2178_ = lean_ctor_get(v_a_2102_, 0);
lean_inc(v_err_2178_);
lean_dec_ref_known(v_a_2102_, 1);
v_onFailure_2179_ = lean_ctor_get(v_inst_2095_, 2);
lean_inc_ref(v_onFailure_2179_);
lean_dec_ref(v_inst_2095_);
v___f_2180_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2180_, 0, v___y_2104_);
lean_closure_set(v___f_2180_, 1, v___f_2096_);
switch(lean_obj_tag(v_err_2178_))
{
case 0:
{
lean_object* v___x_2188_; 
v___x_2188_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2182_ = v___x_2188_;
goto v___jp_2181_;
}
case 1:
{
lean_object* v___x_2189_; 
v___x_2189_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2182_ = v___x_2189_;
goto v___jp_2181_;
}
case 2:
{
lean_object* v___x_2190_; 
v___x_2190_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2182_ = v___x_2190_;
goto v___jp_2181_;
}
case 3:
{
lean_object* v___x_2191_; 
v___x_2191_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2182_ = v___x_2191_;
goto v___jp_2181_;
}
case 4:
{
lean_object* v___x_2192_; 
v___x_2192_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2182_ = v___x_2192_;
goto v___jp_2181_;
}
case 5:
{
lean_object* v___x_2193_; 
v___x_2193_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2182_ = v___x_2193_;
goto v___jp_2181_;
}
case 6:
{
lean_object* v___x_2194_; 
v___x_2194_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2182_ = v___x_2194_;
goto v___jp_2181_;
}
case 7:
{
lean_object* v___x_2195_; 
v___x_2195_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2182_ = v___x_2195_;
goto v___jp_2181_;
}
case 8:
{
lean_object* v___x_2196_; 
v___x_2196_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2182_ = v___x_2196_;
goto v___jp_2181_;
}
case 9:
{
lean_object* v___x_2197_; 
v___x_2197_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2182_ = v___x_2197_;
goto v___jp_2181_;
}
case 10:
{
lean_object* v___x_2198_; 
v___x_2198_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2182_ = v___x_2198_;
goto v___jp_2181_;
}
default: 
{
lean_object* v_message_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_message_2199_ = lean_ctor_get(v_err_2178_, 0);
lean_inc_ref(v_message_2199_);
lean_dec_ref_known(v_err_2178_, 1);
v___x_2200_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2201_ = lean_string_append(v___x_2200_, v_message_2199_);
lean_dec_ref(v_message_2199_);
v___y_2182_ = v___x_2201_;
goto v___jp_2181_;
}
}
v___jp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2183_ = lean_mk_io_user_error(v___y_2182_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = 0;
v___x_2186_ = lean_apply_3(v_onFailure_2179_, v_handler_2097_, v___x_2183_, lean_box(0));
v___x_2187_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2184_, v___x_2185_, v___x_2186_, v___f_2180_);
return v___x_2187_;
}
}
case 4:
{
lean_object* v_requestStream_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___f_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_5118__overap_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec_ref(v_connectionContext_2101_);
lean_dec_ref(v___f_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec(v_handler_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v_inst_2095_);
lean_dec_ref(v_config_2094_);
v_requestStream_2202_ = lean_ctor_get(v___y_2104_, 1);
lean_inc_ref_n(v_requestStream_2202_, 2);
lean_inc_ref(v___y_2104_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2203_, 0, v___y_2104_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2204_, 0, v_requestStream_2202_);
lean_closure_set(v___f_2204_, 1, v___f_2203_);
lean_closure_set(v___f_2204_, 2, v___y_2104_);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = 0;
v___x_2207_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2208_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2209_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2210_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2211_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2211_, 0, lean_box(0));
lean_closure_set(v___x_2211_, 1, lean_box(0));
lean_closure_set(v___x_2211_, 2, v___x_2207_);
lean_closure_set(v___x_2211_, 3, lean_box(0));
lean_closure_set(v___x_2211_, 4, lean_box(0));
lean_closure_set(v___x_2211_, 5, v___x_2210_);
lean_closure_set(v___x_2211_, 6, v___f_2098_);
v___x_5118__overap_2212_ = l_Std_Mutex_atomically___redArg(v___x_2207_, v___f_2208_, v___f_2209_, v_requestStream_2202_, v___x_2211_);
v___x_2213_ = lean_apply_1(v___x_5118__overap_2212_, lean_box(0));
v___x_2214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2205_, v___x_2206_, v___x_2213_, v___f_2204_);
return v___x_2214_;
}
case 6:
{
lean_object* v_machine_2215_; lean_object* v_requestStream_2216_; lean_object* v_respStream_2217_; uint8_t v_requiresData_2218_; lean_object* v_expectData_2219_; lean_object* v_pendingHead_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___f_2223_; lean_object* v___f_2224_; lean_object* v___f_2225_; lean_object* v___f_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___f_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_5143__overap_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref(v_connectionContext_2101_);
lean_dec_ref(v___f_2098_);
lean_dec(v_handler_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v_inst_2095_);
v_machine_2215_ = lean_ctor_get(v___y_2104_, 0);
lean_inc_ref(v_machine_2215_);
v_requestStream_2216_ = lean_ctor_get(v___y_2104_, 1);
lean_inc_ref_n(v_requestStream_2216_, 2);
v_respStream_2217_ = lean_ctor_get(v___y_2104_, 6);
lean_inc(v_respStream_2217_);
v_requiresData_2218_ = lean_ctor_get_uint8(v___y_2104_, sizeof(void*)*9);
v_expectData_2219_ = lean_ctor_get(v___y_2104_, 7);
lean_inc(v_expectData_2219_);
v_pendingHead_2220_ = lean_ctor_get(v___y_2104_, 8);
lean_inc(v_pendingHead_2220_);
lean_dec_ref(v___y_2104_);
v___x_2221_ = lean_box(v_requiresData_2218_);
v___f_2222_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2222_, 0, v_config_2094_);
lean_closure_set(v___f_2222_, 1, v_machine_2215_);
lean_closure_set(v___f_2222_, 2, v___x_2221_);
lean_closure_set(v___f_2222_, 3, v_expectData_2219_);
lean_closure_set(v___f_2222_, 4, v_pendingHead_2220_);
v___f_2223_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2223_, 0, v___f_2222_);
lean_inc_ref(v___f_2223_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2224_, 0, v___f_2223_);
v___f_2225_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2225_, 0, v_respStream_2217_);
lean_closure_set(v___f_2225_, 1, v_inst_2099_);
lean_closure_set(v___f_2225_, 2, v___f_2224_);
lean_closure_set(v___f_2225_, 3, v___f_2223_);
lean_inc_ref(v___f_2225_);
v___f_2226_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2226_, 0, v___f_2225_);
v___f_2227_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2227_, 0, v_requestStream_2216_);
lean_closure_set(v___f_2227_, 1, v___f_2226_);
lean_closure_set(v___f_2227_, 2, v___f_2225_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = 0;
v___x_2230_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2231_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2232_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2233_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2234_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2234_, 0, lean_box(0));
lean_closure_set(v___x_2234_, 1, lean_box(0));
lean_closure_set(v___x_2234_, 2, v___x_2230_);
lean_closure_set(v___x_2234_, 3, lean_box(0));
lean_closure_set(v___x_2234_, 4, lean_box(0));
lean_closure_set(v___x_2234_, 5, v___x_2233_);
lean_closure_set(v___x_2234_, 6, v___f_2100_);
v___x_5143__overap_2235_ = l_Std_Mutex_atomically___redArg(v___x_2230_, v___f_2231_, v___f_2232_, v_requestStream_2216_, v___x_2234_);
v___x_2236_ = lean_apply_1(v___x_5143__overap_2235_, lean_box(0));
v___x_2237_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2228_, v___x_2229_, v___x_2236_, v___f_2227_);
return v___x_2237_;
}
case 7:
{
lean_object* v_pendingHead_2238_; 
lean_dec_ref(v___f_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec_ref(v___f_2098_);
lean_dec_ref(v___f_2096_);
v_pendingHead_2238_ = lean_ctor_get(v___y_2104_, 8);
if (lean_obj_tag(v_pendingHead_2238_) == 1)
{
lean_object* v_machine_2239_; lean_object* v_requestStream_2240_; lean_object* v_keepAliveTimeout_2241_; lean_object* v_currentTimeout_2242_; lean_object* v_headerTimeout_2243_; lean_object* v_response_2244_; lean_object* v_respStream_2245_; uint8_t v_requiresData_2246_; lean_object* v_expectData_2247_; uint8_t v_handlerDispatched_2248_; lean_object* v_val_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_inc_ref(v_pendingHead_2238_);
v_machine_2239_ = lean_ctor_get(v___y_2104_, 0);
lean_inc_ref(v_machine_2239_);
v_requestStream_2240_ = lean_ctor_get(v___y_2104_, 1);
lean_inc_ref(v_requestStream_2240_);
v_keepAliveTimeout_2241_ = lean_ctor_get(v___y_2104_, 2);
lean_inc(v_keepAliveTimeout_2241_);
v_currentTimeout_2242_ = lean_ctor_get(v___y_2104_, 3);
lean_inc(v_currentTimeout_2242_);
v_headerTimeout_2243_ = lean_ctor_get(v___y_2104_, 4);
lean_inc(v_headerTimeout_2243_);
v_response_2244_ = lean_ctor_get(v___y_2104_, 5);
lean_inc_ref(v_response_2244_);
v_respStream_2245_ = lean_ctor_get(v___y_2104_, 6);
lean_inc(v_respStream_2245_);
v_requiresData_2246_ = lean_ctor_get_uint8(v___y_2104_, sizeof(void*)*9);
v_expectData_2247_ = lean_ctor_get(v___y_2104_, 7);
lean_inc(v_expectData_2247_);
v_handlerDispatched_2248_ = lean_ctor_get_uint8(v___y_2104_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2104_);
v_val_2249_ = lean_ctor_get(v_pendingHead_2238_, 0);
lean_inc(v_val_2249_);
v___x_2250_ = lean_box(v_requiresData_2246_);
v___x_2251_ = lean_box(v_handlerDispatched_2248_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2252_, 0, v_requestStream_2240_);
lean_closure_set(v___f_2252_, 1, v_keepAliveTimeout_2241_);
lean_closure_set(v___f_2252_, 2, v_currentTimeout_2242_);
lean_closure_set(v___f_2252_, 3, v_headerTimeout_2243_);
lean_closure_set(v___f_2252_, 4, v_response_2244_);
lean_closure_set(v___f_2252_, 5, v_respStream_2245_);
lean_closure_set(v___f_2252_, 6, v___x_2250_);
lean_closure_set(v___f_2252_, 7, v_expectData_2247_);
lean_closure_set(v___f_2252_, 8, v___x_2251_);
lean_closure_set(v___f_2252_, 9, v_pendingHead_2238_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = 0;
v___x_2255_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2095_, v_handler_2097_, v_machine_2239_, v_val_2249_, v_config_2094_, v_connectionContext_2101_);
v___x_2256_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2253_, v___x_2254_, v___x_2255_, v___f_2252_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec_ref(v_connectionContext_2101_);
lean_dec(v_handler_2097_);
lean_dec_ref(v_inst_2095_);
lean_dec_ref(v_config_2094_);
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___y_2104_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
default: 
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v_a_2102_);
lean_dec_ref(v_connectionContext_2101_);
lean_dec_ref(v___f_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec_ref(v___f_2098_);
lean_dec(v_handler_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v_inst_2095_);
lean_dec_ref(v_config_2094_);
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2104_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_2094_ = stack[0].m_obj;
lean_object* v_inst_2095_ = stack[1].m_obj;
lean_object* v___f_2096_ = stack[2].m_obj;
lean_object* v_handler_2097_ = stack[3].m_obj;
lean_object* v___f_2098_ = stack[4].m_obj;
lean_object* v_inst_2099_ = stack[5].m_obj;
lean_object* v___f_2100_ = stack[6].m_obj;
lean_object* v_connectionContext_2101_ = stack[7].m_obj;
lean_object* v_a_2102_ = stack[8].m_obj;
lean_object* v___y_2104_ = stack[10].m_obj;
lean_object* v_res_2263_;
v_res_2263_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2094_, v_inst_2095_, v___f_2096_, v_handler_2097_, v___f_2098_, v_inst_2099_, v___f_2100_, v_connectionContext_2101_, v_a_2102_, lean_box(0), v___y_2104_);
stack->m_obj
 = v_res_2263_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2264_, lean_object* v_inst_2265_, lean_object* v___f_2266_, lean_object* v_handler_2267_, lean_object* v___f_2268_, lean_object* v_inst_2269_, lean_object* v___f_2270_, lean_object* v_connectionContext_2271_, lean_object* v_a_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2264_, v_inst_2265_, v___f_2266_, v_handler_2267_, v___f_2268_, v_inst_2269_, v___f_2270_, v_connectionContext_2271_, v_a_2272_, v_x_2273_, v___y_2274_);
return v_res_2276_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_x_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2277_ = stack[0].m_obj;
lean_object* v_res_2280_;
v_res_2280_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2277_);
stack->m_obj
 = v_res_2280_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2281_);
return v_res_2283_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_handler_2288_, lean_object* v_config_2289_, lean_object* v_connectionContext_2290_, lean_object* v_events_2291_, lean_object* v_state_2292_){
_start:
{
lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_4072__overap_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___f_2294_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2295_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2295_, 0, v_config_2289_);
lean_closure_set(v___f_2295_, 1, v_inst_2286_);
lean_closure_set(v___f_2295_, 2, v___f_2294_);
lean_closure_set(v___f_2295_, 3, v_handler_2288_);
lean_closure_set(v___f_2295_, 4, v___f_2294_);
lean_closure_set(v___f_2295_, 5, v_inst_2287_);
lean_closure_set(v___f_2295_, 6, v___f_2294_);
lean_closure_set(v___f_2295_, 7, v_connectionContext_2290_);
v___f_2296_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2297_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2298_ = lean_array_size(v_events_2291_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = 0;
v___x_4072__overap_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2297_, v_events_2291_, v___f_2295_, v_sz_2298_, v___x_2299_, v_state_2292_);
v___x_2303_ = lean_apply_1(v___x_4072__overap_2302_, lean_box(0));
v___x_2304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2300_, v___x_2301_, v___x_2303_, v___f_2296_);
return v___x_2304_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2286_ = stack[0].m_obj;
lean_object* v_inst_2287_ = stack[1].m_obj;
lean_object* v_handler_2288_ = stack[2].m_obj;
lean_object* v_config_2289_ = stack[3].m_obj;
lean_object* v_connectionContext_2290_ = stack[4].m_obj;
lean_object* v_events_2291_ = stack[5].m_obj;
lean_object* v_state_2292_ = stack[6].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2286_, v_inst_2287_, v_handler_2288_, v_config_2289_, v_connectionContext_2290_, v_events_2291_, v_state_2292_);
stack->m_obj
 = v_res_2305_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_handler_2308_, lean_object* v_config_2309_, lean_object* v_connectionContext_2310_, lean_object* v_events_2311_, lean_object* v_state_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2306_, v_inst_2307_, v_handler_2308_, v_config_2309_, v_connectionContext_2310_, v_events_2311_, v_state_2312_);
return v_res_2314_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2315_, lean_object* v_00_u03b2_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_handler_2319_, lean_object* v_config_2320_, lean_object* v_connectionContext_2321_, lean_object* v_events_2322_, lean_object* v_state_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2317_, v_inst_2318_, v_handler_2319_, v_config_2320_, v_connectionContext_2321_, v_events_2322_, v_state_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2317_ = stack[2].m_obj;
lean_object* v_inst_2318_ = stack[3].m_obj;
lean_object* v_handler_2319_ = stack[4].m_obj;
lean_object* v_config_2320_ = stack[5].m_obj;
lean_object* v_connectionContext_2321_ = stack[6].m_obj;
lean_object* v_events_2322_ = stack[7].m_obj;
lean_object* v_state_2323_ = stack[8].m_obj;
lean_object* v_res_2326_;
v_res_2326_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_box(0), lean_box(0), v_inst_2317_, v_inst_2318_, v_handler_2319_, v_config_2320_, v_connectionContext_2321_, v_events_2322_, v_state_2323_);
stack->m_obj
 = v_res_2326_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2327_, lean_object* v_00_u03b2_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_handler_2331_, lean_object* v_config_2332_, lean_object* v_connectionContext_2333_, lean_object* v_events_2334_, lean_object* v_state_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2327_, v_00_u03b2_2328_, v_inst_2329_, v_inst_2330_, v_handler_2331_, v_config_2332_, v_connectionContext_2333_, v_events_2334_, v_state_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2338_){
_start:
{
if (lean_obj_tag(v_x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v_x_2338_, 1);
v___x_2340_ = lean_task_pure(v_a_2339_);
return v___x_2340_;
}
else
{
lean_object* v_a_2341_; 
v_a_2341_ = lean_ctor_get(v_x_2338_, 0);
lean_inc_ref(v_a_2341_);
lean_dec_ref_known(v_x_2338_, 1);
return v_a_2341_;
}
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2342_, lean_object* v_requestStream_2343_, lean_object* v_keepAliveTimeout_2344_, lean_object* v_currentTimeout_2345_, lean_object* v_headerTimeout_2346_, lean_object* v_response_2347_, lean_object* v_respStream_2348_, uint8_t v_requiresData_2349_, lean_object* v_expectData_2350_, lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_expectData_2350_);
lean_dec(v_respStream_2348_);
lean_dec_ref(v_response_2347_);
lean_dec(v_headerTimeout_2346_);
lean_dec(v_currentTimeout_2345_);
lean_dec(v_keepAliveTimeout_2344_);
lean_dec_ref(v_requestStream_2343_);
lean_dec_ref(v_machine_2342_);
v_a_2353_ = lean_ctor_get(v_x_2351_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_x_2351_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2355_ = v_x_2351_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v_x_2351_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
else
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2372_; 
v_isSharedCheck_2372_ = !lean_is_exclusive(v_x_2351_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v_x_2351_, 0);
lean_dec(v_unused_2373_);
v___x_2363_ = v_x_2351_;
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v_x_2351_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2365_ = 1;
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2367_, 0, v_machine_2342_);
lean_ctor_set(v___x_2367_, 1, v_requestStream_2343_);
lean_ctor_set(v___x_2367_, 2, v_keepAliveTimeout_2344_);
lean_ctor_set(v___x_2367_, 3, v_currentTimeout_2345_);
lean_ctor_set(v___x_2367_, 4, v_headerTimeout_2346_);
lean_ctor_set(v___x_2367_, 5, v_response_2347_);
lean_ctor_set(v___x_2367_, 6, v_respStream_2348_);
lean_ctor_set(v___x_2367_, 7, v_expectData_2350_);
lean_ctor_set(v___x_2367_, 8, v___x_2366_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*9, v_requiresData_2349_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*9 + 1, v___x_2365_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2367_);
v___x_2369_ = v___x_2363_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_machine_2342_ = stack[0].m_obj;
lean_object* v_requestStream_2343_ = stack[1].m_obj;
lean_object* v_keepAliveTimeout_2344_ = stack[2].m_obj;
lean_object* v_currentTimeout_2345_ = stack[3].m_obj;
lean_object* v_headerTimeout_2346_ = stack[4].m_obj;
lean_object* v_response_2347_ = stack[5].m_obj;
lean_object* v_respStream_2348_ = stack[6].m_obj;
uint8_t v_requiresData_2349_ = stack[7].m_num;
lean_object* v_expectData_2350_ = stack[8].m_obj;
lean_object* v_x_2351_ = stack[9].m_obj;
lean_object* v_res_2374_;
v_res_2374_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2342_, v_requestStream_2343_, v_keepAliveTimeout_2344_, v_currentTimeout_2345_, v_headerTimeout_2346_, v_response_2347_, v_respStream_2348_, v_requiresData_2349_, v_expectData_2350_, v_x_2351_);
stack->m_obj
 = v_res_2374_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2375_, lean_object* v_requestStream_2376_, lean_object* v_keepAliveTimeout_2377_, lean_object* v_currentTimeout_2378_, lean_object* v_headerTimeout_2379_, lean_object* v_response_2380_, lean_object* v_respStream_2381_, lean_object* v_requiresData_2382_, lean_object* v_expectData_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v_requiresData_boxed_2386_; lean_object* v_res_2387_; 
v_requiresData_boxed_2386_ = lean_unbox(v_requiresData_2382_);
v_res_2387_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2375_, v_requestStream_2376_, v_keepAliveTimeout_2377_, v_currentTimeout_2378_, v_headerTimeout_2379_, v_response_2380_, v_respStream_2381_, v_requiresData_boxed_2386_, v_expectData_2383_, v_x_2384_);
return v_res_2387_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2388_, lean_object* v_response_2389_, lean_object* v___x_2390_, lean_object* v___f_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
lean_dec_ref(v___f_2391_);
lean_dec(v___x_2390_);
lean_dec_ref(v_response_2389_);
lean_dec_ref(v_toFunctor_2388_);
v_a_2394_ = lean_ctor_get(v_x_2392_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_x_2392_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v_x_2392_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v_x_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2417_; 
v_a_2403_ = lean_ctor_get(v_x_2392_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_x_2392_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2405_ = v_x_2392_;
v_isShared_2406_ = v_isSharedCheck_2417_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v_x_2392_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2417_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2407_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2407_, 0, lean_box(0));
lean_closure_set(v___x_2407_, 1, lean_box(0));
lean_closure_set(v___x_2407_, 2, v_toFunctor_2388_);
v___x_2408_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2408_, 0, lean_box(0));
lean_closure_set(v___x_2408_, 1, v_response_2389_);
v___x_2409_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2409_, 0, lean_box(0));
lean_closure_set(v___x_2409_, 1, lean_box(0));
lean_closure_set(v___x_2409_, 2, lean_box(0));
lean_closure_set(v___x_2409_, 3, v___x_2407_);
lean_closure_set(v___x_2409_, 4, v___x_2408_);
v___x_2410_ = 0;
lean_inc(v___x_2390_);
v___x_2411_ = l_BaseIO_chainTask___redArg(v_a_2403_, v___x_2409_, v___x_2390_, v___x_2410_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2411_);
v___x_2413_ = v___x_2405_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
v___x_2415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2390_, v___x_2410_, v___x_2414_, v___f_2391_);
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toFunctor_2388_ = stack[0].m_obj;
lean_object* v_response_2389_ = stack[1].m_obj;
lean_object* v___x_2390_ = stack[2].m_obj;
lean_object* v___f_2391_ = stack[3].m_obj;
lean_object* v_x_2392_ = stack[4].m_obj;
lean_object* v_res_2418_;
v_res_2418_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2388_, v_response_2389_, v___x_2390_, v___f_2391_, v_x_2392_);
stack->m_obj
 = v_res_2418_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2419_, lean_object* v_response_2420_, lean_object* v___x_2421_, lean_object* v___f_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2419_, v_response_2420_, v___x_2421_, v___f_2422_, v_x_2423_);
return v_res_2425_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2427_, lean_object* v_handler_2428_, lean_object* v_extensions_2429_, lean_object* v_connectionContext_2430_, lean_object* v_state_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v_toApplicative_2434_; lean_object* v_pendingHead_2435_; 
v___x_2433_ = l_instMonadBaseIO;
v_toApplicative_2434_ = lean_ctor_get(v___x_2433_, 0);
v_pendingHead_2435_ = lean_ctor_get(v_state_2431_, 8);
lean_inc(v_pendingHead_2435_);
if (lean_obj_tag(v_pendingHead_2435_) == 1)
{
lean_object* v_toFunctor_2436_; lean_object* v_machine_2437_; lean_object* v_requestStream_2438_; lean_object* v_keepAliveTimeout_2439_; lean_object* v_currentTimeout_2440_; lean_object* v_headerTimeout_2441_; lean_object* v_response_2442_; lean_object* v_respStream_2443_; uint8_t v_requiresData_2444_; lean_object* v_expectData_2445_; lean_object* v_val_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2468_; 
v_toFunctor_2436_ = lean_ctor_get(v_toApplicative_2434_, 0);
v_machine_2437_ = lean_ctor_get(v_state_2431_, 0);
lean_inc_ref(v_machine_2437_);
v_requestStream_2438_ = lean_ctor_get(v_state_2431_, 1);
lean_inc_ref(v_requestStream_2438_);
v_keepAliveTimeout_2439_ = lean_ctor_get(v_state_2431_, 2);
lean_inc(v_keepAliveTimeout_2439_);
v_currentTimeout_2440_ = lean_ctor_get(v_state_2431_, 3);
lean_inc(v_currentTimeout_2440_);
v_headerTimeout_2441_ = lean_ctor_get(v_state_2431_, 4);
lean_inc(v_headerTimeout_2441_);
v_response_2442_ = lean_ctor_get(v_state_2431_, 5);
lean_inc_ref(v_response_2442_);
v_respStream_2443_ = lean_ctor_get(v_state_2431_, 6);
lean_inc(v_respStream_2443_);
v_requiresData_2444_ = lean_ctor_get_uint8(v_state_2431_, sizeof(void*)*9);
v_expectData_2445_ = lean_ctor_get(v_state_2431_, 7);
lean_inc(v_expectData_2445_);
lean_dec_ref(v_state_2431_);
v_val_2446_ = lean_ctor_get(v_pendingHead_2435_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_pendingHead_2435_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2448_ = v_pendingHead_2435_;
v_isShared_2449_ = v_isSharedCheck_2468_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_val_2446_);
lean_dec(v_pendingHead_2435_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2468_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v_onRequest_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v_onRequest_2450_ = lean_ctor_get(v_inst_2427_, 1);
lean_inc_ref(v_onRequest_2450_);
lean_dec_ref(v_inst_2427_);
v___f_2451_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2452_ = lean_box(v_requiresData_2444_);
lean_inc_ref(v_response_2442_);
lean_inc_ref(v_requestStream_2438_);
v___f_2453_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2453_, 0, v_machine_2437_);
lean_closure_set(v___f_2453_, 1, v_requestStream_2438_);
lean_closure_set(v___f_2453_, 2, v_keepAliveTimeout_2439_);
lean_closure_set(v___f_2453_, 3, v_currentTimeout_2440_);
lean_closure_set(v___f_2453_, 4, v_headerTimeout_2441_);
lean_closure_set(v___f_2453_, 5, v_response_2442_);
lean_closure_set(v___f_2453_, 6, v_respStream_2443_);
lean_closure_set(v___f_2453_, 7, v___x_2452_);
lean_closure_set(v___f_2453_, 8, v_expectData_2445_);
v___x_2454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2454_, 0, v_val_2446_);
lean_ctor_set(v___x_2454_, 1, v_requestStream_2438_);
lean_ctor_set(v___x_2454_, 2, v_extensions_2429_);
v___x_2455_ = lean_apply_3(v_onRequest_2450_, v_handler_2428_, v___x_2454_, v_connectionContext_2430_);
v___x_2456_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2436_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2457_, 0, v_toFunctor_2436_);
lean_closure_set(v___f_2457_, 1, v_response_2442_);
lean_closure_set(v___f_2457_, 2, v___x_2456_);
lean_closure_set(v___f_2457_, 3, v___f_2453_);
v___x_2458_ = 0;
v___x_2459_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2459_, 0, lean_box(0));
lean_closure_set(v___x_2459_, 1, v___x_2455_);
v___x_2460_ = lean_io_as_task(v___x_2459_, v___x_2456_);
v___x_2461_ = 1;
v___x_2462_ = lean_task_bind(v___x_2460_, v___f_2451_, v___x_2456_, v___x_2461_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2462_);
v___x_2464_ = v___x_2448_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
v___x_2466_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2456_, v___x_2458_, v___x_2465_, v___f_2457_);
return v___x_2466_;
}
}
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v_pendingHead_2435_);
lean_dec_ref(v_connectionContext_2430_);
lean_dec(v_extensions_2429_);
lean_dec(v_handler_2428_);
lean_dec_ref(v_inst_2427_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_state_2431_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2427_ = stack[0].m_obj;
lean_object* v_handler_2428_ = stack[1].m_obj;
lean_object* v_extensions_2429_ = stack[2].m_obj;
lean_object* v_connectionContext_2430_ = stack[3].m_obj;
lean_object* v_state_2431_ = stack[4].m_obj;
lean_object* v_res_2471_;
v_res_2471_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2427_, v_handler_2428_, v_extensions_2429_, v_connectionContext_2430_, v_state_2431_);
stack->m_obj
 = v_res_2471_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2472_, lean_object* v_handler_2473_, lean_object* v_extensions_2474_, lean_object* v_connectionContext_2475_, lean_object* v_state_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2472_, v_handler_2473_, v_extensions_2474_, v_connectionContext_2475_, v_state_2476_);
return v_res_2478_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2479_, lean_object* v_inst_2480_, lean_object* v_handler_2481_, lean_object* v_extensions_2482_, lean_object* v_connectionContext_2483_, lean_object* v_state_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2480_, v_handler_2481_, v_extensions_2482_, v_connectionContext_2483_, v_state_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2480_ = stack[1].m_obj;
lean_object* v_handler_2481_ = stack[2].m_obj;
lean_object* v_extensions_2482_ = stack[3].m_obj;
lean_object* v_connectionContext_2483_ = stack[4].m_obj;
lean_object* v_state_2484_ = stack[5].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_box(0), v_inst_2480_, v_handler_2481_, v_extensions_2482_, v_connectionContext_2483_, v_state_2484_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2488_, lean_object* v_inst_2489_, lean_object* v_handler_2490_, lean_object* v_extensions_2491_, lean_object* v_connectionContext_2492_, lean_object* v_state_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2488_, v_inst_2489_, v_handler_2490_, v_extensions_2491_, v_connectionContext_2492_, v_state_2493_);
return v_res_2495_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2496_, lean_object* v_____r_2497_){
_start:
{
lean_object* v_writer_2499_; lean_object* v_reader_2500_; lean_object* v_config_2501_; lean_object* v_events_2502_; lean_object* v_error_2503_; lean_object* v_instant_2504_; uint8_t v_keepAlive_2505_; uint8_t v_forcedFlush_2506_; uint8_t v_pullBodyStalled_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2534_; 
v_writer_2499_ = lean_ctor_get(v_machine_2496_, 1);
v_reader_2500_ = lean_ctor_get(v_machine_2496_, 0);
v_config_2501_ = lean_ctor_get(v_machine_2496_, 2);
v_events_2502_ = lean_ctor_get(v_machine_2496_, 3);
v_error_2503_ = lean_ctor_get(v_machine_2496_, 4);
v_instant_2504_ = lean_ctor_get(v_machine_2496_, 5);
v_keepAlive_2505_ = lean_ctor_get_uint8(v_machine_2496_, sizeof(void*)*6);
v_forcedFlush_2506_ = lean_ctor_get_uint8(v_machine_2496_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2507_ = lean_ctor_get_uint8(v_machine_2496_, sizeof(void*)*6 + 2);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_machine_2496_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2509_ = v_machine_2496_;
v_isShared_2510_ = v_isSharedCheck_2534_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_instant_2504_);
lean_inc(v_error_2503_);
lean_inc(v_events_2502_);
lean_inc(v_config_2501_);
lean_inc(v_writer_2499_);
lean_inc(v_reader_2500_);
lean_dec(v_machine_2496_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2534_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_userData_2511_; lean_object* v_outputData_2512_; lean_object* v_state_2513_; lean_object* v_knownSize_2514_; lean_object* v_messageHead_2515_; uint8_t v_sentMessage_2516_; uint8_t v_omitBody_2517_; lean_object* v_userDataBytes_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2533_; 
v_userData_2511_ = lean_ctor_get(v_writer_2499_, 0);
v_outputData_2512_ = lean_ctor_get(v_writer_2499_, 1);
v_state_2513_ = lean_ctor_get(v_writer_2499_, 2);
v_knownSize_2514_ = lean_ctor_get(v_writer_2499_, 3);
v_messageHead_2515_ = lean_ctor_get(v_writer_2499_, 4);
v_sentMessage_2516_ = lean_ctor_get_uint8(v_writer_2499_, sizeof(void*)*6);
v_omitBody_2517_ = lean_ctor_get_uint8(v_writer_2499_, sizeof(void*)*6 + 2);
v_userDataBytes_2518_ = lean_ctor_get(v_writer_2499_, 5);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_writer_2499_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2520_ = v_writer_2499_;
v_isShared_2521_ = v_isSharedCheck_2533_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_userDataBytes_2518_);
lean_inc(v_messageHead_2515_);
lean_inc(v_knownSize_2514_);
lean_inc(v_state_2513_);
lean_inc(v_outputData_2512_);
lean_inc(v_userData_2511_);
lean_dec(v_writer_2499_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2533_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
uint8_t v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = 1;
if (v_isShared_2521_ == 0)
{
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_userData_2511_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_outputData_2512_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_state_2513_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_knownSize_2514_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_messageHead_2515_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v_userDataBytes_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*6, v_sentMessage_2516_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*6 + 2, v_omitBody_2517_);
v___x_2524_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*6 + 1, v___x_2522_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v___x_2524_);
v___x_2526_ = v___x_2509_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_reader_2500_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_config_2501_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_events_2502_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_error_2503_);
lean_ctor_set(v_reuseFailAlloc_2531_, 5, v_instant_2504_);
lean_ctor_set_uint8(v_reuseFailAlloc_2531_, sizeof(void*)*6, v_keepAlive_2505_);
lean_ctor_set_uint8(v_reuseFailAlloc_2531_, sizeof(void*)*6 + 1, v_forcedFlush_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2531_, sizeof(void*)*6 + 2, v_pullBodyStalled_2507_);
v___x_2526_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_machine_2496_ = stack[0].m_obj;
lean_object* v_____r_2497_ = stack[1].m_obj;
lean_object* v_res_2535_;
v_res_2535_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2496_, v_____r_2497_);
stack->m_obj
 = v_res_2535_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2536_, lean_object* v_____r_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2536_, v_____r_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2540_, lean_object* v_x2_2541_){
_start:
{
lean_object* v_data_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_data_2542_ = lean_ctor_get(v_x2_2541_, 0);
v___x_2543_ = lean_byte_array_size(v_data_2542_);
v___x_2544_ = lean_nat_add(v_x1_2540_, v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2545_, lean_object* v_x2_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2545_, v_x2_2546_);
lean_dec_ref(v_x2_2546_);
lean_dec(v_x1_2545_);
return v_res_2547_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2548_, lean_object* v_machine_2549_, lean_object* v_isClosed_2550_, lean_object* v___f_2551_, lean_object* v___f_2552_, lean_object* v_x_2553_){
_start:
{
lean_object* v___y_2556_; 
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v___f_2552_);
lean_dec_ref(v___f_2551_);
lean_dec_ref(v_isClosed_2550_);
lean_dec_ref(v_machine_2549_);
lean_dec(v_body_2548_);
v_a_2561_ = lean_ctor_get(v_x_2553_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_x_2553_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2563_ = v_x_2553_;
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v_x_2553_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2633_; 
v_a_2570_ = lean_ctor_get(v_x_2553_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_x_2553_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2572_ = v_x_2553_;
v_isShared_2573_ = v_isSharedCheck_2633_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v_x_2553_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2633_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
if (lean_obj_tag(v_a_2570_) == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
lean_dec_ref(v___f_2552_);
lean_dec_ref(v___f_2551_);
lean_dec_ref(v_isClosed_2550_);
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_body_2548_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_machine_2549_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
else
{
lean_object* v_val_2580_; 
lean_del_object(v___x_2572_);
v_val_2580_ = lean_ctor_get(v_a_2570_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v_a_2570_, 1);
if (lean_obj_tag(v_val_2580_) == 0)
{
lean_object* v___x_2581_; uint8_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec_ref(v___f_2552_);
lean_dec_ref(v_machine_2549_);
v___x_2581_ = lean_unsigned_to_nat(0u);
v___x_2582_ = 0;
v___x_2583_ = lean_apply_2(v_isClosed_2550_, v_body_2548_, lean_box(0));
v___x_2584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2581_, v___x_2582_, v___x_2583_, v___f_2551_);
return v___x_2584_;
}
else
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
lean_dec_ref(v___f_2551_);
lean_dec_ref(v_isClosed_2550_);
v_val_2585_ = lean_ctor_get(v_val_2580_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v_val_2580_, 1);
v___x_2586_ = lean_unsigned_to_nat(1u);
v___x_2587_ = lean_mk_empty_array_with_capacity(v___x_2586_);
v___x_2588_ = lean_array_push(v___x_2587_, v_val_2585_);
v___x_2589_ = lean_array_get_size(v___x_2588_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_nat_dec_eq(v___x_2589_, v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v_reader_2592_; lean_object* v_writer_2593_; lean_object* v_config_2594_; lean_object* v_events_2595_; lean_object* v_error_2596_; lean_object* v_instant_2597_; uint8_t v_keepAlive_2598_; uint8_t v_forcedFlush_2599_; uint8_t v_pullBodyStalled_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2632_; 
v_reader_2592_ = lean_ctor_get(v_machine_2549_, 0);
v_writer_2593_ = lean_ctor_get(v_machine_2549_, 1);
v_config_2594_ = lean_ctor_get(v_machine_2549_, 2);
v_events_2595_ = lean_ctor_get(v_machine_2549_, 3);
v_error_2596_ = lean_ctor_get(v_machine_2549_, 4);
v_instant_2597_ = lean_ctor_get(v_machine_2549_, 5);
v_keepAlive_2598_ = lean_ctor_get_uint8(v_machine_2549_, sizeof(void*)*6);
v_forcedFlush_2599_ = lean_ctor_get_uint8(v_machine_2549_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2600_ = lean_ctor_get_uint8(v_machine_2549_, sizeof(void*)*6 + 2);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_machine_2549_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2602_ = v_machine_2549_;
v_isShared_2603_ = v_isSharedCheck_2632_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_instant_2597_);
lean_inc(v_error_2596_);
lean_inc(v_events_2595_);
lean_inc(v_config_2594_);
lean_inc(v_writer_2593_);
lean_inc(v_reader_2592_);
lean_dec(v_machine_2549_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2632_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___y_2605_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_2628_ = lean_nat_dec_lt(v___x_2590_, v___x_2589_);
if (v___x_2628_ == 0)
{
lean_dec_ref(v___f_2552_);
v___y_2605_ = v___x_2590_;
goto v___jp_2604_;
}
else
{
size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((size_t)0ULL);
v___x_2630_ = lean_usize_of_nat(v___x_2589_);
lean_inc_ref(v___x_2588_);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2627_, v___f_2552_, v___x_2588_, v___x_2629_, v___x_2630_, v___x_2590_);
v___y_2605_ = v___x_2631_;
goto v___jp_2604_;
}
v___jp_2604_:
{
lean_object* v_userData_2606_; lean_object* v_outputData_2607_; lean_object* v_state_2608_; lean_object* v_knownSize_2609_; lean_object* v_messageHead_2610_; uint8_t v_sentMessage_2611_; uint8_t v_userClosedBody_2612_; uint8_t v_omitBody_2613_; lean_object* v_userDataBytes_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2626_; 
v_userData_2606_ = lean_ctor_get(v_writer_2593_, 0);
v_outputData_2607_ = lean_ctor_get(v_writer_2593_, 1);
v_state_2608_ = lean_ctor_get(v_writer_2593_, 2);
v_knownSize_2609_ = lean_ctor_get(v_writer_2593_, 3);
v_messageHead_2610_ = lean_ctor_get(v_writer_2593_, 4);
v_sentMessage_2611_ = lean_ctor_get_uint8(v_writer_2593_, sizeof(void*)*6);
v_userClosedBody_2612_ = lean_ctor_get_uint8(v_writer_2593_, sizeof(void*)*6 + 1);
v_omitBody_2613_ = lean_ctor_get_uint8(v_writer_2593_, sizeof(void*)*6 + 2);
v_userDataBytes_2614_ = lean_ctor_get(v_writer_2593_, 5);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_writer_2593_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2616_ = v_writer_2593_;
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_userDataBytes_2614_);
lean_inc(v_messageHead_2610_);
lean_inc(v_knownSize_2609_);
lean_inc(v_state_2608_);
lean_inc(v_outputData_2607_);
lean_inc(v_userData_2606_);
lean_dec(v_writer_2593_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = l_Array_append___redArg(v_userData_2606_, v___x_2588_);
lean_dec_ref(v___x_2588_);
v___x_2619_ = lean_nat_add(v_userDataBytes_2614_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec(v_userDataBytes_2614_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 5, v___x_2619_);
lean_ctor_set(v___x_2616_, 0, v___x_2618_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_outputData_2607_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_state_2608_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_knownSize_2609_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_messageHead_2610_);
lean_ctor_set(v_reuseFailAlloc_2625_, 5, v___x_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*6, v_sentMessage_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*6 + 1, v_userClosedBody_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*6 + 2, v_omitBody_2613_);
v___x_2621_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2621_);
v___x_2623_ = v___x_2602_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_reader_2592_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_config_2594_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_events_2595_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_error_2596_);
lean_ctor_set(v_reuseFailAlloc_2624_, 5, v_instant_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2624_, sizeof(void*)*6, v_keepAlive_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2624_, sizeof(void*)*6 + 1, v_forcedFlush_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2624_, sizeof(void*)*6 + 2, v_pullBodyStalled_2600_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
v___y_2556_ = v___x_2623_;
goto v___jp_2555_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2588_);
lean_dec_ref(v___f_2552_);
v___y_2556_ = v_machine_2549_;
goto v___jp_2555_;
}
}
}
}
}
v___jp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_body_2548_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_2548_ = stack[0].m_obj;
lean_object* v_machine_2549_ = stack[1].m_obj;
lean_object* v_isClosed_2550_ = stack[2].m_obj;
lean_object* v___f_2551_ = stack[3].m_obj;
lean_object* v___f_2552_ = stack[4].m_obj;
lean_object* v_x_2553_ = stack[5].m_obj;
lean_object* v_res_2634_;
v_res_2634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2548_, v_machine_2549_, v_isClosed_2550_, v___f_2551_, v___f_2552_, v_x_2553_);
stack->m_obj
 = v_res_2634_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2635_, lean_object* v_machine_2636_, lean_object* v_isClosed_2637_, lean_object* v___f_2638_, lean_object* v___f_2639_, lean_object* v_x_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2635_, v_machine_2636_, v_isClosed_2637_, v___f_2638_, v___f_2639_, v_x_2640_);
return v_res_2642_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2644_, lean_object* v_machine_2645_, lean_object* v_body_2646_){
_start:
{
lean_object* v_close_2648_; lean_object* v_isClosed_2649_; lean_object* v_tryRecv_2650_; lean_object* v___f_2651_; lean_object* v___f_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___f_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_close_2648_ = lean_ctor_get(v_inst_2644_, 1);
lean_inc_ref(v_close_2648_);
v_isClosed_2649_ = lean_ctor_get(v_inst_2644_, 2);
lean_inc_ref(v_isClosed_2649_);
v_tryRecv_2650_ = lean_ctor_get(v_inst_2644_, 4);
lean_inc_ref(v_tryRecv_2650_);
lean_dec_ref(v_inst_2644_);
lean_inc_ref(v_machine_2645_);
v___f_2651_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2651_, 0, v_machine_2645_);
lean_inc_ref(v___f_2651_);
v___f_2652_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2652_, 0, v___f_2651_);
lean_inc_n(v_body_2646_, 2);
v___f_2653_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2653_, 0, v_close_2648_);
lean_closure_set(v___f_2653_, 1, v_body_2646_);
lean_closure_set(v___f_2653_, 2, v___f_2652_);
lean_closure_set(v___f_2653_, 3, v___f_2651_);
v___f_2654_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2655_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2655_, 0, v_body_2646_);
lean_closure_set(v___f_2655_, 1, v_machine_2645_);
lean_closure_set(v___f_2655_, 2, v_isClosed_2649_);
lean_closure_set(v___f_2655_, 3, v___f_2653_);
lean_closure_set(v___f_2655_, 4, v___f_2654_);
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = 0;
v___x_2658_ = lean_apply_2(v_tryRecv_2650_, v_body_2646_, lean_box(0));
v___x_2659_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2656_, v___x_2657_, v___x_2658_, v___f_2655_);
return v___x_2659_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2644_ = stack[0].m_obj;
lean_object* v_machine_2645_ = stack[1].m_obj;
lean_object* v_body_2646_ = stack[2].m_obj;
lean_object* v_res_2660_;
v_res_2660_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2644_, v_machine_2645_, v_body_2646_);
stack->m_obj
 = v_res_2660_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2661_, lean_object* v_machine_2662_, lean_object* v_body_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2661_, v_machine_2662_, v_body_2663_);
return v_res_2665_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2666_, lean_object* v_inst_2667_, lean_object* v_machine_2668_, lean_object* v_body_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2667_, v_machine_2668_, v_body_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2667_ = stack[1].m_obj;
lean_object* v_machine_2668_ = stack[2].m_obj;
lean_object* v_body_2669_ = stack[3].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_box(0), v_inst_2667_, v_machine_2668_, v_body_2669_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2673_, lean_object* v_inst_2674_, lean_object* v_machine_2675_, lean_object* v_body_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2673_, v_inst_2674_, v_machine_2675_, v_body_2676_);
return v_res_2678_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2685_, lean_object* v_____r_2686_, lean_object* v_st_2687_){
_start:
{
lean_object* v_machine_2689_; lean_object* v_requestStream_2690_; lean_object* v_keepAliveTimeout_2691_; lean_object* v_currentTimeout_2692_; lean_object* v_headerTimeout_2693_; lean_object* v_response_2694_; lean_object* v_respStream_2695_; uint8_t v_requiresData_2696_; lean_object* v_expectData_2697_; uint8_t v_handlerDispatched_2698_; lean_object* v_pendingHead_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2781_; 
v_machine_2689_ = lean_ctor_get(v_st_2687_, 0);
v_requestStream_2690_ = lean_ctor_get(v_st_2687_, 1);
v_keepAliveTimeout_2691_ = lean_ctor_get(v_st_2687_, 2);
v_currentTimeout_2692_ = lean_ctor_get(v_st_2687_, 3);
v_headerTimeout_2693_ = lean_ctor_get(v_st_2687_, 4);
v_response_2694_ = lean_ctor_get(v_st_2687_, 5);
v_respStream_2695_ = lean_ctor_get(v_st_2687_, 6);
v_requiresData_2696_ = lean_ctor_get_uint8(v_st_2687_, sizeof(void*)*9);
v_expectData_2697_ = lean_ctor_get(v_st_2687_, 7);
v_handlerDispatched_2698_ = lean_ctor_get_uint8(v_st_2687_, sizeof(void*)*9 + 1);
v_pendingHead_2699_ = lean_ctor_get(v_st_2687_, 8);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_st_2687_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2701_ = v_st_2687_;
v_isShared_2702_ = v_isSharedCheck_2781_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_pendingHead_2699_);
lean_inc(v_expectData_2697_);
lean_inc(v_respStream_2695_);
lean_inc(v_response_2694_);
lean_inc(v_headerTimeout_2693_);
lean_inc(v_currentTimeout_2692_);
lean_inc(v_keepAliveTimeout_2691_);
lean_inc(v_requestStream_2690_);
lean_inc(v_machine_2689_);
lean_dec(v_st_2687_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2781_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___y_2704_; lean_object* v_reader_2713_; lean_object* v_state_2714_; 
v_reader_2713_ = lean_ctor_get(v_machine_2689_, 0);
lean_inc_ref(v_reader_2713_);
v_state_2714_ = lean_ctor_get(v_reader_2713_, 0);
lean_inc(v_state_2714_);
if (lean_obj_tag(v_state_2714_) == 6)
{
lean_dec_ref(v_reader_2713_);
lean_dec_ref(v_val_2685_);
v___y_2704_ = v_machine_2689_;
goto v___jp_2703_;
}
else
{
if (lean_obj_tag(v_state_2714_) == 7)
{
lean_dec_ref_known(v_state_2714_, 1);
lean_dec_ref(v_reader_2713_);
lean_dec_ref(v_val_2685_);
v___y_2704_ = v_machine_2689_;
goto v___jp_2703_;
}
else
{
lean_object* v_input_2715_; lean_object* v_writer_2716_; lean_object* v_config_2717_; lean_object* v_events_2718_; lean_object* v_error_2719_; lean_object* v_instant_2720_; uint8_t v_keepAlive_2721_; uint8_t v_forcedFlush_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2779_; 
v_input_2715_ = lean_ctor_get(v_reader_2713_, 1);
lean_inc_ref(v_input_2715_);
v_writer_2716_ = lean_ctor_get(v_machine_2689_, 1);
v_config_2717_ = lean_ctor_get(v_machine_2689_, 2);
v_events_2718_ = lean_ctor_get(v_machine_2689_, 3);
v_error_2719_ = lean_ctor_get(v_machine_2689_, 4);
v_instant_2720_ = lean_ctor_get(v_machine_2689_, 5);
v_keepAlive_2721_ = lean_ctor_get_uint8(v_machine_2689_, sizeof(void*)*6);
v_forcedFlush_2722_ = lean_ctor_get_uint8(v_machine_2689_, sizeof(void*)*6 + 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_machine_2689_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_machine_2689_, 0);
lean_dec(v_unused_2780_);
v___x_2724_ = v_machine_2689_;
v_isShared_2725_ = v_isSharedCheck_2779_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_instant_2720_);
lean_inc(v_error_2719_);
lean_inc(v_events_2718_);
lean_inc(v_config_2717_);
lean_inc(v_writer_2716_);
lean_dec(v_machine_2689_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2779_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_messageHead_2726_; lean_object* v_messageCount_2727_; lean_object* v_bodyBytesRead_2728_; lean_object* v_headerBytesRead_2729_; uint8_t v_noMoreInput_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2776_; 
v_messageHead_2726_ = lean_ctor_get(v_reader_2713_, 2);
v_messageCount_2727_ = lean_ctor_get(v_reader_2713_, 3);
v_bodyBytesRead_2728_ = lean_ctor_get(v_reader_2713_, 4);
v_headerBytesRead_2729_ = lean_ctor_get(v_reader_2713_, 5);
v_noMoreInput_2730_ = lean_ctor_get_uint8(v_reader_2713_, sizeof(void*)*6);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_reader_2713_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; lean_object* v_unused_2778_; 
v_unused_2777_ = lean_ctor_get(v_reader_2713_, 1);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_reader_2713_, 0);
lean_dec(v_unused_2778_);
v___x_2732_ = v_reader_2713_;
v_isShared_2733_ = v_isSharedCheck_2776_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_headerBytesRead_2729_);
lean_inc(v_bodyBytesRead_2728_);
lean_inc(v_messageCount_2727_);
lean_inc(v_messageHead_2726_);
lean_dec(v_reader_2713_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2776_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_array_2734_; lean_object* v_idx_2735_; uint8_t v___x_2736_; lean_object* v___y_2738_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_array_2734_ = lean_ctor_get(v_input_2715_, 0);
lean_inc_ref(v_array_2734_);
v_idx_2735_ = lean_ctor_get(v_input_2715_, 1);
lean_inc(v_idx_2735_);
lean_dec_ref(v_input_2715_);
v___x_2736_ = 0;
v___x_2767_ = lean_byte_array_size(v_array_2734_);
v___x_2768_ = lean_nat_dec_le(v___x_2767_, v_idx_2735_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2769_ = l_ByteArray_extract(v_array_2734_, v_idx_2735_, v___x_2767_);
lean_dec_ref(v_array_2734_);
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = lean_byte_array_size(v___x_2769_);
v___x_2772_ = lean_byte_array_size(v_val_2685_);
v___x_2773_ = lean_byte_array_copy_slice(v_val_2685_, v___x_2770_, v___x_2769_, v___x_2771_, v___x_2772_, v___x_2768_);
lean_dec_ref(v_val_2685_);
v___x_2774_ = l_ByteArray_mkIterator(v___x_2773_);
v___y_2738_ = v___x_2774_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2775_; 
lean_dec(v_idx_2735_);
lean_dec_ref(v_array_2734_);
v___x_2775_ = l_ByteArray_mkIterator(v_val_2685_);
v___y_2738_ = v___x_2775_;
goto v___jp_2737_;
}
v___jp_2737_:
{
lean_object* v_maxHeaderBytes_2739_; lean_object* v_maxStartLineLength_2740_; lean_object* v_maxChunkLineLength_2741_; lean_object* v_maxBodySize_2742_; lean_object* v_array_2743_; lean_object* v_idx_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_maxHeaderBytes_2739_ = lean_ctor_get(v_config_2717_, 2);
v_maxStartLineLength_2740_ = lean_ctor_get(v_config_2717_, 5);
v_maxChunkLineLength_2741_ = lean_ctor_get(v_config_2717_, 13);
v_maxBodySize_2742_ = lean_ctor_get(v_config_2717_, 15);
v_array_2743_ = lean_ctor_get(v___y_2738_, 0);
v_idx_2744_ = lean_ctor_get(v___y_2738_, 1);
v___x_2745_ = lean_nat_add(v_maxBodySize_2742_, v_maxHeaderBytes_2739_);
v___x_2746_ = lean_nat_add(v___x_2745_, v_maxStartLineLength_2740_);
lean_dec(v___x_2745_);
v___x_2747_ = lean_nat_add(v___x_2746_, v_maxChunkLineLength_2741_);
lean_dec(v___x_2746_);
v___x_2748_ = lean_byte_array_size(v_array_2743_);
v___x_2749_ = lean_nat_sub(v___x_2748_, v_idx_2744_);
v___x_2750_ = lean_nat_dec_lt(v___x_2747_, v___x_2749_);
lean_dec(v___x_2749_);
lean_dec(v___x_2747_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2752_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v___y_2738_);
v___x_2752_ = v___x_2732_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_state_2714_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___y_2738_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_messageHead_2726_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_messageCount_2727_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_bodyBytesRead_2728_);
lean_ctor_set(v_reuseFailAlloc_2756_, 5, v_headerBytesRead_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*6, v_noMoreInput_2730_);
v___x_2752_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v_machine_2754_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2752_);
v_machine_2754_ = v___x_2724_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_writer_2716_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_config_2717_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_events_2718_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_error_2719_);
lean_ctor_set(v_reuseFailAlloc_2755_, 5, v_instant_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*6, v_keepAlive_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*6 + 1, v_forcedFlush_2722_);
v_machine_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_ctor_set_uint8(v_machine_2754_, sizeof(void*)*6 + 2, v___x_2736_);
v___y_2704_ = v_machine_2754_;
goto v___jp_2703_;
}
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
lean_dec(v_error_2719_);
lean_dec(v_state_2714_);
v___x_2757_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2758_ = lean_array_push(v_events_2718_, v___x_2757_);
v___x_2759_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v___y_2738_);
lean_ctor_set(v___x_2732_, 0, v___x_2759_);
v___x_2761_ = v___x_2732_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___y_2738_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_messageHead_2726_);
lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_messageCount_2727_);
lean_ctor_set(v_reuseFailAlloc_2766_, 4, v_bodyBytesRead_2728_);
lean_ctor_set(v_reuseFailAlloc_2766_, 5, v_headerBytesRead_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2766_, sizeof(void*)*6, v_noMoreInput_2730_);
v___x_2761_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 4, v___x_2762_);
lean_ctor_set(v___x_2724_, 3, v___x_2758_);
lean_ctor_set(v___x_2724_, 0, v___x_2761_);
v___x_2764_ = v___x_2724_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_writer_2716_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_config_2717_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2765_, 5, v_instant_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*6, v_keepAlive_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*6 + 1, v_forcedFlush_2722_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*6 + 2, v___x_2736_);
v___y_2704_ = v___x_2764_;
goto v___jp_2703_;
}
}
}
}
}
}
}
}
v___jp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___y_2704_);
v___x_2706_ = v___x_2701_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___y_2704_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_requestStream_2690_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_keepAliveTimeout_2691_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_currentTimeout_2692_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v_headerTimeout_2693_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_response_2694_);
lean_ctor_set(v_reuseFailAlloc_2712_, 6, v_respStream_2695_);
lean_ctor_set(v_reuseFailAlloc_2712_, 7, v_expectData_2697_);
lean_ctor_set(v_reuseFailAlloc_2712_, 8, v_pendingHead_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2712_, sizeof(void*)*9, v_requiresData_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2712_, sizeof(void*)*9 + 1, v_handlerDispatched_2698_);
v___x_2706_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2707_ = 0;
v___x_2708_ = lean_box(v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2685_ = stack[0].m_obj;
lean_object* v_____r_2686_ = stack[1].m_obj;
lean_object* v_st_2687_ = stack[2].m_obj;
lean_object* v_res_2782_;
v_res_2782_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2685_, v_____r_2686_, v_st_2687_);
stack->m_obj
 = v_res_2782_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2783_, lean_object* v_____r_2784_, lean_object* v_st_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2783_, v_____r_2784_, v_st_2785_);
return v_res_2787_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2788_, lean_object* v_machine_2789_, lean_object* v_requestStream_2790_, lean_object* v_currentTimeout_2791_, lean_object* v_response_2792_, lean_object* v_respStream_2793_, uint8_t v_requiresData_2794_, lean_object* v_expectData_2795_, uint8_t v_handlerDispatched_2796_, lean_object* v_pendingHead_2797_, lean_object* v___f_2798_, lean_object* v_x_2799_){
_start:
{
if (lean_obj_tag(v_x_2799_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___f_2798_);
lean_dec(v_pendingHead_2797_);
lean_dec(v_expectData_2795_);
lean_dec(v_respStream_2793_);
lean_dec_ref(v_response_2792_);
lean_dec(v_currentTimeout_2791_);
lean_dec_ref(v_requestStream_2790_);
lean_dec_ref(v_machine_2789_);
v_a_2801_ = lean_ctor_get(v_x_2799_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2803_ = v_x_2799_;
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v_x_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v_headerTimeout_2811_; lean_object* v_second_2812_; lean_object* v_nano_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v_second_2817_; lean_object* v_nano_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_nanos_2822_; lean_object* v___x_2823_; lean_object* v_nanos_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2810_ = lean_ctor_get(v_x_2799_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v_x_2799_, 1);
v_headerTimeout_2811_ = lean_ctor_get(v_config_2788_, 6);
v_second_2812_ = lean_ctor_get(v_a_2810_, 0);
lean_inc(v_second_2812_);
v_nano_2813_ = lean_ctor_get(v_a_2810_, 1);
lean_inc(v_nano_2813_);
lean_dec(v_a_2810_);
v___x_2814_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2815_ = lean_int_mul(v_headerTimeout_2811_, v___x_2814_);
v___x_2816_ = l_Std_Time_Duration_ofNanoseconds(v___x_2815_);
lean_dec(v___x_2815_);
v_second_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_second_2817_);
v_nano_2818_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_nano_2818_);
lean_dec_ref(v___x_2816_);
v___x_2819_ = lean_box(0);
v___x_2820_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2821_ = lean_int_mul(v_second_2812_, v___x_2820_);
lean_dec(v_second_2812_);
v_nanos_2822_ = lean_int_add(v___x_2821_, v_nano_2813_);
lean_dec(v_nano_2813_);
lean_dec(v___x_2821_);
v___x_2823_ = lean_int_mul(v_second_2817_, v___x_2820_);
lean_dec(v_second_2817_);
v_nanos_2824_ = lean_int_add(v___x_2823_, v_nano_2818_);
lean_dec(v_nano_2818_);
lean_dec(v___x_2823_);
v___x_2825_ = lean_int_add(v_nanos_2822_, v_nanos_2824_);
lean_dec(v_nanos_2824_);
lean_dec(v_nanos_2822_);
v___x_2826_ = l_Std_Time_Duration_ofNanoseconds(v___x_2825_);
lean_dec(v___x_2825_);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2828_, 0, v_machine_2789_);
lean_ctor_set(v___x_2828_, 1, v_requestStream_2790_);
lean_ctor_set(v___x_2828_, 2, v___x_2819_);
lean_ctor_set(v___x_2828_, 3, v_currentTimeout_2791_);
lean_ctor_set(v___x_2828_, 4, v___x_2827_);
lean_ctor_set(v___x_2828_, 5, v_response_2792_);
lean_ctor_set(v___x_2828_, 6, v_respStream_2793_);
lean_ctor_set(v___x_2828_, 7, v_expectData_2795_);
lean_ctor_set(v___x_2828_, 8, v_pendingHead_2797_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*9, v_requiresData_2794_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*9 + 1, v_handlerDispatched_2796_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_apply_3(v___f_2798_, v___x_2829_, v___x_2828_, lean_box(0));
return v___x_2830_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_2788_ = stack[0].m_obj;
lean_object* v_machine_2789_ = stack[1].m_obj;
lean_object* v_requestStream_2790_ = stack[2].m_obj;
lean_object* v_currentTimeout_2791_ = stack[3].m_obj;
lean_object* v_response_2792_ = stack[4].m_obj;
lean_object* v_respStream_2793_ = stack[5].m_obj;
uint8_t v_requiresData_2794_ = stack[6].m_num;
lean_object* v_expectData_2795_ = stack[7].m_obj;
uint8_t v_handlerDispatched_2796_ = stack[8].m_num;
lean_object* v_pendingHead_2797_ = stack[9].m_obj;
lean_object* v___f_2798_ = stack[10].m_obj;
lean_object* v_x_2799_ = stack[11].m_obj;
lean_object* v_res_2831_;
v_res_2831_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2788_, v_machine_2789_, v_requestStream_2790_, v_currentTimeout_2791_, v_response_2792_, v_respStream_2793_, v_requiresData_2794_, v_expectData_2795_, v_handlerDispatched_2796_, v_pendingHead_2797_, v___f_2798_, v_x_2799_);
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2832_, lean_object* v_machine_2833_, lean_object* v_requestStream_2834_, lean_object* v_currentTimeout_2835_, lean_object* v_response_2836_, lean_object* v_respStream_2837_, lean_object* v_requiresData_2838_, lean_object* v_expectData_2839_, lean_object* v_handlerDispatched_2840_, lean_object* v_pendingHead_2841_, lean_object* v___f_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_requiresData_boxed_2845_; uint8_t v_handlerDispatched_boxed_2846_; lean_object* v_res_2847_; 
v_requiresData_boxed_2845_ = lean_unbox(v_requiresData_2838_);
v_handlerDispatched_boxed_2846_ = lean_unbox(v_handlerDispatched_2840_);
v_res_2847_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2832_, v_machine_2833_, v_requestStream_2834_, v_currentTimeout_2835_, v_response_2836_, v_respStream_2837_, v_requiresData_boxed_2845_, v_expectData_2839_, v_handlerDispatched_boxed_2846_, v_pendingHead_2841_, v___f_2842_, v_x_2843_);
lean_dec_ref(v_config_2832_);
return v_res_2847_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2848_, lean_object* v_requestStream_2849_, lean_object* v_keepAliveTimeout_2850_, lean_object* v_currentTimeout_2851_, lean_object* v_headerTimeout_2852_, lean_object* v_response_2853_, uint8_t v_requiresData_2854_, lean_object* v_expectData_2855_, uint8_t v_handlerDispatched_2856_, lean_object* v_pendingHead_2857_, lean_object* v_____r_2858_){
_start:
{
lean_object* v_writer_2860_; lean_object* v_reader_2861_; lean_object* v_config_2862_; lean_object* v_events_2863_; lean_object* v_error_2864_; lean_object* v_instant_2865_; uint8_t v_keepAlive_2866_; uint8_t v_forcedFlush_2867_; uint8_t v_pullBodyStalled_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2898_; 
v_writer_2860_ = lean_ctor_get(v_machine_2848_, 1);
v_reader_2861_ = lean_ctor_get(v_machine_2848_, 0);
v_config_2862_ = lean_ctor_get(v_machine_2848_, 2);
v_events_2863_ = lean_ctor_get(v_machine_2848_, 3);
v_error_2864_ = lean_ctor_get(v_machine_2848_, 4);
v_instant_2865_ = lean_ctor_get(v_machine_2848_, 5);
v_keepAlive_2866_ = lean_ctor_get_uint8(v_machine_2848_, sizeof(void*)*6);
v_forcedFlush_2867_ = lean_ctor_get_uint8(v_machine_2848_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2868_ = lean_ctor_get_uint8(v_machine_2848_, sizeof(void*)*6 + 2);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_machine_2848_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2870_ = v_machine_2848_;
v_isShared_2871_ = v_isSharedCheck_2898_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_instant_2865_);
lean_inc(v_error_2864_);
lean_inc(v_events_2863_);
lean_inc(v_config_2862_);
lean_inc(v_writer_2860_);
lean_inc(v_reader_2861_);
lean_dec(v_machine_2848_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2898_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_userData_2872_; lean_object* v_outputData_2873_; lean_object* v_state_2874_; lean_object* v_knownSize_2875_; lean_object* v_messageHead_2876_; uint8_t v_sentMessage_2877_; uint8_t v_omitBody_2878_; lean_object* v_userDataBytes_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2897_; 
v_userData_2872_ = lean_ctor_get(v_writer_2860_, 0);
v_outputData_2873_ = lean_ctor_get(v_writer_2860_, 1);
v_state_2874_ = lean_ctor_get(v_writer_2860_, 2);
v_knownSize_2875_ = lean_ctor_get(v_writer_2860_, 3);
v_messageHead_2876_ = lean_ctor_get(v_writer_2860_, 4);
v_sentMessage_2877_ = lean_ctor_get_uint8(v_writer_2860_, sizeof(void*)*6);
v_omitBody_2878_ = lean_ctor_get_uint8(v_writer_2860_, sizeof(void*)*6 + 2);
v_userDataBytes_2879_ = lean_ctor_get(v_writer_2860_, 5);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_writer_2860_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2881_ = v_writer_2860_;
v_isShared_2882_ = v_isSharedCheck_2897_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_userDataBytes_2879_);
lean_inc(v_messageHead_2876_);
lean_inc(v_knownSize_2875_);
lean_inc(v_state_2874_);
lean_inc(v_outputData_2873_);
lean_inc(v_userData_2872_);
lean_dec(v_writer_2860_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2897_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = 1;
if (v_isShared_2882_ == 0)
{
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_userData_2872_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_outputData_2873_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_state_2874_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_knownSize_2875_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_messageHead_2876_);
lean_ctor_set(v_reuseFailAlloc_2896_, 5, v_userDataBytes_2879_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*6, v_sentMessage_2877_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*6 + 2, v_omitBody_2878_);
v___x_2885_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2887_; 
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*6 + 1, v___x_2883_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2885_);
v___x_2887_ = v___x_2870_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_reader_2861_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_config_2862_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_events_2863_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_error_2864_);
lean_ctor_set(v_reuseFailAlloc_2895_, 5, v_instant_2865_);
lean_ctor_set_uint8(v_reuseFailAlloc_2895_, sizeof(void*)*6, v_keepAlive_2866_);
lean_ctor_set_uint8(v_reuseFailAlloc_2895_, sizeof(void*)*6 + 1, v_forcedFlush_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2895_, sizeof(void*)*6 + 2, v_pullBodyStalled_2868_);
v___x_2887_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v_requestStream_2849_);
lean_ctor_set(v___x_2889_, 2, v_keepAliveTimeout_2850_);
lean_ctor_set(v___x_2889_, 3, v_currentTimeout_2851_);
lean_ctor_set(v___x_2889_, 4, v_headerTimeout_2852_);
lean_ctor_set(v___x_2889_, 5, v_response_2853_);
lean_ctor_set(v___x_2889_, 6, v___x_2888_);
lean_ctor_set(v___x_2889_, 7, v_expectData_2855_);
lean_ctor_set(v___x_2889_, 8, v_pendingHead_2857_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*9, v_requiresData_2854_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*9 + 1, v_handlerDispatched_2856_);
v___x_2890_ = 0;
v___x_2891_ = lean_box(v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2889_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_machine_2848_ = stack[0].m_obj;
lean_object* v_requestStream_2849_ = stack[1].m_obj;
lean_object* v_keepAliveTimeout_2850_ = stack[2].m_obj;
lean_object* v_currentTimeout_2851_ = stack[3].m_obj;
lean_object* v_headerTimeout_2852_ = stack[4].m_obj;
lean_object* v_response_2853_ = stack[5].m_obj;
uint8_t v_requiresData_2854_ = stack[6].m_num;
lean_object* v_expectData_2855_ = stack[7].m_obj;
uint8_t v_handlerDispatched_2856_ = stack[8].m_num;
lean_object* v_pendingHead_2857_ = stack[9].m_obj;
lean_object* v_____r_2858_ = stack[10].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2848_, v_requestStream_2849_, v_keepAliveTimeout_2850_, v_currentTimeout_2851_, v_headerTimeout_2852_, v_response_2853_, v_requiresData_2854_, v_expectData_2855_, v_handlerDispatched_2856_, v_pendingHead_2857_, v_____r_2858_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2900_, lean_object* v_requestStream_2901_, lean_object* v_keepAliveTimeout_2902_, lean_object* v_currentTimeout_2903_, lean_object* v_headerTimeout_2904_, lean_object* v_response_2905_, lean_object* v_requiresData_2906_, lean_object* v_expectData_2907_, lean_object* v_handlerDispatched_2908_, lean_object* v_pendingHead_2909_, lean_object* v_____r_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_requiresData_boxed_2912_; uint8_t v_handlerDispatched_boxed_2913_; lean_object* v_res_2914_; 
v_requiresData_boxed_2912_ = lean_unbox(v_requiresData_2906_);
v_handlerDispatched_boxed_2913_ = lean_unbox(v_handlerDispatched_2908_);
v_res_2914_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2900_, v_requestStream_2901_, v_keepAliveTimeout_2902_, v_currentTimeout_2903_, v_headerTimeout_2904_, v_response_2905_, v_requiresData_boxed_2912_, v_expectData_2907_, v_handlerDispatched_boxed_2913_, v_pendingHead_2909_, v_____r_2910_);
return v_res_2914_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2915_, lean_object* v_x_2916_){
_start:
{
if (lean_obj_tag(v_x_2916_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v___f_2915_);
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
lean_object* v_a_2927_; lean_object* v___x_2928_; 
v_a_2927_ = lean_ctor_get(v_x_2916_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v_x_2916_, 1);
v___x_2928_ = lean_apply_2(v___f_2915_, v_a_2927_, lean_box(0));
return v___x_2928_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2915_ = stack[0].m_obj;
lean_object* v_x_2916_ = stack[1].m_obj;
lean_object* v_res_2929_;
v_res_2929_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2915_, v_x_2916_);
stack->m_obj
 = v_res_2929_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2930_, v_x_2931_);
return v_res_2933_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2934_, lean_object* v_val_2935_, lean_object* v___f_2936_, lean_object* v___f_2937_, lean_object* v_x_2938_){
_start:
{
if (lean_obj_tag(v_x_2938_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v___f_2937_);
lean_dec_ref(v___f_2936_);
lean_dec(v_val_2935_);
lean_dec_ref(v_close_2934_);
v_a_2940_ = lean_ctor_get(v_x_2938_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_x_2938_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2942_ = v_x_2938_;
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v_x_2938_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
return v___x_2946_;
}
}
}
else
{
lean_object* v_a_2949_; uint8_t v___x_2950_; 
v_a_2949_ = lean_ctor_get(v_x_2938_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v_x_2938_, 1);
v___x_2950_ = lean_unbox(v_a_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v___f_2937_);
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_apply_2(v_close_2934_, v_val_2935_, lean_box(0));
v___x_2953_ = lean_unbox(v_a_2949_);
lean_dec(v_a_2949_);
v___x_2954_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2951_, v___x_2953_, v___x_2952_, v___f_2936_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v_a_2949_);
lean_dec_ref(v___f_2936_);
lean_dec(v_val_2935_);
lean_dec_ref(v_close_2934_);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_apply_2(v___f_2937_, v___x_2955_, lean_box(0));
return v___x_2956_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_close_2934_ = stack[0].m_obj;
lean_object* v_val_2935_ = stack[1].m_obj;
lean_object* v___f_2936_ = stack[2].m_obj;
lean_object* v___f_2937_ = stack[3].m_obj;
lean_object* v_x_2938_ = stack[4].m_obj;
lean_object* v_res_2957_;
v_res_2957_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2934_, v_val_2935_, v___f_2936_, v___f_2937_, v_x_2938_);
stack->m_obj
 = v_res_2957_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2958_, lean_object* v_val_2959_, lean_object* v___f_2960_, lean_object* v___f_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2958_, v_val_2959_, v___f_2960_, v___f_2961_, v_x_2962_);
return v_res_2964_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_2965_, lean_object* v_handler_2966_, lean_object* v_x_2967_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_object* v_a_2969_; lean_object* v_onFailure_2970_; lean_object* v___x_2971_; 
v_a_2969_ = lean_ctor_get(v_x_2967_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v_x_2967_, 1);
v_onFailure_2970_ = lean_ctor_get(v_inst_2965_, 2);
lean_inc_ref(v_onFailure_2970_);
lean_dec_ref(v_inst_2965_);
v___x_2971_ = lean_apply_3(v_onFailure_2970_, v_handler_2966_, v_a_2969_, lean_box(0));
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; 
lean_dec(v_handler_2966_);
lean_dec_ref(v_inst_2965_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_x_2967_);
return v___x_2972_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2965_ = stack[0].m_obj;
lean_object* v_handler_2966_ = stack[1].m_obj;
lean_object* v_x_2967_ = stack[2].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2965_, v_handler_2966_, v_x_2967_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_2974_, lean_object* v_handler_2975_, lean_object* v_x_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2974_, v_handler_2975_, v_x_2976_);
return v_res_2978_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_2979_, lean_object* v_____r_2980_){
_start:
{
uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2982_ = 0;
v___x_2983_ = lean_box(v___x_2982_);
v___x_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2984_, 0, v_st_2979_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_st_2979_ = stack[0].m_obj;
lean_object* v_____r_2980_ = stack[1].m_obj;
lean_object* v_res_2987_;
v_res_2987_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2979_, v_____r_2980_);
stack->m_obj
 = v_res_2987_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_2988_, lean_object* v_____r_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2988_, v_____r_2989_);
return v_res_2991_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2992_, lean_object* v___f_2993_, lean_object* v___f_2994_, lean_object* v_x_2995_){
_start:
{
if (lean_obj_tag(v_x_2995_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___f_2994_);
lean_dec_ref(v___f_2993_);
lean_dec_ref(v_requestStream_2992_);
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
lean_object* v_a_3006_; uint8_t v___x_3007_; 
v_a_3006_ = lean_ctor_get(v_x_2995_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v_x_2995_, 1);
v___x_3007_ = lean_unbox(v_a_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v___f_2994_);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = l_Std_Http_Body_Stream_close(v_requestStream_2992_);
v___x_3010_ = lean_unbox(v_a_3006_);
lean_dec(v_a_3006_);
v___x_3011_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3008_, v___x_3010_, v___x_3009_, v___f_2993_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec(v_a_3006_);
lean_dec_ref(v___f_2993_);
lean_dec_ref(v_requestStream_2992_);
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_apply_2(v___f_2994_, v___x_3012_, lean_box(0));
return v___x_3013_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestStream_2992_ = stack[0].m_obj;
lean_object* v___f_2993_ = stack[1].m_obj;
lean_object* v___f_2994_ = stack[2].m_obj;
lean_object* v_x_2995_ = stack[3].m_obj;
lean_object* v_res_3014_;
v_res_3014_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2992_, v___f_2993_, v___f_2994_, v_x_2995_);
stack->m_obj
 = v_res_3014_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_3015_, lean_object* v___f_3016_, lean_object* v___f_3017_, lean_object* v_x_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_3015_, v___f_3016_, v___f_3017_, v_x_3018_);
return v_res_3020_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t v_final_3021_, lean_object* v___f_3022_, lean_object* v___f_3023_, lean_object* v_requestStream_3024_, lean_object* v___f_3025_, lean_object* v_x_3026_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v___f_3025_);
lean_dec_ref(v_requestStream_3024_);
lean_dec_ref(v___f_3023_);
lean_dec_ref(v___f_3022_);
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
lean_dec_ref_known(v_x_3026_, 1);
if (v_final_3021_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec_ref(v___f_3025_);
lean_dec_ref(v_requestStream_3024_);
lean_dec_ref(v___f_3023_);
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_apply_2(v___f_3022_, v___x_3037_, lean_box(0));
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_6684__overap_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v___f_3022_);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = 0;
v___x_3041_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3042_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3043_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3044_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3045_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3045_, 0, lean_box(0));
lean_closure_set(v___x_3045_, 1, lean_box(0));
lean_closure_set(v___x_3045_, 2, v___x_3041_);
lean_closure_set(v___x_3045_, 3, lean_box(0));
lean_closure_set(v___x_3045_, 4, lean_box(0));
lean_closure_set(v___x_3045_, 5, v___x_3044_);
lean_closure_set(v___x_3045_, 6, v___f_3023_);
v___x_6684__overap_3046_ = l_Std_Mutex_atomically___redArg(v___x_3041_, v___f_3042_, v___f_3043_, v_requestStream_3024_, v___x_3045_);
v___x_3047_ = lean_apply_1(v___x_6684__overap_3046_, lean_box(0));
v___x_3048_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3039_, v___x_3040_, v___x_3047_, v___f_3025_);
return v___x_3048_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_final_3021_ = stack[0].m_num;
lean_object* v___f_3022_ = stack[1].m_obj;
lean_object* v___f_3023_ = stack[2].m_obj;
lean_object* v_requestStream_3024_ = stack[3].m_obj;
lean_object* v___f_3025_ = stack[4].m_obj;
lean_object* v_x_3026_ = stack[5].m_obj;
lean_object* v_res_3049_;
v_res_3049_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_3021_, v___f_3022_, v___f_3023_, v_requestStream_3024_, v___f_3025_, v_x_3026_);
stack->m_obj
 = v_res_3049_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_final_3050_, lean_object* v___f_3051_, lean_object* v___f_3052_, lean_object* v_requestStream_3053_, lean_object* v___f_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v_final_boxed_3057_; lean_object* v_res_3058_; 
v_final_boxed_3057_ = lean_unbox(v_final_3050_);
v_res_3058_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_boxed_3057_, v___f_3051_, v___f_3052_, v_requestStream_3053_, v___f_3054_, v_x_3055_);
return v_res_3058_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_3059_, lean_object* v_x_3060_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v_state_3059_);
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
lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3100_; 
v_isSharedCheck_3100_ = !lean_is_exclusive(v_x_3060_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v_x_3060_, 0);
lean_dec(v_unused_3101_);
v___x_3072_ = v_x_3060_;
v_isShared_3073_ = v_isSharedCheck_3100_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v_x_3060_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3100_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_machine_3074_; lean_object* v_requestStream_3075_; lean_object* v_keepAliveTimeout_3076_; lean_object* v_currentTimeout_3077_; lean_object* v_headerTimeout_3078_; lean_object* v_response_3079_; lean_object* v_respStream_3080_; uint8_t v_requiresData_3081_; lean_object* v_expectData_3082_; lean_object* v_pendingHead_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3099_; 
v_machine_3074_ = lean_ctor_get(v_state_3059_, 0);
v_requestStream_3075_ = lean_ctor_get(v_state_3059_, 1);
v_keepAliveTimeout_3076_ = lean_ctor_get(v_state_3059_, 2);
v_currentTimeout_3077_ = lean_ctor_get(v_state_3059_, 3);
v_headerTimeout_3078_ = lean_ctor_get(v_state_3059_, 4);
v_response_3079_ = lean_ctor_get(v_state_3059_, 5);
v_respStream_3080_ = lean_ctor_get(v_state_3059_, 6);
v_requiresData_3081_ = lean_ctor_get_uint8(v_state_3059_, sizeof(void*)*9);
v_expectData_3082_ = lean_ctor_get(v_state_3059_, 7);
v_pendingHead_3083_ = lean_ctor_get(v_state_3059_, 8);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_state_3059_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3085_ = v_state_3059_;
v_isShared_3086_ = v_isSharedCheck_3099_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_pendingHead_3083_);
lean_inc(v_expectData_3082_);
lean_inc(v_respStream_3080_);
lean_inc(v_response_3079_);
lean_inc(v_headerTimeout_3078_);
lean_inc(v_currentTimeout_3077_);
lean_inc(v_keepAliveTimeout_3076_);
lean_inc(v_requestStream_3075_);
lean_inc(v_machine_3074_);
lean_dec(v_state_3059_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3099_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3091_; 
v___x_3087_ = lean_box(52);
v___x_3088_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3074_, v___x_3087_);
v___x_3089_ = 0;
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3088_);
v___x_3091_ = v___x_3085_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_requestStream_3075_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_keepAliveTimeout_3076_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_currentTimeout_3077_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_headerTimeout_3078_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_response_3079_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_respStream_3080_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_expectData_3082_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_pendingHead_3083_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*9, v_requiresData_3081_);
v___x_3091_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*9 + 1, v___x_3089_);
v___x_3092_ = lean_box(v___x_3089_);
v___x_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3093_);
v___x_3095_ = v___x_3072_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
return v___x_3096_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_3059_ = stack[0].m_obj;
lean_object* v_x_3060_ = stack[1].m_obj;
lean_object* v_res_3102_;
v_res_3102_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3059_, v_x_3060_);
stack->m_obj
 = v_res_3102_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3103_, lean_object* v_x_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3103_, v_x_3104_);
return v_res_3106_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3107_, lean_object* v_requestStream_3108_, lean_object* v_keepAliveTimeout_3109_, lean_object* v_currentTimeout_3110_, lean_object* v_headerTimeout_3111_, lean_object* v_response_3112_, lean_object* v_respStream_3113_, uint8_t v_requiresData_3114_, lean_object* v_expectData_3115_, lean_object* v_pendingHead_3116_, lean_object* v_____r_3117_){
_start:
{
uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3119_ = 0;
v___x_3120_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3120_, 0, v_machine_3107_);
lean_ctor_set(v___x_3120_, 1, v_requestStream_3108_);
lean_ctor_set(v___x_3120_, 2, v_keepAliveTimeout_3109_);
lean_ctor_set(v___x_3120_, 3, v_currentTimeout_3110_);
lean_ctor_set(v___x_3120_, 4, v_headerTimeout_3111_);
lean_ctor_set(v___x_3120_, 5, v_response_3112_);
lean_ctor_set(v___x_3120_, 6, v_respStream_3113_);
lean_ctor_set(v___x_3120_, 7, v_expectData_3115_);
lean_ctor_set(v___x_3120_, 8, v_pendingHead_3116_);
lean_ctor_set_uint8(v___x_3120_, sizeof(void*)*9, v_requiresData_3114_);
lean_ctor_set_uint8(v___x_3120_, sizeof(void*)*9 + 1, v___x_3119_);
v___x_3121_ = lean_box(v___x_3119_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3120_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_machine_3107_ = stack[0].m_obj;
lean_object* v_requestStream_3108_ = stack[1].m_obj;
lean_object* v_keepAliveTimeout_3109_ = stack[2].m_obj;
lean_object* v_currentTimeout_3110_ = stack[3].m_obj;
lean_object* v_headerTimeout_3111_ = stack[4].m_obj;
lean_object* v_response_3112_ = stack[5].m_obj;
lean_object* v_respStream_3113_ = stack[6].m_obj;
uint8_t v_requiresData_3114_ = stack[7].m_num;
lean_object* v_expectData_3115_ = stack[8].m_obj;
lean_object* v_pendingHead_3116_ = stack[9].m_obj;
lean_object* v_____r_3117_ = stack[10].m_obj;
lean_object* v_res_3125_;
v_res_3125_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3107_, v_requestStream_3108_, v_keepAliveTimeout_3109_, v_currentTimeout_3110_, v_headerTimeout_3111_, v_response_3112_, v_respStream_3113_, v_requiresData_3114_, v_expectData_3115_, v_pendingHead_3116_, v_____r_3117_);
stack->m_obj
 = v_res_3125_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3126_, lean_object* v_requestStream_3127_, lean_object* v_keepAliveTimeout_3128_, lean_object* v_currentTimeout_3129_, lean_object* v_headerTimeout_3130_, lean_object* v_response_3131_, lean_object* v_respStream_3132_, lean_object* v_requiresData_3133_, lean_object* v_expectData_3134_, lean_object* v_pendingHead_3135_, lean_object* v_____r_3136_, lean_object* v___y_3137_){
_start:
{
uint8_t v_requiresData_boxed_3138_; lean_object* v_res_3139_; 
v_requiresData_boxed_3138_ = lean_unbox(v_requiresData_3133_);
v_res_3139_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3126_, v_requestStream_3127_, v_keepAliveTimeout_3128_, v_currentTimeout_3129_, v_headerTimeout_3130_, v_response_3131_, v_respStream_3132_, v_requiresData_boxed_3138_, v_expectData_3134_, v_pendingHead_3135_, v_____r_3136_);
return v_res_3139_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3140_, lean_object* v_body_3141_, lean_object* v___f_3142_, lean_object* v___f_3143_, lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v___f_3143_);
lean_dec_ref(v___f_3142_);
lean_dec(v_body_3141_);
lean_dec_ref(v_close_3140_);
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
lean_object* v_a_3155_; uint8_t v___x_3156_; 
v_a_3155_ = lean_ctor_get(v_x_3144_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v_x_3144_, 1);
v___x_3156_ = lean_unbox(v_a_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; 
lean_dec_ref(v___f_3143_);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = lean_apply_2(v_close_3140_, v_body_3141_, lean_box(0));
v___x_3159_ = lean_unbox(v_a_3155_);
lean_dec(v_a_3155_);
v___x_3160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3157_, v___x_3159_, v___x_3158_, v___f_3142_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec(v_a_3155_);
lean_dec_ref(v___f_3142_);
lean_dec(v_body_3141_);
lean_dec_ref(v_close_3140_);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_apply_2(v___f_3143_, v___x_3161_, lean_box(0));
return v___x_3162_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_close_3140_ = stack[0].m_obj;
lean_object* v_body_3141_ = stack[1].m_obj;
lean_object* v___f_3142_ = stack[2].m_obj;
lean_object* v___f_3143_ = stack[3].m_obj;
lean_object* v_x_3144_ = stack[4].m_obj;
lean_object* v_res_3163_;
v_res_3163_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3140_, v_body_3141_, v___f_3142_, v___f_3143_, v_x_3144_);
stack->m_obj
 = v_res_3163_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3164_, lean_object* v_body_3165_, lean_object* v___f_3166_, lean_object* v___f_3167_, lean_object* v_x_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3164_, v_body_3165_, v___f_3166_, v___f_3167_, v_x_3168_);
return v_res_3170_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3171_, lean_object* v_keepAliveTimeout_3172_, lean_object* v_currentTimeout_3173_, lean_object* v_headerTimeout_3174_, lean_object* v_response_3175_, uint8_t v_requiresData_3176_, lean_object* v_expectData_3177_, uint8_t v___x_3178_, lean_object* v_pendingHead_3179_, lean_object* v_____x_3180_){
_start:
{
lean_object* v_snd_3182_; lean_object* v_fst_3183_; lean_object* v_fst_3184_; lean_object* v_snd_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3195_; 
v_snd_3182_ = lean_ctor_get(v_____x_3180_, 1);
lean_inc(v_snd_3182_);
v_fst_3183_ = lean_ctor_get(v_____x_3180_, 0);
lean_inc(v_fst_3183_);
lean_dec_ref(v_____x_3180_);
v_fst_3184_ = lean_ctor_get(v_snd_3182_, 0);
v_snd_3185_ = lean_ctor_get(v_snd_3182_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_snd_3182_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3187_ = v_snd_3182_;
v_isShared_3188_ = v_isSharedCheck_3195_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_snd_3185_);
lean_inc(v_fst_3184_);
lean_dec(v_snd_3182_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3195_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3189_, 0, v_fst_3183_);
lean_ctor_set(v___x_3189_, 1, v_requestStream_3171_);
lean_ctor_set(v___x_3189_, 2, v_keepAliveTimeout_3172_);
lean_ctor_set(v___x_3189_, 3, v_currentTimeout_3173_);
lean_ctor_set(v___x_3189_, 4, v_headerTimeout_3174_);
lean_ctor_set(v___x_3189_, 5, v_response_3175_);
lean_ctor_set(v___x_3189_, 6, v_fst_3184_);
lean_ctor_set(v___x_3189_, 7, v_expectData_3177_);
lean_ctor_set(v___x_3189_, 8, v_pendingHead_3179_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*9, v_requiresData_3176_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*9 + 1, v___x_3178_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3189_);
v___x_3191_ = v___x_3187_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_snd_3185_);
v___x_3191_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
return v___x_3193_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestStream_3171_ = stack[0].m_obj;
lean_object* v_keepAliveTimeout_3172_ = stack[1].m_obj;
lean_object* v_currentTimeout_3173_ = stack[2].m_obj;
lean_object* v_headerTimeout_3174_ = stack[3].m_obj;
lean_object* v_response_3175_ = stack[4].m_obj;
uint8_t v_requiresData_3176_ = stack[5].m_num;
lean_object* v_expectData_3177_ = stack[6].m_obj;
uint8_t v___x_3178_ = stack[7].m_num;
lean_object* v_pendingHead_3179_ = stack[8].m_obj;
lean_object* v_____x_3180_ = stack[9].m_obj;
lean_object* v_res_3196_;
v_res_3196_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3171_, v_keepAliveTimeout_3172_, v_currentTimeout_3173_, v_headerTimeout_3174_, v_response_3175_, v_requiresData_3176_, v_expectData_3177_, v___x_3178_, v_pendingHead_3179_, v_____x_3180_);
stack->m_obj
 = v_res_3196_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3197_, lean_object* v_keepAliveTimeout_3198_, lean_object* v_currentTimeout_3199_, lean_object* v_headerTimeout_3200_, lean_object* v_response_3201_, lean_object* v_requiresData_3202_, lean_object* v_expectData_3203_, lean_object* v___x_3204_, lean_object* v_pendingHead_3205_, lean_object* v_____x_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v_requiresData_boxed_3208_; uint8_t v___x_7807__boxed_3209_; lean_object* v_res_3210_; 
v_requiresData_boxed_3208_ = lean_unbox(v_requiresData_3202_);
v___x_7807__boxed_3209_ = lean_unbox(v___x_3204_);
v_res_3210_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3197_, v_keepAliveTimeout_3198_, v_currentTimeout_3199_, v_headerTimeout_3200_, v_response_3201_, v_requiresData_boxed_3208_, v_expectData_3203_, v___x_7807__boxed_3209_, v_pendingHead_3205_, v_____x_3206_);
return v_res_3210_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3211_, lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3212_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v___f_3211_);
v_a_3214_ = lean_ctor_get(v_x_3212_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_x_3212_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3216_ = v_x_3212_;
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v_x_3212_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3224_; 
v_a_3223_ = lean_ctor_get(v_x_3212_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v_x_3212_, 1);
v___x_3224_ = lean_apply_2(v___f_3211_, v_a_3223_, lean_box(0));
return v___x_3224_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3211_ = stack[0].m_obj;
lean_object* v_x_3212_ = stack[1].m_obj;
lean_object* v_res_3225_;
v_res_3225_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3211_, v_x_3212_);
stack->m_obj
 = v_res_3225_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3226_, lean_object* v_x_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3226_, v_x_3227_);
return v_res_3229_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3230_, lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3241_; 
v_a_3233_ = lean_ctor_get(v_x_3231_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_x_3231_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3235_ = v_x_3231_;
v_isShared_3236_ = v_isSharedCheck_3241_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v_x_3231_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3241_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3261_; 
v_a_3242_ = lean_ctor_get(v_x_3231_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_x_3231_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3244_ = v_x_3231_;
v_isShared_3245_ = v_isSharedCheck_3261_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v_x_3231_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3261_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v_fst_3246_; lean_object* v_snd_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3260_; 
v_fst_3246_ = lean_ctor_get(v_a_3242_, 0);
v_snd_3247_ = lean_ctor_get(v_a_3242_, 1);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_a_3242_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3249_ = v_a_3242_;
v_isShared_3250_ = v_isSharedCheck_3260_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_snd_3247_);
lean_inc(v_fst_3246_);
lean_dec(v_a_3242_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3260_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = lean_box(v___x_3230_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3251_);
lean_ctor_set(v___x_3249_, 0, v_snd_3247_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_snd_3247_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v_fst_3246_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3254_);
v___x_3256_ = v___x_3244_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
return v___x_3257_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3230_ = stack[0].m_num;
lean_object* v_x_3231_ = stack[1].m_obj;
lean_object* v_res_3262_;
v_res_3262_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_3230_, v_x_3231_);
stack->m_obj
 = v_res_3262_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3263_, lean_object* v_x_3264_, lean_object* v___y_3265_){
_start:
{
uint8_t v___x_7912__boxed_3266_; lean_object* v_res_3267_; 
v___x_7912__boxed_3266_ = lean_unbox(v___x_3263_);
v_res_3267_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7912__boxed_3266_, v_x_3264_);
return v_res_3267_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3268_, uint8_t v___x_3269_, lean_object* v_fst_3270_, lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v_fst_3270_);
lean_dec(v_snd_3268_);
v_a_3273_ = lean_ctor_get(v_x_3271_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_x_3271_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3275_ = v_x_3271_;
v_isShared_3276_ = v_isSharedCheck_3281_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v_x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3281_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
}
}
else
{
lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3292_; 
v_isSharedCheck_3292_ = !lean_is_exclusive(v_x_3271_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; 
v_unused_3293_ = lean_ctor_get(v_x_3271_, 0);
lean_dec(v_unused_3293_);
v___x_3283_ = v_x_3271_;
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
else
{
lean_dec(v_x_3271_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3285_ = lean_box(v___x_3269_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_snd_3268_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_fst_3270_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3287_);
v___x_3289_ = v___x_3283_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3268_ = stack[0].m_obj;
uint8_t v___x_3269_ = stack[1].m_num;
lean_object* v_fst_3270_ = stack[2].m_obj;
lean_object* v_x_3271_ = stack[3].m_obj;
lean_object* v_res_3294_;
v_res_3294_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3268_, v___x_3269_, v_fst_3270_, v_x_3271_);
stack->m_obj
 = v_res_3294_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3295_, lean_object* v___x_3296_, lean_object* v_fst_3297_, lean_object* v_x_3298_, lean_object* v___y_3299_){
_start:
{
uint8_t v___x_8015__boxed_3300_; lean_object* v_res_3301_; 
v___x_8015__boxed_3300_ = lean_unbox(v___x_3296_);
v_res_3301_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3295_, v___x_8015__boxed_3300_, v_fst_3297_, v_x_3298_);
return v_res_3301_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3302_, lean_object* v_handler_3303_, uint8_t v___x_3304_, lean_object* v___f_3305_, lean_object* v_x_3306_){
_start:
{
if (lean_obj_tag(v_x_3306_) == 0)
{
lean_object* v_a_3308_; lean_object* v_onFailure_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_a_3308_ = lean_ctor_get(v_x_3306_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v_x_3306_, 1);
v_onFailure_3309_ = lean_ctor_get(v_inst_3302_, 2);
lean_inc_ref(v_onFailure_3309_);
lean_dec_ref(v_inst_3302_);
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = lean_apply_3(v_onFailure_3309_, v_handler_3303_, v_a_3308_, lean_box(0));
v___x_3312_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3310_, v___x_3304_, v___x_3311_, v___f_3305_);
return v___x_3312_;
}
else
{
lean_object* v___x_3313_; 
lean_dec_ref(v___f_3305_);
lean_dec(v_handler_3303_);
lean_dec_ref(v_inst_3302_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_x_3306_);
return v___x_3313_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3302_ = stack[0].m_obj;
lean_object* v_handler_3303_ = stack[1].m_obj;
uint8_t v___x_3304_ = stack[2].m_num;
lean_object* v___f_3305_ = stack[3].m_obj;
lean_object* v_x_3306_ = stack[4].m_obj;
lean_object* v_res_3314_;
v_res_3314_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3302_, v_handler_3303_, v___x_3304_, v___f_3305_, v_x_3306_);
stack->m_obj
 = v_res_3314_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3315_, lean_object* v_handler_3316_, lean_object* v___x_3317_, lean_object* v___f_3318_, lean_object* v_x_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v___x_8104__boxed_3321_; lean_object* v_res_3322_; 
v___x_8104__boxed_3321_ = lean_unbox(v___x_3317_);
v_res_3322_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3315_, v_handler_3316_, v___x_8104__boxed_3321_, v___f_3318_, v_x_3319_);
return v_res_3322_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3323_, lean_object* v___f_3324_, uint8_t v___x_3325_, lean_object* v_inst_3326_, lean_object* v_handler_3327_, lean_object* v_inst_3328_, lean_object* v___f_3329_, lean_object* v___f_3330_, lean_object* v_x_3331_){
_start:
{
if (lean_obj_tag(v_x_3331_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3341_; 
lean_dec_ref(v___f_3330_);
lean_dec_ref(v___f_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec(v_handler_3327_);
lean_dec_ref(v_inst_3326_);
lean_dec_ref(v___f_3324_);
v_a_3333_ = lean_ctor_get(v_x_3331_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_x_3331_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3335_ = v_x_3331_;
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v_x_3331_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3375_; 
v_a_3342_ = lean_ctor_get(v_x_3331_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_x_3331_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3344_ = v_x_3331_;
v_isShared_3345_ = v_isSharedCheck_3375_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v_x_3331_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3375_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_snd_3346_; 
v_snd_3346_ = lean_ctor_get(v_a_3342_, 1);
lean_inc(v_snd_3346_);
if (lean_obj_tag(v_snd_3346_) == 0)
{
lean_object* v_fst_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref(v___f_3330_);
lean_dec_ref(v___f_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec(v_handler_3327_);
lean_dec_ref(v_inst_3326_);
v_fst_3347_ = lean_ctor_get(v_a_3342_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v_a_3342_, 1);
lean_dec(v_unused_3363_);
v___x_3349_ = v_a_3342_;
v_isShared_3350_ = v_isSharedCheck_3362_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_fst_3347_);
lean_dec(v_a_3342_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3362_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_box(v___x_3323_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v___x_3351_);
lean_ctor_set(v___x_3349_, 0, v_snd_3346_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_snd_3346_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v_fst_3347_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_unsigned_to_nat(0u);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3354_);
v___x_3357_ = v___x_3344_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
v___x_3357_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
v___x_3359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3355_, v___x_3323_, v___x_3358_, v___f_3324_);
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_fst_3364_; lean_object* v_val_3365_; lean_object* v___x_3366_; lean_object* v___f_3367_; lean_object* v___x_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_del_object(v___x_3344_);
lean_dec_ref(v___f_3324_);
v_fst_3364_ = lean_ctor_get(v_a_3342_, 0);
lean_inc_n(v_fst_3364_, 2);
lean_dec(v_a_3342_);
v_val_3365_ = lean_ctor_get(v_snd_3346_, 0);
lean_inc(v_val_3365_);
v___x_3366_ = lean_box(v___x_3325_);
v___f_3367_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3367_, 0, v_snd_3346_);
lean_closure_set(v___f_3367_, 1, v___x_3366_);
lean_closure_set(v___f_3367_, 2, v_fst_3364_);
v___x_3368_ = lean_box(v___x_3323_);
v___f_3369_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3369_, 0, v_inst_3326_);
lean_closure_set(v___f_3369_, 1, v_handler_3327_);
lean_closure_set(v___f_3369_, 2, v___x_3368_);
lean_closure_set(v___f_3369_, 3, v___f_3367_);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3328_, v_fst_3364_, v_val_3365_);
v___x_3372_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3370_, v___x_3323_, v___x_3371_, v___f_3329_);
v___x_3373_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3370_, v___x_3323_, v___x_3372_, v___f_3369_);
v___x_3374_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3370_, v___x_3323_, v___x_3373_, v___f_3330_);
return v___x_3374_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3323_ = stack[0].m_num;
lean_object* v___f_3324_ = stack[1].m_obj;
uint8_t v___x_3325_ = stack[2].m_num;
lean_object* v_inst_3326_ = stack[3].m_obj;
lean_object* v_handler_3327_ = stack[4].m_obj;
lean_object* v_inst_3328_ = stack[5].m_obj;
lean_object* v___f_3329_ = stack[6].m_obj;
lean_object* v___f_3330_ = stack[7].m_obj;
lean_object* v_x_3331_ = stack[8].m_obj;
lean_object* v_res_3376_;
v_res_3376_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_3323_, v___f_3324_, v___x_3325_, v_inst_3326_, v_handler_3327_, v_inst_3328_, v___f_3329_, v___f_3330_, v_x_3331_);
stack->m_obj
 = v_res_3376_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3377_, lean_object* v___f_3378_, lean_object* v___x_3379_, lean_object* v_inst_3380_, lean_object* v_handler_3381_, lean_object* v_inst_3382_, lean_object* v___f_3383_, lean_object* v___f_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_){
_start:
{
uint8_t v___x_8144__boxed_3387_; uint8_t v___x_8146__boxed_3388_; lean_object* v_res_3389_; 
v___x_8144__boxed_3387_ = lean_unbox(v___x_3377_);
v___x_8146__boxed_3388_ = lean_unbox(v___x_3379_);
v_res_3389_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_8144__boxed_3387_, v___f_3378_, v___x_8146__boxed_3388_, v_inst_3380_, v_handler_3381_, v_inst_3382_, v___f_3383_, v___f_3384_, v_x_3385_);
return v_res_3389_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3390_, lean_object* v_x_3391_){
_start:
{
if (lean_obj_tag(v_x_3391_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v_state_3390_);
v_a_3393_ = lean_ctor_get(v_x_3391_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_x_3391_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3395_ = v_x_3391_;
v_isShared_3396_ = v_isSharedCheck_3401_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v_x_3391_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3401_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
}
else
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3431_; 
v_isSharedCheck_3431_ = !lean_is_exclusive(v_x_3391_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v_x_3391_, 0);
lean_dec(v_unused_3432_);
v___x_3403_ = v_x_3391_;
v_isShared_3404_ = v_isSharedCheck_3431_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v_x_3391_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3431_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_machine_3405_; lean_object* v_requestStream_3406_; lean_object* v_keepAliveTimeout_3407_; lean_object* v_currentTimeout_3408_; lean_object* v_headerTimeout_3409_; lean_object* v_response_3410_; lean_object* v_respStream_3411_; uint8_t v_requiresData_3412_; lean_object* v_expectData_3413_; lean_object* v_pendingHead_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3430_; 
v_machine_3405_ = lean_ctor_get(v_state_3390_, 0);
v_requestStream_3406_ = lean_ctor_get(v_state_3390_, 1);
v_keepAliveTimeout_3407_ = lean_ctor_get(v_state_3390_, 2);
v_currentTimeout_3408_ = lean_ctor_get(v_state_3390_, 3);
v_headerTimeout_3409_ = lean_ctor_get(v_state_3390_, 4);
v_response_3410_ = lean_ctor_get(v_state_3390_, 5);
v_respStream_3411_ = lean_ctor_get(v_state_3390_, 6);
v_requiresData_3412_ = lean_ctor_get_uint8(v_state_3390_, sizeof(void*)*9);
v_expectData_3413_ = lean_ctor_get(v_state_3390_, 7);
v_pendingHead_3414_ = lean_ctor_get(v_state_3390_, 8);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_state_3390_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3416_ = v_state_3390_;
v_isShared_3417_ = v_isSharedCheck_3430_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_pendingHead_3414_);
lean_inc(v_expectData_3413_);
lean_inc(v_respStream_3411_);
lean_inc(v_response_3410_);
lean_inc(v_headerTimeout_3409_);
lean_inc(v_currentTimeout_3408_);
lean_inc(v_keepAliveTimeout_3407_);
lean_inc(v_requestStream_3406_);
lean_inc(v_machine_3405_);
lean_dec(v_state_3390_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3430_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3422_; 
v___x_3418_ = lean_box(31);
v___x_3419_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3405_, v___x_3418_);
v___x_3420_ = 0;
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3419_);
v___x_3422_ = v___x_3416_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_requestStream_3406_);
lean_ctor_set(v_reuseFailAlloc_3429_, 2, v_keepAliveTimeout_3407_);
lean_ctor_set(v_reuseFailAlloc_3429_, 3, v_currentTimeout_3408_);
lean_ctor_set(v_reuseFailAlloc_3429_, 4, v_headerTimeout_3409_);
lean_ctor_set(v_reuseFailAlloc_3429_, 5, v_response_3410_);
lean_ctor_set(v_reuseFailAlloc_3429_, 6, v_respStream_3411_);
lean_ctor_set(v_reuseFailAlloc_3429_, 7, v_expectData_3413_);
lean_ctor_set(v_reuseFailAlloc_3429_, 8, v_pendingHead_3414_);
lean_ctor_set_uint8(v_reuseFailAlloc_3429_, sizeof(void*)*9, v_requiresData_3412_);
v___x_3422_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*9 + 1, v___x_3420_);
v___x_3423_ = lean_box(v___x_3420_);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3424_);
v___x_3426_ = v___x_3403_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_3390_ = stack[0].m_obj;
lean_object* v_x_3391_ = stack[1].m_obj;
lean_object* v_res_3433_;
v_res_3433_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3390_, v_x_3391_);
stack->m_obj
 = v_res_3433_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3434_, lean_object* v_x_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3434_, v_x_3435_);
return v_res_3437_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3443_ = lean_mk_io_user_error(v___x_3442_);
return v___x_3443_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3444_, lean_object* v_inst_3445_, lean_object* v_handler_3446_, lean_object* v_config_3447_, lean_object* v_event_3448_, lean_object* v_state_3449_){
_start:
{
switch(lean_obj_tag(v_event_3448_))
{
case 0:
{
lean_object* v_x_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_handler_3446_);
lean_dec_ref(v_inst_3445_);
lean_dec_ref(v_inst_3444_);
v_x_3451_ = lean_ctor_get(v_event_3448_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_event_3448_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3453_ = v_event_3448_;
v_isShared_3454_ = v_isSharedCheck_3558_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_x_3451_);
lean_dec(v_event_3448_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3558_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
if (lean_obj_tag(v_x_3451_) == 0)
{
lean_object* v_machine_3455_; lean_object* v_reader_3456_; lean_object* v_requestStream_3457_; lean_object* v_keepAliveTimeout_3458_; lean_object* v_currentTimeout_3459_; lean_object* v_headerTimeout_3460_; lean_object* v_response_3461_; lean_object* v_respStream_3462_; uint8_t v_requiresData_3463_; lean_object* v_expectData_3464_; uint8_t v_handlerDispatched_3465_; lean_object* v_pendingHead_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_config_3447_);
v_machine_3455_ = lean_ctor_get(v_state_3449_, 0);
lean_inc_ref(v_machine_3455_);
v_reader_3456_ = lean_ctor_get(v_machine_3455_, 0);
lean_inc_ref(v_reader_3456_);
v_requestStream_3457_ = lean_ctor_get(v_state_3449_, 1);
v_keepAliveTimeout_3458_ = lean_ctor_get(v_state_3449_, 2);
v_currentTimeout_3459_ = lean_ctor_get(v_state_3449_, 3);
v_headerTimeout_3460_ = lean_ctor_get(v_state_3449_, 4);
v_response_3461_ = lean_ctor_get(v_state_3449_, 5);
v_respStream_3462_ = lean_ctor_get(v_state_3449_, 6);
v_requiresData_3463_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3464_ = lean_ctor_get(v_state_3449_, 7);
v_handlerDispatched_3465_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9 + 1);
v_pendingHead_3466_ = lean_ctor_get(v_state_3449_, 8);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_state_3449_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v_state_3449_, 0);
lean_dec(v_unused_3510_);
v___x_3468_ = v_state_3449_;
v_isShared_3469_ = v_isSharedCheck_3509_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_pendingHead_3466_);
lean_inc(v_expectData_3464_);
lean_inc(v_respStream_3462_);
lean_inc(v_response_3461_);
lean_inc(v_headerTimeout_3460_);
lean_inc(v_currentTimeout_3459_);
lean_inc(v_keepAliveTimeout_3458_);
lean_inc(v_requestStream_3457_);
lean_dec(v_state_3449_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3509_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_writer_3470_; lean_object* v_config_3471_; lean_object* v_events_3472_; lean_object* v_error_3473_; lean_object* v_instant_3474_; uint8_t v_keepAlive_3475_; uint8_t v_forcedFlush_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3507_; 
v_writer_3470_ = lean_ctor_get(v_machine_3455_, 1);
v_config_3471_ = lean_ctor_get(v_machine_3455_, 2);
v_events_3472_ = lean_ctor_get(v_machine_3455_, 3);
v_error_3473_ = lean_ctor_get(v_machine_3455_, 4);
v_instant_3474_ = lean_ctor_get(v_machine_3455_, 5);
v_keepAlive_3475_ = lean_ctor_get_uint8(v_machine_3455_, sizeof(void*)*6);
v_forcedFlush_3476_ = lean_ctor_get_uint8(v_machine_3455_, sizeof(void*)*6 + 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_machine_3455_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; 
v_unused_3508_ = lean_ctor_get(v_machine_3455_, 0);
lean_dec(v_unused_3508_);
v___x_3478_ = v_machine_3455_;
v_isShared_3479_ = v_isSharedCheck_3507_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_instant_3474_);
lean_inc(v_error_3473_);
lean_inc(v_events_3472_);
lean_inc(v_config_3471_);
lean_inc(v_writer_3470_);
lean_dec(v_machine_3455_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3507_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_state_3480_; lean_object* v_input_3481_; lean_object* v_messageHead_3482_; lean_object* v_messageCount_3483_; lean_object* v_bodyBytesRead_3484_; lean_object* v_headerBytesRead_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3506_; 
v_state_3480_ = lean_ctor_get(v_reader_3456_, 0);
v_input_3481_ = lean_ctor_get(v_reader_3456_, 1);
v_messageHead_3482_ = lean_ctor_get(v_reader_3456_, 2);
v_messageCount_3483_ = lean_ctor_get(v_reader_3456_, 3);
v_bodyBytesRead_3484_ = lean_ctor_get(v_reader_3456_, 4);
v_headerBytesRead_3485_ = lean_ctor_get(v_reader_3456_, 5);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_reader_3456_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3487_ = v_reader_3456_;
v_isShared_3488_ = v_isSharedCheck_3506_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_headerBytesRead_3485_);
lean_inc(v_bodyBytesRead_3484_);
lean_inc(v_messageCount_3483_);
lean_inc(v_messageHead_3482_);
lean_inc(v_input_3481_);
lean_inc(v_state_3480_);
lean_dec(v_reader_3456_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3506_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
uint8_t v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = 1;
if (v_isShared_3488_ == 0)
{
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_state_3480_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_input_3481_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_messageHead_3482_);
lean_ctor_set(v_reuseFailAlloc_3505_, 3, v_messageCount_3483_);
lean_ctor_set(v_reuseFailAlloc_3505_, 4, v_bodyBytesRead_3484_);
lean_ctor_set(v_reuseFailAlloc_3505_, 5, v_headerBytesRead_3485_);
v___x_3491_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
uint8_t v___x_3492_; lean_object* v___x_3494_; 
lean_ctor_set_uint8(v___x_3491_, sizeof(void*)*6, v___x_3489_);
v___x_3492_ = 0;
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3491_);
v___x_3494_ = v___x_3478_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_writer_3470_);
lean_ctor_set(v_reuseFailAlloc_3504_, 2, v_config_3471_);
lean_ctor_set(v_reuseFailAlloc_3504_, 3, v_events_3472_);
lean_ctor_set(v_reuseFailAlloc_3504_, 4, v_error_3473_);
lean_ctor_set(v_reuseFailAlloc_3504_, 5, v_instant_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3504_, sizeof(void*)*6, v_keepAlive_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3504_, sizeof(void*)*6 + 1, v_forcedFlush_3476_);
v___x_3494_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3496_; 
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*6 + 2, v___x_3492_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3494_);
v___x_3496_ = v___x_3468_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_requestStream_3457_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_keepAliveTimeout_3458_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_currentTimeout_3459_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_headerTimeout_3460_);
lean_ctor_set(v_reuseFailAlloc_3503_, 5, v_response_3461_);
lean_ctor_set(v_reuseFailAlloc_3503_, 6, v_respStream_3462_);
lean_ctor_set(v_reuseFailAlloc_3503_, 7, v_expectData_3464_);
lean_ctor_set(v_reuseFailAlloc_3503_, 8, v_pendingHead_3466_);
lean_ctor_set_uint8(v_reuseFailAlloc_3503_, sizeof(void*)*9, v_requiresData_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3503_, sizeof(void*)*9 + 1, v_handlerDispatched_3465_);
v___x_3496_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3497_ = lean_box(v___x_3492_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3496_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set_tag(v___x_3453_, 1);
lean_ctor_set(v___x_3453_, 0, v___x_3498_);
v___x_3500_ = v___x_3453_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
return v___x_3501_;
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
lean_object* v_val_3511_; lean_object* v_machine_3512_; lean_object* v_requestStream_3513_; lean_object* v_keepAliveTimeout_3514_; lean_object* v_currentTimeout_3515_; lean_object* v_response_3516_; lean_object* v_respStream_3517_; uint8_t v_requiresData_3518_; lean_object* v_expectData_3519_; uint8_t v_handlerDispatched_3520_; lean_object* v_pendingHead_3521_; lean_object* v___f_3522_; 
lean_del_object(v___x_3453_);
v_val_3511_ = lean_ctor_get(v_x_3451_, 0);
lean_inc_n(v_val_3511_, 2);
lean_dec_ref_known(v_x_3451_, 1);
v_machine_3512_ = lean_ctor_get(v_state_3449_, 0);
v_requestStream_3513_ = lean_ctor_get(v_state_3449_, 1);
v_keepAliveTimeout_3514_ = lean_ctor_get(v_state_3449_, 2);
lean_inc(v_keepAliveTimeout_3514_);
v_currentTimeout_3515_ = lean_ctor_get(v_state_3449_, 3);
v_response_3516_ = lean_ctor_get(v_state_3449_, 5);
v_respStream_3517_ = lean_ctor_get(v_state_3449_, 6);
v_requiresData_3518_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3519_ = lean_ctor_get(v_state_3449_, 7);
v_handlerDispatched_3520_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9 + 1);
v_pendingHead_3521_ = lean_ctor_get(v_state_3449_, 8);
v___f_3522_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3522_, 0, v_val_3511_);
if (lean_obj_tag(v_keepAliveTimeout_3514_) == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_dec_ref(v___f_3522_);
lean_dec_ref(v_config_3447_);
v___x_3523_ = lean_box(0);
v___x_3524_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3511_, v___x_3523_, v_state_3449_);
return v___x_3524_;
}
else
{
lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3556_; 
lean_inc(v_pendingHead_3521_);
lean_inc(v_expectData_3519_);
lean_inc(v_respStream_3517_);
lean_inc_ref(v_response_3516_);
lean_inc(v_currentTimeout_3515_);
lean_inc_ref(v_requestStream_3513_);
lean_inc_ref(v_machine_3512_);
lean_dec(v_val_3511_);
lean_dec_ref(v_state_3449_);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_keepAliveTimeout_3514_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v_keepAliveTimeout_3514_, 0);
lean_dec(v_unused_3557_);
v___x_3526_ = v_keepAliveTimeout_3514_;
v_isShared_3527_ = v_isSharedCheck_3556_;
goto v_resetjp_3525_;
}
else
{
lean_dec(v_keepAliveTimeout_3514_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3556_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___f_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v_val_3534_; lean_object* v___x_3539_; 
v___x_3528_ = lean_box(v_requiresData_3518_);
v___x_3529_ = lean_box(v_handlerDispatched_3520_);
v___f_3530_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3530_, 0, v_config_3447_);
lean_closure_set(v___f_3530_, 1, v_machine_3512_);
lean_closure_set(v___f_3530_, 2, v_requestStream_3513_);
lean_closure_set(v___f_3530_, 3, v_currentTimeout_3515_);
lean_closure_set(v___f_3530_, 4, v_response_3516_);
lean_closure_set(v___f_3530_, 5, v_respStream_3517_);
lean_closure_set(v___f_3530_, 6, v___x_3528_);
lean_closure_set(v___f_3530_, 7, v_expectData_3519_);
lean_closure_set(v___f_3530_, 8, v___x_3529_);
lean_closure_set(v___f_3530_, 9, v_pendingHead_3521_);
lean_closure_set(v___f_3530_, 10, v___f_3522_);
v___x_3531_ = lean_unsigned_to_nat(0u);
v___x_3532_ = 0;
v___x_3539_ = lean_get_current_time();
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 1);
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
v_val_3534_ = v___x_3545_;
goto v___jp_3533_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3539_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3539_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set_tag(v___x_3550_, 0);
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
v_val_3534_ = v___x_3553_;
goto v___jp_3533_;
}
}
}
v___jp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 0);
lean_ctor_set(v___x_3526_, 0, v_val_3534_);
v___x_3536_ = v___x_3526_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_val_3534_);
v___x_3536_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; 
v___x_3537_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3531_, v___x_3532_, v___x_3536_, v___f_3530_);
return v___x_3537_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3670_; 
lean_dec_ref(v_config_3447_);
lean_dec(v_handler_3446_);
lean_dec_ref(v_inst_3444_);
v_x_3559_ = lean_ctor_get(v_event_3448_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_event_3448_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3561_ = v_event_3448_;
v_isShared_3562_ = v_isSharedCheck_3670_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_x_3559_);
lean_dec(v_event_3448_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3670_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
if (lean_obj_tag(v_x_3559_) == 0)
{
lean_object* v_machine_3563_; lean_object* v_requestStream_3564_; lean_object* v_keepAliveTimeout_3565_; lean_object* v_currentTimeout_3566_; lean_object* v_headerTimeout_3567_; lean_object* v_response_3568_; lean_object* v_respStream_3569_; uint8_t v_requiresData_3570_; lean_object* v_expectData_3571_; uint8_t v_handlerDispatched_3572_; lean_object* v_pendingHead_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___f_3576_; 
lean_del_object(v___x_3561_);
v_machine_3563_ = lean_ctor_get(v_state_3449_, 0);
lean_inc_ref_n(v_machine_3563_, 2);
v_requestStream_3564_ = lean_ctor_get(v_state_3449_, 1);
lean_inc_ref_n(v_requestStream_3564_, 2);
v_keepAliveTimeout_3565_ = lean_ctor_get(v_state_3449_, 2);
lean_inc_n(v_keepAliveTimeout_3565_, 2);
v_currentTimeout_3566_ = lean_ctor_get(v_state_3449_, 3);
lean_inc_n(v_currentTimeout_3566_, 2);
v_headerTimeout_3567_ = lean_ctor_get(v_state_3449_, 4);
lean_inc_n(v_headerTimeout_3567_, 2);
v_response_3568_ = lean_ctor_get(v_state_3449_, 5);
lean_inc_ref_n(v_response_3568_, 2);
v_respStream_3569_ = lean_ctor_get(v_state_3449_, 6);
lean_inc(v_respStream_3569_);
v_requiresData_3570_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3571_ = lean_ctor_get(v_state_3449_, 7);
lean_inc_n(v_expectData_3571_, 2);
v_handlerDispatched_3572_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9 + 1);
v_pendingHead_3573_ = lean_ctor_get(v_state_3449_, 8);
lean_inc_n(v_pendingHead_3573_, 2);
lean_dec_ref(v_state_3449_);
v___x_3574_ = lean_box(v_requiresData_3570_);
v___x_3575_ = lean_box(v_handlerDispatched_3572_);
v___f_3576_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3576_, 0, v_machine_3563_);
lean_closure_set(v___f_3576_, 1, v_requestStream_3564_);
lean_closure_set(v___f_3576_, 2, v_keepAliveTimeout_3565_);
lean_closure_set(v___f_3576_, 3, v_currentTimeout_3566_);
lean_closure_set(v___f_3576_, 4, v_headerTimeout_3567_);
lean_closure_set(v___f_3576_, 5, v_response_3568_);
lean_closure_set(v___f_3576_, 6, v___x_3574_);
lean_closure_set(v___f_3576_, 7, v_expectData_3571_);
lean_closure_set(v___f_3576_, 8, v___x_3575_);
lean_closure_set(v___f_3576_, 9, v_pendingHead_3573_);
if (lean_obj_tag(v_respStream_3569_) == 1)
{
lean_object* v_val_3577_; lean_object* v_close_3578_; lean_object* v_isClosed_3579_; lean_object* v___f_3580_; lean_object* v___f_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_dec(v_pendingHead_3573_);
lean_dec(v_expectData_3571_);
lean_dec_ref(v_response_3568_);
lean_dec(v_headerTimeout_3567_);
lean_dec(v_currentTimeout_3566_);
lean_dec(v_keepAliveTimeout_3565_);
lean_dec_ref(v_requestStream_3564_);
lean_dec_ref(v_machine_3563_);
v_val_3577_ = lean_ctor_get(v_respStream_3569_, 0);
lean_inc_n(v_val_3577_, 2);
lean_dec_ref_known(v_respStream_3569_, 1);
v_close_3578_ = lean_ctor_get(v_inst_3445_, 1);
lean_inc_ref(v_close_3578_);
v_isClosed_3579_ = lean_ctor_get(v_inst_3445_, 2);
lean_inc_ref(v_isClosed_3579_);
lean_dec_ref(v_inst_3445_);
lean_inc_ref(v___f_3576_);
v___f_3580_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3580_, 0, v___f_3576_);
v___f_3581_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3581_, 0, v_close_3578_);
lean_closure_set(v___f_3581_, 1, v_val_3577_);
lean_closure_set(v___f_3581_, 2, v___f_3580_);
lean_closure_set(v___f_3581_, 3, v___f_3576_);
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = 0;
v___x_3584_ = lean_apply_2(v_isClosed_3579_, v_val_3577_, lean_box(0));
v___x_3585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3582_, v___x_3583_, v___x_3584_, v___f_3581_);
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec_ref(v___f_3576_);
lean_dec(v_respStream_3569_);
lean_dec_ref(v_inst_3445_);
v___x_3586_ = lean_box(0);
v___x_3587_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3563_, v_requestStream_3564_, v_keepAliveTimeout_3565_, v_currentTimeout_3566_, v_headerTimeout_3567_, v_response_3568_, v_requiresData_3570_, v_expectData_3571_, v_handlerDispatched_3572_, v_pendingHead_3573_, v___x_3586_);
return v___x_3587_;
}
}
else
{
lean_object* v_val_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref(v_inst_3445_);
v_val_3588_ = lean_ctor_get(v_x_3559_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_x_3559_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3590_ = v_x_3559_;
v_isShared_3591_ = v_isSharedCheck_3669_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_val_3588_);
lean_dec(v_x_3559_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3669_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v_machine_3592_; lean_object* v_requestStream_3593_; lean_object* v_keepAliveTimeout_3594_; lean_object* v_currentTimeout_3595_; lean_object* v_headerTimeout_3596_; lean_object* v_response_3597_; lean_object* v_respStream_3598_; uint8_t v_requiresData_3599_; lean_object* v_expectData_3600_; uint8_t v_handlerDispatched_3601_; lean_object* v_pendingHead_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3668_; 
v_machine_3592_ = lean_ctor_get(v_state_3449_, 0);
v_requestStream_3593_ = lean_ctor_get(v_state_3449_, 1);
v_keepAliveTimeout_3594_ = lean_ctor_get(v_state_3449_, 2);
v_currentTimeout_3595_ = lean_ctor_get(v_state_3449_, 3);
v_headerTimeout_3596_ = lean_ctor_get(v_state_3449_, 4);
v_response_3597_ = lean_ctor_get(v_state_3449_, 5);
v_respStream_3598_ = lean_ctor_get(v_state_3449_, 6);
v_requiresData_3599_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3600_ = lean_ctor_get(v_state_3449_, 7);
v_handlerDispatched_3601_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9 + 1);
v_pendingHead_3602_ = lean_ctor_get(v_state_3449_, 8);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_state_3449_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3604_ = v_state_3449_;
v_isShared_3605_ = v_isSharedCheck_3668_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_pendingHead_3602_);
lean_inc(v_expectData_3600_);
lean_inc(v_respStream_3598_);
lean_inc(v_response_3597_);
lean_inc(v_headerTimeout_3596_);
lean_inc(v_currentTimeout_3595_);
lean_inc(v_keepAliveTimeout_3594_);
lean_inc(v_requestStream_3593_);
lean_inc(v_machine_3592_);
lean_dec(v_state_3449_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3668_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___y_3607_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3620_ = lean_unsigned_to_nat(1u);
v___x_3621_ = lean_mk_empty_array_with_capacity(v___x_3620_);
v___x_3622_ = lean_array_push(v___x_3621_, v_val_3588_);
v___x_3623_ = lean_array_get_size(v___x_3622_);
v___x_3624_ = lean_unsigned_to_nat(0u);
v___x_3625_ = lean_nat_dec_eq(v___x_3623_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_object* v_reader_3626_; lean_object* v_writer_3627_; lean_object* v_config_3628_; lean_object* v_events_3629_; lean_object* v_error_3630_; lean_object* v_instant_3631_; uint8_t v_keepAlive_3632_; uint8_t v_forcedFlush_3633_; uint8_t v_pullBodyStalled_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3667_; 
v_reader_3626_ = lean_ctor_get(v_machine_3592_, 0);
v_writer_3627_ = lean_ctor_get(v_machine_3592_, 1);
v_config_3628_ = lean_ctor_get(v_machine_3592_, 2);
v_events_3629_ = lean_ctor_get(v_machine_3592_, 3);
v_error_3630_ = lean_ctor_get(v_machine_3592_, 4);
v_instant_3631_ = lean_ctor_get(v_machine_3592_, 5);
v_keepAlive_3632_ = lean_ctor_get_uint8(v_machine_3592_, sizeof(void*)*6);
v_forcedFlush_3633_ = lean_ctor_get_uint8(v_machine_3592_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3634_ = lean_ctor_get_uint8(v_machine_3592_, sizeof(void*)*6 + 2);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_machine_3592_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3636_ = v_machine_3592_;
v_isShared_3637_ = v_isSharedCheck_3667_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_instant_3631_);
lean_inc(v_error_3630_);
lean_inc(v_events_3629_);
lean_inc(v_config_3628_);
lean_inc(v_writer_3627_);
lean_inc(v_reader_3626_);
lean_dec(v_machine_3592_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3667_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___y_3639_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_3662_ = lean_nat_dec_lt(v___x_3624_, v___x_3623_);
if (v___x_3662_ == 0)
{
v___y_3639_ = v___x_3624_;
goto v___jp_3638_;
}
else
{
lean_object* v___f_3663_; size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___f_3663_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = lean_usize_of_nat(v___x_3623_);
lean_inc_ref(v___x_3622_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3661_, v___f_3663_, v___x_3622_, v___x_3664_, v___x_3665_, v___x_3624_);
v___y_3639_ = v___x_3666_;
goto v___jp_3638_;
}
v___jp_3638_:
{
lean_object* v_userData_3640_; lean_object* v_outputData_3641_; lean_object* v_state_3642_; lean_object* v_knownSize_3643_; lean_object* v_messageHead_3644_; uint8_t v_sentMessage_3645_; uint8_t v_userClosedBody_3646_; uint8_t v_omitBody_3647_; lean_object* v_userDataBytes_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3660_; 
v_userData_3640_ = lean_ctor_get(v_writer_3627_, 0);
v_outputData_3641_ = lean_ctor_get(v_writer_3627_, 1);
v_state_3642_ = lean_ctor_get(v_writer_3627_, 2);
v_knownSize_3643_ = lean_ctor_get(v_writer_3627_, 3);
v_messageHead_3644_ = lean_ctor_get(v_writer_3627_, 4);
v_sentMessage_3645_ = lean_ctor_get_uint8(v_writer_3627_, sizeof(void*)*6);
v_userClosedBody_3646_ = lean_ctor_get_uint8(v_writer_3627_, sizeof(void*)*6 + 1);
v_omitBody_3647_ = lean_ctor_get_uint8(v_writer_3627_, sizeof(void*)*6 + 2);
v_userDataBytes_3648_ = lean_ctor_get(v_writer_3627_, 5);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_writer_3627_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3650_ = v_writer_3627_;
v_isShared_3651_ = v_isSharedCheck_3660_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_userDataBytes_3648_);
lean_inc(v_messageHead_3644_);
lean_inc(v_knownSize_3643_);
lean_inc(v_state_3642_);
lean_inc(v_outputData_3641_);
lean_inc(v_userData_3640_);
lean_dec(v_writer_3627_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3660_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3652_ = l_Array_append___redArg(v_userData_3640_, v___x_3622_);
lean_dec_ref(v___x_3622_);
v___x_3653_ = lean_nat_add(v_userDataBytes_3648_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec(v_userDataBytes_3648_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 5, v___x_3653_);
lean_ctor_set(v___x_3650_, 0, v___x_3652_);
v___x_3655_ = v___x_3650_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_outputData_3641_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_state_3642_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v_knownSize_3643_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v_messageHead_3644_);
lean_ctor_set(v_reuseFailAlloc_3659_, 5, v___x_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3659_, sizeof(void*)*6, v_sentMessage_3645_);
lean_ctor_set_uint8(v_reuseFailAlloc_3659_, sizeof(void*)*6 + 1, v_userClosedBody_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3659_, sizeof(void*)*6 + 2, v_omitBody_3647_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 1, v___x_3655_);
v___x_3657_ = v___x_3636_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_reader_3626_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v_config_3628_);
lean_ctor_set(v_reuseFailAlloc_3658_, 3, v_events_3629_);
lean_ctor_set(v_reuseFailAlloc_3658_, 4, v_error_3630_);
lean_ctor_set(v_reuseFailAlloc_3658_, 5, v_instant_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*6, v_keepAlive_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*6 + 1, v_forcedFlush_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*6 + 2, v_pullBodyStalled_3634_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
v___y_3607_ = v___x_3657_;
goto v___jp_3606_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3622_);
v___y_3607_ = v_machine_3592_;
goto v___jp_3606_;
}
v___jp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___y_3607_);
v___x_3609_ = v___x_3604_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___y_3607_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_requestStream_3593_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_keepAliveTimeout_3594_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_currentTimeout_3595_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_headerTimeout_3596_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_response_3597_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_respStream_3598_);
lean_ctor_set(v_reuseFailAlloc_3619_, 7, v_expectData_3600_);
lean_ctor_set(v_reuseFailAlloc_3619_, 8, v_pendingHead_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, sizeof(void*)*9, v_requiresData_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, sizeof(void*)*9 + 1, v_handlerDispatched_3601_);
v___x_3609_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
uint8_t v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3610_ = 0;
v___x_3611_ = lean_box(v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3609_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3612_);
v___x_3614_ = v___x_3590_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3614_);
v___x_3616_ = v___x_3561_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
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
uint8_t v_x_3671_; 
lean_dec_ref(v_config_3447_);
lean_dec_ref(v_inst_3445_);
v_x_3671_ = lean_ctor_get_uint8(v_event_3448_, 0);
lean_dec_ref_known(v_event_3448_, 0);
if (v_x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec(v_handler_3446_);
lean_dec_ref(v_inst_3444_);
v___x_3672_ = lean_box(v_x_3671_);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v_state_3449_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
else
{
lean_object* v_machine_3676_; lean_object* v_requestStream_3677_; lean_object* v_keepAliveTimeout_3678_; lean_object* v_currentTimeout_3679_; lean_object* v_headerTimeout_3680_; lean_object* v_response_3681_; lean_object* v_respStream_3682_; uint8_t v_requiresData_3683_; lean_object* v_expectData_3684_; uint8_t v_handlerDispatched_3685_; lean_object* v_pendingHead_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3736_; 
v_machine_3676_ = lean_ctor_get(v_state_3449_, 0);
v_requestStream_3677_ = lean_ctor_get(v_state_3449_, 1);
v_keepAliveTimeout_3678_ = lean_ctor_get(v_state_3449_, 2);
v_currentTimeout_3679_ = lean_ctor_get(v_state_3449_, 3);
v_headerTimeout_3680_ = lean_ctor_get(v_state_3449_, 4);
v_response_3681_ = lean_ctor_get(v_state_3449_, 5);
v_respStream_3682_ = lean_ctor_get(v_state_3449_, 6);
v_requiresData_3683_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3684_ = lean_ctor_get(v_state_3449_, 7);
v_handlerDispatched_3685_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9 + 1);
v_pendingHead_3686_ = lean_ctor_get(v_state_3449_, 8);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_state_3449_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3688_ = v_state_3449_;
v_isShared_3689_ = v_isSharedCheck_3736_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_pendingHead_3686_);
lean_inc(v_expectData_3684_);
lean_inc(v_respStream_3682_);
lean_inc(v_response_3681_);
lean_inc(v_headerTimeout_3680_);
lean_inc(v_currentTimeout_3679_);
lean_inc(v_keepAliveTimeout_3678_);
lean_inc(v_requestStream_3677_);
lean_inc(v_machine_3676_);
lean_dec(v_state_3449_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3736_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v_fst_3692_; lean_object* v_snd_3693_; lean_object* v_reader_3694_; lean_object* v_writer_3695_; lean_object* v_config_3696_; lean_object* v_events_3697_; lean_object* v_error_3698_; lean_object* v_instant_3699_; uint8_t v_keepAlive_3700_; uint8_t v_forcedFlush_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3735_; 
v___x_3690_ = 0;
v___x_3691_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3690_, v_machine_3676_);
v_fst_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_fst_3692_);
v_snd_3693_ = lean_ctor_get(v___x_3691_, 1);
lean_inc(v_snd_3693_);
lean_dec_ref(v___x_3691_);
v_reader_3694_ = lean_ctor_get(v_fst_3692_, 0);
v_writer_3695_ = lean_ctor_get(v_fst_3692_, 1);
v_config_3696_ = lean_ctor_get(v_fst_3692_, 2);
v_events_3697_ = lean_ctor_get(v_fst_3692_, 3);
v_error_3698_ = lean_ctor_get(v_fst_3692_, 4);
v_instant_3699_ = lean_ctor_get(v_fst_3692_, 5);
v_keepAlive_3700_ = lean_ctor_get_uint8(v_fst_3692_, sizeof(void*)*6);
v_forcedFlush_3701_ = lean_ctor_get_uint8(v_fst_3692_, sizeof(void*)*6 + 1);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_fst_3692_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3703_ = v_fst_3692_;
v_isShared_3704_ = v_isSharedCheck_3735_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_instant_3699_);
lean_inc(v_error_3698_);
lean_inc(v_events_3697_);
lean_inc(v_config_3696_);
lean_inc(v_writer_3695_);
lean_inc(v_reader_3694_);
lean_dec(v_fst_3692_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3735_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___f_3705_; lean_object* v___f_3706_; uint8_t v___y_3708_; 
v___f_3705_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_3706_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_3706_, 0, v_inst_3444_);
lean_closure_set(v___f_3706_, 1, v_handler_3446_);
if (lean_obj_tag(v_snd_3693_) == 0)
{
uint8_t v_sentMessage_3731_; 
v_sentMessage_3731_ = lean_ctor_get_uint8(v_writer_3695_, sizeof(void*)*6);
if (v_sentMessage_3731_ == 0)
{
lean_object* v_state_3732_; 
v_state_3732_ = lean_ctor_get(v_reader_3694_, 0);
if (lean_obj_tag(v_state_3732_) == 2)
{
v___y_3708_ = v_x_3671_;
goto v___jp_3707_;
}
else
{
v___y_3708_ = v_sentMessage_3731_;
goto v___jp_3707_;
}
}
else
{
uint8_t v___x_3733_; 
v___x_3733_ = 0;
v___y_3708_ = v___x_3733_;
goto v___jp_3707_;
}
}
else
{
uint8_t v___x_3734_; 
v___x_3734_ = 0;
v___y_3708_ = v___x_3734_;
goto v___jp_3707_;
}
v___jp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3704_ == 0)
{
v___x_3710_ = v___x_3703_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_reader_3694_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_writer_3695_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_config_3696_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_events_3697_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_error_3698_);
lean_ctor_set(v_reuseFailAlloc_3730_, 5, v_instant_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3730_, sizeof(void*)*6, v_keepAlive_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3730_, sizeof(void*)*6 + 1, v_forcedFlush_3701_);
v___x_3710_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v_st_3712_; 
lean_ctor_set_uint8(v___x_3710_, sizeof(void*)*6 + 2, v___y_3708_);
lean_inc_ref(v_requestStream_3677_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v___x_3710_);
v_st_3712_ = v___x_3688_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_requestStream_3677_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_keepAliveTimeout_3678_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_currentTimeout_3679_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_headerTimeout_3680_);
lean_ctor_set(v_reuseFailAlloc_3729_, 5, v_response_3681_);
lean_ctor_set(v_reuseFailAlloc_3729_, 6, v_respStream_3682_);
lean_ctor_set(v_reuseFailAlloc_3729_, 7, v_expectData_3684_);
lean_ctor_set(v_reuseFailAlloc_3729_, 8, v_pendingHead_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, sizeof(void*)*9, v_requiresData_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, sizeof(void*)*9 + 1, v_handlerDispatched_3685_);
v_st_3712_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___f_3713_; 
lean_inc_ref(v_st_3712_);
v___f_3713_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3713_, 0, v_st_3712_);
if (lean_obj_tag(v_snd_3693_) == 1)
{
lean_object* v_val_3714_; uint8_t v_final_3715_; uint8_t v_incomplete_3716_; lean_object* v_chunk_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___x_3720_; lean_object* v___f_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v_st_3712_);
v_val_3714_ = lean_ctor_get(v_snd_3693_, 0);
lean_inc(v_val_3714_);
lean_dec_ref_known(v_snd_3693_, 1);
v_final_3715_ = lean_ctor_get_uint8(v_val_3714_, sizeof(void*)*1);
v_incomplete_3716_ = lean_ctor_get_uint8(v_val_3714_, sizeof(void*)*1 + 1);
v_chunk_3717_ = lean_ctor_get(v_val_3714_, 0);
lean_inc_ref(v_chunk_3717_);
lean_dec(v_val_3714_);
lean_inc_ref_n(v___f_3713_, 2);
v___f_3718_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3718_, 0, v___f_3713_);
lean_inc_ref_n(v_requestStream_3677_, 2);
v___f_3719_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3719_, 0, v_requestStream_3677_);
lean_closure_set(v___f_3719_, 1, v___f_3718_);
lean_closure_set(v___f_3719_, 2, v___f_3713_);
v___x_3720_ = lean_box(v_final_3715_);
v___f_3721_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_3721_, 0, v___x_3720_);
lean_closure_set(v___f_3721_, 1, v___f_3713_);
lean_closure_set(v___f_3721_, 2, v___f_3705_);
lean_closure_set(v___f_3721_, 3, v_requestStream_3677_);
lean_closure_set(v___f_3721_, 4, v___f_3719_);
v___x_3722_ = lean_unsigned_to_nat(0u);
v___x_3723_ = 0;
v___x_3724_ = l_Std_Http_Body_Stream_send(v_requestStream_3677_, v_chunk_3717_, v_incomplete_3716_);
v___x_3725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3722_, v___x_3723_, v___x_3724_, v___f_3706_);
v___x_3726_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3722_, v___x_3723_, v___x_3725_, v___f_3721_);
return v___x_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
lean_dec_ref(v___f_3713_);
lean_dec_ref(v___f_3706_);
lean_dec(v_snd_3693_);
lean_dec_ref(v_requestStream_3677_);
v___x_3727_ = lean_box(0);
v___x_3728_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3712_, v___x_3727_);
return v___x_3728_;
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
lean_object* v_x_3737_; 
v_x_3737_ = lean_ctor_get(v_event_3448_, 0);
lean_inc_ref(v_x_3737_);
lean_dec_ref_known(v_event_3448_, 1);
if (lean_obj_tag(v_x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v_onFailure_3739_; lean_object* v___f_3740_; lean_object* v___x_3741_; uint8_t v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v_config_3447_);
lean_dec_ref(v_inst_3445_);
v_a_3738_ = lean_ctor_get(v_x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v_x_3737_, 1);
v_onFailure_3739_ = lean_ctor_get(v_inst_3444_, 2);
lean_inc_ref(v_onFailure_3739_);
lean_dec_ref(v_inst_3444_);
v___f_3740_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3740_, 0, v_state_3449_);
v___x_3741_ = lean_unsigned_to_nat(0u);
v___x_3742_ = 0;
v___x_3743_ = lean_apply_3(v_onFailure_3739_, v_handler_3446_, v_a_3738_, lean_box(0));
v___x_3744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3741_, v___x_3742_, v___x_3743_, v___f_3740_);
return v___x_3744_;
}
else
{
lean_object* v_machine_3745_; lean_object* v_reader_3746_; lean_object* v_state_3747_; 
v_machine_3745_ = lean_ctor_get(v_state_3449_, 0);
lean_inc_ref(v_machine_3745_);
v_reader_3746_ = lean_ctor_get(v_machine_3745_, 0);
v_state_3747_ = lean_ctor_get(v_reader_3746_, 0);
if (lean_obj_tag(v_state_3747_) == 7)
{
lean_object* v_a_3748_; lean_object* v_requestStream_3749_; lean_object* v_keepAliveTimeout_3750_; lean_object* v_currentTimeout_3751_; lean_object* v_headerTimeout_3752_; lean_object* v_response_3753_; lean_object* v_respStream_3754_; uint8_t v_requiresData_3755_; lean_object* v_expectData_3756_; lean_object* v_pendingHead_3757_; lean_object* v_close_3758_; lean_object* v_isClosed_3759_; lean_object* v_body_3760_; lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___f_3763_; lean_object* v___f_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec_ref(v_config_3447_);
lean_dec(v_handler_3446_);
lean_dec_ref(v_inst_3444_);
v_a_3748_ = lean_ctor_get(v_x_3737_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v_x_3737_, 1);
v_requestStream_3749_ = lean_ctor_get(v_state_3449_, 1);
lean_inc_ref(v_requestStream_3749_);
v_keepAliveTimeout_3750_ = lean_ctor_get(v_state_3449_, 2);
lean_inc(v_keepAliveTimeout_3750_);
v_currentTimeout_3751_ = lean_ctor_get(v_state_3449_, 3);
lean_inc(v_currentTimeout_3751_);
v_headerTimeout_3752_ = lean_ctor_get(v_state_3449_, 4);
lean_inc(v_headerTimeout_3752_);
v_response_3753_ = lean_ctor_get(v_state_3449_, 5);
lean_inc_ref(v_response_3753_);
v_respStream_3754_ = lean_ctor_get(v_state_3449_, 6);
lean_inc(v_respStream_3754_);
v_requiresData_3755_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3756_ = lean_ctor_get(v_state_3449_, 7);
lean_inc(v_expectData_3756_);
v_pendingHead_3757_ = lean_ctor_get(v_state_3449_, 8);
lean_inc(v_pendingHead_3757_);
lean_dec_ref(v_state_3449_);
v_close_3758_ = lean_ctor_get(v_inst_3445_, 1);
lean_inc_ref(v_close_3758_);
v_isClosed_3759_ = lean_ctor_get(v_inst_3445_, 2);
lean_inc_ref(v_isClosed_3759_);
lean_dec_ref(v_inst_3445_);
v_body_3760_ = lean_ctor_get(v_a_3748_, 1);
lean_inc_n(v_body_3760_, 2);
lean_dec(v_a_3748_);
v___x_3761_ = lean_box(v_requiresData_3755_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3762_, 0, v_machine_3745_);
lean_closure_set(v___f_3762_, 1, v_requestStream_3749_);
lean_closure_set(v___f_3762_, 2, v_keepAliveTimeout_3750_);
lean_closure_set(v___f_3762_, 3, v_currentTimeout_3751_);
lean_closure_set(v___f_3762_, 4, v_headerTimeout_3752_);
lean_closure_set(v___f_3762_, 5, v_response_3753_);
lean_closure_set(v___f_3762_, 6, v_respStream_3754_);
lean_closure_set(v___f_3762_, 7, v___x_3761_);
lean_closure_set(v___f_3762_, 8, v_expectData_3756_);
lean_closure_set(v___f_3762_, 9, v_pendingHead_3757_);
lean_inc_ref(v___f_3762_);
v___f_3763_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3763_, 0, v___f_3762_);
v___f_3764_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3764_, 0, v_close_3758_);
lean_closure_set(v___f_3764_, 1, v_body_3760_);
lean_closure_set(v___f_3764_, 2, v___f_3763_);
lean_closure_set(v___f_3764_, 3, v___f_3762_);
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = 0;
v___x_3767_ = lean_apply_2(v_isClosed_3759_, v_body_3760_, lean_box(0));
v___x_3768_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3765_, v___x_3766_, v___x_3767_, v___f_3764_);
return v___x_3768_;
}
else
{
lean_object* v_a_3769_; lean_object* v_requestStream_3770_; lean_object* v_keepAliveTimeout_3771_; lean_object* v_currentTimeout_3772_; lean_object* v_headerTimeout_3773_; lean_object* v_response_3774_; uint8_t v_requiresData_3775_; lean_object* v_expectData_3776_; lean_object* v_pendingHead_3777_; uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___f_3783_; uint8_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___f_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_a_3769_ = lean_ctor_get(v_x_3737_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v_x_3737_, 1);
v_requestStream_3770_ = lean_ctor_get(v_state_3449_, 1);
lean_inc_ref(v_requestStream_3770_);
v_keepAliveTimeout_3771_ = lean_ctor_get(v_state_3449_, 2);
lean_inc(v_keepAliveTimeout_3771_);
v_currentTimeout_3772_ = lean_ctor_get(v_state_3449_, 3);
lean_inc(v_currentTimeout_3772_);
v_headerTimeout_3773_ = lean_ctor_get(v_state_3449_, 4);
lean_inc(v_headerTimeout_3773_);
v_response_3774_ = lean_ctor_get(v_state_3449_, 5);
lean_inc_ref(v_response_3774_);
v_requiresData_3775_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3776_ = lean_ctor_get(v_state_3449_, 7);
lean_inc(v_expectData_3776_);
v_pendingHead_3777_ = lean_ctor_get(v_state_3449_, 8);
lean_inc(v_pendingHead_3777_);
lean_dec_ref(v_state_3449_);
v___x_3778_ = 0;
v___x_3779_ = lean_box(v_requiresData_3775_);
v___x_3780_ = lean_box(v___x_3778_);
v___f_3781_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3781_, 0, v_requestStream_3770_);
lean_closure_set(v___f_3781_, 1, v_keepAliveTimeout_3771_);
lean_closure_set(v___f_3781_, 2, v_currentTimeout_3772_);
lean_closure_set(v___f_3781_, 3, v_headerTimeout_3773_);
lean_closure_set(v___f_3781_, 4, v_response_3774_);
lean_closure_set(v___f_3781_, 5, v___x_3779_);
lean_closure_set(v___f_3781_, 6, v_expectData_3776_);
lean_closure_set(v___f_3781_, 7, v___x_3780_);
lean_closure_set(v___f_3781_, 8, v_pendingHead_3777_);
v___f_3782_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3782_, 0, v___f_3781_);
v___f_3783_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3784_ = 1;
v___x_3785_ = lean_box(v___x_3778_);
v___x_3786_ = lean_box(v___x_3784_);
lean_inc_ref(v_inst_3445_);
lean_inc_ref(v___f_3782_);
v___f_3787_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3787_, 0, v___x_3785_);
lean_closure_set(v___f_3787_, 1, v___f_3782_);
lean_closure_set(v___f_3787_, 2, v___x_3786_);
lean_closure_set(v___f_3787_, 3, v_inst_3444_);
lean_closure_set(v___f_3787_, 4, v_handler_3446_);
lean_closure_set(v___f_3787_, 5, v_inst_3445_);
lean_closure_set(v___f_3787_, 6, v___f_3783_);
lean_closure_set(v___f_3787_, 7, v___f_3782_);
v___x_3788_ = lean_unsigned_to_nat(0u);
v___x_3789_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3445_, v_config_3447_, v_machine_3745_, v_a_3769_);
v___x_3790_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3788_, v___x_3778_, v___x_3789_, v___f_3787_);
return v___x_3790_;
}
}
}
case 4:
{
lean_object* v_onFailure_3791_; lean_object* v___f_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec_ref(v_config_3447_);
lean_dec_ref(v_inst_3445_);
v_onFailure_3791_ = lean_ctor_get(v_inst_3444_, 2);
lean_inc_ref(v_onFailure_3791_);
lean_dec_ref(v_inst_3444_);
v___f_3792_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3792_, 0, v_state_3449_);
v___x_3793_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = 0;
v___x_3796_ = lean_apply_3(v_onFailure_3791_, v_handler_3446_, v___x_3793_, lean_box(0));
v___x_3797_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3794_, v___x_3795_, v___x_3796_, v___f_3792_);
return v___x_3797_;
}
case 5:
{
lean_object* v_machine_3798_; lean_object* v_requestStream_3799_; lean_object* v_keepAliveTimeout_3800_; lean_object* v_currentTimeout_3801_; lean_object* v_headerTimeout_3802_; lean_object* v_response_3803_; lean_object* v_respStream_3804_; uint8_t v_requiresData_3805_; lean_object* v_expectData_3806_; lean_object* v_pendingHead_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v_config_3447_);
lean_dec(v_handler_3446_);
lean_dec_ref(v_inst_3445_);
lean_dec_ref(v_inst_3444_);
v_machine_3798_ = lean_ctor_get(v_state_3449_, 0);
v_requestStream_3799_ = lean_ctor_get(v_state_3449_, 1);
v_keepAliveTimeout_3800_ = lean_ctor_get(v_state_3449_, 2);
v_currentTimeout_3801_ = lean_ctor_get(v_state_3449_, 3);
v_headerTimeout_3802_ = lean_ctor_get(v_state_3449_, 4);
v_response_3803_ = lean_ctor_get(v_state_3449_, 5);
v_respStream_3804_ = lean_ctor_get(v_state_3449_, 6);
v_requiresData_3805_ = lean_ctor_get_uint8(v_state_3449_, sizeof(void*)*9);
v_expectData_3806_ = lean_ctor_get(v_state_3449_, 7);
v_pendingHead_3807_ = lean_ctor_get(v_state_3449_, 8);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_state_3449_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3809_ = v_state_3449_;
v_isShared_3810_ = v_isSharedCheck_3821_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_pendingHead_3807_);
lean_inc(v_expectData_3806_);
lean_inc(v_respStream_3804_);
lean_inc(v_response_3803_);
lean_inc(v_headerTimeout_3802_);
lean_inc(v_currentTimeout_3801_);
lean_inc(v_keepAliveTimeout_3800_);
lean_inc(v_requestStream_3799_);
lean_inc(v_machine_3798_);
lean_dec(v_state_3449_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3821_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; lean_object* v___x_3815_; 
v___x_3811_ = lean_box(55);
v___x_3812_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3798_, v___x_3811_);
v___x_3813_ = 0;
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3815_ = v___x_3809_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_requestStream_3799_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_keepAliveTimeout_3800_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_currentTimeout_3801_);
lean_ctor_set(v_reuseFailAlloc_3820_, 4, v_headerTimeout_3802_);
lean_ctor_set(v_reuseFailAlloc_3820_, 5, v_response_3803_);
lean_ctor_set(v_reuseFailAlloc_3820_, 6, v_respStream_3804_);
lean_ctor_set(v_reuseFailAlloc_3820_, 7, v_expectData_3806_);
lean_ctor_set(v_reuseFailAlloc_3820_, 8, v_pendingHead_3807_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*9, v_requiresData_3805_);
v___x_3815_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*9 + 1, v___x_3813_);
v___x_3816_ = lean_box(v___x_3813_);
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
return v___x_3819_;
}
}
}
default: 
{
uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec_ref(v_config_3447_);
lean_dec(v_handler_3446_);
lean_dec_ref(v_inst_3445_);
lean_dec_ref(v_inst_3444_);
v___x_3822_ = 1;
v___x_3823_ = lean_box(v___x_3822_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v_state_3449_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3444_ = stack[0].m_obj;
lean_object* v_inst_3445_ = stack[1].m_obj;
lean_object* v_handler_3446_ = stack[2].m_obj;
lean_object* v_config_3447_ = stack[3].m_obj;
lean_object* v_event_3448_ = stack[4].m_obj;
lean_object* v_state_3449_ = stack[5].m_obj;
lean_object* v_res_3827_;
v_res_3827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3444_, v_inst_3445_, v_handler_3446_, v_config_3447_, v_event_3448_, v_state_3449_);
stack->m_obj
 = v_res_3827_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3828_, lean_object* v_inst_3829_, lean_object* v_handler_3830_, lean_object* v_config_3831_, lean_object* v_event_3832_, lean_object* v_state_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3828_, v_inst_3829_, v_handler_3830_, v_config_3831_, v_event_3832_, v_state_3833_);
return v_res_3835_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3836_, lean_object* v_00_u03b2_3837_, lean_object* v_inst_3838_, lean_object* v_inst_3839_, lean_object* v_handler_3840_, lean_object* v_config_3841_, lean_object* v_event_3842_, lean_object* v_state_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3838_, v_inst_3839_, v_handler_3840_, v_config_3841_, v_event_3842_, v_state_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3838_ = stack[2].m_obj;
lean_object* v_inst_3839_ = stack[3].m_obj;
lean_object* v_handler_3840_ = stack[4].m_obj;
lean_object* v_config_3841_ = stack[5].m_obj;
lean_object* v_event_3842_ = stack[6].m_obj;
lean_object* v_state_3843_ = stack[7].m_obj;
lean_object* v_res_3846_;
v_res_3846_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_box(0), lean_box(0), v_inst_3838_, v_inst_3839_, v_handler_3840_, v_config_3841_, v_event_3842_, v_state_3843_);
stack->m_obj
 = v_res_3846_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3847_, lean_object* v_00_u03b2_3848_, lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_handler_3851_, lean_object* v_config_3852_, lean_object* v_event_3853_, lean_object* v_state_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3847_, v_00_u03b2_3848_, v_inst_3849_, v_inst_3850_, v_handler_3851_, v_config_3852_, v_event_3853_, v_state_3854_);
return v_res_3856_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3857_, uint8_t v_handlerDispatched_3858_, lean_object* v_keepAliveTimeout_3859_, lean_object* v_headerTimeout_3860_, lean_object* v_expectData_3861_, lean_object* v_respStream_3862_, lean_object* v_currentTimeout_3863_, lean_object* v_response_3864_, lean_object* v_socket_3865_, uint8_t v_requiresData_3866_, uint8_t v_sentMessage_3867_, lean_object* v_reader_3868_, uint8_t v_requestBodyInterested_3869_, lean_object* v_requestBody_3870_){
_start:
{
lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3884_; 
if (v_requiresData_3866_ == 0)
{
if (v_handlerDispatched_3858_ == 0)
{
goto v___jp_3887_;
}
else
{
if (lean_obj_tag(v_respStream_3862_) == 0)
{
if (v_sentMessage_3867_ == 0)
{
lean_object* v_state_3891_; 
v_state_3891_ = lean_ctor_get(v_reader_3868_, 0);
if (lean_obj_tag(v_state_3891_) == 2)
{
if (v_requestBodyInterested_3869_ == 0)
{
lean_dec(v_socket_3865_);
goto v___jp_3889_;
}
else
{
goto v___jp_3887_;
}
}
else
{
lean_dec(v_socket_3865_);
goto v___jp_3889_;
}
}
else
{
goto v___jp_3887_;
}
}
else
{
goto v___jp_3887_;
}
}
}
else
{
goto v___jp_3887_;
}
v___jp_3872_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3880_, 0, v___y_3874_);
lean_ctor_set(v___x_3880_, 1, v___y_3876_);
lean_ctor_set(v___x_3880_, 2, v___y_3879_);
lean_ctor_set(v___x_3880_, 3, v___y_3877_);
lean_ctor_set(v___x_3880_, 4, v_requestBody_3870_);
lean_ctor_set(v___x_3880_, 5, v___y_3878_);
lean_ctor_set(v___x_3880_, 6, v___y_3873_);
lean_ctor_set(v___x_3880_, 7, v___y_3875_);
lean_ctor_set(v___x_3880_, 8, v_connectionContext_3857_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
v___jp_3883_:
{
if (v_handlerDispatched_3858_ == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref(v_response_3864_);
v___x_3885_ = lean_box(0);
v___y_3873_ = v_keepAliveTimeout_3859_;
v___y_3874_ = v___y_3884_;
v___y_3875_ = v_headerTimeout_3860_;
v___y_3876_ = v_expectData_3861_;
v___y_3877_ = v_respStream_3862_;
v___y_3878_ = v_currentTimeout_3863_;
v___y_3879_ = v___x_3885_;
goto v___jp_3872_;
}
else
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_response_3864_);
v___y_3873_ = v_keepAliveTimeout_3859_;
v___y_3874_ = v___y_3884_;
v___y_3875_ = v_headerTimeout_3860_;
v___y_3876_ = v_expectData_3861_;
v___y_3877_ = v_respStream_3862_;
v___y_3878_ = v_currentTimeout_3863_;
v___y_3879_ = v___x_3886_;
goto v___jp_3872_;
}
}
v___jp_3887_:
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_socket_3865_);
v___y_3884_ = v___x_3888_;
goto v___jp_3883_;
}
v___jp_3889_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_box(0);
v___y_3884_ = v___x_3890_;
goto v___jp_3883_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_connectionContext_3857_ = stack[0].m_obj;
uint8_t v_handlerDispatched_3858_ = stack[1].m_num;
lean_object* v_keepAliveTimeout_3859_ = stack[2].m_obj;
lean_object* v_headerTimeout_3860_ = stack[3].m_obj;
lean_object* v_expectData_3861_ = stack[4].m_obj;
lean_object* v_respStream_3862_ = stack[5].m_obj;
lean_object* v_currentTimeout_3863_ = stack[6].m_obj;
lean_object* v_response_3864_ = stack[7].m_obj;
lean_object* v_socket_3865_ = stack[8].m_obj;
uint8_t v_requiresData_3866_ = stack[9].m_num;
uint8_t v_sentMessage_3867_ = stack[10].m_num;
lean_object* v_reader_3868_ = stack[11].m_obj;
uint8_t v_requestBodyInterested_3869_ = stack[12].m_num;
lean_object* v_requestBody_3870_ = stack[13].m_obj;
lean_object* v_res_3892_;
v_res_3892_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3857_, v_handlerDispatched_3858_, v_keepAliveTimeout_3859_, v_headerTimeout_3860_, v_expectData_3861_, v_respStream_3862_, v_currentTimeout_3863_, v_response_3864_, v_socket_3865_, v_requiresData_3866_, v_sentMessage_3867_, v_reader_3868_, v_requestBodyInterested_3869_, v_requestBody_3870_);
stack->m_obj
 = v_res_3892_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3893_, lean_object* v_handlerDispatched_3894_, lean_object* v_keepAliveTimeout_3895_, lean_object* v_headerTimeout_3896_, lean_object* v_expectData_3897_, lean_object* v_respStream_3898_, lean_object* v_currentTimeout_3899_, lean_object* v_response_3900_, lean_object* v_socket_3901_, lean_object* v_requiresData_3902_, lean_object* v_sentMessage_3903_, lean_object* v_reader_3904_, lean_object* v_requestBodyInterested_3905_, lean_object* v_requestBody_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v_handlerDispatched_boxed_3908_; uint8_t v_requiresData_boxed_3909_; uint8_t v_sentMessage_boxed_3910_; uint8_t v_requestBodyInterested_boxed_3911_; lean_object* v_res_3912_; 
v_handlerDispatched_boxed_3908_ = lean_unbox(v_handlerDispatched_3894_);
v_requiresData_boxed_3909_ = lean_unbox(v_requiresData_3902_);
v_sentMessage_boxed_3910_ = lean_unbox(v_sentMessage_3903_);
v_requestBodyInterested_boxed_3911_ = lean_unbox(v_requestBodyInterested_3905_);
v_res_3912_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3893_, v_handlerDispatched_boxed_3908_, v_keepAliveTimeout_3895_, v_headerTimeout_3896_, v_expectData_3897_, v_respStream_3898_, v_currentTimeout_3899_, v_response_3900_, v_socket_3901_, v_requiresData_boxed_3909_, v_sentMessage_boxed_3910_, v_reader_3904_, v_requestBodyInterested_boxed_3911_, v_requestBody_3906_);
lean_dec_ref(v_reader_3904_);
return v_res_3912_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3913_, lean_object* v_x_3914_){
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
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3913_ = stack[0].m_obj;
lean_object* v_x_3914_ = stack[1].m_obj;
lean_object* v_res_3927_;
v_res_3927_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3913_, v_x_3914_);
stack->m_obj
 = v_res_3927_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3928_, lean_object* v_x_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3928_, v_x_3929_);
return v_res_3931_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3936_, uint8_t v_handlerDispatched_3937_, lean_object* v_keepAliveTimeout_3938_, lean_object* v_headerTimeout_3939_, lean_object* v_expectData_3940_, lean_object* v_respStream_3941_, lean_object* v_currentTimeout_3942_, lean_object* v_response_3943_, lean_object* v_socket_3944_, uint8_t v_requiresData_3945_, uint8_t v_sentMessage_3946_, lean_object* v_reader_3947_, uint8_t v_pullBodyStalled_3948_, uint8_t v_requestBodyOpen_3949_, lean_object* v_requestStream_3950_, uint8_t v_requestBodyInterested_3951_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; lean_object* v___f_3958_; uint8_t v___y_3960_; 
v___x_3953_ = lean_box(v_handlerDispatched_3937_);
v___x_3954_ = lean_box(v_requiresData_3945_);
v___x_3955_ = lean_box(v_sentMessage_3946_);
v___x_3956_ = lean_box(v_requestBodyInterested_3951_);
lean_inc_ref(v_reader_3947_);
v___f_3957_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3957_, 0, v_connectionContext_3936_);
lean_closure_set(v___f_3957_, 1, v___x_3953_);
lean_closure_set(v___f_3957_, 2, v_keepAliveTimeout_3938_);
lean_closure_set(v___f_3957_, 3, v_headerTimeout_3939_);
lean_closure_set(v___f_3957_, 4, v_expectData_3940_);
lean_closure_set(v___f_3957_, 5, v_respStream_3941_);
lean_closure_set(v___f_3957_, 6, v_currentTimeout_3942_);
lean_closure_set(v___f_3957_, 7, v_response_3943_);
lean_closure_set(v___f_3957_, 8, v_socket_3944_);
lean_closure_set(v___f_3957_, 9, v___x_3954_);
lean_closure_set(v___f_3957_, 10, v___x_3955_);
lean_closure_set(v___f_3957_, 11, v_reader_3947_);
lean_closure_set(v___f_3957_, 12, v___x_3956_);
v___f_3958_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3958_, 0, v___f_3957_);
if (v_sentMessage_3946_ == 0)
{
lean_object* v_state_3964_; 
v_state_3964_ = lean_ctor_get(v_reader_3947_, 0);
lean_inc(v_state_3964_);
lean_dec_ref(v_reader_3947_);
if (lean_obj_tag(v_state_3964_) == 2)
{
lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3975_; 
v_isSharedCheck_3975_ = !lean_is_exclusive(v_state_3964_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; 
v_unused_3976_ = lean_ctor_get(v_state_3964_, 0);
lean_dec(v_unused_3976_);
v___x_3966_ = v_state_3964_;
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
else
{
lean_dec(v_state_3964_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
if (v_pullBodyStalled_3948_ == 0)
{
if (v_requestBodyOpen_3949_ == 0)
{
lean_del_object(v___x_3966_);
lean_dec_ref(v_requestStream_3950_);
v___y_3960_ = v_requestBodyOpen_3949_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 1);
lean_ctor_set(v___x_3966_, 0, v_requestStream_3950_);
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_requestStream_3950_);
v___x_3969_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3970_, v_pullBodyStalled_3948_, v___x_3972_, v___f_3958_);
return v___x_3973_;
}
}
}
else
{
lean_del_object(v___x_3966_);
lean_dec_ref(v_requestStream_3950_);
v___y_3960_ = v_sentMessage_3946_;
goto v___jp_3959_;
}
}
}
else
{
lean_dec(v_state_3964_);
lean_dec_ref(v_requestStream_3950_);
v___y_3960_ = v_sentMessage_3946_;
goto v___jp_3959_;
}
}
else
{
uint8_t v___x_3977_; 
lean_dec_ref(v_requestStream_3950_);
lean_dec_ref(v_reader_3947_);
v___x_3977_ = 0;
v___y_3960_ = v___x_3977_;
goto v___jp_3959_;
}
v___jp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3963_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3961_, v___y_3960_, v___x_3962_, v___f_3958_);
return v___x_3963_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_connectionContext_3936_ = stack[0].m_obj;
uint8_t v_handlerDispatched_3937_ = stack[1].m_num;
lean_object* v_keepAliveTimeout_3938_ = stack[2].m_obj;
lean_object* v_headerTimeout_3939_ = stack[3].m_obj;
lean_object* v_expectData_3940_ = stack[4].m_obj;
lean_object* v_respStream_3941_ = stack[5].m_obj;
lean_object* v_currentTimeout_3942_ = stack[6].m_obj;
lean_object* v_response_3943_ = stack[7].m_obj;
lean_object* v_socket_3944_ = stack[8].m_obj;
uint8_t v_requiresData_3945_ = stack[9].m_num;
uint8_t v_sentMessage_3946_ = stack[10].m_num;
lean_object* v_reader_3947_ = stack[11].m_obj;
uint8_t v_pullBodyStalled_3948_ = stack[12].m_num;
uint8_t v_requestBodyOpen_3949_ = stack[13].m_num;
lean_object* v_requestStream_3950_ = stack[14].m_obj;
uint8_t v_requestBodyInterested_3951_ = stack[15].m_num;
lean_object* v_res_3978_;
v_res_3978_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3936_, v_handlerDispatched_3937_, v_keepAliveTimeout_3938_, v_headerTimeout_3939_, v_expectData_3940_, v_respStream_3941_, v_currentTimeout_3942_, v_response_3943_, v_socket_3944_, v_requiresData_3945_, v_sentMessage_3946_, v_reader_3947_, v_pullBodyStalled_3948_, v_requestBodyOpen_3949_, v_requestStream_3950_, v_requestBodyInterested_3951_);
stack->m_obj
 = v_res_3978_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3979_ = _args[0];
lean_object* v_handlerDispatched_3980_ = _args[1];
lean_object* v_keepAliveTimeout_3981_ = _args[2];
lean_object* v_headerTimeout_3982_ = _args[3];
lean_object* v_expectData_3983_ = _args[4];
lean_object* v_respStream_3984_ = _args[5];
lean_object* v_currentTimeout_3985_ = _args[6];
lean_object* v_response_3986_ = _args[7];
lean_object* v_socket_3987_ = _args[8];
lean_object* v_requiresData_3988_ = _args[9];
lean_object* v_sentMessage_3989_ = _args[10];
lean_object* v_reader_3990_ = _args[11];
lean_object* v_pullBodyStalled_3991_ = _args[12];
lean_object* v_requestBodyOpen_3992_ = _args[13];
lean_object* v_requestStream_3993_ = _args[14];
lean_object* v_requestBodyInterested_3994_ = _args[15];
lean_object* v___y_3995_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3996_; uint8_t v_requiresData_boxed_3997_; uint8_t v_sentMessage_boxed_3998_; uint8_t v_pullBodyStalled_boxed_3999_; uint8_t v_requestBodyOpen_boxed_4000_; uint8_t v_requestBodyInterested_boxed_4001_; lean_object* v_res_4002_; 
v_handlerDispatched_boxed_3996_ = lean_unbox(v_handlerDispatched_3980_);
v_requiresData_boxed_3997_ = lean_unbox(v_requiresData_3988_);
v_sentMessage_boxed_3998_ = lean_unbox(v_sentMessage_3989_);
v_pullBodyStalled_boxed_3999_ = lean_unbox(v_pullBodyStalled_3991_);
v_requestBodyOpen_boxed_4000_ = lean_unbox(v_requestBodyOpen_3992_);
v_requestBodyInterested_boxed_4001_ = lean_unbox(v_requestBodyInterested_3994_);
v_res_4002_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3979_, v_handlerDispatched_boxed_3996_, v_keepAliveTimeout_3981_, v_headerTimeout_3982_, v_expectData_3983_, v_respStream_3984_, v_currentTimeout_3985_, v_response_3986_, v_socket_3987_, v_requiresData_boxed_3997_, v_sentMessage_boxed_3998_, v_reader_3990_, v_pullBodyStalled_boxed_3999_, v_requestBodyOpen_boxed_4000_, v_requestStream_3993_, v_requestBodyInterested_boxed_4001_);
return v_res_4002_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_4003_, lean_object* v_x_4004_){
_start:
{
if (lean_obj_tag(v_x_4004_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v___f_4003_);
v_a_4006_ = lean_ctor_get(v_x_4004_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_x_4004_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4008_ = v_x_4004_;
v_isShared_4009_ = v_isSharedCheck_4014_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v_x_4004_);
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
lean_object* v_a_4015_; lean_object* v___x_4016_; 
v_a_4015_ = lean_ctor_get(v_x_4004_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v_x_4004_, 1);
v___x_4016_ = lean_apply_2(v___f_4003_, v_a_4015_, lean_box(0));
return v___x_4016_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4003_ = stack[0].m_obj;
lean_object* v_x_4004_ = stack[1].m_obj;
lean_object* v_res_4017_;
v_res_4017_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_4003_, v_x_4004_);
stack->m_obj
 = v_res_4017_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_4018_, v_x_4019_);
return v_res_4021_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_4022_, uint8_t v_handlerDispatched_4023_, lean_object* v_keepAliveTimeout_4024_, lean_object* v_headerTimeout_4025_, lean_object* v_expectData_4026_, lean_object* v_respStream_4027_, lean_object* v_currentTimeout_4028_, lean_object* v_response_4029_, lean_object* v_socket_4030_, uint8_t v_requiresData_4031_, uint8_t v_sentMessage_4032_, lean_object* v_reader_4033_, uint8_t v_pullBodyStalled_4034_, lean_object* v_requestStream_4035_, uint8_t v_requestBodyOpen_4036_){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___f_4043_; lean_object* v___f_4044_; uint8_t v___y_4046_; 
v___x_4038_ = lean_box(v_handlerDispatched_4023_);
v___x_4039_ = lean_box(v_requiresData_4031_);
v___x_4040_ = lean_box(v_sentMessage_4032_);
v___x_4041_ = lean_box(v_pullBodyStalled_4034_);
v___x_4042_ = lean_box(v_requestBodyOpen_4036_);
lean_inc_ref(v_requestStream_4035_);
lean_inc_ref(v_reader_4033_);
v___f_4043_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_4043_, 0, v_connectionContext_4022_);
lean_closure_set(v___f_4043_, 1, v___x_4038_);
lean_closure_set(v___f_4043_, 2, v_keepAliveTimeout_4024_);
lean_closure_set(v___f_4043_, 3, v_headerTimeout_4025_);
lean_closure_set(v___f_4043_, 4, v_expectData_4026_);
lean_closure_set(v___f_4043_, 5, v_respStream_4027_);
lean_closure_set(v___f_4043_, 6, v_currentTimeout_4028_);
lean_closure_set(v___f_4043_, 7, v_response_4029_);
lean_closure_set(v___f_4043_, 8, v_socket_4030_);
lean_closure_set(v___f_4043_, 9, v___x_4039_);
lean_closure_set(v___f_4043_, 10, v___x_4040_);
lean_closure_set(v___f_4043_, 11, v_reader_4033_);
lean_closure_set(v___f_4043_, 12, v___x_4041_);
lean_closure_set(v___f_4043_, 13, v___x_4042_);
lean_closure_set(v___f_4043_, 14, v_requestStream_4035_);
v___f_4044_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4044_, 0, v___f_4043_);
if (v_sentMessage_4032_ == 0)
{
lean_object* v_state_4052_; 
v_state_4052_ = lean_ctor_get(v_reader_4033_, 0);
lean_inc(v_state_4052_);
lean_dec_ref(v_reader_4033_);
if (lean_obj_tag(v_state_4052_) == 2)
{
lean_dec_ref_known(v_state_4052_, 1);
if (v_requestBodyOpen_4036_ == 0)
{
lean_dec_ref(v_requestStream_4035_);
v___y_4046_ = v_requestBodyOpen_4036_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_4035_);
v___x_4055_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4053_, v_sentMessage_4032_, v___x_4054_, v___f_4044_);
return v___x_4055_;
}
}
else
{
lean_dec(v_state_4052_);
lean_dec_ref(v_requestStream_4035_);
v___y_4046_ = v_sentMessage_4032_;
goto v___jp_4045_;
}
}
else
{
uint8_t v___x_4056_; 
lean_dec_ref(v_requestStream_4035_);
lean_dec_ref(v_reader_4033_);
v___x_4056_ = 0;
v___y_4046_ = v___x_4056_;
goto v___jp_4045_;
}
v___jp_4045_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4047_ = lean_unsigned_to_nat(0u);
v___x_4048_ = lean_box(v___y_4046_);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
v___x_4051_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4047_, v___y_4046_, v___x_4050_, v___f_4044_);
return v___x_4051_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_connectionContext_4022_ = stack[0].m_obj;
uint8_t v_handlerDispatched_4023_ = stack[1].m_num;
lean_object* v_keepAliveTimeout_4024_ = stack[2].m_obj;
lean_object* v_headerTimeout_4025_ = stack[3].m_obj;
lean_object* v_expectData_4026_ = stack[4].m_obj;
lean_object* v_respStream_4027_ = stack[5].m_obj;
lean_object* v_currentTimeout_4028_ = stack[6].m_obj;
lean_object* v_response_4029_ = stack[7].m_obj;
lean_object* v_socket_4030_ = stack[8].m_obj;
uint8_t v_requiresData_4031_ = stack[9].m_num;
uint8_t v_sentMessage_4032_ = stack[10].m_num;
lean_object* v_reader_4033_ = stack[11].m_obj;
uint8_t v_pullBodyStalled_4034_ = stack[12].m_num;
lean_object* v_requestStream_4035_ = stack[13].m_obj;
uint8_t v_requestBodyOpen_4036_ = stack[14].m_num;
lean_object* v_res_4057_;
v_res_4057_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_4022_, v_handlerDispatched_4023_, v_keepAliveTimeout_4024_, v_headerTimeout_4025_, v_expectData_4026_, v_respStream_4027_, v_currentTimeout_4028_, v_response_4029_, v_socket_4030_, v_requiresData_4031_, v_sentMessage_4032_, v_reader_4033_, v_pullBodyStalled_4034_, v_requestStream_4035_, v_requestBodyOpen_4036_);
stack->m_obj
 = v_res_4057_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_4058_, lean_object* v_handlerDispatched_4059_, lean_object* v_keepAliveTimeout_4060_, lean_object* v_headerTimeout_4061_, lean_object* v_expectData_4062_, lean_object* v_respStream_4063_, lean_object* v_currentTimeout_4064_, lean_object* v_response_4065_, lean_object* v_socket_4066_, lean_object* v_requiresData_4067_, lean_object* v_sentMessage_4068_, lean_object* v_reader_4069_, lean_object* v_pullBodyStalled_4070_, lean_object* v_requestStream_4071_, lean_object* v_requestBodyOpen_4072_, lean_object* v___y_4073_){
_start:
{
uint8_t v_handlerDispatched_boxed_4074_; uint8_t v_requiresData_boxed_4075_; uint8_t v_sentMessage_boxed_4076_; uint8_t v_pullBodyStalled_boxed_4077_; uint8_t v_requestBodyOpen_boxed_4078_; lean_object* v_res_4079_; 
v_handlerDispatched_boxed_4074_ = lean_unbox(v_handlerDispatched_4059_);
v_requiresData_boxed_4075_ = lean_unbox(v_requiresData_4067_);
v_sentMessage_boxed_4076_ = lean_unbox(v_sentMessage_4068_);
v_pullBodyStalled_boxed_4077_ = lean_unbox(v_pullBodyStalled_4070_);
v_requestBodyOpen_boxed_4078_ = lean_unbox(v_requestBodyOpen_4072_);
v_res_4079_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_4058_, v_handlerDispatched_boxed_4074_, v_keepAliveTimeout_4060_, v_headerTimeout_4061_, v_expectData_4062_, v_respStream_4063_, v_currentTimeout_4064_, v_response_4065_, v_socket_4066_, v_requiresData_boxed_4075_, v_sentMessage_boxed_4076_, v_reader_4069_, v_pullBodyStalled_boxed_4077_, v_requestStream_4071_, v_requestBodyOpen_boxed_4078_);
return v_res_4079_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_4080_, lean_object* v___f_4081_, uint8_t v___x_4082_, lean_object* v_x_4083_){
_start:
{
uint8_t v___y_4086_; 
if (lean_obj_tag(v_x_4083_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4100_; 
lean_dec_ref(v___f_4081_);
v_a_4092_ = lean_ctor_get(v_x_4083_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_x_4083_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4094_ = v_x_4083_;
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v_x_4083_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
}
else
{
lean_object* v_a_4101_; uint8_t v___x_4102_; 
v_a_4101_ = lean_ctor_get(v_x_4083_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v_x_4083_, 1);
v___x_4102_ = lean_unbox(v_a_4101_);
lean_dec(v_a_4101_);
if (v___x_4102_ == 0)
{
v___y_4086_ = v___x_4082_;
goto v___jp_4085_;
}
else
{
v___y_4086_ = v_sentMessage_4080_;
goto v___jp_4085_;
}
}
v___jp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = lean_box(v___y_4086_);
v___x_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
v___x_4091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4087_, v_sentMessage_4080_, v___x_4090_, v___f_4081_);
return v___x_4091_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_sentMessage_4080_ = stack[0].m_num;
lean_object* v___f_4081_ = stack[1].m_obj;
uint8_t v___x_4082_ = stack[2].m_num;
lean_object* v_x_4083_ = stack[3].m_obj;
lean_object* v_res_4103_;
v_res_4103_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_4080_, v___f_4081_, v___x_4082_, v_x_4083_);
stack->m_obj
 = v_res_4103_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4104_, lean_object* v___f_4105_, lean_object* v___x_4106_, lean_object* v_x_4107_, lean_object* v___y_4108_){
_start:
{
uint8_t v_sentMessage_boxed_4109_; uint8_t v___x_2997__boxed_4110_; lean_object* v_res_4111_; 
v_sentMessage_boxed_4109_ = lean_unbox(v_sentMessage_4104_);
v___x_2997__boxed_4110_ = lean_unbox(v___x_4106_);
v_res_4111_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4109_, v___f_4105_, v___x_2997__boxed_4110_, v_x_4107_);
return v_res_4111_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___f_4112_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4113_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4114_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4115_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4115_, 0, lean_box(0));
lean_closure_set(v___x_4115_, 1, lean_box(0));
lean_closure_set(v___x_4115_, 2, v___x_4114_);
lean_closure_set(v___x_4115_, 3, lean_box(0));
lean_closure_set(v___x_4115_, 4, lean_box(0));
lean_closure_set(v___x_4115_, 5, v___x_4113_);
lean_closure_set(v___x_4115_, 6, v___f_4112_);
return v___x_4115_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4116_, lean_object* v_connectionContext_4117_, lean_object* v_state_4118_){
_start:
{
lean_object* v_machine_4120_; lean_object* v_writer_4121_; lean_object* v_requestStream_4122_; lean_object* v_keepAliveTimeout_4123_; lean_object* v_currentTimeout_4124_; lean_object* v_headerTimeout_4125_; lean_object* v_response_4126_; lean_object* v_respStream_4127_; uint8_t v_requiresData_4128_; lean_object* v_expectData_4129_; uint8_t v_handlerDispatched_4130_; lean_object* v_reader_4131_; uint8_t v_pullBodyStalled_4132_; uint8_t v_sentMessage_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___f_4138_; lean_object* v___f_4139_; uint8_t v___y_4141_; 
v_machine_4120_ = lean_ctor_get(v_state_4118_, 0);
lean_inc_ref(v_machine_4120_);
v_writer_4121_ = lean_ctor_get(v_machine_4120_, 1);
lean_inc_ref(v_writer_4121_);
v_requestStream_4122_ = lean_ctor_get(v_state_4118_, 1);
lean_inc_ref_n(v_requestStream_4122_, 2);
v_keepAliveTimeout_4123_ = lean_ctor_get(v_state_4118_, 2);
lean_inc(v_keepAliveTimeout_4123_);
v_currentTimeout_4124_ = lean_ctor_get(v_state_4118_, 3);
lean_inc(v_currentTimeout_4124_);
v_headerTimeout_4125_ = lean_ctor_get(v_state_4118_, 4);
lean_inc(v_headerTimeout_4125_);
v_response_4126_ = lean_ctor_get(v_state_4118_, 5);
lean_inc_ref(v_response_4126_);
v_respStream_4127_ = lean_ctor_get(v_state_4118_, 6);
lean_inc(v_respStream_4127_);
v_requiresData_4128_ = lean_ctor_get_uint8(v_state_4118_, sizeof(void*)*9);
v_expectData_4129_ = lean_ctor_get(v_state_4118_, 7);
lean_inc(v_expectData_4129_);
v_handlerDispatched_4130_ = lean_ctor_get_uint8(v_state_4118_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4118_);
v_reader_4131_ = lean_ctor_get(v_machine_4120_, 0);
lean_inc_ref_n(v_reader_4131_, 2);
v_pullBodyStalled_4132_ = lean_ctor_get_uint8(v_machine_4120_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4120_);
v_sentMessage_4133_ = lean_ctor_get_uint8(v_writer_4121_, sizeof(void*)*6);
lean_dec_ref(v_writer_4121_);
v___x_4134_ = lean_box(v_handlerDispatched_4130_);
v___x_4135_ = lean_box(v_requiresData_4128_);
v___x_4136_ = lean_box(v_sentMessage_4133_);
v___x_4137_ = lean_box(v_pullBodyStalled_4132_);
v___f_4138_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4138_, 0, v_connectionContext_4117_);
lean_closure_set(v___f_4138_, 1, v___x_4134_);
lean_closure_set(v___f_4138_, 2, v_keepAliveTimeout_4123_);
lean_closure_set(v___f_4138_, 3, v_headerTimeout_4125_);
lean_closure_set(v___f_4138_, 4, v_expectData_4129_);
lean_closure_set(v___f_4138_, 5, v_respStream_4127_);
lean_closure_set(v___f_4138_, 6, v_currentTimeout_4124_);
lean_closure_set(v___f_4138_, 7, v_response_4126_);
lean_closure_set(v___f_4138_, 8, v_socket_4116_);
lean_closure_set(v___f_4138_, 9, v___x_4135_);
lean_closure_set(v___f_4138_, 10, v___x_4136_);
lean_closure_set(v___f_4138_, 11, v_reader_4131_);
lean_closure_set(v___f_4138_, 12, v___x_4137_);
lean_closure_set(v___f_4138_, 13, v_requestStream_4122_);
v___f_4139_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4139_, 0, v___f_4138_);
if (v_sentMessage_4133_ == 0)
{
lean_object* v_state_4147_; 
v_state_4147_ = lean_ctor_get(v_reader_4131_, 0);
lean_inc(v_state_4147_);
lean_dec_ref(v_reader_4131_);
if (lean_obj_tag(v_state_4147_) == 2)
{
uint8_t v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___f_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___f_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; lean_object* v___x_2542__overap_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_dec_ref_known(v_state_4147_, 1);
v___x_4148_ = 1;
v___x_4149_ = lean_box(v_sentMessage_4133_);
v___x_4150_ = lean_box(v___x_4148_);
v___f_4151_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4151_, 0, v___x_4149_);
lean_closure_set(v___f_4151_, 1, v___f_4139_);
lean_closure_set(v___f_4151_, 2, v___x_4150_);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4154_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4155_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4156_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2542__overap_4157_ = l_Std_Mutex_atomically___redArg(v___x_4153_, v___f_4154_, v___f_4155_, v_requestStream_4122_, v___x_4156_);
v___x_4158_ = lean_apply_1(v___x_2542__overap_4157_, lean_box(0));
v___x_4159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4152_, v_sentMessage_4133_, v___x_4158_, v___f_4151_);
return v___x_4159_;
}
else
{
lean_dec(v_state_4147_);
lean_dec_ref(v_requestStream_4122_);
v___y_4141_ = v_sentMessage_4133_;
goto v___jp_4140_;
}
}
else
{
uint8_t v___x_4160_; 
lean_dec_ref(v_reader_4131_);
lean_dec_ref(v_requestStream_4122_);
v___x_4160_ = 0;
v___y_4141_ = v___x_4160_;
goto v___jp_4140_;
}
v___jp_4140_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4142_ = lean_unsigned_to_nat(0u);
v___x_4143_ = lean_box(v___y_4141_);
v___x_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v___x_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
v___x_4146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4142_, v___y_4141_, v___x_4145_, v___f_4139_);
return v___x_4146_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_4116_ = stack[0].m_obj;
lean_object* v_connectionContext_4117_ = stack[1].m_obj;
lean_object* v_state_4118_ = stack[2].m_obj;
lean_object* v_res_4161_;
v_res_4161_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4116_, v_connectionContext_4117_, v_state_4118_);
stack->m_obj
 = v_res_4161_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4162_, lean_object* v_connectionContext_4163_, lean_object* v_state_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4162_, v_connectionContext_4163_, v_state_4164_);
return v_res_4166_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4167_, lean_object* v_00_u03b2_4168_, lean_object* v_inst_4169_, lean_object* v_socket_4170_, lean_object* v_connectionContext_4171_, lean_object* v_state_4172_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4170_, v_connectionContext_4171_, v_state_4172_);
return v___x_4174_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4169_ = stack[2].m_obj;
lean_object* v_socket_4170_ = stack[3].m_obj;
lean_object* v_connectionContext_4171_ = stack[4].m_obj;
lean_object* v_state_4172_ = stack[5].m_obj;
lean_object* v_res_4175_;
v_res_4175_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_box(0), lean_box(0), v_inst_4169_, v_socket_4170_, v_connectionContext_4171_, v_state_4172_);
stack->m_obj
 = v_res_4175_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4176_, lean_object* v_00_u03b2_4177_, lean_object* v_inst_4178_, lean_object* v_socket_4179_, lean_object* v_connectionContext_4180_, lean_object* v_state_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4176_, v_00_u03b2_4177_, v_inst_4178_, v_socket_4179_, v_connectionContext_4180_, v_state_4181_);
lean_dec_ref(v_inst_4178_);
return v_res_4183_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4184_){
_start:
{
if (lean_obj_tag(v_x_4184_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4194_; 
v_a_4186_ = lean_ctor_get(v_x_4184_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_x_4184_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4188_ = v_x_4184_;
v_isShared_4189_ = v_isSharedCheck_4194_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v_x_4184_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4194_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4204_; 
v_a_4195_ = lean_ctor_get(v_x_4184_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_x_4184_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4197_ = v_x_4184_;
v_isShared_4198_ = v_isSharedCheck_4204_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v_x_4184_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4204_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4199_, 0, v_a_4195_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4199_);
v___x_4201_ = v___x_4197_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4199_);
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
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4184_ = stack[0].m_obj;
lean_object* v_res_4205_;
v_res_4205_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4184_);
stack->m_obj
 = v_res_4205_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4206_);
return v_res_4208_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4213_){
_start:
{
if (lean_obj_tag(v_x_4213_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4223_; 
v_a_4215_ = lean_ctor_get(v_x_4213_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_x_4213_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4217_ = v_x_4213_;
v_isShared_4218_ = v_isSharedCheck_4223_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v_x_4213_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4223_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
return v___x_4221_;
}
}
}
else
{
lean_object* v___x_4224_; 
lean_dec_ref_known(v_x_4213_, 1);
v___x_4224_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_4224_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4213_ = stack[0].m_obj;
lean_object* v_res_4225_;
v_res_4225_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4213_);
stack->m_obj
 = v_res_4225_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4226_);
return v_res_4228_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_4229_, lean_object* v_handler_4230_, lean_object* v___f_4231_, lean_object* v_x_4232_){
_start:
{
if (lean_obj_tag(v_x_4232_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_a_4234_ = lean_ctor_get(v_x_4232_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v_x_4232_, 1);
v___x_4235_ = lean_unsigned_to_nat(0u);
v___x_4236_ = 0;
v___x_4237_ = lean_apply_3(v_onFailure_4229_, v_handler_4230_, v_a_4234_, lean_box(0));
v___x_4238_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4235_, v___x_4236_, v___x_4237_, v___f_4231_);
return v___x_4238_;
}
else
{
lean_object* v___x_4239_; 
lean_dec_ref(v___f_4231_);
lean_dec(v_handler_4230_);
lean_dec_ref(v_onFailure_4229_);
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v_x_4232_);
return v___x_4239_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_onFailure_4229_ = stack[0].m_obj;
lean_object* v_handler_4230_ = stack[1].m_obj;
lean_object* v___f_4231_ = stack[2].m_obj;
lean_object* v_x_4232_ = stack[3].m_obj;
lean_object* v_res_4240_;
v_res_4240_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_4229_, v_handler_4230_, v___f_4231_, v_x_4232_);
stack->m_obj
 = v_res_4240_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_4241_, lean_object* v_handler_4242_, lean_object* v___f_4243_, lean_object* v_x_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_4241_, v_handler_4242_, v___f_4243_, v_x_4244_);
return v_res_4246_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4247_){
_start:
{
if (lean_obj_tag(v_x_4247_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4257_; 
v_a_4249_ = lean_ctor_get(v_x_4247_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_x_4247_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4251_ = v_x_4247_;
v_isShared_4252_ = v_isSharedCheck_4257_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v_x_4247_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4257_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v___x_4255_; 
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4276_; 
v_a_4258_ = lean_ctor_get(v_x_4247_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_x_4247_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4260_ = v_x_4247_;
v_isShared_4261_ = v_isSharedCheck_4276_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v_x_4247_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4276_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v_snd_4262_; uint8_t v___x_4263_; 
v_snd_4262_ = lean_ctor_get(v_a_4258_, 1);
v___x_4263_ = lean_unbox(v_snd_4262_);
if (v___x_4263_ == 0)
{
lean_object* v_fst_4264_; lean_object* v___x_4265_; lean_object* v___x_4267_; 
v_fst_4264_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_fst_4264_);
lean_dec(v_a_4258_);
v___x_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4265_, 0, v_fst_4264_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4265_);
v___x_4267_ = v___x_4260_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
return v___x_4268_;
}
}
else
{
lean_object* v_fst_4270_; lean_object* v___x_4271_; lean_object* v___x_4273_; 
v_fst_4270_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_fst_4270_);
lean_dec(v_a_4258_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_fst_4270_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4271_);
v___x_4273_ = v___x_4260_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4271_);
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
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4247_ = stack[0].m_obj;
lean_object* v_res_4277_;
v_res_4277_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4247_);
stack->m_obj
 = v_res_4277_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4278_);
return v_res_4280_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4281_, lean_object* v_socket_4282_, lean_object* v_____r_4283_){
_start:
{
lean_object* v_val_4286_; lean_object* v_close_4288_; lean_object* v___x_4289_; 
v_close_4288_ = lean_ctor_get(v_inst_4281_, 3);
lean_inc_ref(v_close_4288_);
lean_dec_ref(v_inst_4281_);
v___x_4289_ = lean_apply_2(v_close_4288_, v_socket_4282_, lean_box(0));
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4289_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 1);
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
v_val_4286_ = v___x_4295_;
goto v___jp_4285_;
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_a_4298_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4289_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4289_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set_tag(v___x_4300_, 0);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
v_val_4286_ = v___x_4303_;
goto v___jp_4285_;
}
}
}
v___jp_4285_:
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v_val_4286_);
return v___x_4287_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4281_ = stack[0].m_obj;
lean_object* v_socket_4282_ = stack[1].m_obj;
lean_object* v_____r_4283_ = stack[2].m_obj;
lean_object* v_res_4306_;
v_res_4306_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4281_, v_socket_4282_, v_____r_4283_);
stack->m_obj
 = v_res_4306_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4307_, lean_object* v_socket_4308_, lean_object* v_____r_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4307_, v_socket_4308_, v_____r_4309_);
return v_res_4311_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4312_, lean_object* v_x_4313_){
_start:
{
if (lean_obj_tag(v_x_4313_) == 0)
{
lean_object* v___x_4315_; 
lean_dec_ref(v___f_4312_);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v_x_4313_);
return v___x_4315_;
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4317_; 
v_a_4316_ = lean_ctor_get(v_x_4313_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v_x_4313_, 1);
v___x_4317_ = lean_apply_2(v___f_4312_, v_a_4316_, lean_box(0));
return v___x_4317_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4312_ = stack[0].m_obj;
lean_object* v_x_4313_ = stack[1].m_obj;
lean_object* v_res_4318_;
v_res_4318_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4312_, v_x_4313_);
stack->m_obj
 = v_res_4318_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4319_, lean_object* v_x_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4319_, v_x_4320_);
return v_res_4322_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4323_, lean_object* v_val_4324_, lean_object* v___f_4325_, lean_object* v___f_4326_, lean_object* v_x_4327_){
_start:
{
if (lean_obj_tag(v_x_4327_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4337_; 
lean_dec_ref(v___f_4326_);
lean_dec_ref(v___f_4325_);
lean_dec(v_val_4324_);
lean_dec_ref(v_close_4323_);
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
lean_object* v_a_4338_; uint8_t v___x_4339_; 
v_a_4338_ = lean_ctor_get(v_x_4327_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v_x_4327_, 1);
v___x_4339_ = lean_unbox(v_a_4338_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; 
lean_dec_ref(v___f_4326_);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_apply_2(v_close_4323_, v_val_4324_, lean_box(0));
v___x_4342_ = lean_unbox(v_a_4338_);
lean_dec(v_a_4338_);
v___x_4343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4340_, v___x_4342_, v___x_4341_, v___f_4325_);
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_dec(v_a_4338_);
lean_dec_ref(v___f_4325_);
lean_dec(v_val_4324_);
lean_dec_ref(v_close_4323_);
v___x_4344_ = lean_box(0);
v___x_4345_ = lean_apply_2(v___f_4326_, v___x_4344_, lean_box(0));
return v___x_4345_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_close_4323_ = stack[0].m_obj;
lean_object* v_val_4324_ = stack[1].m_obj;
lean_object* v___f_4325_ = stack[2].m_obj;
lean_object* v___f_4326_ = stack[3].m_obj;
lean_object* v_x_4327_ = stack[4].m_obj;
lean_object* v_res_4346_;
v_res_4346_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4323_, v_val_4324_, v___f_4325_, v___f_4326_, v_x_4327_);
stack->m_obj
 = v_res_4346_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4347_, lean_object* v_val_4348_, lean_object* v___f_4349_, lean_object* v___f_4350_, lean_object* v_x_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4347_, v_val_4348_, v___f_4349_, v___f_4350_, v_x_4351_);
return v_res_4353_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4354_, lean_object* v_responseBodyInstance_4355_, lean_object* v___f_4356_, lean_object* v___f_4357_, lean_object* v_____r_4358_){
_start:
{
if (lean_obj_tag(v_respStream_4354_) == 1)
{
lean_object* v_val_4360_; lean_object* v_close_4361_; lean_object* v_isClosed_4362_; lean_object* v___f_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v_val_4360_ = lean_ctor_get(v_respStream_4354_, 0);
lean_inc_n(v_val_4360_, 2);
lean_dec_ref_known(v_respStream_4354_, 1);
v_close_4361_ = lean_ctor_get(v_responseBodyInstance_4355_, 1);
lean_inc_ref(v_close_4361_);
v_isClosed_4362_ = lean_ctor_get(v_responseBodyInstance_4355_, 2);
lean_inc_ref(v_isClosed_4362_);
lean_dec_ref(v_responseBodyInstance_4355_);
v___f_4363_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4363_, 0, v_close_4361_);
lean_closure_set(v___f_4363_, 1, v_val_4360_);
lean_closure_set(v___f_4363_, 2, v___f_4356_);
lean_closure_set(v___f_4363_, 3, v___f_4357_);
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = 0;
v___x_4366_ = lean_apply_2(v_isClosed_4362_, v_val_4360_, lean_box(0));
v___x_4367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4364_, v___x_4365_, v___x_4366_, v___f_4363_);
return v___x_4367_;
}
else
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
lean_dec_ref(v___f_4356_);
lean_dec_ref(v_responseBodyInstance_4355_);
lean_dec(v_respStream_4354_);
v___x_4368_ = lean_box(0);
v___x_4369_ = lean_apply_2(v___f_4357_, v___x_4368_, lean_box(0));
return v___x_4369_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_respStream_4354_ = stack[0].m_obj;
lean_object* v_responseBodyInstance_4355_ = stack[1].m_obj;
lean_object* v___f_4356_ = stack[2].m_obj;
lean_object* v___f_4357_ = stack[3].m_obj;
lean_object* v_____r_4358_ = stack[4].m_obj;
lean_object* v_res_4370_;
v_res_4370_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4354_, v_responseBodyInstance_4355_, v___f_4356_, v___f_4357_, v_____r_4358_);
stack->m_obj
 = v_res_4370_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4371_, lean_object* v_responseBodyInstance_4372_, lean_object* v___f_4373_, lean_object* v___f_4374_, lean_object* v_____r_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4371_, v_responseBodyInstance_4372_, v___f_4373_, v___f_4374_, v_____r_4375_);
return v_res_4377_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4378_, lean_object* v___f_4379_, lean_object* v___f_4380_, lean_object* v_x_4381_){
_start:
{
if (lean_obj_tag(v_x_4381_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4391_; 
lean_dec_ref(v___f_4380_);
lean_dec_ref(v___f_4379_);
lean_dec_ref(v_requestStream_4378_);
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
lean_object* v_a_4392_; uint8_t v___x_4393_; 
v_a_4392_ = lean_ctor_get(v_x_4381_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v_x_4381_, 1);
v___x_4393_ = lean_unbox(v_a_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; lean_object* v___x_4397_; 
lean_dec_ref(v___f_4380_);
v___x_4394_ = lean_unsigned_to_nat(0u);
v___x_4395_ = l_Std_Http_Body_Stream_close(v_requestStream_4378_);
v___x_4396_ = lean_unbox(v_a_4392_);
lean_dec(v_a_4392_);
v___x_4397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4394_, v___x_4396_, v___x_4395_, v___f_4379_);
return v___x_4397_;
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
lean_dec(v_a_4392_);
lean_dec_ref(v___f_4379_);
lean_dec_ref(v_requestStream_4378_);
v___x_4398_ = lean_box(0);
v___x_4399_ = lean_apply_2(v___f_4380_, v___x_4398_, lean_box(0));
return v___x_4399_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestStream_4378_ = stack[0].m_obj;
lean_object* v___f_4379_ = stack[1].m_obj;
lean_object* v___f_4380_ = stack[2].m_obj;
lean_object* v_x_4381_ = stack[3].m_obj;
lean_object* v_res_4400_;
v_res_4400_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4378_, v___f_4379_, v___f_4380_, v_x_4381_);
stack->m_obj
 = v_res_4400_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4401_, lean_object* v___f_4402_, lean_object* v___f_4403_, lean_object* v_x_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4401_, v___f_4402_, v___f_4403_, v_x_4404_);
return v_res_4406_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4407_, lean_object* v___f_4408_, lean_object* v___f_4409_, lean_object* v___f_4410_, lean_object* v_x_4411_){
_start:
{
if (lean_obj_tag(v_x_4411_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4421_; 
lean_dec_ref(v___f_4410_);
lean_dec_ref(v___f_4409_);
lean_dec_ref(v___f_4408_);
lean_dec_ref(v_responseBodyInstance_4407_);
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
lean_object* v_a_4422_; lean_object* v_requestStream_4423_; lean_object* v_respStream_4424_; lean_object* v___f_4425_; lean_object* v___f_4426_; lean_object* v___f_4427_; lean_object* v___x_4428_; uint8_t v___x_4429_; lean_object* v___x_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4542__overap_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_a_4422_ = lean_ctor_get(v_x_4411_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v_x_4411_, 1);
v_requestStream_4423_ = lean_ctor_get(v_a_4422_, 1);
lean_inc_ref_n(v_requestStream_4423_, 2);
v_respStream_4424_ = lean_ctor_get(v_a_4422_, 6);
lean_inc(v_respStream_4424_);
lean_dec(v_a_4422_);
v___f_4425_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4425_, 0, v_respStream_4424_);
lean_closure_set(v___f_4425_, 1, v_responseBodyInstance_4407_);
lean_closure_set(v___f_4425_, 2, v___f_4408_);
lean_closure_set(v___f_4425_, 3, v___f_4409_);
lean_inc_ref(v___f_4425_);
v___f_4426_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4426_, 0, v___f_4425_);
v___f_4427_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4427_, 0, v_requestStream_4423_);
lean_closure_set(v___f_4427_, 1, v___f_4426_);
lean_closure_set(v___f_4427_, 2, v___f_4425_);
v___x_4428_ = lean_unsigned_to_nat(0u);
v___x_4429_ = 0;
v___x_4430_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4431_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4432_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4433_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4434_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4434_, 0, lean_box(0));
lean_closure_set(v___x_4434_, 1, lean_box(0));
lean_closure_set(v___x_4434_, 2, v___x_4430_);
lean_closure_set(v___x_4434_, 3, lean_box(0));
lean_closure_set(v___x_4434_, 4, lean_box(0));
lean_closure_set(v___x_4434_, 5, v___x_4433_);
lean_closure_set(v___x_4434_, 6, v___f_4410_);
v___x_4542__overap_4435_ = l_Std_Mutex_atomically___redArg(v___x_4430_, v___f_4431_, v___f_4432_, v_requestStream_4423_, v___x_4434_);
v___x_4436_ = lean_apply_1(v___x_4542__overap_4435_, lean_box(0));
v___x_4437_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4428_, v___x_4429_, v___x_4436_, v___f_4427_);
return v___x_4437_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_responseBodyInstance_4407_ = stack[0].m_obj;
lean_object* v___f_4408_ = stack[1].m_obj;
lean_object* v___f_4409_ = stack[2].m_obj;
lean_object* v___f_4410_ = stack[3].m_obj;
lean_object* v_x_4411_ = stack[4].m_obj;
lean_object* v_res_4438_;
v_res_4438_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4407_, v___f_4408_, v___f_4409_, v___f_4410_, v_x_4411_);
stack->m_obj
 = v_res_4438_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4439_, lean_object* v___f_4440_, lean_object* v___f_4441_, lean_object* v___f_4442_, lean_object* v_x_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4439_, v___f_4440_, v___f_4441_, v___f_4442_, v_x_4443_);
return v_res_4445_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4446_, lean_object* v_responseBodyInstance_4447_, lean_object* v_handler_4448_, lean_object* v_config_4449_, lean_object* v___x_4450_, uint8_t v___x_4451_, lean_object* v___f_4452_, lean_object* v_x_4453_){
_start:
{
if (lean_obj_tag(v_x_4453_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4463_; 
lean_dec_ref(v___f_4452_);
lean_dec_ref(v___x_4450_);
lean_dec_ref(v_config_4449_);
lean_dec(v_handler_4448_);
lean_dec_ref(v_responseBodyInstance_4447_);
lean_dec_ref(v_h_4446_);
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
lean_object* v_a_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v_a_4464_ = lean_ctor_get(v_x_4453_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v_x_4453_, 1);
v___x_4465_ = lean_unsigned_to_nat(0u);
v___x_4466_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4446_, v_responseBodyInstance_4447_, v_handler_4448_, v_config_4449_, v_a_4464_, v___x_4450_);
v___x_4467_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4465_, v___x_4451_, v___x_4466_, v___f_4452_);
return v___x_4467_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_4446_ = stack[0].m_obj;
lean_object* v_responseBodyInstance_4447_ = stack[1].m_obj;
lean_object* v_handler_4448_ = stack[2].m_obj;
lean_object* v_config_4449_ = stack[3].m_obj;
lean_object* v___x_4450_ = stack[4].m_obj;
uint8_t v___x_4451_ = stack[5].m_num;
lean_object* v___f_4452_ = stack[6].m_obj;
lean_object* v_x_4453_ = stack[7].m_obj;
lean_object* v_res_4468_;
v_res_4468_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4446_, v_responseBodyInstance_4447_, v_handler_4448_, v_config_4449_, v___x_4450_, v___x_4451_, v___f_4452_, v_x_4453_);
stack->m_obj
 = v_res_4468_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4469_, lean_object* v_responseBodyInstance_4470_, lean_object* v_handler_4471_, lean_object* v_config_4472_, lean_object* v___x_4473_, lean_object* v___x_4474_, lean_object* v___f_4475_, lean_object* v_x_4476_, lean_object* v___y_4477_){
_start:
{
uint8_t v___x_5428__boxed_4478_; lean_object* v_res_4479_; 
v___x_5428__boxed_4478_ = lean_unbox(v___x_4474_);
v_res_4479_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4469_, v_responseBodyInstance_4470_, v_handler_4471_, v_config_4472_, v___x_4473_, v___x_5428__boxed_4478_, v___f_4475_, v_x_4476_);
return v_res_4479_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4480_, lean_object* v_h_4481_, lean_object* v_responseBodyInstance_4482_, lean_object* v_config_4483_, lean_object* v_handler_4484_, uint8_t v___x_4485_, lean_object* v___f_4486_, lean_object* v_x_4487_){
_start:
{
if (lean_obj_tag(v_x_4487_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4497_; 
lean_dec_ref(v___f_4486_);
lean_dec(v_handler_4484_);
lean_dec_ref(v_config_4483_);
lean_dec_ref(v_responseBodyInstance_4482_);
lean_dec_ref(v_h_4481_);
lean_dec_ref(v_inst_4480_);
v_a_4489_ = lean_ctor_get(v_x_4487_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_x_4487_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4491_ = v_x_4487_;
v_isShared_4492_ = v_isSharedCheck_4497_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v_x_4487_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4497_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4498_ = lean_ctor_get(v_x_4487_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v_x_4487_, 1);
v___x_4499_ = lean_unsigned_to_nat(0u);
v___x_4500_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4480_, v_h_4481_, v_responseBodyInstance_4482_, v_config_4483_, v_handler_4484_, v_a_4498_);
v___x_4501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4499_, v___x_4485_, v___x_4500_, v___f_4486_);
return v___x_4501_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4480_ = stack[0].m_obj;
lean_object* v_h_4481_ = stack[1].m_obj;
lean_object* v_responseBodyInstance_4482_ = stack[2].m_obj;
lean_object* v_config_4483_ = stack[3].m_obj;
lean_object* v_handler_4484_ = stack[4].m_obj;
uint8_t v___x_4485_ = stack[5].m_num;
lean_object* v___f_4486_ = stack[6].m_obj;
lean_object* v_x_4487_ = stack[7].m_obj;
lean_object* v_res_4502_;
v_res_4502_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4480_, v_h_4481_, v_responseBodyInstance_4482_, v_config_4483_, v_handler_4484_, v___x_4485_, v___f_4486_, v_x_4487_);
stack->m_obj
 = v_res_4502_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4503_, lean_object* v_h_4504_, lean_object* v_responseBodyInstance_4505_, lean_object* v_config_4506_, lean_object* v_handler_4507_, lean_object* v___x_4508_, lean_object* v___f_4509_, lean_object* v_x_4510_, lean_object* v___y_4511_){
_start:
{
uint8_t v___x_5492__boxed_4512_; lean_object* v_res_4513_; 
v___x_5492__boxed_4512_ = lean_unbox(v___x_4508_);
v_res_4513_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4503_, v_h_4504_, v_responseBodyInstance_4505_, v_config_4506_, v_handler_4507_, v___x_5492__boxed_4512_, v___f_4509_, v_x_4510_);
return v_res_4513_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4514_, lean_object* v_h_4515_, lean_object* v_responseBodyInstance_4516_, lean_object* v_handler_4517_, lean_object* v_config_4518_, lean_object* v___f_4519_, lean_object* v_inst_4520_, lean_object* v_socket_4521_, lean_object* v_connectionContext_4522_, lean_object* v_x_4523_){
_start:
{
if (lean_obj_tag(v_x_4523_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4533_; 
lean_dec_ref(v_connectionContext_4522_);
lean_dec(v_socket_4521_);
lean_dec_ref(v_inst_4520_);
lean_dec_ref(v___f_4519_);
lean_dec_ref(v_config_4518_);
lean_dec(v_handler_4517_);
lean_dec_ref(v_responseBodyInstance_4516_);
lean_dec_ref(v_h_4515_);
v_a_4525_ = lean_ctor_get(v_x_4523_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_x_4523_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4527_ = v_x_4523_;
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v_x_4523_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4568_; 
v_a_4534_ = lean_ctor_get(v_x_4523_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v_x_4523_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4536_ = v_x_4523_;
v_isShared_4537_ = v_isSharedCheck_4568_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v_x_4523_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4568_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v_machine_4544_; lean_object* v_requestStream_4545_; lean_object* v_keepAliveTimeout_4546_; lean_object* v_currentTimeout_4547_; lean_object* v_headerTimeout_4548_; lean_object* v_response_4549_; lean_object* v_respStream_4550_; uint8_t v_requiresData_4551_; lean_object* v_expectData_4552_; uint8_t v_handlerDispatched_4553_; lean_object* v_pendingHead_4554_; 
v_machine_4544_ = lean_ctor_get(v_a_4534_, 0);
v_requestStream_4545_ = lean_ctor_get(v_a_4534_, 1);
v_keepAliveTimeout_4546_ = lean_ctor_get(v_a_4534_, 2);
v_currentTimeout_4547_ = lean_ctor_get(v_a_4534_, 3);
v_headerTimeout_4548_ = lean_ctor_get(v_a_4534_, 4);
v_response_4549_ = lean_ctor_get(v_a_4534_, 5);
v_respStream_4550_ = lean_ctor_get(v_a_4534_, 6);
v_requiresData_4551_ = lean_ctor_get_uint8(v_a_4534_, sizeof(void*)*9);
v_expectData_4552_ = lean_ctor_get(v_a_4534_, 7);
v_handlerDispatched_4553_ = lean_ctor_get_uint8(v_a_4534_, sizeof(void*)*9 + 1);
v_pendingHead_4554_ = lean_ctor_get(v_a_4534_, 8);
if (v_requiresData_4551_ == 0)
{
if (v_handlerDispatched_4553_ == 0)
{
if (lean_obj_tag(v_respStream_4550_) == 0)
{
lean_object* v_writer_4564_; uint8_t v_sentMessage_4565_; 
v_writer_4564_ = lean_ctor_get(v_machine_4544_, 1);
v_sentMessage_4565_ = lean_ctor_get_uint8(v_writer_4564_, sizeof(void*)*6);
if (v_sentMessage_4565_ == 0)
{
lean_object* v_reader_4566_; lean_object* v_state_4567_; 
v_reader_4566_ = lean_ctor_get(v_machine_4544_, 0);
v_state_4567_ = lean_ctor_get(v_reader_4566_, 0);
if (lean_obj_tag(v_state_4567_) == 2)
{
lean_inc(v_respStream_4550_);
lean_inc(v_pendingHead_4554_);
lean_inc(v_expectData_4552_);
lean_inc_ref(v_response_4549_);
lean_inc(v_headerTimeout_4548_);
lean_inc(v_currentTimeout_4547_);
lean_inc(v_keepAliveTimeout_4546_);
lean_inc_ref(v_requestStream_4545_);
lean_inc_ref(v_machine_4544_);
lean_del_object(v___x_4536_);
lean_dec(v_a_4534_);
goto v___jp_4555_;
}
else
{
lean_dec_ref(v_connectionContext_4522_);
lean_dec(v_socket_4521_);
lean_dec_ref(v_inst_4520_);
lean_dec_ref(v___f_4519_);
lean_dec_ref(v_config_4518_);
lean_dec(v_handler_4517_);
lean_dec_ref(v_responseBodyInstance_4516_);
lean_dec_ref(v_h_4515_);
goto v___jp_4538_;
}
}
else
{
lean_dec_ref(v_connectionContext_4522_);
lean_dec(v_socket_4521_);
lean_dec_ref(v_inst_4520_);
lean_dec_ref(v___f_4519_);
lean_dec_ref(v_config_4518_);
lean_dec(v_handler_4517_);
lean_dec_ref(v_responseBodyInstance_4516_);
lean_dec_ref(v_h_4515_);
goto v___jp_4538_;
}
}
else
{
lean_inc_ref(v_respStream_4550_);
lean_inc(v_pendingHead_4554_);
lean_inc(v_expectData_4552_);
lean_inc_ref(v_response_4549_);
lean_inc(v_headerTimeout_4548_);
lean_inc(v_currentTimeout_4547_);
lean_inc(v_keepAliveTimeout_4546_);
lean_inc_ref(v_requestStream_4545_);
lean_inc_ref(v_machine_4544_);
lean_del_object(v___x_4536_);
lean_dec(v_a_4534_);
goto v___jp_4555_;
}
}
else
{
lean_inc(v_pendingHead_4554_);
lean_inc(v_expectData_4552_);
lean_inc(v_respStream_4550_);
lean_inc_ref(v_response_4549_);
lean_inc(v_headerTimeout_4548_);
lean_inc(v_currentTimeout_4547_);
lean_inc(v_keepAliveTimeout_4546_);
lean_inc_ref(v_requestStream_4545_);
lean_inc_ref(v_machine_4544_);
lean_del_object(v___x_4536_);
lean_dec(v_a_4534_);
goto v___jp_4555_;
}
}
else
{
lean_inc(v_pendingHead_4554_);
lean_inc(v_expectData_4552_);
lean_inc(v_respStream_4550_);
lean_inc_ref(v_response_4549_);
lean_inc(v_headerTimeout_4548_);
lean_inc(v_currentTimeout_4547_);
lean_inc(v_keepAliveTimeout_4546_);
lean_inc_ref(v_requestStream_4545_);
lean_inc_ref(v_machine_4544_);
lean_del_object(v___x_4536_);
lean_dec(v_a_4534_);
goto v___jp_4555_;
}
v___jp_4538_:
{
lean_object* v___x_4539_; lean_object* v___x_4541_; 
v___x_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4539_, 0, v_a_4534_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4539_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4539_);
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
v___jp_4555_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___f_4558_; lean_object* v___x_4559_; lean_object* v___f_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4556_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4556_, 0, v_machine_4544_);
lean_ctor_set(v___x_4556_, 1, v_requestStream_4545_);
lean_ctor_set(v___x_4556_, 2, v_keepAliveTimeout_4546_);
lean_ctor_set(v___x_4556_, 3, v_currentTimeout_4547_);
lean_ctor_set(v___x_4556_, 4, v_headerTimeout_4548_);
lean_ctor_set(v___x_4556_, 5, v_response_4549_);
lean_ctor_set(v___x_4556_, 6, v_respStream_4550_);
lean_ctor_set(v___x_4556_, 7, v_expectData_4552_);
lean_ctor_set(v___x_4556_, 8, v_pendingHead_4554_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*9, v___x_4514_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*9 + 1, v_handlerDispatched_4553_);
v___x_4557_ = lean_box(v___x_4514_);
lean_inc_ref(v___x_4556_);
lean_inc_ref(v_config_4518_);
lean_inc(v_handler_4517_);
lean_inc_ref(v_responseBodyInstance_4516_);
lean_inc_ref(v_h_4515_);
v___f_4558_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4558_, 0, v_h_4515_);
lean_closure_set(v___f_4558_, 1, v_responseBodyInstance_4516_);
lean_closure_set(v___f_4558_, 2, v_handler_4517_);
lean_closure_set(v___f_4558_, 3, v_config_4518_);
lean_closure_set(v___f_4558_, 4, v___x_4556_);
lean_closure_set(v___f_4558_, 5, v___x_4557_);
lean_closure_set(v___f_4558_, 6, v___f_4519_);
v___x_4559_ = lean_box(v___x_4514_);
v___f_4560_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4560_, 0, v_inst_4520_);
lean_closure_set(v___f_4560_, 1, v_h_4515_);
lean_closure_set(v___f_4560_, 2, v_responseBodyInstance_4516_);
lean_closure_set(v___f_4560_, 3, v_config_4518_);
lean_closure_set(v___f_4560_, 4, v_handler_4517_);
lean_closure_set(v___f_4560_, 5, v___x_4559_);
lean_closure_set(v___f_4560_, 6, v___f_4558_);
v___x_4561_ = lean_unsigned_to_nat(0u);
v___x_4562_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4521_, v_connectionContext_4522_, v___x_4556_);
v___x_4563_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4561_, v___x_4514_, v___x_4562_, v___f_4560_);
return v___x_4563_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4514_ = stack[0].m_num;
lean_object* v_h_4515_ = stack[1].m_obj;
lean_object* v_responseBodyInstance_4516_ = stack[2].m_obj;
lean_object* v_handler_4517_ = stack[3].m_obj;
lean_object* v_config_4518_ = stack[4].m_obj;
lean_object* v___f_4519_ = stack[5].m_obj;
lean_object* v_inst_4520_ = stack[6].m_obj;
lean_object* v_socket_4521_ = stack[7].m_obj;
lean_object* v_connectionContext_4522_ = stack[8].m_obj;
lean_object* v_x_4523_ = stack[9].m_obj;
lean_object* v_res_4569_;
v_res_4569_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_4514_, v_h_4515_, v_responseBodyInstance_4516_, v_handler_4517_, v_config_4518_, v___f_4519_, v_inst_4520_, v_socket_4521_, v_connectionContext_4522_, v_x_4523_);
stack->m_obj
 = v_res_4569_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4570_, lean_object* v_h_4571_, lean_object* v_responseBodyInstance_4572_, lean_object* v_handler_4573_, lean_object* v_config_4574_, lean_object* v___f_4575_, lean_object* v_inst_4576_, lean_object* v_socket_4577_, lean_object* v_connectionContext_4578_, lean_object* v_x_4579_, lean_object* v___y_4580_){
_start:
{
uint8_t v___x_5555__boxed_4581_; lean_object* v_res_4582_; 
v___x_5555__boxed_4581_ = lean_unbox(v___x_4570_);
v_res_4582_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5555__boxed_4581_, v_h_4571_, v_responseBodyInstance_4572_, v_handler_4573_, v_config_4574_, v___f_4575_, v_inst_4576_, v_socket_4577_, v_connectionContext_4578_, v_x_4579_);
return v_res_4582_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4583_, lean_object* v_handler_4584_, lean_object* v_extensions_4585_, lean_object* v_connectionContext_4586_, uint8_t v___x_4587_, lean_object* v___f_4588_, lean_object* v_x_4589_){
_start:
{
if (lean_obj_tag(v_x_4589_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4599_; 
lean_dec_ref(v___f_4588_);
lean_dec_ref(v_connectionContext_4586_);
lean_dec(v_extensions_4585_);
lean_dec(v_handler_4584_);
lean_dec_ref(v_h_4583_);
v_a_4591_ = lean_ctor_get(v_x_4589_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_x_4589_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4593_ = v_x_4589_;
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v_x_4589_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v_a_4600_ = lean_ctor_get(v_x_4589_, 0);
lean_inc(v_a_4600_);
lean_dec_ref_known(v_x_4589_, 1);
v___x_4601_ = lean_unsigned_to_nat(0u);
v___x_4602_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4583_, v_handler_4584_, v_extensions_4585_, v_connectionContext_4586_, v_a_4600_);
v___x_4603_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4601_, v___x_4587_, v___x_4602_, v___f_4588_);
return v___x_4603_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_4583_ = stack[0].m_obj;
lean_object* v_handler_4584_ = stack[1].m_obj;
lean_object* v_extensions_4585_ = stack[2].m_obj;
lean_object* v_connectionContext_4586_ = stack[3].m_obj;
uint8_t v___x_4587_ = stack[4].m_num;
lean_object* v___f_4588_ = stack[5].m_obj;
lean_object* v_x_4589_ = stack[6].m_obj;
lean_object* v_res_4604_;
v_res_4604_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4583_, v_handler_4584_, v_extensions_4585_, v_connectionContext_4586_, v___x_4587_, v___f_4588_, v_x_4589_);
stack->m_obj
 = v_res_4604_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4605_, lean_object* v_handler_4606_, lean_object* v_extensions_4607_, lean_object* v_connectionContext_4608_, lean_object* v___x_4609_, lean_object* v___f_4610_, lean_object* v_x_4611_, lean_object* v___y_4612_){
_start:
{
uint8_t v___x_5669__boxed_4613_; lean_object* v_res_4614_; 
v___x_5669__boxed_4613_ = lean_unbox(v___x_4609_);
v_res_4614_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4605_, v_handler_4606_, v_extensions_4607_, v_connectionContext_4608_, v___x_5669__boxed_4613_, v___f_4610_, v_x_4611_);
return v_res_4614_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4615_, lean_object* v_responseBodyInstance_4616_, lean_object* v_handler_4617_, lean_object* v_config_4618_, lean_object* v_connectionContext_4619_, lean_object* v_events_4620_, lean_object* v___x_4621_, uint8_t v___x_4622_, lean_object* v___f_4623_, lean_object* v_____r_4624_){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4615_, v_responseBodyInstance_4616_, v_handler_4617_, v_config_4618_, v_connectionContext_4619_, v_events_4620_, v___x_4621_);
v___x_4628_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4626_, v___x_4622_, v___x_4627_, v___f_4623_);
return v___x_4628_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_4615_ = stack[0].m_obj;
lean_object* v_responseBodyInstance_4616_ = stack[1].m_obj;
lean_object* v_handler_4617_ = stack[2].m_obj;
lean_object* v_config_4618_ = stack[3].m_obj;
lean_object* v_connectionContext_4619_ = stack[4].m_obj;
lean_object* v_events_4620_ = stack[5].m_obj;
lean_object* v___x_4621_ = stack[6].m_obj;
uint8_t v___x_4622_ = stack[7].m_num;
lean_object* v___f_4623_ = stack[8].m_obj;
lean_object* v_____r_4624_ = stack[9].m_obj;
lean_object* v_res_4629_;
v_res_4629_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4615_, v_responseBodyInstance_4616_, v_handler_4617_, v_config_4618_, v_connectionContext_4619_, v_events_4620_, v___x_4621_, v___x_4622_, v___f_4623_, v_____r_4624_);
stack->m_obj
 = v_res_4629_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4630_, lean_object* v_responseBodyInstance_4631_, lean_object* v_handler_4632_, lean_object* v_config_4633_, lean_object* v_connectionContext_4634_, lean_object* v_events_4635_, lean_object* v___x_4636_, lean_object* v___x_4637_, lean_object* v___f_4638_, lean_object* v_____r_4639_, lean_object* v___y_4640_){
_start:
{
uint8_t v___x_5729__boxed_4641_; lean_object* v_res_4642_; 
v___x_5729__boxed_4641_ = lean_unbox(v___x_4637_);
v_res_4642_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4630_, v_responseBodyInstance_4631_, v_handler_4632_, v_config_4633_, v_connectionContext_4634_, v_events_4635_, v___x_4636_, v___x_5729__boxed_4641_, v___f_4638_, v_____r_4639_);
return v_res_4642_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4643_, lean_object* v___f_4644_, lean_object* v_x_4645_){
_start:
{
if (lean_obj_tag(v_x_4645_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4655_; 
lean_dec_ref(v___f_4644_);
lean_dec_ref(v___x_4643_);
v_a_4647_ = lean_ctor_get(v_x_4645_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v_x_4645_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4649_ = v_x_4645_;
v_isShared_4650_ = v_isSharedCheck_4655_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v_x_4645_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4655_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
}
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4667_; 
v_a_4656_ = lean_ctor_get(v_x_4645_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v_x_4645_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4658_ = v_x_4645_;
v_isShared_4659_ = v_isSharedCheck_4667_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v_x_4645_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4667_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
if (lean_obj_tag(v_a_4656_) == 0)
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
lean_dec_ref(v___f_4644_);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4643_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4660_);
v___x_4662_ = v___x_4658_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4663_; 
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
}
else
{
lean_object* v_val_4665_; lean_object* v___x_4666_; 
lean_del_object(v___x_4658_);
lean_dec_ref(v___x_4643_);
v_val_4665_ = lean_ctor_get(v_a_4656_, 0);
lean_inc(v_val_4665_);
lean_dec_ref_known(v_a_4656_, 1);
v___x_4666_ = lean_apply_2(v___f_4644_, v_val_4665_, lean_box(0));
return v___x_4666_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4643_ = stack[0].m_obj;
lean_object* v___f_4644_ = stack[1].m_obj;
lean_object* v_x_4645_ = stack[2].m_obj;
lean_object* v_res_4668_;
v_res_4668_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4643_, v___f_4644_, v_x_4645_);
stack->m_obj
 = v_res_4668_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4669_, lean_object* v___f_4670_, lean_object* v_x_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4669_, v___f_4670_, v_x_4671_);
return v_res_4673_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4674_, lean_object* v_responseBodyInstance_4675_, lean_object* v_handler_4676_, lean_object* v_config_4677_, lean_object* v_connectionContext_4678_, uint8_t v___x_4679_, lean_object* v___f_4680_, lean_object* v_inst_4681_, lean_object* v_socket_4682_, lean_object* v___f_4683_, lean_object* v___f_4684_, lean_object* v_x_4685_, lean_object* v_____s_4686_){
_start:
{
lean_object* v_machine_4688_; lean_object* v_reader_4689_; lean_object* v_requestStream_4690_; lean_object* v_keepAliveTimeout_4691_; lean_object* v_currentTimeout_4692_; lean_object* v_headerTimeout_4693_; lean_object* v_response_4694_; lean_object* v_respStream_4695_; uint8_t v_requiresData_4696_; lean_object* v_expectData_4697_; uint8_t v_handlerDispatched_4698_; lean_object* v_pendingHead_4699_; lean_object* v_writer_4700_; lean_object* v_state_4701_; uint8_t v___x_4702_; 
v_machine_4688_ = lean_ctor_get(v_____s_4686_, 0);
v_reader_4689_ = lean_ctor_get(v_machine_4688_, 0);
v_requestStream_4690_ = lean_ctor_get(v_____s_4686_, 1);
v_keepAliveTimeout_4691_ = lean_ctor_get(v_____s_4686_, 2);
v_currentTimeout_4692_ = lean_ctor_get(v_____s_4686_, 3);
v_headerTimeout_4693_ = lean_ctor_get(v_____s_4686_, 4);
v_response_4694_ = lean_ctor_get(v_____s_4686_, 5);
v_respStream_4695_ = lean_ctor_get(v_____s_4686_, 6);
v_requiresData_4696_ = lean_ctor_get_uint8(v_____s_4686_, sizeof(void*)*9);
v_expectData_4697_ = lean_ctor_get(v_____s_4686_, 7);
v_handlerDispatched_4698_ = lean_ctor_get_uint8(v_____s_4686_, sizeof(void*)*9 + 1);
v_pendingHead_4699_ = lean_ctor_get(v_____s_4686_, 8);
v_writer_4700_ = lean_ctor_get(v_machine_4688_, 1);
v_state_4701_ = lean_ctor_get(v_reader_4689_, 0);
v___x_4702_ = 0;
if (lean_obj_tag(v_state_4701_) == 6)
{
lean_object* v_state_4724_; 
v_state_4724_ = lean_ctor_get(v_writer_4700_, 2);
if (lean_obj_tag(v_state_4724_) == 7)
{
lean_object* v_outputData_4725_; lean_object* v_size_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v_outputData_4725_ = lean_ctor_get(v_writer_4700_, 1);
v_size_4726_ = lean_ctor_get(v_outputData_4725_, 1);
v___x_4727_ = lean_unsigned_to_nat(0u);
v___x_4728_ = lean_nat_dec_eq(v_size_4726_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_inc(v_pendingHead_4699_);
lean_inc(v_expectData_4697_);
lean_inc(v_respStream_4695_);
lean_inc_ref(v_response_4694_);
lean_inc(v_headerTimeout_4693_);
lean_inc(v_currentTimeout_4692_);
lean_inc(v_keepAliveTimeout_4691_);
lean_inc_ref(v_requestStream_4690_);
lean_inc_ref(v_machine_4688_);
lean_dec_ref(v_____s_4686_);
goto v___jp_4703_;
}
else
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
lean_dec_ref(v___f_4684_);
lean_dec_ref(v___f_4683_);
lean_dec(v_socket_4682_);
lean_dec_ref(v_inst_4681_);
lean_dec_ref(v___f_4680_);
lean_dec_ref(v_connectionContext_4678_);
lean_dec_ref(v_config_4677_);
lean_dec(v_handler_4676_);
lean_dec_ref(v_responseBodyInstance_4675_);
lean_dec_ref(v_h_4674_);
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v_____s_4686_);
v___x_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4729_);
v___x_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
return v___x_4731_;
}
}
else
{
lean_inc(v_pendingHead_4699_);
lean_inc(v_expectData_4697_);
lean_inc(v_respStream_4695_);
lean_inc_ref(v_response_4694_);
lean_inc(v_headerTimeout_4693_);
lean_inc(v_currentTimeout_4692_);
lean_inc(v_keepAliveTimeout_4691_);
lean_inc_ref(v_requestStream_4690_);
lean_inc_ref(v_machine_4688_);
lean_dec_ref(v_____s_4686_);
goto v___jp_4703_;
}
}
else
{
lean_inc(v_pendingHead_4699_);
lean_inc(v_expectData_4697_);
lean_inc(v_respStream_4695_);
lean_inc_ref(v_response_4694_);
lean_inc(v_headerTimeout_4693_);
lean_inc(v_currentTimeout_4692_);
lean_inc(v_keepAliveTimeout_4691_);
lean_inc_ref(v_requestStream_4690_);
lean_inc_ref(v_machine_4688_);
lean_dec_ref(v_____s_4686_);
goto v___jp_4703_;
}
v___jp_4703_:
{
lean_object* v___x_4704_; lean_object* v_snd_4705_; lean_object* v_output_4706_; lean_object* v_fst_4707_; lean_object* v_events_4708_; lean_object* v_data_4709_; lean_object* v_size_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___f_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; 
v___x_4704_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4702_, v_machine_4688_);
v_snd_4705_ = lean_ctor_get(v___x_4704_, 1);
lean_inc(v_snd_4705_);
v_output_4706_ = lean_ctor_get(v_snd_4705_, 1);
lean_inc_ref(v_output_4706_);
v_fst_4707_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_fst_4707_);
lean_dec_ref(v___x_4704_);
v_events_4708_ = lean_ctor_get(v_snd_4705_, 0);
lean_inc_ref_n(v_events_4708_, 2);
lean_dec(v_snd_4705_);
v_data_4709_ = lean_ctor_get(v_output_4706_, 0);
lean_inc_ref(v_data_4709_);
v_size_4710_ = lean_ctor_get(v_output_4706_, 1);
lean_inc(v_size_4710_);
lean_dec_ref(v_output_4706_);
v___x_4711_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4711_, 0, v_fst_4707_);
lean_ctor_set(v___x_4711_, 1, v_requestStream_4690_);
lean_ctor_set(v___x_4711_, 2, v_keepAliveTimeout_4691_);
lean_ctor_set(v___x_4711_, 3, v_currentTimeout_4692_);
lean_ctor_set(v___x_4711_, 4, v_headerTimeout_4693_);
lean_ctor_set(v___x_4711_, 5, v_response_4694_);
lean_ctor_set(v___x_4711_, 6, v_respStream_4695_);
lean_ctor_set(v___x_4711_, 7, v_expectData_4697_);
lean_ctor_set(v___x_4711_, 8, v_pendingHead_4699_);
lean_ctor_set_uint8(v___x_4711_, sizeof(void*)*9, v_requiresData_4696_);
lean_ctor_set_uint8(v___x_4711_, sizeof(void*)*9 + 1, v_handlerDispatched_4698_);
v___x_4712_ = lean_box(v___x_4679_);
lean_inc_ref(v___f_4680_);
lean_inc_ref(v___x_4711_);
lean_inc_ref(v_connectionContext_4678_);
lean_inc_ref(v_config_4677_);
lean_inc(v_handler_4676_);
lean_inc_ref(v_responseBodyInstance_4675_);
lean_inc_ref(v_h_4674_);
v___f_4713_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4713_, 0, v_h_4674_);
lean_closure_set(v___f_4713_, 1, v_responseBodyInstance_4675_);
lean_closure_set(v___f_4713_, 2, v_handler_4676_);
lean_closure_set(v___f_4713_, 3, v_config_4677_);
lean_closure_set(v___f_4713_, 4, v_connectionContext_4678_);
lean_closure_set(v___f_4713_, 5, v_events_4708_);
lean_closure_set(v___f_4713_, 6, v___x_4711_);
lean_closure_set(v___f_4713_, 7, v___x_4712_);
lean_closure_set(v___f_4713_, 8, v___f_4680_);
v___x_4714_ = lean_unsigned_to_nat(0u);
v___x_4715_ = lean_nat_dec_lt(v___x_4714_, v_size_4710_);
lean_dec(v_size_4710_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
lean_dec_ref(v___f_4713_);
lean_dec_ref(v_data_4709_);
lean_dec_ref(v___f_4684_);
lean_dec_ref(v___f_4683_);
lean_dec(v_socket_4682_);
lean_dec_ref(v_inst_4681_);
v___x_4716_ = lean_box(0);
v___x_4717_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4674_, v_responseBodyInstance_4675_, v_handler_4676_, v_config_4677_, v_connectionContext_4678_, v_events_4708_, v___x_4711_, v___x_4679_, v___f_4680_, v___x_4716_);
return v___x_4717_;
}
else
{
lean_object* v_sendAll_4718_; lean_object* v___f_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
lean_dec_ref(v_events_4708_);
lean_dec_ref(v___f_4680_);
lean_dec_ref(v_connectionContext_4678_);
lean_dec_ref(v_config_4677_);
lean_dec(v_handler_4676_);
lean_dec_ref(v_responseBodyInstance_4675_);
lean_dec_ref(v_h_4674_);
v_sendAll_4718_ = lean_ctor_get(v_inst_4681_, 1);
lean_inc_ref(v_sendAll_4718_);
lean_dec_ref(v_inst_4681_);
v___f_4719_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4719_, 0, v___x_4711_);
lean_closure_set(v___f_4719_, 1, v___f_4713_);
v___x_4720_ = lean_apply_3(v_sendAll_4718_, v_socket_4682_, v_data_4709_, lean_box(0));
v___x_4721_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4714_, v___x_4679_, v___x_4720_, v___f_4683_);
v___x_4722_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4714_, v___x_4679_, v___x_4721_, v___f_4684_);
v___x_4723_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4714_, v___x_4679_, v___x_4722_, v___f_4719_);
return v___x_4723_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_4674_ = stack[0].m_obj;
lean_object* v_responseBodyInstance_4675_ = stack[1].m_obj;
lean_object* v_handler_4676_ = stack[2].m_obj;
lean_object* v_config_4677_ = stack[3].m_obj;
lean_object* v_connectionContext_4678_ = stack[4].m_obj;
uint8_t v___x_4679_ = stack[5].m_num;
lean_object* v___f_4680_ = stack[6].m_obj;
lean_object* v_inst_4681_ = stack[7].m_obj;
lean_object* v_socket_4682_ = stack[8].m_obj;
lean_object* v___f_4683_ = stack[9].m_obj;
lean_object* v___f_4684_ = stack[10].m_obj;
lean_object* v_x_4685_ = stack[11].m_obj;
lean_object* v_____s_4686_ = stack[12].m_obj;
lean_object* v_res_4732_;
v_res_4732_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4674_, v_responseBodyInstance_4675_, v_handler_4676_, v_config_4677_, v_connectionContext_4678_, v___x_4679_, v___f_4680_, v_inst_4681_, v_socket_4682_, v___f_4683_, v___f_4684_, v_x_4685_, v_____s_4686_);
stack->m_obj
 = v_res_4732_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4733_, lean_object* v_responseBodyInstance_4734_, lean_object* v_handler_4735_, lean_object* v_config_4736_, lean_object* v_connectionContext_4737_, lean_object* v___x_4738_, lean_object* v___f_4739_, lean_object* v_inst_4740_, lean_object* v_socket_4741_, lean_object* v___f_4742_, lean_object* v___f_4743_, lean_object* v_x_4744_, lean_object* v_____s_4745_, lean_object* v___y_4746_){
_start:
{
uint8_t v___x_5845__boxed_4747_; lean_object* v_res_4748_; 
v___x_5845__boxed_4747_ = lean_unbox(v___x_4738_);
v_res_4748_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4733_, v_responseBodyInstance_4734_, v_handler_4735_, v_config_4736_, v_connectionContext_4737_, v___x_5845__boxed_4747_, v___f_4739_, v_inst_4740_, v_socket_4741_, v___f_4742_, v___f_4743_, v_x_4744_, v_____s_4745_);
return v_res_4748_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4749_, lean_object* v_x_4750_){
_start:
{
if (lean_obj_tag(v_x_4750_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4760_; 
v_a_4752_ = lean_ctor_get(v_x_4750_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_x_4750_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4754_ = v_x_4750_;
v_isShared_4755_ = v_isSharedCheck_4760_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v_x_4750_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4760_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4758_; 
v___x_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
return v___x_4758_;
}
}
}
else
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec_ref_known(v_x_4750_, 1);
v___x_4761_ = l_IO_Promise_result_x21___redArg(v_a_4749_);
v___x_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4749_ = stack[0].m_obj;
lean_object* v_x_4750_ = stack[1].m_obj;
lean_object* v_res_4763_;
v_res_4763_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4749_, v_x_4750_);
stack->m_obj
 = v_res_4763_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4764_, lean_object* v_x_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4764_, v_x_4765_);
lean_dec(v_a_4764_);
return v_res_4767_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4768_, lean_object* v___x_4769_, lean_object* v___x_4770_, uint8_t v___x_4771_, lean_object* v_x_4772_){
_start:
{
if (lean_obj_tag(v_x_4772_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4782_; 
lean_dec_ref(v___x_4770_);
lean_dec(v___x_4769_);
lean_dec_ref(v___f_4768_);
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
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4794_; 
v_a_4783_ = lean_ctor_get(v_x_4772_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_x_4772_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4785_ = v_x_4772_;
v_isShared_4786_ = v_isSharedCheck_4794_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v_x_4772_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4794_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___f_4787_; lean_object* v___x_4788_; lean_object* v___x_4790_; 
lean_inc(v_a_4783_);
v___f_4787_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4787_, 0, v_a_4783_);
lean_inc(v___x_4769_);
v___x_4788_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4768_, v___x_4769_, v_a_4783_, v___x_4770_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4788_);
v___x_4790_ = v___x_4785_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4788_);
v___x_4790_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
v___x_4792_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4769_, v___x_4771_, v___x_4791_, v___f_4787_);
return v___x_4792_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4768_ = stack[0].m_obj;
lean_object* v___x_4769_ = stack[1].m_obj;
lean_object* v___x_4770_ = stack[2].m_obj;
uint8_t v___x_4771_ = stack[3].m_num;
lean_object* v_x_4772_ = stack[4].m_obj;
lean_object* v_res_4795_;
v_res_4795_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4768_, v___x_4769_, v___x_4770_, v___x_4771_, v_x_4772_);
stack->m_obj
 = v_res_4795_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4796_, lean_object* v___x_4797_, lean_object* v___x_4798_, lean_object* v___x_4799_, lean_object* v_x_4800_, lean_object* v___y_4801_){
_start:
{
uint8_t v___x_6003__boxed_4802_; lean_object* v_res_4803_; 
v___x_6003__boxed_4802_ = lean_unbox(v___x_4799_);
v_res_4803_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4796_, v___x_4797_, v___x_4798_, v___x_6003__boxed_4802_, v_x_4800_);
return v_res_4803_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4804_, lean_object* v_h_4805_, lean_object* v_responseBodyInstance_4806_, lean_object* v_handler_4807_, lean_object* v___f_4808_, lean_object* v_inst_4809_, lean_object* v_socket_4810_, lean_object* v_connectionContext_4811_, lean_object* v_extensions_4812_, lean_object* v___f_4813_, lean_object* v___f_4814_, lean_object* v_machine_4815_, lean_object* v_a_4816_, lean_object* v___x_4817_, lean_object* v___f_4818_, lean_object* v_x_4819_){
_start:
{
if (lean_obj_tag(v_x_4819_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v___f_4818_);
lean_dec(v___x_4817_);
lean_dec_ref(v_a_4816_);
lean_dec_ref(v_machine_4815_);
lean_dec_ref(v___f_4814_);
lean_dec_ref(v___f_4813_);
lean_dec(v_extensions_4812_);
lean_dec_ref(v_connectionContext_4811_);
lean_dec(v_socket_4810_);
lean_dec_ref(v_inst_4809_);
lean_dec_ref(v___f_4808_);
lean_dec(v_handler_4807_);
lean_dec_ref(v_responseBodyInstance_4806_);
lean_dec_ref(v_h_4805_);
lean_dec_ref(v_config_4804_);
v_a_4821_ = lean_ctor_get(v_x_4819_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v_x_4819_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4823_ = v_x_4819_;
v_isShared_4824_ = v_isSharedCheck_4829_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v_x_4819_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4829_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4827_; 
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4855_; 
v_a_4830_ = lean_ctor_get(v_x_4819_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v_x_4819_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4832_ = v_x_4819_;
v_isShared_4833_ = v_isSharedCheck_4855_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v_x_4819_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4855_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_keepAliveTimeout_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; lean_object* v___x_4838_; lean_object* v___f_4839_; lean_object* v___x_4840_; lean_object* v___f_4841_; lean_object* v___x_4842_; lean_object* v___f_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___f_4847_; lean_object* v___x_4848_; lean_object* v___x_4850_; 
v_keepAliveTimeout_4834_ = lean_ctor_get(v_config_4804_, 5);
lean_inc_n(v_keepAliveTimeout_4834_, 2);
v___x_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4835_, 0, v_keepAliveTimeout_4834_);
v___x_4836_ = lean_box(0);
v___x_4837_ = 0;
v___x_4838_ = lean_box(v___x_4837_);
lean_inc_ref_n(v_connectionContext_4811_, 2);
lean_inc(v_socket_4810_);
lean_inc_ref(v_inst_4809_);
lean_inc_ref(v_config_4804_);
lean_inc_n(v_handler_4807_, 2);
lean_inc_ref(v_responseBodyInstance_4806_);
lean_inc_ref_n(v_h_4805_, 2);
v___f_4839_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4839_, 0, v___x_4838_);
lean_closure_set(v___f_4839_, 1, v_h_4805_);
lean_closure_set(v___f_4839_, 2, v_responseBodyInstance_4806_);
lean_closure_set(v___f_4839_, 3, v_handler_4807_);
lean_closure_set(v___f_4839_, 4, v_config_4804_);
lean_closure_set(v___f_4839_, 5, v___f_4808_);
lean_closure_set(v___f_4839_, 6, v_inst_4809_);
lean_closure_set(v___f_4839_, 7, v_socket_4810_);
lean_closure_set(v___f_4839_, 8, v_connectionContext_4811_);
v___x_4840_ = lean_box(v___x_4837_);
v___f_4841_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4841_, 0, v_h_4805_);
lean_closure_set(v___f_4841_, 1, v_handler_4807_);
lean_closure_set(v___f_4841_, 2, v_extensions_4812_);
lean_closure_set(v___f_4841_, 3, v_connectionContext_4811_);
lean_closure_set(v___f_4841_, 4, v___x_4840_);
lean_closure_set(v___f_4841_, 5, v___f_4839_);
v___x_4842_ = lean_box(v___x_4837_);
v___f_4843_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4843_, 0, v_h_4805_);
lean_closure_set(v___f_4843_, 1, v_responseBodyInstance_4806_);
lean_closure_set(v___f_4843_, 2, v_handler_4807_);
lean_closure_set(v___f_4843_, 3, v_config_4804_);
lean_closure_set(v___f_4843_, 4, v_connectionContext_4811_);
lean_closure_set(v___f_4843_, 5, v___x_4842_);
lean_closure_set(v___f_4843_, 6, v___f_4841_);
lean_closure_set(v___f_4843_, 7, v_inst_4809_);
lean_closure_set(v___f_4843_, 8, v_socket_4810_);
lean_closure_set(v___f_4843_, 9, v___f_4813_);
lean_closure_set(v___f_4843_, 10, v___f_4814_);
v___x_4844_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4844_, 0, v_machine_4815_);
lean_ctor_set(v___x_4844_, 1, v_a_4816_);
lean_ctor_set(v___x_4844_, 2, v___x_4835_);
lean_ctor_set(v___x_4844_, 3, v_keepAliveTimeout_4834_);
lean_ctor_set(v___x_4844_, 4, v___x_4836_);
lean_ctor_set(v___x_4844_, 5, v_a_4830_);
lean_ctor_set(v___x_4844_, 6, v___x_4836_);
lean_ctor_set(v___x_4844_, 7, v___x_4817_);
lean_ctor_set(v___x_4844_, 8, v___x_4836_);
lean_ctor_set_uint8(v___x_4844_, sizeof(void*)*9, v___x_4837_);
lean_ctor_set_uint8(v___x_4844_, sizeof(void*)*9 + 1, v___x_4837_);
v___x_4845_ = lean_unsigned_to_nat(0u);
v___x_4846_ = lean_box(v___x_4837_);
v___f_4847_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4847_, 0, v___f_4843_);
lean_closure_set(v___f_4847_, 1, v___x_4845_);
lean_closure_set(v___f_4847_, 2, v___x_4844_);
lean_closure_set(v___f_4847_, 3, v___x_4846_);
v___x_4848_ = lean_io_promise_new();
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4848_);
v___x_4850_ = v___x_4832_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4850_);
v___x_4852_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4845_, v___x_4837_, v___x_4851_, v___f_4847_);
v___x_4853_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4845_, v___x_4837_, v___x_4852_, v___f_4818_);
return v___x_4853_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_4804_ = stack[0].m_obj;
lean_object* v_h_4805_ = stack[1].m_obj;
lean_object* v_responseBodyInstance_4806_ = stack[2].m_obj;
lean_object* v_handler_4807_ = stack[3].m_obj;
lean_object* v___f_4808_ = stack[4].m_obj;
lean_object* v_inst_4809_ = stack[5].m_obj;
lean_object* v_socket_4810_ = stack[6].m_obj;
lean_object* v_connectionContext_4811_ = stack[7].m_obj;
lean_object* v_extensions_4812_ = stack[8].m_obj;
lean_object* v___f_4813_ = stack[9].m_obj;
lean_object* v___f_4814_ = stack[10].m_obj;
lean_object* v_machine_4815_ = stack[11].m_obj;
lean_object* v_a_4816_ = stack[12].m_obj;
lean_object* v___x_4817_ = stack[13].m_obj;
lean_object* v___f_4818_ = stack[14].m_obj;
lean_object* v_x_4819_ = stack[15].m_obj;
lean_object* v_res_4856_;
v_res_4856_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4804_, v_h_4805_, v_responseBodyInstance_4806_, v_handler_4807_, v___f_4808_, v_inst_4809_, v_socket_4810_, v_connectionContext_4811_, v_extensions_4812_, v___f_4813_, v___f_4814_, v_machine_4815_, v_a_4816_, v___x_4817_, v___f_4818_, v_x_4819_);
stack->m_obj
 = v_res_4856_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4857_ = _args[0];
lean_object* v_h_4858_ = _args[1];
lean_object* v_responseBodyInstance_4859_ = _args[2];
lean_object* v_handler_4860_ = _args[3];
lean_object* v___f_4861_ = _args[4];
lean_object* v_inst_4862_ = _args[5];
lean_object* v_socket_4863_ = _args[6];
lean_object* v_connectionContext_4864_ = _args[7];
lean_object* v_extensions_4865_ = _args[8];
lean_object* v___f_4866_ = _args[9];
lean_object* v___f_4867_ = _args[10];
lean_object* v_machine_4868_ = _args[11];
lean_object* v_a_4869_ = _args[12];
lean_object* v___x_4870_ = _args[13];
lean_object* v___f_4871_ = _args[14];
lean_object* v_x_4872_ = _args[15];
lean_object* v___y_4873_ = _args[16];
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4857_, v_h_4858_, v_responseBodyInstance_4859_, v_handler_4860_, v___f_4861_, v_inst_4862_, v_socket_4863_, v_connectionContext_4864_, v_extensions_4865_, v___f_4866_, v___f_4867_, v_machine_4868_, v_a_4869_, v___x_4870_, v___f_4871_, v_x_4872_);
return v_res_4874_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4875_, lean_object* v_h_4876_, lean_object* v_responseBodyInstance_4877_, lean_object* v_handler_4878_, lean_object* v___f_4879_, lean_object* v_inst_4880_, lean_object* v_socket_4881_, lean_object* v_connectionContext_4882_, lean_object* v_extensions_4883_, lean_object* v___f_4884_, lean_object* v___f_4885_, lean_object* v_machine_4886_, lean_object* v___f_4887_, lean_object* v_x_4888_){
_start:
{
if (lean_obj_tag(v_x_4888_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4898_; 
lean_dec_ref(v___f_4887_);
lean_dec_ref(v_machine_4886_);
lean_dec_ref(v___f_4885_);
lean_dec_ref(v___f_4884_);
lean_dec(v_extensions_4883_);
lean_dec_ref(v_connectionContext_4882_);
lean_dec(v_socket_4881_);
lean_dec_ref(v_inst_4880_);
lean_dec_ref(v___f_4879_);
lean_dec(v_handler_4878_);
lean_dec_ref(v_responseBodyInstance_4877_);
lean_dec_ref(v_h_4876_);
lean_dec_ref(v_config_4875_);
v_a_4890_ = lean_ctor_get(v_x_4888_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_x_4888_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4892_ = v_x_4888_;
v_isShared_4893_ = v_isSharedCheck_4898_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v_x_4888_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4898_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4893_ == 0)
{
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
lean_object* v___x_4896_; 
v___x_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
return v___x_4896_;
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4913_; 
v_a_4899_ = lean_ctor_get(v_x_4888_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v_x_4888_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4901_ = v_x_4888_;
v_isShared_4902_ = v_isSharedCheck_4913_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v_x_4888_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4913_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___f_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4909_; 
v___x_4903_ = lean_box(0);
v___f_4904_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4904_, 0, v_config_4875_);
lean_closure_set(v___f_4904_, 1, v_h_4876_);
lean_closure_set(v___f_4904_, 2, v_responseBodyInstance_4877_);
lean_closure_set(v___f_4904_, 3, v_handler_4878_);
lean_closure_set(v___f_4904_, 4, v___f_4879_);
lean_closure_set(v___f_4904_, 5, v_inst_4880_);
lean_closure_set(v___f_4904_, 6, v_socket_4881_);
lean_closure_set(v___f_4904_, 7, v_connectionContext_4882_);
lean_closure_set(v___f_4904_, 8, v_extensions_4883_);
lean_closure_set(v___f_4904_, 9, v___f_4884_);
lean_closure_set(v___f_4904_, 10, v___f_4885_);
lean_closure_set(v___f_4904_, 11, v_machine_4886_);
lean_closure_set(v___f_4904_, 12, v_a_4899_);
lean_closure_set(v___f_4904_, 13, v___x_4903_);
lean_closure_set(v___f_4904_, 14, v___f_4887_);
v___x_4905_ = lean_unsigned_to_nat(0u);
v___x_4906_ = 0;
v___x_4907_ = l_Std_CloseableChannel_new___redArg(v___x_4903_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4907_);
v___x_4909_ = v___x_4901_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4907_);
v___x_4909_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
v___x_4911_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4905_, v___x_4906_, v___x_4910_, v___f_4904_);
return v___x_4911_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_4875_ = stack[0].m_obj;
lean_object* v_h_4876_ = stack[1].m_obj;
lean_object* v_responseBodyInstance_4877_ = stack[2].m_obj;
lean_object* v_handler_4878_ = stack[3].m_obj;
lean_object* v___f_4879_ = stack[4].m_obj;
lean_object* v_inst_4880_ = stack[5].m_obj;
lean_object* v_socket_4881_ = stack[6].m_obj;
lean_object* v_connectionContext_4882_ = stack[7].m_obj;
lean_object* v_extensions_4883_ = stack[8].m_obj;
lean_object* v___f_4884_ = stack[9].m_obj;
lean_object* v___f_4885_ = stack[10].m_obj;
lean_object* v_machine_4886_ = stack[11].m_obj;
lean_object* v___f_4887_ = stack[12].m_obj;
lean_object* v_x_4888_ = stack[13].m_obj;
lean_object* v_res_4914_;
v_res_4914_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4875_, v_h_4876_, v_responseBodyInstance_4877_, v_handler_4878_, v___f_4879_, v_inst_4880_, v_socket_4881_, v_connectionContext_4882_, v_extensions_4883_, v___f_4884_, v___f_4885_, v_machine_4886_, v___f_4887_, v_x_4888_);
stack->m_obj
 = v_res_4914_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4915_, lean_object* v_h_4916_, lean_object* v_responseBodyInstance_4917_, lean_object* v_handler_4918_, lean_object* v___f_4919_, lean_object* v_inst_4920_, lean_object* v_socket_4921_, lean_object* v_connectionContext_4922_, lean_object* v_extensions_4923_, lean_object* v___f_4924_, lean_object* v___f_4925_, lean_object* v_machine_4926_, lean_object* v___f_4927_, lean_object* v_x_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4915_, v_h_4916_, v_responseBodyInstance_4917_, v_handler_4918_, v___f_4919_, v_inst_4920_, v_socket_4921_, v_connectionContext_4922_, v_extensions_4923_, v___f_4924_, v___f_4925_, v_machine_4926_, v___f_4927_, v_x_4928_);
return v_res_4930_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4934_, lean_object* v_h_4935_, lean_object* v_connection_4936_, lean_object* v_config_4937_, lean_object* v_connectionContext_4938_, lean_object* v_handler_4939_){
_start:
{
lean_object* v_responseBodyInstance_4941_; lean_object* v_onFailure_4942_; lean_object* v_socket_4943_; lean_object* v_machine_4944_; lean_object* v_extensions_4945_; lean_object* v___f_4946_; lean_object* v___f_4947_; lean_object* v___f_4948_; lean_object* v___f_4949_; lean_object* v___f_4950_; lean_object* v___f_4951_; lean_object* v___f_4952_; lean_object* v___f_4953_; lean_object* v___f_4954_; lean_object* v___x_4955_; uint8_t v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v_responseBodyInstance_4941_ = lean_ctor_get(v_h_4935_, 0);
lean_inc_ref_n(v_responseBodyInstance_4941_, 2);
v_onFailure_4942_ = lean_ctor_get(v_h_4935_, 2);
v_socket_4943_ = lean_ctor_get(v_connection_4936_, 0);
lean_inc_n(v_socket_4943_, 2);
v_machine_4944_ = lean_ctor_get(v_connection_4936_, 1);
lean_inc_ref(v_machine_4944_);
v_extensions_4945_ = lean_ctor_get(v_connection_4936_, 2);
lean_inc(v_extensions_4945_);
lean_dec_ref(v_connection_4936_);
v___f_4946_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4947_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4948_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4939_);
lean_inc_ref(v_onFailure_4942_);
v___f_4949_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4949_, 0, v_onFailure_4942_);
lean_closure_set(v___f_4949_, 1, v_handler_4939_);
lean_closure_set(v___f_4949_, 2, v___f_4948_);
v___f_4950_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4934_);
v___f_4951_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4951_, 0, v_inst_4934_);
lean_closure_set(v___f_4951_, 1, v_socket_4943_);
lean_inc_ref(v___f_4951_);
v___f_4952_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4952_, 0, v___f_4951_);
v___f_4953_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4953_, 0, v_responseBodyInstance_4941_);
lean_closure_set(v___f_4953_, 1, v___f_4952_);
lean_closure_set(v___f_4953_, 2, v___f_4951_);
lean_closure_set(v___f_4953_, 3, v___f_4946_);
v___f_4954_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4954_, 0, v_config_4937_);
lean_closure_set(v___f_4954_, 1, v_h_4935_);
lean_closure_set(v___f_4954_, 2, v_responseBodyInstance_4941_);
lean_closure_set(v___f_4954_, 3, v_handler_4939_);
lean_closure_set(v___f_4954_, 4, v___f_4950_);
lean_closure_set(v___f_4954_, 5, v_inst_4934_);
lean_closure_set(v___f_4954_, 6, v_socket_4943_);
lean_closure_set(v___f_4954_, 7, v_connectionContext_4938_);
lean_closure_set(v___f_4954_, 8, v_extensions_4945_);
lean_closure_set(v___f_4954_, 9, v___f_4947_);
lean_closure_set(v___f_4954_, 10, v___f_4949_);
lean_closure_set(v___f_4954_, 11, v_machine_4944_);
lean_closure_set(v___f_4954_, 12, v___f_4953_);
v___x_4955_ = lean_unsigned_to_nat(0u);
v___x_4956_ = 0;
v___x_4957_ = l_Std_Http_Body_mkStream();
v___x_4958_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4955_, v___x_4956_, v___x_4957_, v___f_4954_);
return v___x_4958_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4934_ = stack[0].m_obj;
lean_object* v_h_4935_ = stack[1].m_obj;
lean_object* v_connection_4936_ = stack[2].m_obj;
lean_object* v_config_4937_ = stack[3].m_obj;
lean_object* v_connectionContext_4938_ = stack[4].m_obj;
lean_object* v_handler_4939_ = stack[5].m_obj;
lean_object* v_res_4959_;
v_res_4959_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4934_, v_h_4935_, v_connection_4936_, v_config_4937_, v_connectionContext_4938_, v_handler_4939_);
stack->m_obj
 = v_res_4959_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4960_, lean_object* v_h_4961_, lean_object* v_connection_4962_, lean_object* v_config_4963_, lean_object* v_connectionContext_4964_, lean_object* v_handler_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4960_, v_h_4961_, v_connection_4962_, v_config_4963_, v_connectionContext_4964_, v_handler_4965_);
return v_res_4967_;
}
}
lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4968_, lean_object* v_00_u03c3_4969_, lean_object* v_inst_4970_, lean_object* v_h_4971_, lean_object* v_connection_4972_, lean_object* v_config_4973_, lean_object* v_connectionContext_4974_, lean_object* v_handler_4975_){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4970_, v_h_4971_, v_connection_4972_, v_config_4973_, v_connectionContext_4974_, v_handler_4975_);
return v___x_4977_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4970_ = stack[2].m_obj;
lean_object* v_h_4971_ = stack[3].m_obj;
lean_object* v_connection_4972_ = stack[4].m_obj;
lean_object* v_config_4973_ = stack[5].m_obj;
lean_object* v_connectionContext_4974_ = stack[6].m_obj;
lean_object* v_handler_4975_ = stack[7].m_obj;
lean_object* v_res_4978_;
v_res_4978_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_box(0), lean_box(0), v_inst_4970_, v_h_4971_, v_connection_4972_, v_config_4973_, v_connectionContext_4974_, v_handler_4975_);
stack->m_obj
 = v_res_4978_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4979_, lean_object* v_00_u03c3_4980_, lean_object* v_inst_4981_, lean_object* v_h_4982_, lean_object* v_connection_4983_, lean_object* v_config_4984_, lean_object* v_connectionContext_4985_, lean_object* v_handler_4986_, lean_object* v_a_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4979_, v_00_u03c3_4980_, v_inst_4981_, v_h_4982_, v_connection_4983_, v_config_4984_, v_connectionContext_4985_, v_handler_4986_);
return v_res_4988_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = 0;
v___x_4990_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4989_);
return v___x_4990_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = lean_unsigned_to_nat(4096u);
v___x_4992_ = lean_mk_empty_byte_array(v___x_4991_);
return v___x_4992_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4994_ = l_ByteArray_mkIterator(v___x_4993_);
return v___x_4994_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4995_ = 0;
v___x_4996_ = lean_unsigned_to_nat(0u);
v___x_4997_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4998_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4999_ = lean_box(0);
v___x_5000_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
lean_ctor_set(v___x_5000_, 1, v___x_4998_);
lean_ctor_set(v___x_5000_, 2, v___x_4997_);
lean_ctor_set(v___x_5000_, 3, v___x_4996_);
lean_ctor_set(v___x_5000_, 4, v___x_4996_);
lean_ctor_set(v___x_5000_, 5, v___x_4996_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*6, v___x_4995_);
return v___x_5000_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = 1;
v___x_5009_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_5008_);
return v___x_5009_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_5010_; uint8_t v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5010_ = lean_unsigned_to_nat(0u);
v___x_5011_ = 0;
v___x_5012_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_5013_ = lean_box(0);
v___x_5014_ = lean_box(0);
v___x_5015_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_5016_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_5017_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
lean_ctor_set(v___x_5017_, 1, v___x_5015_);
lean_ctor_set(v___x_5017_, 2, v___x_5014_);
lean_ctor_set(v___x_5017_, 3, v___x_5013_);
lean_ctor_set(v___x_5017_, 4, v___x_5012_);
lean_ctor_set(v___x_5017_, 5, v___x_5010_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*6, v___x_5011_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*6 + 1, v___x_5011_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*6 + 2, v___x_5011_);
return v___x_5017_;
}
}
lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_5018_, lean_object* v_client_5019_, lean_object* v_extensions_5020_, lean_object* v_inst_5021_, lean_object* v_inst_5022_, lean_object* v_handler_5023_, lean_object* v_x_5024_){
_start:
{
if (lean_obj_tag(v_x_5024_) == 0)
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5034_; 
lean_dec(v_handler_5023_);
lean_dec_ref(v_inst_5022_);
lean_dec_ref(v_inst_5021_);
lean_dec(v_extensions_5020_);
lean_dec(v_client_5019_);
lean_dec_ref(v_config_5018_);
v_a_5026_ = lean_ctor_get(v_x_5024_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v_x_5024_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5028_ = v_x_5024_;
v_isShared_5029_ = v_isSharedCheck_5034_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v_x_5024_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5034_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
lean_object* v___x_5032_; 
v___x_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5031_);
return v___x_5032_;
}
}
}
else
{
lean_object* v_a_5035_; uint8_t v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; uint8_t v_enableKeepAlive_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v_a_5035_ = lean_ctor_get(v_x_5024_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v_x_5024_, 1);
v___x_5036_ = 0;
v___x_5037_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_5038_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_5039_ = lean_box(0);
v___x_5040_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_5041_ = l_Std_Http_Config_toH1Config(v_config_5018_);
v_enableKeepAlive_5042_ = lean_ctor_get_uint8(v___x_5041_, sizeof(void*)*18);
v___x_5043_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_5043_, 0, v___x_5037_);
lean_ctor_set(v___x_5043_, 1, v___x_5040_);
lean_ctor_set(v___x_5043_, 2, v___x_5041_);
lean_ctor_set(v___x_5043_, 3, v___x_5038_);
lean_ctor_set(v___x_5043_, 4, v___x_5039_);
lean_ctor_set(v___x_5043_, 5, v___x_5039_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*6, v_enableKeepAlive_5042_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*6 + 1, v___x_5036_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*6 + 2, v___x_5036_);
v___x_5044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5044_, 0, v_client_5019_);
lean_ctor_set(v___x_5044_, 1, v___x_5043_);
lean_ctor_set(v___x_5044_, 2, v_extensions_5020_);
v___x_5045_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_5021_, v_inst_5022_, v___x_5044_, v_config_5018_, v_a_5035_, v_handler_5023_);
return v___x_5045_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serveConnection___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_5018_ = stack[0].m_obj;
lean_object* v_client_5019_ = stack[1].m_obj;
lean_object* v_extensions_5020_ = stack[2].m_obj;
lean_object* v_inst_5021_ = stack[3].m_obj;
lean_object* v_inst_5022_ = stack[4].m_obj;
lean_object* v_handler_5023_ = stack[5].m_obj;
lean_object* v_x_5024_ = stack[6].m_obj;
lean_object* v_res_5046_;
v_res_5046_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_5018_, v_client_5019_, v_extensions_5020_, v_inst_5021_, v_inst_5022_, v_handler_5023_, v_x_5024_);
stack->m_obj
 = v_res_5046_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_5047_, lean_object* v_client_5048_, lean_object* v_extensions_5049_, lean_object* v_inst_5050_, lean_object* v_inst_5051_, lean_object* v_handler_5052_, lean_object* v_x_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_5047_, v_client_5048_, v_extensions_5049_, v_inst_5050_, v_inst_5051_, v_handler_5052_, v_x_5053_);
return v_res_5055_;
}
}
lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_5056_, lean_object* v_inst_5057_, lean_object* v_client_5058_, lean_object* v_handler_5059_, lean_object* v_config_5060_, lean_object* v_extensions_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v___f_5064_; lean_object* v___x_5065_; uint8_t v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___f_5064_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5064_, 0, v_config_5060_);
lean_closure_set(v___f_5064_, 1, v_client_5058_);
lean_closure_set(v___f_5064_, 2, v_extensions_5061_);
lean_closure_set(v___f_5064_, 3, v_inst_5056_);
lean_closure_set(v___f_5064_, 4, v_inst_5057_);
lean_closure_set(v___f_5064_, 5, v_handler_5059_);
v___x_5065_ = lean_unsigned_to_nat(0u);
v___x_5066_ = 0;
lean_inc_ref(v_a_5062_);
v___x_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_a_5062_);
v___x_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
v___x_5069_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5065_, v___x_5066_, v___x_5068_, v___f_5064_);
return v___x_5069_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serveConnection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5056_ = stack[0].m_obj;
lean_object* v_inst_5057_ = stack[1].m_obj;
lean_object* v_client_5058_ = stack[2].m_obj;
lean_object* v_handler_5059_ = stack[3].m_obj;
lean_object* v_config_5060_ = stack[4].m_obj;
lean_object* v_extensions_5061_ = stack[5].m_obj;
lean_object* v_a_5062_ = stack[6].m_obj;
lean_object* v_res_5070_;
v_res_5070_ = l_Std_Http_Server_serveConnection___redArg(v_inst_5056_, v_inst_5057_, v_client_5058_, v_handler_5059_, v_config_5060_, v_extensions_5061_, v_a_5062_);
stack->m_obj
 = v_res_5070_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_5071_, lean_object* v_inst_5072_, lean_object* v_client_5073_, lean_object* v_handler_5074_, lean_object* v_config_5075_, lean_object* v_extensions_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Std_Http_Server_serveConnection___redArg(v_inst_5071_, v_inst_5072_, v_client_5073_, v_handler_5074_, v_config_5075_, v_extensions_5076_, v_a_5077_);
lean_dec_ref(v_a_5077_);
return v_res_5079_;
}
}
lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_5080_, lean_object* v_00_u03c3_5081_, lean_object* v_inst_5082_, lean_object* v_inst_5083_, lean_object* v_client_5084_, lean_object* v_handler_5085_, lean_object* v_config_5086_, lean_object* v_extensions_5087_, lean_object* v_a_5088_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = l_Std_Http_Server_serveConnection___redArg(v_inst_5082_, v_inst_5083_, v_client_5084_, v_handler_5085_, v_config_5086_, v_extensions_5087_, v_a_5088_);
return v___x_5090_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serveConnection_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5082_ = stack[2].m_obj;
lean_object* v_inst_5083_ = stack[3].m_obj;
lean_object* v_client_5084_ = stack[4].m_obj;
lean_object* v_handler_5085_ = stack[5].m_obj;
lean_object* v_config_5086_ = stack[6].m_obj;
lean_object* v_extensions_5087_ = stack[7].m_obj;
lean_object* v_a_5088_ = stack[8].m_obj;
lean_object* v_res_5091_;
v_res_5091_ = l_Std_Http_Server_serveConnection(lean_box(0), lean_box(0), v_inst_5082_, v_inst_5083_, v_client_5084_, v_handler_5085_, v_config_5086_, v_extensions_5087_, v_a_5088_);
stack->m_obj
 = v_res_5091_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_5092_, lean_object* v_00_u03c3_5093_, lean_object* v_inst_5094_, lean_object* v_inst_5095_, lean_object* v_client_5096_, lean_object* v_handler_5097_, lean_object* v_config_5098_, lean_object* v_extensions_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Std_Http_Server_serveConnection(v_t_5092_, v_00_u03c3_5093_, v_inst_5094_, v_inst_5095_, v_client_5096_, v_handler_5097_, v_config_5098_, v_extensions_5099_, v_a_5100_);
lean_dec_ref(v_a_5100_);
return v_res_5102_;
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
