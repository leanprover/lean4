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
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1203_, lean_object* v___f_1204_, lean_object* v___f_1205_, lean_object* v_x1_1206_, lean_object* v_x2_1207_){
_start:
{
lean_object* v_fst_1208_; uint8_t v___x_1209_; 
v_fst_1208_ = lean_ctor_get(v_x2_1207_, 0);
lean_inc(v_fst_1208_);
v___x_1209_ = lean_string_dec_eq(v___x_1203_, v_fst_1208_);
if (v___x_1209_ == 0)
{
lean_object* v_entries_1210_; lean_object* v_indexes_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1222_; 
v_entries_1210_ = lean_ctor_get(v_x1_1206_, 0);
v_indexes_1211_ = lean_ctor_get(v_x1_1206_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x1_1206_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1213_ = v_x1_1206_;
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_indexes_1211_);
lean_inc(v_entries_1210_);
lean_dec(v_x1_1206_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_i_1215_; lean_object* v_f_1216_; lean_object* v_entries_1217_; lean_object* v_indexes_1218_; lean_object* v___x_1220_; 
v_i_1215_ = lean_array_get_size(v_entries_1210_);
v_f_1216_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3_spec__5___lam__0), 2, 1);
lean_closure_set(v_f_1216_, 0, v_i_1215_);
v_entries_1217_ = lean_array_push(v_entries_1210_, v_x2_1207_);
v_indexes_1218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1204_, v___f_1205_, v_indexes_1211_, v_fst_1208_, v_f_1216_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_indexes_1218_);
lean_ctor_set(v___x_1213_, 0, v_entries_1217_);
v___x_1220_ = v___x_1213_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_entries_1217_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_indexes_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_dec(v_fst_1208_);
lean_dec_ref(v_x2_1207_);
lean_dec_ref(v___f_1205_);
lean_dec_ref(v___f_1204_);
return v_x1_1206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1223_, lean_object* v___f_1224_, lean_object* v___f_1225_, lean_object* v_x1_1226_, lean_object* v_x2_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1223_, v___f_1224_, v___f_1225_, v_x1_1226_, v_x2_1227_);
lean_dec_ref(v___x_1223_);
return v_res_1228_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Std_Internal_IndexMultiMap_empty___redArg();
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1259_, lean_object* v_body_1260_, lean_object* v_close_1261_, lean_object* v_isClosed_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___y_1266_; uint8_t v_omitBody_1267_; lean_object* v_reader_1280_; lean_object* v_writer_1281_; lean_object* v_config_1282_; lean_object* v_events_1283_; lean_object* v_error_1284_; lean_object* v_instant_1285_; uint8_t v_keepAlive_1286_; uint8_t v_forcedFlush_1287_; uint8_t v_pullBodyStalled_1288_; lean_object* v___y_1308_; uint8_t v___y_1312_; lean_object* v___y_1313_; uint8_t v___y_1314_; 
if (lean_obj_tag(v_x_1263_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_isClosed_1262_);
lean_dec_ref(v_close_1261_);
lean_dec(v_body_1260_);
lean_dec_ref(v___y_1259_);
v_a_1324_ = lean_ctor_get(v_x_1263_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1263_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1326_ = v_x_1263_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v_x_1263_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
else
{
lean_object* v_writer_1333_; lean_object* v_a_1334_; lean_object* v_reader_1335_; lean_object* v_config_1336_; lean_object* v_events_1337_; lean_object* v_error_1338_; lean_object* v_instant_1339_; uint8_t v_keepAlive_1340_; uint8_t v_forcedFlush_1341_; uint8_t v_pullBodyStalled_1342_; lean_object* v_userData_1343_; lean_object* v_outputData_1344_; lean_object* v_state_1345_; lean_object* v_knownSize_1346_; lean_object* v_messageHead_1347_; uint8_t v_sentMessage_1348_; uint8_t v_userClosedBody_1349_; uint8_t v_omitBody_1350_; lean_object* v_userDataBytes_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1453_; 
v_writer_1333_ = lean_ctor_get(v___y_1259_, 1);
lean_inc_ref(v_writer_1333_);
v_a_1334_ = lean_ctor_get(v_x_1263_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v_x_1263_, 1);
v_reader_1335_ = lean_ctor_get(v___y_1259_, 0);
v_config_1336_ = lean_ctor_get(v___y_1259_, 2);
v_events_1337_ = lean_ctor_get(v___y_1259_, 3);
v_error_1338_ = lean_ctor_get(v___y_1259_, 4);
v_instant_1339_ = lean_ctor_get(v___y_1259_, 5);
v_keepAlive_1340_ = lean_ctor_get_uint8(v___y_1259_, sizeof(void*)*6);
v_forcedFlush_1341_ = lean_ctor_get_uint8(v___y_1259_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1342_ = lean_ctor_get_uint8(v___y_1259_, sizeof(void*)*6 + 2);
v_userData_1343_ = lean_ctor_get(v_writer_1333_, 0);
v_outputData_1344_ = lean_ctor_get(v_writer_1333_, 1);
v_state_1345_ = lean_ctor_get(v_writer_1333_, 2);
v_knownSize_1346_ = lean_ctor_get(v_writer_1333_, 3);
v_messageHead_1347_ = lean_ctor_get(v_writer_1333_, 4);
v_sentMessage_1348_ = lean_ctor_get_uint8(v_writer_1333_, sizeof(void*)*6);
v_userClosedBody_1349_ = lean_ctor_get_uint8(v_writer_1333_, sizeof(void*)*6 + 1);
v_omitBody_1350_ = lean_ctor_get_uint8(v_writer_1333_, sizeof(void*)*6 + 2);
v_userDataBytes_1351_ = lean_ctor_get(v_writer_1333_, 5);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_writer_1333_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1353_ = v_writer_1333_;
v_isShared_1354_ = v_isSharedCheck_1453_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_userDataBytes_1351_);
lean_inc(v_messageHead_1347_);
lean_inc(v_knownSize_1346_);
lean_inc(v_state_1345_);
lean_inc(v_outputData_1344_);
lean_inc(v_userData_1343_);
lean_dec(v_writer_1333_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1453_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_box(1);
v___x_1356_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1345_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_del_object(v___x_1353_);
lean_dec(v_userDataBytes_1351_);
lean_dec(v_messageHead_1347_);
lean_dec(v_knownSize_1346_);
lean_dec(v_state_1345_);
lean_dec_ref(v_outputData_1344_);
lean_dec_ref(v_userData_1343_);
lean_dec(v_a_1334_);
v___y_1266_ = v___y_1259_;
v_omitBody_1267_ = v_omitBody_1350_;
goto v___jp_1265_;
}
else
{
if (v_sentMessage_1348_ == 0)
{
lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1446_; 
lean_inc(v_instant_1339_);
lean_inc(v_error_1338_);
lean_inc_ref(v_events_1337_);
lean_inc_ref(v_config_1336_);
lean_inc_ref(v_reader_1335_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___y_1259_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1447_ = lean_ctor_get(v___y_1259_, 5);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v___y_1259_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v___y_1259_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v___y_1259_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v___y_1259_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v___y_1259_, 0);
lean_dec(v_unused_1452_);
v___x_1358_ = v___y_1259_;
v_isShared_1359_ = v_isSharedCheck_1446_;
goto v_resetjp_1357_;
}
else
{
lean_dec(v___y_1259_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1446_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_status_1360_; uint8_t v___x_1361_; uint8_t v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; uint8_t v___y_1367_; uint8_t v___y_1382_; uint8_t v___y_1383_; uint8_t v___y_1400_; uint16_t v___x_1402_; uint16_t v___x_1403_; uint8_t v___x_1404_; 
v_status_1360_ = lean_ctor_get(v_a_1334_, 0);
v___x_1361_ = 0;
v___x_1402_ = 100;
v___x_1403_ = l_Std_Http_Status_toCode(v_status_1360_);
v___x_1404_ = lean_uint16_dec_le(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_dec(v_messageHead_1347_);
v___y_1400_ = v___x_1404_;
goto v___jp_1399_;
}
else
{
uint16_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = 200;
v___x_1406_ = lean_uint16_dec_lt(v___x_1403_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_dec(v_messageHead_1347_);
v___y_1400_ = v___x_1406_;
goto v___jp_1399_;
}
else
{
uint8_t v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1416_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___f_1434_; uint8_t v___x_1435_; 
lean_del_object(v___x_1358_);
lean_del_object(v___x_1353_);
v___x_1407_ = 1;
v___x_1431_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1407_, v_a_1334_);
v___x_1432_ = l_Std_Http_Header_Name_contentLength;
v___f_1433_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1434_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1435_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1433_, v___f_1434_, v___x_1432_, v___x_1431_);
if (v___x_1435_ == 0)
{
v___y_1416_ = v___x_1431_;
goto v___jp_1415_;
}
else
{
lean_object* v_entries_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_entries_1436_ = lean_ctor_get(v___x_1431_, 0);
lean_inc_ref(v_entries_1436_);
lean_dec_ref(v___x_1431_);
v___x_1437_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_array_get_size(v_entries_1436_);
v___x_1440_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1441_ = lean_nat_dec_lt(v___x_1438_, v___x_1439_);
if (v___x_1441_ == 0)
{
lean_dec_ref(v_entries_1436_);
v___y_1416_ = v___x_1437_;
goto v___jp_1415_;
}
else
{
lean_object* v___f_1442_; size_t v___x_1443_; size_t v___x_1444_; lean_object* v___x_1445_; 
v___f_1442_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__14);
v___x_1443_ = ((size_t)0ULL);
v___x_1444_ = lean_usize_of_nat(v___x_1439_);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1440_, v___f_1442_, v_entries_1436_, v___x_1443_, v___x_1444_, v___x_1437_);
v___y_1416_ = v___x_1445_;
goto v___jp_1415_;
}
}
v___jp_1408_:
{
lean_object* v_message_1410_; lean_object* v___x_2524__overap_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_message_1410_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___x_1407_, v_a_1334_, v___y_1409_);
v___x_2524__overap_1411_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___x_1407_);
v___x_1412_ = lean_apply_2(v___x_2524__overap_1411_, v_outputData_1344_, v_message_1410_);
v___x_1413_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1413_, 0, v_userData_1343_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
lean_ctor_set(v___x_1413_, 2, v_state_1345_);
lean_ctor_set(v___x_1413_, 3, v_knownSize_1346_);
lean_ctor_set(v___x_1413_, 4, v_messageHead_1347_);
lean_ctor_set(v___x_1413_, 5, v_userDataBytes_1351_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*6, v_sentMessage_1348_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*6 + 1, v_userClosedBody_1349_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*6 + 2, v_omitBody_1350_);
v___x_1414_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1414_, 0, v_reader_1335_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
lean_ctor_set(v___x_1414_, 2, v_config_1336_);
lean_ctor_set(v___x_1414_, 3, v_events_1337_);
lean_ctor_set(v___x_1414_, 4, v_error_1338_);
lean_ctor_set(v___x_1414_, 5, v_instant_1339_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*6, v_keepAlive_1340_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*6 + 1, v_forcedFlush_1341_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*6 + 2, v_pullBodyStalled_1342_);
v___y_1266_ = v___x_1414_;
v_omitBody_1267_ = v_omitBody_1350_;
goto v___jp_1265_;
}
v___jp_1415_:
{
lean_object* v___x_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; uint8_t v___x_1420_; 
v___x_1417_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1419_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1420_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1418_, v___f_1419_, v___x_1417_, v___y_1416_);
if (v___x_1420_ == 0)
{
v___y_1409_ = v___y_1416_;
goto v___jp_1408_;
}
else
{
lean_object* v_entries_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_entries_1421_ = lean_ctor_get(v___y_1416_, 0);
lean_inc_ref(v_entries_1421_);
lean_dec_ref(v___y_1416_);
v___x_1422_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__2);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_array_get_size(v_entries_1421_);
v___x_1425_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1426_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
if (v___x_1426_ == 0)
{
lean_dec_ref(v_entries_1421_);
v___y_1409_ = v___x_1422_;
goto v___jp_1408_;
}
else
{
lean_object* v___f_1427_; size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
v___f_1427_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__13);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = lean_usize_of_nat(v___x_1424_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1425_, v___f_1427_, v_entries_1421_, v___x_1428_, v___x_1429_, v___x_1422_);
v___y_1409_ = v___x_1430_;
goto v___jp_1408_;
}
}
}
}
}
v___jp_1362_:
{
lean_object* v_headerSize_1368_; lean_object* v_machine_1369_; lean_object* v_machine_1370_; lean_object* v_reader_1371_; lean_object* v_state_1372_; 
v_headerSize_1368_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1364_, v_a_1334_, v___y_1363_);
v_machine_1369_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1361_, v___y_1365_, v_headerSize_1368_, v___y_1367_);
v_machine_1370_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1361_, v_machine_1369_, v_a_1334_);
lean_dec(v_a_1334_);
v_reader_1371_ = lean_ctor_get(v_machine_1370_, 0);
v_state_1372_ = lean_ctor_get(v_reader_1371_, 0);
if (lean_obj_tag(v_state_1372_) == 7)
{
v___y_1312_ = v___y_1363_;
v___y_1313_ = v_machine_1370_;
v___y_1314_ = v___y_1366_;
goto v___jp_1311_;
}
else
{
if (v___y_1363_ == 0)
{
lean_object* v_writer_1373_; lean_object* v_config_1374_; lean_object* v_events_1375_; lean_object* v_error_1376_; lean_object* v_instant_1377_; uint8_t v_keepAlive_1378_; uint8_t v_forcedFlush_1379_; uint8_t v_pullBodyStalled_1380_; 
lean_inc_ref(v_reader_1371_);
v_writer_1373_ = lean_ctor_get(v_machine_1370_, 1);
lean_inc_ref(v_writer_1373_);
v_config_1374_ = lean_ctor_get(v_machine_1370_, 2);
lean_inc_ref(v_config_1374_);
v_events_1375_ = lean_ctor_get(v_machine_1370_, 3);
lean_inc_ref(v_events_1375_);
v_error_1376_ = lean_ctor_get(v_machine_1370_, 4);
lean_inc(v_error_1376_);
v_instant_1377_ = lean_ctor_get(v_machine_1370_, 5);
lean_inc(v_instant_1377_);
v_keepAlive_1378_ = lean_ctor_get_uint8(v_machine_1370_, sizeof(void*)*6);
v_forcedFlush_1379_ = lean_ctor_get_uint8(v_machine_1370_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1380_ = lean_ctor_get_uint8(v_machine_1370_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_1370_);
v_reader_1280_ = v_reader_1371_;
v_writer_1281_ = v_writer_1373_;
v_config_1282_ = v_config_1374_;
v_events_1283_ = v_events_1375_;
v_error_1284_ = v_error_1376_;
v_instant_1285_ = v_instant_1377_;
v_keepAlive_1286_ = v_keepAlive_1378_;
v_forcedFlush_1287_ = v_forcedFlush_1379_;
v_pullBodyStalled_1288_ = v_pullBodyStalled_1380_;
goto v___jp_1279_;
}
else
{
v___y_1312_ = v___y_1363_;
v___y_1313_ = v_machine_1370_;
v___y_1314_ = v___y_1366_;
goto v___jp_1311_;
}
}
}
v___jp_1381_:
{
uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v_indexes_1386_; lean_object* v___x_1388_; 
v___x_1384_ = 1;
v___x_1385_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1384_, v_a_1334_);
v_indexes_1386_ = lean_ctor_get(v___x_1385_, 1);
lean_inc_ref(v_indexes_1386_);
lean_dec_ref(v___x_1385_);
lean_inc(v_a_1334_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_a_1334_);
v___x_1388_ = v___x_1353_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_userData_1343_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_outputData_1344_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_state_1345_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_knownSize_1346_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_a_1334_);
lean_ctor_set(v_reuseFailAlloc_1398_, 5, v_userDataBytes_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*6 + 1, v_userClosedBody_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*6 + 2, v_omitBody_1350_);
v___x_1388_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v_machine_1390_; 
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*6, v___x_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1388_);
v_machine_1390_ = v___x_1358_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_reader_1335_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_config_1336_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_events_1337_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_error_1338_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_instant_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*6, v_keepAlive_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*6 + 1, v_forcedFlush_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*6 + 2, v_pullBodyStalled_1342_);
v_machine_1390_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; uint8_t v___x_1394_; 
v___x_1391_ = l_Std_Http_Header_Name_contentLength;
v___f_1392_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0));
v___f_1393_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__1));
v___x_1394_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1392_, v___f_1393_, v_indexes_1386_, v___x_1391_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1396_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1392_, v___f_1393_, v_indexes_1386_, v___x_1395_);
lean_dec_ref(v_indexes_1386_);
v___y_1363_ = v___y_1382_;
v___y_1364_ = v___x_1384_;
v___y_1365_ = v_machine_1390_;
v___y_1366_ = v___y_1383_;
v___y_1367_ = v___x_1396_;
goto v___jp_1362_;
}
else
{
lean_dec_ref(v_indexes_1386_);
v___y_1363_ = v___y_1382_;
v___y_1364_ = v___x_1384_;
v___y_1365_ = v_machine_1390_;
v___y_1366_ = v___y_1383_;
v___y_1367_ = v___x_1394_;
goto v___jp_1362_;
}
}
}
}
v___jp_1399_:
{
lean_object* v_state_1401_; 
v_state_1401_ = lean_ctor_get(v_reader_1335_, 0);
if (lean_obj_tag(v_state_1401_) == 7)
{
v___y_1382_ = v___y_1400_;
v___y_1383_ = v___x_1356_;
goto v___jp_1381_;
}
else
{
v___y_1382_ = v___y_1400_;
v___y_1383_ = v___y_1400_;
goto v___jp_1381_;
}
}
}
}
else
{
lean_del_object(v___x_1353_);
lean_dec(v_userDataBytes_1351_);
lean_dec(v_messageHead_1347_);
lean_dec(v_knownSize_1346_);
lean_dec(v_state_1345_);
lean_dec_ref(v_outputData_1344_);
lean_dec_ref(v_userData_1343_);
lean_dec(v_a_1334_);
v___y_1266_ = v___y_1259_;
v_omitBody_1267_ = v_omitBody_1350_;
goto v___jp_1265_;
}
}
}
}
v___jp_1265_:
{
if (v_omitBody_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_isClosed_1262_);
lean_dec_ref(v_close_1261_);
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
lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___f_1272_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1272_, 0, v___y_1266_);
lean_inc_ref(v___f_1272_);
v___f_1273_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1273_, 0, v___f_1272_);
lean_inc(v_body_1260_);
v___f_1274_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1274_, 0, v_close_1261_);
lean_closure_set(v___f_1274_, 1, v_body_1260_);
lean_closure_set(v___f_1274_, 2, v___f_1273_);
lean_closure_set(v___f_1274_, 3, v___f_1272_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = 0;
v___x_1277_ = lean_apply_2(v_isClosed_1262_, v_body_1260_, lean_box(0));
v___x_1278_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1275_, v___x_1276_, v___x_1277_, v___f_1274_);
return v___x_1278_;
}
}
v___jp_1279_:
{
lean_object* v_userData_1289_; lean_object* v_outputData_1290_; lean_object* v_knownSize_1291_; lean_object* v_messageHead_1292_; uint8_t v_sentMessage_1293_; uint8_t v_userClosedBody_1294_; uint8_t v_omitBody_1295_; lean_object* v_userDataBytes_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1305_; 
v_userData_1289_ = lean_ctor_get(v_writer_1281_, 0);
v_outputData_1290_ = lean_ctor_get(v_writer_1281_, 1);
v_knownSize_1291_ = lean_ctor_get(v_writer_1281_, 3);
v_messageHead_1292_ = lean_ctor_get(v_writer_1281_, 4);
v_sentMessage_1293_ = lean_ctor_get_uint8(v_writer_1281_, sizeof(void*)*6);
v_userClosedBody_1294_ = lean_ctor_get_uint8(v_writer_1281_, sizeof(void*)*6 + 1);
v_omitBody_1295_ = lean_ctor_get_uint8(v_writer_1281_, sizeof(void*)*6 + 2);
v_userDataBytes_1296_ = lean_ctor_get(v_writer_1281_, 5);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_writer_1281_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_writer_1281_, 2);
lean_dec(v_unused_1306_);
v___x_1298_ = v_writer_1281_;
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_userDataBytes_1296_);
lean_inc(v_messageHead_1292_);
lean_inc(v_knownSize_1291_);
lean_inc(v_outputData_1290_);
lean_inc(v_userData_1289_);
lean_dec(v_writer_1281_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_box(2);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 2, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_userData_1289_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_outputData_1290_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v_knownSize_1291_);
lean_ctor_set(v_reuseFailAlloc_1304_, 4, v_messageHead_1292_);
lean_ctor_set(v_reuseFailAlloc_1304_, 5, v_userDataBytes_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*6, v_sentMessage_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*6 + 1, v_userClosedBody_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*6 + 2, v_omitBody_1295_);
v___x_1302_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1303_, 0, v_reader_1280_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
lean_ctor_set(v___x_1303_, 2, v_config_1282_);
lean_ctor_set(v___x_1303_, 3, v_events_1283_);
lean_ctor_set(v___x_1303_, 4, v_error_1284_);
lean_ctor_set(v___x_1303_, 5, v_instant_1285_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*6, v_keepAlive_1286_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*6 + 1, v_forcedFlush_1287_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*6 + 2, v_pullBodyStalled_1288_);
v___y_1266_ = v___x_1303_;
v_omitBody_1267_ = v_omitBody_1295_;
goto v___jp_1265_;
}
}
}
v___jp_1307_:
{
lean_object* v_writer_1309_; uint8_t v_omitBody_1310_; 
v_writer_1309_ = lean_ctor_get(v___y_1308_, 1);
v_omitBody_1310_ = lean_ctor_get_uint8(v_writer_1309_, sizeof(void*)*6 + 2);
v___y_1266_ = v___y_1308_;
v_omitBody_1267_ = v_omitBody_1310_;
goto v___jp_1265_;
}
v___jp_1311_:
{
if (v___y_1314_ == 0)
{
v___y_1308_ = v___y_1313_;
goto v___jp_1307_;
}
else
{
if (v___y_1312_ == 0)
{
lean_object* v_reader_1315_; lean_object* v_writer_1316_; lean_object* v_config_1317_; lean_object* v_events_1318_; lean_object* v_error_1319_; lean_object* v_instant_1320_; uint8_t v_keepAlive_1321_; uint8_t v_forcedFlush_1322_; uint8_t v_pullBodyStalled_1323_; 
v_reader_1315_ = lean_ctor_get(v___y_1313_, 0);
lean_inc_ref(v_reader_1315_);
v_writer_1316_ = lean_ctor_get(v___y_1313_, 1);
lean_inc_ref(v_writer_1316_);
v_config_1317_ = lean_ctor_get(v___y_1313_, 2);
lean_inc_ref(v_config_1317_);
v_events_1318_ = lean_ctor_get(v___y_1313_, 3);
lean_inc_ref(v_events_1318_);
v_error_1319_ = lean_ctor_get(v___y_1313_, 4);
lean_inc(v_error_1319_);
v_instant_1320_ = lean_ctor_get(v___y_1313_, 5);
lean_inc(v_instant_1320_);
v_keepAlive_1321_ = lean_ctor_get_uint8(v___y_1313_, sizeof(void*)*6);
v_forcedFlush_1322_ = lean_ctor_get_uint8(v___y_1313_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1323_ = lean_ctor_get_uint8(v___y_1313_, sizeof(void*)*6 + 2);
lean_dec_ref(v___y_1313_);
v_reader_1280_ = v_reader_1315_;
v_writer_1281_ = v_writer_1316_;
v_config_1282_ = v_config_1317_;
v_events_1283_ = v_events_1318_;
v_error_1284_ = v_error_1319_;
v_instant_1285_ = v_instant_1320_;
v_keepAlive_1286_ = v_keepAlive_1321_;
v_forcedFlush_1287_ = v_forcedFlush_1322_;
v_pullBodyStalled_1288_ = v_pullBodyStalled_1323_;
goto v___jp_1279_;
}
else
{
v___y_1308_ = v___y_1313_;
goto v___jp_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1454_, lean_object* v_body_1455_, lean_object* v_close_1456_, lean_object* v_isClosed_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1454_, v_body_1455_, v_close_1456_, v_isClosed_1457_, v_x_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_body_1461_, lean_object* v_close_1462_, lean_object* v_isClosed_1463_, lean_object* v_config_1464_, lean_object* v_line_1465_, lean_object* v_machine_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v___y_1470_; 
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_machine_1466_);
lean_dec_ref(v_line_1465_);
lean_dec_ref(v_isClosed_1463_);
lean_dec_ref(v_close_1462_);
lean_dec(v_body_1461_);
v_a_1476_ = lean_ctor_get(v_x_1467_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_x_1467_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1478_ = v_x_1467_;
v_isShared_1479_ = v_isSharedCheck_1484_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v_x_1467_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1484_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
}
else
{
lean_object* v_a_1485_; 
v_a_1485_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v_x_1467_, 1);
if (lean_obj_tag(v_a_1485_) == 1)
{
lean_object* v_writer_1486_; lean_object* v_reader_1487_; lean_object* v_config_1488_; lean_object* v_events_1489_; lean_object* v_error_1490_; lean_object* v_instant_1491_; uint8_t v_keepAlive_1492_; uint8_t v_forcedFlush_1493_; uint8_t v_pullBodyStalled_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1517_; 
v_writer_1486_ = lean_ctor_get(v_machine_1466_, 1);
v_reader_1487_ = lean_ctor_get(v_machine_1466_, 0);
v_config_1488_ = lean_ctor_get(v_machine_1466_, 2);
v_events_1489_ = lean_ctor_get(v_machine_1466_, 3);
v_error_1490_ = lean_ctor_get(v_machine_1466_, 4);
v_instant_1491_ = lean_ctor_get(v_machine_1466_, 5);
v_keepAlive_1492_ = lean_ctor_get_uint8(v_machine_1466_, sizeof(void*)*6);
v_forcedFlush_1493_ = lean_ctor_get_uint8(v_machine_1466_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1494_ = lean_ctor_get_uint8(v_machine_1466_, sizeof(void*)*6 + 2);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_machine_1466_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1496_ = v_machine_1466_;
v_isShared_1497_ = v_isSharedCheck_1517_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_instant_1491_);
lean_inc(v_error_1490_);
lean_inc(v_events_1489_);
lean_inc(v_config_1488_);
lean_inc(v_writer_1486_);
lean_inc(v_reader_1487_);
lean_dec(v_machine_1466_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1517_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_userData_1498_; lean_object* v_outputData_1499_; lean_object* v_state_1500_; lean_object* v_messageHead_1501_; uint8_t v_sentMessage_1502_; uint8_t v_userClosedBody_1503_; uint8_t v_omitBody_1504_; lean_object* v_userDataBytes_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1515_; 
v_userData_1498_ = lean_ctor_get(v_writer_1486_, 0);
v_outputData_1499_ = lean_ctor_get(v_writer_1486_, 1);
v_state_1500_ = lean_ctor_get(v_writer_1486_, 2);
v_messageHead_1501_ = lean_ctor_get(v_writer_1486_, 4);
v_sentMessage_1502_ = lean_ctor_get_uint8(v_writer_1486_, sizeof(void*)*6);
v_userClosedBody_1503_ = lean_ctor_get_uint8(v_writer_1486_, sizeof(void*)*6 + 1);
v_omitBody_1504_ = lean_ctor_get_uint8(v_writer_1486_, sizeof(void*)*6 + 2);
v_userDataBytes_1505_ = lean_ctor_get(v_writer_1486_, 5);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_writer_1486_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_writer_1486_, 3);
lean_dec(v_unused_1516_);
v___x_1507_ = v_writer_1486_;
v_isShared_1508_ = v_isSharedCheck_1515_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_userDataBytes_1505_);
lean_inc(v_messageHead_1501_);
lean_inc(v_state_1500_);
lean_inc(v_outputData_1499_);
lean_inc(v_userData_1498_);
lean_dec(v_writer_1486_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1515_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 3, v_a_1485_);
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_userData_1498_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_outputData_1499_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_state_1500_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_a_1485_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_messageHead_1501_);
lean_ctor_set(v_reuseFailAlloc_1514_, 5, v_userDataBytes_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*6, v_sentMessage_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*6 + 1, v_userClosedBody_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*6 + 2, v_omitBody_1504_);
v___x_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v___x_1510_);
v___x_1512_ = v___x_1496_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_reader_1487_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_config_1488_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_events_1489_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_error_1490_);
lean_ctor_set(v_reuseFailAlloc_1513_, 5, v_instant_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*6, v_keepAlive_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*6 + 1, v_forcedFlush_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*6 + 2, v_pullBodyStalled_1494_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
v___y_1470_ = v___x_1512_;
goto v___jp_1469_;
}
}
}
}
}
else
{
lean_dec(v_a_1485_);
v___y_1470_ = v_machine_1466_;
goto v___jp_1469_;
}
}
v___jp_1469_:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___f_1471_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1471_, 0, v___y_1470_);
lean_closure_set(v___f_1471_, 1, v_body_1461_);
lean_closure_set(v___f_1471_, 2, v_close_1462_);
lean_closure_set(v___f_1471_, 3, v_isClosed_1463_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = 0;
v___x_1474_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1464_, v_line_1465_);
v___x_1475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1472_, v___x_1473_, v___x_1474_, v___f_1471_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_body_1518_, lean_object* v_close_1519_, lean_object* v_isClosed_1520_, lean_object* v_config_1521_, lean_object* v_line_1522_, lean_object* v_machine_1523_, lean_object* v_x_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_body_1518_, v_close_1519_, v_isClosed_1520_, v_config_1521_, v_line_1522_, v_machine_1523_, v_x_1524_);
lean_dec_ref(v_config_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1527_, lean_object* v_config_1528_, lean_object* v_machine_1529_, lean_object* v_res_1530_){
_start:
{
lean_object* v_close_1532_; lean_object* v_isClosed_1533_; lean_object* v_getKnownSize_1534_; lean_object* v_line_1535_; lean_object* v_body_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_close_1532_ = lean_ctor_get(v_inst_1527_, 1);
lean_inc_ref(v_close_1532_);
v_isClosed_1533_ = lean_ctor_get(v_inst_1527_, 2);
lean_inc_ref(v_isClosed_1533_);
v_getKnownSize_1534_ = lean_ctor_get(v_inst_1527_, 5);
lean_inc_ref(v_getKnownSize_1534_);
lean_dec_ref(v_inst_1527_);
v_line_1535_ = lean_ctor_get(v_res_1530_, 0);
lean_inc_ref(v_line_1535_);
v_body_1536_ = lean_ctor_get(v_res_1530_, 1);
lean_inc_n(v_body_1536_, 2);
lean_dec_ref(v_res_1530_);
v___f_1537_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1537_, 0, v_body_1536_);
lean_closure_set(v___f_1537_, 1, v_close_1532_);
lean_closure_set(v___f_1537_, 2, v_isClosed_1533_);
lean_closure_set(v___f_1537_, 3, v_config_1528_);
lean_closure_set(v___f_1537_, 4, v_line_1535_);
lean_closure_set(v___f_1537_, 5, v_machine_1529_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = 0;
v___x_1540_ = lean_apply_2(v_getKnownSize_1534_, v_body_1536_, lean_box(0));
v___x_1541_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1538_, v___x_1539_, v___x_1540_, v___f_1537_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1542_, lean_object* v_config_1543_, lean_object* v_machine_1544_, lean_object* v_res_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1542_, v_config_1543_, v_machine_1544_, v_res_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1548_, lean_object* v_inst_1549_, lean_object* v_config_1550_, lean_object* v_machine_1551_, lean_object* v_res_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1549_, v_config_1550_, v_machine_1551_, v_res_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1555_, lean_object* v_inst_1556_, lean_object* v_config_1557_, lean_object* v_machine_1558_, lean_object* v_res_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1555_, v_inst_1556_, v_config_1557_, v_machine_1558_, v_res_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v_closed_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_closed_1565_ = lean_ctor_get_uint8(v_____do__lift_1562_, sizeof(void*)*6);
v___x_1566_ = lean_box(v_closed_1565_);
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v_____do__lift_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1573_, lean_object* v_x_1574_){
_start:
{
if (lean_obj_tag(v_x_1574_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___x_1573_);
v_a_1576_ = lean_ctor_get(v_x_1574_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v_x_1574_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v_x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
else
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1593_; 
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_x_1574_, 0);
lean_dec(v_unused_1594_);
v___x_1586_ = v_x_1574_;
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_x_1574_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1573_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1595_, lean_object* v_x_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1595_, v_x_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v_pendingProducer_1607_; lean_object* v_pendingConsumer_1608_; lean_object* v_interestWaiter_1609_; uint8_t v_closed_1610_; lean_object* v_pendingIncompleteChunk_1611_; lean_object* v_closeError_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1621_; 
v___x_1606_ = lean_st_ref_take(v___y_1604_);
v_pendingProducer_1607_ = lean_ctor_get(v___x_1606_, 0);
v_pendingConsumer_1608_ = lean_ctor_get(v___x_1606_, 1);
v_interestWaiter_1609_ = lean_ctor_get(v___x_1606_, 2);
v_closed_1610_ = lean_ctor_get_uint8(v___x_1606_, sizeof(void*)*6);
v_pendingIncompleteChunk_1611_ = lean_ctor_get(v___x_1606_, 4);
v_closeError_1612_ = lean_ctor_get(v___x_1606_, 5);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1606_, 3);
lean_dec(v_unused_1622_);
v___x_1614_ = v___x_1606_;
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_closeError_1612_);
lean_inc(v_pendingIncompleteChunk_1611_);
lean_inc(v_interestWaiter_1609_);
lean_inc(v_pendingConsumer_1608_);
lean_inc(v_pendingProducer_1607_);
lean_dec(v___x_1606_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v___x_1603_);
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_pendingProducer_1607_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_pendingConsumer_1608_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_interestWaiter_1609_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_pendingIncompleteChunk_1611_);
lean_ctor_set(v_reuseFailAlloc_1620_, 5, v_closeError_1612_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*6, v_closed_1610_);
v___x_1617_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_st_ref_put(v___y_1604_, v___x_1617_);
v___x_1619_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1623_, v___y_1624_);
lean_dec(v___y_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1627_, lean_object* v_requestStream_1628_, lean_object* v_keepAliveTimeout_1629_, lean_object* v_currentTimeout_1630_, lean_object* v_headerTimeout_1631_, lean_object* v_response_1632_, lean_object* v_respStream_1633_, lean_object* v_expectData_1634_, uint8_t v_handlerDispatched_1635_, lean_object* v_____r_1636_){
_start:
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1638_ = 0;
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1640_, 0, v_machine_1627_);
lean_ctor_set(v___x_1640_, 1, v_requestStream_1628_);
lean_ctor_set(v___x_1640_, 2, v_keepAliveTimeout_1629_);
lean_ctor_set(v___x_1640_, 3, v_currentTimeout_1630_);
lean_ctor_set(v___x_1640_, 4, v_headerTimeout_1631_);
lean_ctor_set(v___x_1640_, 5, v_response_1632_);
lean_ctor_set(v___x_1640_, 6, v_respStream_1633_);
lean_ctor_set(v___x_1640_, 7, v_expectData_1634_);
lean_ctor_set(v___x_1640_, 8, v___x_1639_);
lean_ctor_set_uint8(v___x_1640_, sizeof(void*)*9, v___x_1638_);
lean_ctor_set_uint8(v___x_1640_, sizeof(void*)*9 + 1, v_handlerDispatched_1635_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1644_, lean_object* v_requestStream_1645_, lean_object* v_keepAliveTimeout_1646_, lean_object* v_currentTimeout_1647_, lean_object* v_headerTimeout_1648_, lean_object* v_response_1649_, lean_object* v_respStream_1650_, lean_object* v_expectData_1651_, lean_object* v_handlerDispatched_1652_, lean_object* v_____r_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v_handlerDispatched_boxed_1655_; lean_object* v_res_1656_; 
v_handlerDispatched_boxed_1655_ = lean_unbox(v_handlerDispatched_1652_);
v_res_1656_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1644_, v_requestStream_1645_, v_keepAliveTimeout_1646_, v_currentTimeout_1647_, v_headerTimeout_1648_, v_response_1649_, v_respStream_1650_, v_expectData_1651_, v_handlerDispatched_boxed_1655_, v_____r_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1657_, lean_object* v_x_1658_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v___f_1657_);
v_a_1660_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1662_ = v_x_1658_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v_x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
v_a_1669_ = lean_ctor_get(v_x_1658_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1670_ = lean_apply_2(v___f_1657_, v_a_1669_, lean_box(0));
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1671_, v_x_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1675_, lean_object* v___f_1676_, lean_object* v___f_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v___f_1677_);
lean_dec_ref(v___f_1676_);
lean_dec_ref(v_requestStream_1675_);
v_a_1680_ = lean_ctor_get(v_x_1678_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1682_ = v_x_1678_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v_x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
}
else
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v_x_1678_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v_x_1678_, 1);
v___x_1690_ = lean_unbox(v_a_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; 
lean_dec_ref(v___f_1677_);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = l_Std_Http_Body_Stream_close(v_requestStream_1675_);
v___x_1693_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___x_1694_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1691_, v___x_1693_, v___x_1692_, v___f_1676_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_a_1689_);
lean_dec_ref(v___f_1676_);
lean_dec_ref(v_requestStream_1675_);
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_apply_2(v___f_1677_, v___x_1695_, lean_box(0));
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1697_, lean_object* v___f_1698_, lean_object* v___f_1699_, lean_object* v_x_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1697_, v___f_1698_, v___f_1699_, v_x_1700_);
return v_res_1702_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1703_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_1704_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___f_1711_; lean_object* v___f_1712_; 
v___x_1710_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1711_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1712_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1712_, 0, v___f_1711_);
lean_closure_set(v___f_1712_, 1, v___x_1710_);
return v___f_1712_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; 
v___x_1721_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1722_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1723_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1723_, 0, v___f_1722_);
lean_closure_set(v___f_1723_, 1, v___x_1721_);
return v___f_1723_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1724_; lean_object* v___x_1725_; 
v___f_1724_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1725_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1725_, 0, lean_box(0));
lean_closure_set(v___x_1725_, 1, lean_box(0));
lean_closure_set(v___x_1725_, 2, lean_box(0));
lean_closure_set(v___x_1725_, 3, v___f_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1726_, lean_object* v___f_1727_, lean_object* v_x_1728_){
_start:
{
if (lean_obj_tag(v_x_1728_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___f_1727_);
lean_dec_ref(v___y_1726_);
v_a_1730_ = lean_ctor_get(v_x_1728_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1728_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1732_ = v_x_1728_;
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v_x_1728_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
else
{
lean_object* v_machine_1739_; lean_object* v_requestStream_1740_; lean_object* v_keepAliveTimeout_1741_; lean_object* v_currentTimeout_1742_; lean_object* v_headerTimeout_1743_; lean_object* v_response_1744_; lean_object* v_respStream_1745_; lean_object* v_expectData_1746_; uint8_t v_handlerDispatched_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___f_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_4870__overap_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref_known(v_x_1728_, 1);
v_machine_1739_ = lean_ctor_get(v___y_1726_, 0);
lean_inc_ref(v_machine_1739_);
v_requestStream_1740_ = lean_ctor_get(v___y_1726_, 1);
lean_inc_ref_n(v_requestStream_1740_, 3);
v_keepAliveTimeout_1741_ = lean_ctor_get(v___y_1726_, 2);
lean_inc(v_keepAliveTimeout_1741_);
v_currentTimeout_1742_ = lean_ctor_get(v___y_1726_, 3);
lean_inc(v_currentTimeout_1742_);
v_headerTimeout_1743_ = lean_ctor_get(v___y_1726_, 4);
lean_inc(v_headerTimeout_1743_);
v_response_1744_ = lean_ctor_get(v___y_1726_, 5);
lean_inc_ref(v_response_1744_);
v_respStream_1745_ = lean_ctor_get(v___y_1726_, 6);
lean_inc(v_respStream_1745_);
v_expectData_1746_ = lean_ctor_get(v___y_1726_, 7);
lean_inc(v_expectData_1746_);
v_handlerDispatched_1747_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1726_);
v___x_1748_ = lean_box(v_handlerDispatched_1747_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1749_, 0, v_machine_1739_);
lean_closure_set(v___f_1749_, 1, v_requestStream_1740_);
lean_closure_set(v___f_1749_, 2, v_keepAliveTimeout_1741_);
lean_closure_set(v___f_1749_, 3, v_currentTimeout_1742_);
lean_closure_set(v___f_1749_, 4, v_headerTimeout_1743_);
lean_closure_set(v___f_1749_, 5, v_response_1744_);
lean_closure_set(v___f_1749_, 6, v_respStream_1745_);
lean_closure_set(v___f_1749_, 7, v_expectData_1746_);
lean_closure_set(v___f_1749_, 8, v___x_1748_);
lean_inc_ref(v___f_1749_);
v___f_1750_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1750_, 0, v___f_1749_);
v___f_1751_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1751_, 0, v_requestStream_1740_);
lean_closure_set(v___f_1751_, 1, v___f_1750_);
lean_closure_set(v___f_1751_, 2, v___f_1749_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = 0;
v___x_1754_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1755_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1756_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1757_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1758_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1758_, 0, lean_box(0));
lean_closure_set(v___x_1758_, 1, lean_box(0));
lean_closure_set(v___x_1758_, 2, v___x_1754_);
lean_closure_set(v___x_1758_, 3, lean_box(0));
lean_closure_set(v___x_1758_, 4, lean_box(0));
lean_closure_set(v___x_1758_, 5, v___x_1757_);
lean_closure_set(v___x_1758_, 6, v___f_1727_);
v___x_4870__overap_1759_ = l_Std_Mutex_atomically___redArg(v___x_1754_, v___f_1755_, v___f_1756_, v_requestStream_1740_, v___x_1758_);
v___x_1760_ = lean_apply_1(v___x_4870__overap_1759_, lean_box(0));
v___x_1761_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1752_, v___x_1753_, v___x_1760_, v___f_1751_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1762_, lean_object* v___f_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1762_, v___f_1763_, v_x_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1767_, lean_object* v_x_1768_){
_start:
{
if (lean_obj_tag(v_x_1768_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___y_1767_);
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
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1787_; 
v_isSharedCheck_1787_ = !lean_is_exclusive(v_x_1768_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v_x_1768_, 0);
lean_dec(v_unused_1788_);
v___x_1780_ = v_x_1768_;
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v_x_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___y_1767_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1789_, v_x_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1793_, lean_object* v___f_1794_, lean_object* v___y_1795_, lean_object* v_x_1796_){
_start:
{
if (lean_obj_tag(v_x_1796_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v___y_1795_);
lean_dec_ref(v___f_1794_);
lean_dec_ref(v_requestStream_1793_);
v_a_1798_ = lean_ctor_get(v_x_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v_x_1796_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v_x_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1798_);
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
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1821_; 
v_a_1807_ = lean_ctor_get(v_x_1796_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1796_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1809_ = v_x_1796_;
v_isShared_1810_ = v_isSharedCheck_1821_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v_x_1796_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1821_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_unbox(v_a_1807_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; 
lean_del_object(v___x_1809_);
lean_dec_ref(v___y_1795_);
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = l_Std_Http_Body_Stream_close(v_requestStream_1793_);
v___x_1814_ = lean_unbox(v_a_1807_);
lean_dec(v_a_1807_);
v___x_1815_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1812_, v___x_1814_, v___x_1813_, v___f_1794_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec(v_a_1807_);
lean_dec_ref(v___f_1794_);
lean_dec_ref(v_requestStream_1793_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1795_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1816_);
v___x_1818_ = v___x_1809_;
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1822_, lean_object* v___f_1823_, lean_object* v___y_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1822_, v___f_1823_, v___y_1824_, v_x_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1828_, lean_object* v_machine_1829_, lean_object* v_a_1830_, uint8_t v_requiresData_1831_, lean_object* v_expectData_1832_, lean_object* v_pendingHead_1833_, lean_object* v_x_1834_){
_start:
{
if (lean_obj_tag(v_x_1834_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_pendingHead_1833_);
lean_dec(v_expectData_1832_);
lean_dec_ref(v_a_1830_);
lean_dec_ref(v_machine_1829_);
v_a_1836_ = lean_ctor_get(v_x_1834_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_x_1834_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v_x_1834_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v_x_1834_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1836_);
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
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1859_; 
v_a_1845_ = lean_ctor_get(v_x_1834_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_x_1834_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1847_ = v_x_1834_;
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v_x_1834_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_keepAliveTimeout_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v_keepAliveTimeout_1849_ = lean_ctor_get(v_config_1828_, 5);
lean_inc_n(v_keepAliveTimeout_1849_, 2);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_keepAliveTimeout_1849_);
v___x_1851_ = lean_box(0);
v___x_1852_ = 0;
v___x_1853_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1853_, 0, v_machine_1829_);
lean_ctor_set(v___x_1853_, 1, v_a_1830_);
lean_ctor_set(v___x_1853_, 2, v___x_1850_);
lean_ctor_set(v___x_1853_, 3, v_keepAliveTimeout_1849_);
lean_ctor_set(v___x_1853_, 4, v___x_1851_);
lean_ctor_set(v___x_1853_, 5, v_a_1845_);
lean_ctor_set(v___x_1853_, 6, v___x_1851_);
lean_ctor_set(v___x_1853_, 7, v_expectData_1832_);
lean_ctor_set(v___x_1853_, 8, v_pendingHead_1833_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*9, v_requiresData_1831_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*9 + 1, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1854_);
v___x_1856_ = v___x_1847_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1854_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1860_, lean_object* v_machine_1861_, lean_object* v_a_1862_, lean_object* v_requiresData_1863_, lean_object* v_expectData_1864_, lean_object* v_pendingHead_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v_requiresData_boxed_1868_; lean_object* v_res_1869_; 
v_requiresData_boxed_1868_ = lean_unbox(v_requiresData_1863_);
v_res_1869_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1860_, v_machine_1861_, v_a_1862_, v_requiresData_boxed_1868_, v_expectData_1864_, v_pendingHead_1865_, v_x_1866_);
lean_dec_ref(v_config_1860_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1870_, lean_object* v_machine_1871_, uint8_t v_requiresData_1872_, lean_object* v_expectData_1873_, lean_object* v_pendingHead_1874_, lean_object* v_x_1875_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_pendingHead_1874_);
lean_dec(v_expectData_1873_);
lean_dec_ref(v_machine_1871_);
lean_dec_ref(v_config_1870_);
v_a_1877_ = lean_ctor_get(v_x_1875_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v_x_1875_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v_x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1901_; 
v_a_1886_ = lean_ctor_get(v_x_1875_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1888_ = v_x_1875_;
v_isShared_1889_ = v_isSharedCheck_1901_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v_x_1875_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1901_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1890_ = lean_box(v_requiresData_1872_);
v___f_1891_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1891_, 0, v_config_1870_);
lean_closure_set(v___f_1891_, 1, v_machine_1871_);
lean_closure_set(v___f_1891_, 2, v_a_1886_);
lean_closure_set(v___f_1891_, 3, v___x_1890_);
lean_closure_set(v___f_1891_, 4, v_expectData_1873_);
lean_closure_set(v___f_1891_, 5, v_pendingHead_1874_);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = 0;
v___x_1895_ = l_Std_CloseableChannel_new___redArg(v___x_1892_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1895_);
v___x_1897_ = v___x_1888_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
v___x_1899_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1893_, v___x_1894_, v___x_1898_, v___f_1891_);
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1902_, lean_object* v_machine_1903_, lean_object* v_requiresData_1904_, lean_object* v_expectData_1905_, lean_object* v_pendingHead_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_){
_start:
{
uint8_t v_requiresData_boxed_1909_; lean_object* v_res_1910_; 
v_requiresData_boxed_1909_ = lean_unbox(v_requiresData_1904_);
v_res_1910_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1902_, v_machine_1903_, v_requiresData_boxed_1909_, v_expectData_1905_, v_pendingHead_1906_, v_x_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1911_, lean_object* v_____r_1912_){
_start:
{
lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = 0;
v___x_1916_ = l_Std_Http_Body_mkStream();
v___x_1917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1914_, v___x_1915_, v___x_1916_, v___f_1911_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1918_, lean_object* v_____r_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1918_, v_____r_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1922_, lean_object* v_val_1923_, lean_object* v___f_1924_, lean_object* v___f_1925_, lean_object* v_x_1926_){
_start:
{
if (lean_obj_tag(v_x_1926_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v___f_1925_);
lean_dec_ref(v___f_1924_);
lean_dec(v_val_1923_);
lean_dec_ref(v_close_1922_);
v_a_1928_ = lean_ctor_get(v_x_1926_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_x_1926_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1930_ = v_x_1926_;
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v_x_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1937_; uint8_t v___x_1938_; 
v_a_1937_ = lean_ctor_get(v_x_1926_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v_x_1926_, 1);
v___x_1938_ = lean_unbox(v_a_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
lean_dec_ref(v___f_1925_);
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = lean_apply_2(v_close_1922_, v_val_1923_, lean_box(0));
v___x_1941_ = lean_unbox(v_a_1937_);
lean_dec(v_a_1937_);
v___x_1942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1939_, v___x_1941_, v___x_1940_, v___f_1924_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_a_1937_);
lean_dec_ref(v___f_1924_);
lean_dec(v_val_1923_);
lean_dec_ref(v_close_1922_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_apply_2(v___f_1925_, v___x_1943_, lean_box(0));
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1945_, lean_object* v_val_1946_, lean_object* v___f_1947_, lean_object* v___f_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1945_, v_val_1946_, v___f_1947_, v___f_1948_, v_x_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1952_, lean_object* v_inst_1953_, lean_object* v___f_1954_, lean_object* v___f_1955_, lean_object* v_____r_1956_){
_start:
{
if (lean_obj_tag(v_respStream_1952_) == 1)
{
lean_object* v_val_1958_; lean_object* v_close_1959_; lean_object* v_isClosed_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_val_1958_ = lean_ctor_get(v_respStream_1952_, 0);
lean_inc_n(v_val_1958_, 2);
lean_dec_ref_known(v_respStream_1952_, 1);
v_close_1959_ = lean_ctor_get(v_inst_1953_, 1);
lean_inc_ref(v_close_1959_);
v_isClosed_1960_ = lean_ctor_get(v_inst_1953_, 2);
lean_inc_ref(v_isClosed_1960_);
lean_dec_ref(v_inst_1953_);
v___f_1961_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1961_, 0, v_close_1959_);
lean_closure_set(v___f_1961_, 1, v_val_1958_);
lean_closure_set(v___f_1961_, 2, v___f_1954_);
lean_closure_set(v___f_1961_, 3, v___f_1955_);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = 0;
v___x_1964_ = lean_apply_2(v_isClosed_1960_, v_val_1958_, lean_box(0));
v___x_1965_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1962_, v___x_1963_, v___x_1964_, v___f_1961_);
return v___x_1965_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v___f_1954_);
lean_dec_ref(v_inst_1953_);
lean_dec(v_respStream_1952_);
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_apply_2(v___f_1955_, v___x_1966_, lean_box(0));
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1968_, lean_object* v_inst_1969_, lean_object* v___f_1970_, lean_object* v___f_1971_, lean_object* v_____r_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1968_, v_inst_1969_, v___f_1970_, v___f_1971_, v_____r_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1975_, lean_object* v_keepAliveTimeout_1976_, lean_object* v_currentTimeout_1977_, lean_object* v_headerTimeout_1978_, lean_object* v_response_1979_, lean_object* v_respStream_1980_, uint8_t v_requiresData_1981_, lean_object* v_expectData_1982_, uint8_t v_handlerDispatched_1983_, lean_object* v_pendingHead_1984_, lean_object* v_x_1985_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_pendingHead_1984_);
lean_dec(v_expectData_1982_);
lean_dec(v_respStream_1980_);
lean_dec_ref(v_response_1979_);
lean_dec(v_headerTimeout_1978_);
lean_dec(v_currentTimeout_1977_);
lean_dec(v_keepAliveTimeout_1976_);
lean_dec_ref(v_requestStream_1975_);
v_a_1987_ = lean_ctor_get(v_x_1985_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_x_1985_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1989_ = v_x_1985_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v_x_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1987_);
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
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2017_; 
v_a_1996_ = lean_ctor_get(v_x_1985_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_x_1985_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1998_ = v_x_1985_;
v_isShared_1999_ = v_isSharedCheck_2017_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v_x_1985_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2017_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_snd_2000_; uint8_t v___x_2001_; 
v_snd_2000_ = lean_ctor_get(v_a_1996_, 1);
v___x_2001_ = lean_unbox(v_snd_2000_);
if (v___x_2001_ == 0)
{
lean_object* v_fst_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v_fst_2002_ = lean_ctor_get(v_a_1996_, 0);
lean_inc(v_fst_2002_);
lean_dec(v_a_1996_);
v___x_2003_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2003_, 0, v_fst_2002_);
lean_ctor_set(v___x_2003_, 1, v_requestStream_1975_);
lean_ctor_set(v___x_2003_, 2, v_keepAliveTimeout_1976_);
lean_ctor_set(v___x_2003_, 3, v_currentTimeout_1977_);
lean_ctor_set(v___x_2003_, 4, v_headerTimeout_1978_);
lean_ctor_set(v___x_2003_, 5, v_response_1979_);
lean_ctor_set(v___x_2003_, 6, v_respStream_1980_);
lean_ctor_set(v___x_2003_, 7, v_expectData_1982_);
lean_ctor_set(v___x_2003_, 8, v_pendingHead_1984_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*9, v_requiresData_1981_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*9 + 1, v_handlerDispatched_1983_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2004_);
v___x_2006_ = v___x_1998_;
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
else
{
lean_object* v_fst_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_dec(v_pendingHead_1984_);
v_fst_2009_ = lean_ctor_get(v_a_1996_, 0);
lean_inc(v_fst_2009_);
lean_dec(v_a_1996_);
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2011_, 0, v_fst_2009_);
lean_ctor_set(v___x_2011_, 1, v_requestStream_1975_);
lean_ctor_set(v___x_2011_, 2, v_keepAliveTimeout_1976_);
lean_ctor_set(v___x_2011_, 3, v_currentTimeout_1977_);
lean_ctor_set(v___x_2011_, 4, v_headerTimeout_1978_);
lean_ctor_set(v___x_2011_, 5, v_response_1979_);
lean_ctor_set(v___x_2011_, 6, v_respStream_1980_);
lean_ctor_set(v___x_2011_, 7, v_expectData_1982_);
lean_ctor_set(v___x_2011_, 8, v___x_2010_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*9, v_requiresData_1981_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*9 + 1, v_handlerDispatched_1983_);
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2012_);
v___x_2014_ = v___x_1998_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_2018_, lean_object* v_keepAliveTimeout_2019_, lean_object* v_currentTimeout_2020_, lean_object* v_headerTimeout_2021_, lean_object* v_response_2022_, lean_object* v_respStream_2023_, lean_object* v_requiresData_2024_, lean_object* v_expectData_2025_, lean_object* v_handlerDispatched_2026_, lean_object* v_pendingHead_2027_, lean_object* v_x_2028_, lean_object* v___y_2029_){
_start:
{
uint8_t v_requiresData_boxed_2030_; uint8_t v_handlerDispatched_boxed_2031_; lean_object* v_res_2032_; 
v_requiresData_boxed_2030_ = lean_unbox(v_requiresData_2024_);
v_handlerDispatched_boxed_2031_ = lean_unbox(v_handlerDispatched_2026_);
v_res_2032_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_2018_, v_keepAliveTimeout_2019_, v_currentTimeout_2020_, v_headerTimeout_2021_, v_response_2022_, v_respStream_2023_, v_requiresData_boxed_2030_, v_expectData_2025_, v_handlerDispatched_boxed_2031_, v_pendingHead_2027_, v_x_2028_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2045_, lean_object* v_inst_2046_, lean_object* v___f_2047_, lean_object* v_handler_2048_, lean_object* v___f_2049_, lean_object* v_inst_2050_, lean_object* v___f_2051_, lean_object* v_connectionContext_2052_, lean_object* v_a_2053_, lean_object* v_x_2054_, lean_object* v___y_2055_){
_start:
{
switch(lean_obj_tag(v_a_2053_))
{
case 0:
{
lean_object* v_head_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v_connectionContext_2052_);
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_inst_2050_);
lean_dec_ref(v___f_2049_);
lean_dec(v_handler_2048_);
lean_dec_ref(v___f_2047_);
lean_dec_ref(v_inst_2046_);
v_head_2057_ = lean_ctor_get(v_a_2053_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2053_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2059_ = v_a_2053_;
v_isShared_2060_ = v_isSharedCheck_2100_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_head_2057_);
lean_dec(v_a_2053_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2100_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_machine_2061_; lean_object* v_requestStream_2062_; lean_object* v_response_2063_; lean_object* v_respStream_2064_; uint8_t v_requiresData_2065_; lean_object* v_expectData_2066_; uint8_t v_handlerDispatched_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2095_; 
v_machine_2061_ = lean_ctor_get(v___y_2055_, 0);
v_requestStream_2062_ = lean_ctor_get(v___y_2055_, 1);
v_response_2063_ = lean_ctor_get(v___y_2055_, 5);
v_respStream_2064_ = lean_ctor_get(v___y_2055_, 6);
v_requiresData_2065_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*9);
v_expectData_2066_ = lean_ctor_get(v___y_2055_, 7);
v_handlerDispatched_2067_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*9 + 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___y_2055_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2096_ = lean_ctor_get(v___y_2055_, 8);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v___y_2055_, 4);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v___y_2055_, 3);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v___y_2055_, 2);
lean_dec(v_unused_2099_);
v___x_2069_ = v___y_2055_;
v_isShared_2070_ = v_isSharedCheck_2095_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_expectData_2066_);
lean_inc(v_respStream_2064_);
lean_inc(v_response_2063_);
lean_inc(v_requestStream_2062_);
lean_inc(v_machine_2061_);
lean_dec(v___y_2055_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2095_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_lingeringTimeout_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v_lingeringTimeout_2071_ = lean_ctor_get(v_config_2045_, 4);
lean_inc(v_lingeringTimeout_2071_);
lean_dec_ref(v_config_2045_);
v___x_2072_ = lean_box(0);
lean_inc(v_head_2057_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
v___x_2074_ = v___x_2059_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_head_2057_);
v___x_2074_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
lean_inc_ref(v_requestStream_2062_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 8, v___x_2074_);
lean_ctor_set(v___x_2069_, 4, v___x_2072_);
lean_ctor_set(v___x_2069_, 3, v_lingeringTimeout_2071_);
lean_ctor_set(v___x_2069_, 2, v___x_2072_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_machine_2061_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_requestStream_2062_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_lingeringTimeout_2071_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_response_2063_);
lean_ctor_set(v_reuseFailAlloc_2093_, 6, v_respStream_2064_);
lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_expectData_2066_);
lean_ctor_set(v_reuseFailAlloc_2093_, 8, v___x_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2093_, sizeof(void*)*9, v_requiresData_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2093_, sizeof(void*)*9 + 1, v_handlerDispatched_2067_);
v___x_2076_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
uint8_t v___x_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = 0;
v___x_2078_ = 1;
v___x_2079_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2077_, v_head_2057_, v___x_2078_);
lean_dec(v_head_2057_);
if (lean_obj_tag(v___x_2079_) == 1)
{
lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___x_5061__overap_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___f_2080_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2080_, 0, v___x_2076_);
v___f_2081_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2081_, 0, v___x_2079_);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = 0;
v___x_2084_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2085_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2086_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_2087_ = l_Std_Mutex_atomically___redArg(v___x_2084_, v___f_2085_, v___f_2086_, v_requestStream_2062_, v___f_2081_);
v___x_2088_ = lean_apply_1(v___x_5061__overap_2087_, lean_box(0));
v___x_2089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2082_, v___x_2083_, v___x_2088_, v___f_2080_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___x_2079_);
lean_dec_ref(v_requestStream_2062_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2076_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_connectionContext_2052_);
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_inst_2050_);
lean_dec_ref(v___f_2049_);
lean_dec(v_handler_2048_);
lean_dec_ref(v___f_2047_);
lean_dec_ref(v_inst_2046_);
lean_dec_ref(v_config_2045_);
v_size_2101_ = lean_ctor_get(v_a_2053_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_a_2053_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2103_ = v_a_2053_;
v_isShared_2104_ = v_isSharedCheck_2128_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_size_2101_);
lean_dec(v_a_2053_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2128_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v_machine_2105_; lean_object* v_requestStream_2106_; lean_object* v_keepAliveTimeout_2107_; lean_object* v_currentTimeout_2108_; lean_object* v_headerTimeout_2109_; lean_object* v_response_2110_; lean_object* v_respStream_2111_; uint8_t v_handlerDispatched_2112_; lean_object* v_pendingHead_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2126_; 
v_machine_2105_ = lean_ctor_get(v___y_2055_, 0);
v_requestStream_2106_ = lean_ctor_get(v___y_2055_, 1);
v_keepAliveTimeout_2107_ = lean_ctor_get(v___y_2055_, 2);
v_currentTimeout_2108_ = lean_ctor_get(v___y_2055_, 3);
v_headerTimeout_2109_ = lean_ctor_get(v___y_2055_, 4);
v_response_2110_ = lean_ctor_get(v___y_2055_, 5);
v_respStream_2111_ = lean_ctor_get(v___y_2055_, 6);
v_handlerDispatched_2112_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*9 + 1);
v_pendingHead_2113_ = lean_ctor_get(v___y_2055_, 8);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___y_2055_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v___y_2055_, 7);
lean_dec(v_unused_2127_);
v___x_2115_ = v___y_2055_;
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_pendingHead_2113_);
lean_inc(v_respStream_2111_);
lean_inc(v_response_2110_);
lean_inc(v_headerTimeout_2109_);
lean_inc(v_currentTimeout_2108_);
lean_inc(v_keepAliveTimeout_2107_);
lean_inc(v_requestStream_2106_);
lean_inc(v_machine_2105_);
lean_dec(v___y_2055_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = 1;
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 7, v_size_2101_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_machine_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_requestStream_2106_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_keepAliveTimeout_2107_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_currentTimeout_2108_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_headerTimeout_2109_);
lean_ctor_set(v_reuseFailAlloc_2125_, 5, v_response_2110_);
lean_ctor_set(v_reuseFailAlloc_2125_, 6, v_respStream_2111_);
lean_ctor_set(v_reuseFailAlloc_2125_, 7, v_size_2101_);
lean_ctor_set(v_reuseFailAlloc_2125_, 8, v_pendingHead_2113_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*9 + 1, v_handlerDispatched_2112_);
v___x_2119_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2121_; 
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*9, v___x_2117_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2119_);
v___x_2121_ = v___x_2103_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2129_; lean_object* v_onFailure_2130_; lean_object* v___f_2131_; lean_object* v___y_2133_; 
lean_dec_ref(v_connectionContext_2052_);
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_inst_2050_);
lean_dec_ref(v___f_2049_);
lean_dec_ref(v_config_2045_);
v_err_2129_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_err_2129_);
lean_dec_ref_known(v_a_2053_, 1);
v_onFailure_2130_ = lean_ctor_get(v_inst_2046_, 2);
lean_inc_ref(v_onFailure_2130_);
lean_dec_ref(v_inst_2046_);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2131_, 0, v___y_2055_);
lean_closure_set(v___f_2131_, 1, v___f_2047_);
switch(lean_obj_tag(v_err_2129_))
{
case 0:
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_2133_ = v___x_2139_;
goto v___jp_2132_;
}
case 1:
{
lean_object* v___x_2140_; 
v___x_2140_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_2133_ = v___x_2140_;
goto v___jp_2132_;
}
case 2:
{
lean_object* v___x_2141_; 
v___x_2141_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_2133_ = v___x_2141_;
goto v___jp_2132_;
}
case 3:
{
lean_object* v___x_2142_; 
v___x_2142_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_2133_ = v___x_2142_;
goto v___jp_2132_;
}
case 4:
{
lean_object* v___x_2143_; 
v___x_2143_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_2133_ = v___x_2143_;
goto v___jp_2132_;
}
case 5:
{
lean_object* v___x_2144_; 
v___x_2144_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_2133_ = v___x_2144_;
goto v___jp_2132_;
}
case 6:
{
lean_object* v___x_2145_; 
v___x_2145_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_2133_ = v___x_2145_;
goto v___jp_2132_;
}
case 7:
{
lean_object* v___x_2146_; 
v___x_2146_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_2133_ = v___x_2146_;
goto v___jp_2132_;
}
case 8:
{
lean_object* v___x_2147_; 
v___x_2147_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_2133_ = v___x_2147_;
goto v___jp_2132_;
}
case 9:
{
lean_object* v___x_2148_; 
v___x_2148_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_2133_ = v___x_2148_;
goto v___jp_2132_;
}
case 10:
{
lean_object* v___x_2149_; 
v___x_2149_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_2133_ = v___x_2149_;
goto v___jp_2132_;
}
default: 
{
lean_object* v_message_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_message_2150_ = lean_ctor_get(v_err_2129_, 0);
lean_inc_ref(v_message_2150_);
lean_dec_ref_known(v_err_2129_, 1);
v___x_2151_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2152_ = lean_string_append(v___x_2151_, v_message_2150_);
lean_dec_ref(v_message_2150_);
v___y_2133_ = v___x_2152_;
goto v___jp_2132_;
}
}
v___jp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2134_ = lean_mk_io_user_error(v___y_2133_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = 0;
v___x_2137_ = lean_apply_3(v_onFailure_2130_, v_handler_2048_, v___x_2134_, lean_box(0));
v___x_2138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2135_, v___x_2136_, v___x_2137_, v___f_2131_);
return v___x_2138_;
}
}
case 4:
{
lean_object* v_requestStream_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_5118__overap_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v_connectionContext_2052_);
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_inst_2050_);
lean_dec(v_handler_2048_);
lean_dec_ref(v___f_2047_);
lean_dec_ref(v_inst_2046_);
lean_dec_ref(v_config_2045_);
v_requestStream_2153_ = lean_ctor_get(v___y_2055_, 1);
lean_inc_ref_n(v_requestStream_2153_, 2);
lean_inc_ref(v___y_2055_);
v___f_2154_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2154_, 0, v___y_2055_);
v___f_2155_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2155_, 0, v_requestStream_2153_);
lean_closure_set(v___f_2155_, 1, v___f_2154_);
lean_closure_set(v___f_2155_, 2, v___y_2055_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = 0;
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
lean_closure_set(v___x_2162_, 6, v___f_2049_);
v___x_5118__overap_2163_ = l_Std_Mutex_atomically___redArg(v___x_2158_, v___f_2159_, v___f_2160_, v_requestStream_2153_, v___x_2162_);
v___x_2164_ = lean_apply_1(v___x_5118__overap_2163_, lean_box(0));
v___x_2165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2156_, v___x_2157_, v___x_2164_, v___f_2155_);
return v___x_2165_;
}
case 6:
{
lean_object* v_machine_2166_; lean_object* v_requestStream_2167_; lean_object* v_respStream_2168_; uint8_t v_requiresData_2169_; lean_object* v_expectData_2170_; lean_object* v_pendingHead_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; lean_object* v___f_2175_; lean_object* v___f_2176_; lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_5143__overap_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_dec_ref(v_connectionContext_2052_);
lean_dec_ref(v___f_2049_);
lean_dec(v_handler_2048_);
lean_dec_ref(v___f_2047_);
lean_dec_ref(v_inst_2046_);
v_machine_2166_ = lean_ctor_get(v___y_2055_, 0);
lean_inc_ref(v_machine_2166_);
v_requestStream_2167_ = lean_ctor_get(v___y_2055_, 1);
lean_inc_ref_n(v_requestStream_2167_, 2);
v_respStream_2168_ = lean_ctor_get(v___y_2055_, 6);
lean_inc(v_respStream_2168_);
v_requiresData_2169_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*9);
v_expectData_2170_ = lean_ctor_get(v___y_2055_, 7);
lean_inc(v_expectData_2170_);
v_pendingHead_2171_ = lean_ctor_get(v___y_2055_, 8);
lean_inc(v_pendingHead_2171_);
lean_dec_ref(v___y_2055_);
v___x_2172_ = lean_box(v_requiresData_2169_);
v___f_2173_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2173_, 0, v_config_2045_);
lean_closure_set(v___f_2173_, 1, v_machine_2166_);
lean_closure_set(v___f_2173_, 2, v___x_2172_);
lean_closure_set(v___f_2173_, 3, v_expectData_2170_);
lean_closure_set(v___f_2173_, 4, v_pendingHead_2171_);
v___f_2174_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2174_, 0, v___f_2173_);
lean_inc_ref(v___f_2174_);
v___f_2175_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2175_, 0, v___f_2174_);
v___f_2176_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2176_, 0, v_respStream_2168_);
lean_closure_set(v___f_2176_, 1, v_inst_2050_);
lean_closure_set(v___f_2176_, 2, v___f_2175_);
lean_closure_set(v___f_2176_, 3, v___f_2174_);
lean_inc_ref(v___f_2176_);
v___f_2177_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2177_, 0, v___f_2176_);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2178_, 0, v_requestStream_2167_);
lean_closure_set(v___f_2178_, 1, v___f_2177_);
lean_closure_set(v___f_2178_, 2, v___f_2176_);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = 0;
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
lean_closure_set(v___x_2185_, 6, v___f_2051_);
v___x_5143__overap_2186_ = l_Std_Mutex_atomically___redArg(v___x_2181_, v___f_2182_, v___f_2183_, v_requestStream_2167_, v___x_2185_);
v___x_2187_ = lean_apply_1(v___x_5143__overap_2186_, lean_box(0));
v___x_2188_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2179_, v___x_2180_, v___x_2187_, v___f_2178_);
return v___x_2188_;
}
case 7:
{
lean_object* v_pendingHead_2189_; 
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_inst_2050_);
lean_dec_ref(v___f_2049_);
lean_dec_ref(v___f_2047_);
v_pendingHead_2189_ = lean_ctor_get(v___y_2055_, 8);
if (lean_obj_tag(v_pendingHead_2189_) == 1)
{
lean_object* v_machine_2190_; lean_object* v_requestStream_2191_; lean_object* v_keepAliveTimeout_2192_; lean_object* v_currentTimeout_2193_; lean_object* v_headerTimeout_2194_; lean_object* v_response_2195_; lean_object* v_respStream_2196_; uint8_t v_requiresData_2197_; lean_object* v_expectData_2198_; uint8_t v_handlerDispatched_2199_; lean_object* v_val_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_inc_ref(v_pendingHead_2189_);
v_machine_2190_ = lean_ctor_get(v___y_2055_, 0);
lean_inc_ref(v_machine_2190_);
v_requestStream_2191_ = lean_ctor_get(v___y_2055_, 1);
lean_inc_ref(v_requestStream_2191_);
v_keepAliveTimeout_2192_ = lean_ctor_get(v___y_2055_, 2);
lean_inc(v_keepAliveTimeout_2192_);
v_currentTimeout_2193_ = lean_ctor_get(v___y_2055_, 3);
lean_inc(v_currentTimeout_2193_);
v_headerTimeout_2194_ = lean_ctor_get(v___y_2055_, 4);
lean_inc(v_headerTimeout_2194_);
v_response_2195_ = lean_ctor_get(v___y_2055_, 5);
lean_inc_ref(v_response_2195_);
v_respStream_2196_ = lean_ctor_get(v___y_2055_, 6);
lean_inc(v_respStream_2196_);
v_requiresData_2197_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*9);
v_expectData_2198_ = lean_ctor_get(v___y_2055_, 7);
lean_inc(v_expectData_2198_);
v_handlerDispatched_2199_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2055_);
v_val_2200_ = lean_ctor_get(v_pendingHead_2189_, 0);
lean_inc(v_val_2200_);
v___x_2201_ = lean_box(v_requiresData_2197_);
v___x_2202_ = lean_box(v_handlerDispatched_2199_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2203_, 0, v_requestStream_2191_);
lean_closure_set(v___f_2203_, 1, v_keepAliveTimeout_2192_);
lean_closure_set(v___f_2203_, 2, v_currentTimeout_2193_);
lean_closure_set(v___f_2203_, 3, v_headerTimeout_2194_);
lean_closure_set(v___f_2203_, 4, v_response_2195_);
lean_closure_set(v___f_2203_, 5, v_respStream_2196_);
lean_closure_set(v___f_2203_, 6, v___x_2201_);
lean_closure_set(v___f_2203_, 7, v_expectData_2198_);
lean_closure_set(v___f_2203_, 8, v___x_2202_);
lean_closure_set(v___f_2203_, 9, v_pendingHead_2189_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = 0;
v___x_2206_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2046_, v_handler_2048_, v_machine_2190_, v_val_2200_, v_config_2045_, v_connectionContext_2052_);
v___x_2207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2204_, v___x_2205_, v___x_2206_, v___f_2203_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref(v_connectionContext_2052_);
lean_dec(v_handler_2048_);
lean_dec_ref(v_inst_2046_);
lean_dec_ref(v_config_2045_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___y_2055_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
default: 
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v_a_2053_);
lean_dec_ref(v_connectionContext_2052_);
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_inst_2050_);
lean_dec_ref(v___f_2049_);
lean_dec(v_handler_2048_);
lean_dec_ref(v___f_2047_);
lean_dec_ref(v_inst_2046_);
lean_dec_ref(v_config_2045_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2055_);
v___x_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2214_, lean_object* v_inst_2215_, lean_object* v___f_2216_, lean_object* v_handler_2217_, lean_object* v___f_2218_, lean_object* v_inst_2219_, lean_object* v___f_2220_, lean_object* v_connectionContext_2221_, lean_object* v_a_2222_, lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2214_, v_inst_2215_, v___f_2216_, v_handler_2217_, v___f_2218_, v_inst_2219_, v___f_2220_, v_connectionContext_2221_, v_a_2222_, v_x_2223_, v___y_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_x_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_handler_2237_, lean_object* v_config_2238_, lean_object* v_connectionContext_2239_, lean_object* v_events_2240_, lean_object* v_state_2241_){
_start:
{
lean_object* v___f_2243_; lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_4072__overap_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___f_2243_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2244_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2244_, 0, v_config_2238_);
lean_closure_set(v___f_2244_, 1, v_inst_2235_);
lean_closure_set(v___f_2244_, 2, v___f_2243_);
lean_closure_set(v___f_2244_, 3, v_handler_2237_);
lean_closure_set(v___f_2244_, 4, v___f_2243_);
lean_closure_set(v___f_2244_, 5, v_inst_2236_);
lean_closure_set(v___f_2244_, 6, v___f_2243_);
lean_closure_set(v___f_2244_, 7, v_connectionContext_2239_);
v___f_2245_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2246_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2247_ = lean_array_size(v_events_2240_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = 0;
v___x_4072__overap_2251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2246_, v_events_2240_, v___f_2244_, v_sz_2247_, v___x_2248_, v_state_2241_);
v___x_2252_ = lean_apply_1(v___x_4072__overap_2251_, lean_box(0));
v___x_2253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2249_, v___x_2250_, v___x_2252_, v___f_2245_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_handler_2256_, lean_object* v_config_2257_, lean_object* v_connectionContext_2258_, lean_object* v_events_2259_, lean_object* v_state_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2254_, v_inst_2255_, v_handler_2256_, v_config_2257_, v_connectionContext_2258_, v_events_2259_, v_state_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2263_, lean_object* v_00_u03b2_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_handler_2267_, lean_object* v_config_2268_, lean_object* v_connectionContext_2269_, lean_object* v_events_2270_, lean_object* v_state_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2265_, v_inst_2266_, v_handler_2267_, v_config_2268_, v_connectionContext_2269_, v_events_2270_, v_state_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2274_, lean_object* v_00_u03b2_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_handler_2278_, lean_object* v_config_2279_, lean_object* v_connectionContext_2280_, lean_object* v_events_2281_, lean_object* v_state_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2274_, v_00_u03b2_2275_, v_inst_2276_, v_inst_2277_, v_handler_2278_, v_config_2279_, v_connectionContext_2280_, v_events_2281_, v_state_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v_x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v_x_2285_, 1);
v___x_2287_ = lean_task_pure(v_a_2286_);
return v___x_2287_;
}
else
{
lean_object* v_a_2288_; 
v_a_2288_ = lean_ctor_get(v_x_2285_, 0);
lean_inc_ref(v_a_2288_);
lean_dec_ref_known(v_x_2285_, 1);
return v_a_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2289_, lean_object* v_requestStream_2290_, lean_object* v_keepAliveTimeout_2291_, lean_object* v_currentTimeout_2292_, lean_object* v_headerTimeout_2293_, lean_object* v_response_2294_, lean_object* v_respStream_2295_, uint8_t v_requiresData_2296_, lean_object* v_expectData_2297_, lean_object* v_x_2298_){
_start:
{
if (lean_obj_tag(v_x_2298_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_expectData_2297_);
lean_dec(v_respStream_2295_);
lean_dec_ref(v_response_2294_);
lean_dec(v_headerTimeout_2293_);
lean_dec(v_currentTimeout_2292_);
lean_dec(v_keepAliveTimeout_2291_);
lean_dec_ref(v_requestStream_2290_);
lean_dec_ref(v_machine_2289_);
v_a_2300_ = lean_ctor_get(v_x_2298_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_x_2298_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v_x_2298_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v_x_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
}
else
{
lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2319_; 
v_isSharedCheck_2319_ = !lean_is_exclusive(v_x_2298_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_x_2298_, 0);
lean_dec(v_unused_2320_);
v___x_2310_ = v_x_2298_;
v_isShared_2311_ = v_isSharedCheck_2319_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v_x_2298_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2319_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2312_ = 1;
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2314_, 0, v_machine_2289_);
lean_ctor_set(v___x_2314_, 1, v_requestStream_2290_);
lean_ctor_set(v___x_2314_, 2, v_keepAliveTimeout_2291_);
lean_ctor_set(v___x_2314_, 3, v_currentTimeout_2292_);
lean_ctor_set(v___x_2314_, 4, v_headerTimeout_2293_);
lean_ctor_set(v___x_2314_, 5, v_response_2294_);
lean_ctor_set(v___x_2314_, 6, v_respStream_2295_);
lean_ctor_set(v___x_2314_, 7, v_expectData_2297_);
lean_ctor_set(v___x_2314_, 8, v___x_2313_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*9, v_requiresData_2296_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*9 + 1, v___x_2312_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2314_);
v___x_2316_ = v___x_2310_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2321_, lean_object* v_requestStream_2322_, lean_object* v_keepAliveTimeout_2323_, lean_object* v_currentTimeout_2324_, lean_object* v_headerTimeout_2325_, lean_object* v_response_2326_, lean_object* v_respStream_2327_, lean_object* v_requiresData_2328_, lean_object* v_expectData_2329_, lean_object* v_x_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v_requiresData_boxed_2332_; lean_object* v_res_2333_; 
v_requiresData_boxed_2332_ = lean_unbox(v_requiresData_2328_);
v_res_2333_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2321_, v_requestStream_2322_, v_keepAliveTimeout_2323_, v_currentTimeout_2324_, v_headerTimeout_2325_, v_response_2326_, v_respStream_2327_, v_requiresData_boxed_2332_, v_expectData_2329_, v_x_2330_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2334_, lean_object* v_response_2335_, lean_object* v___x_2336_, lean_object* v___f_2337_, lean_object* v_x_2338_){
_start:
{
if (lean_obj_tag(v_x_2338_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v___f_2337_);
lean_dec(v___x_2336_);
lean_dec_ref(v_response_2335_);
lean_dec_ref(v_toFunctor_2334_);
v_a_2340_ = lean_ctor_get(v_x_2338_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2338_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2342_ = v_x_2338_;
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v_x_2338_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2363_; 
v_a_2349_ = lean_ctor_get(v_x_2338_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_x_2338_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2351_ = v_x_2338_;
v_isShared_2352_ = v_isSharedCheck_2363_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v_x_2338_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2363_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2353_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2353_, 0, lean_box(0));
lean_closure_set(v___x_2353_, 1, lean_box(0));
lean_closure_set(v___x_2353_, 2, v_toFunctor_2334_);
v___x_2354_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2354_, 0, lean_box(0));
lean_closure_set(v___x_2354_, 1, v_response_2335_);
v___x_2355_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2355_, 0, lean_box(0));
lean_closure_set(v___x_2355_, 1, lean_box(0));
lean_closure_set(v___x_2355_, 2, lean_box(0));
lean_closure_set(v___x_2355_, 3, v___x_2353_);
lean_closure_set(v___x_2355_, 4, v___x_2354_);
v___x_2356_ = 0;
lean_inc(v___x_2336_);
v___x_2357_ = l_BaseIO_chainTask___redArg(v_a_2349_, v___x_2355_, v___x_2336_, v___x_2356_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2357_);
v___x_2359_ = v___x_2351_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
v___x_2361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2336_, v___x_2356_, v___x_2360_, v___f_2337_);
return v___x_2361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2364_, lean_object* v_response_2365_, lean_object* v___x_2366_, lean_object* v___f_2367_, lean_object* v_x_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2364_, v_response_2365_, v___x_2366_, v___f_2367_, v_x_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2372_, lean_object* v_handler_2373_, lean_object* v_extensions_2374_, lean_object* v_connectionContext_2375_, lean_object* v_state_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v_toApplicative_2379_; lean_object* v_pendingHead_2380_; 
v___x_2378_ = l_instMonadBaseIO;
v_toApplicative_2379_ = lean_ctor_get(v___x_2378_, 0);
v_pendingHead_2380_ = lean_ctor_get(v_state_2376_, 8);
lean_inc(v_pendingHead_2380_);
if (lean_obj_tag(v_pendingHead_2380_) == 1)
{
lean_object* v_toFunctor_2381_; lean_object* v_machine_2382_; lean_object* v_requestStream_2383_; lean_object* v_keepAliveTimeout_2384_; lean_object* v_currentTimeout_2385_; lean_object* v_headerTimeout_2386_; lean_object* v_response_2387_; lean_object* v_respStream_2388_; uint8_t v_requiresData_2389_; lean_object* v_expectData_2390_; lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2413_; 
v_toFunctor_2381_ = lean_ctor_get(v_toApplicative_2379_, 0);
v_machine_2382_ = lean_ctor_get(v_state_2376_, 0);
lean_inc_ref(v_machine_2382_);
v_requestStream_2383_ = lean_ctor_get(v_state_2376_, 1);
lean_inc_ref(v_requestStream_2383_);
v_keepAliveTimeout_2384_ = lean_ctor_get(v_state_2376_, 2);
lean_inc(v_keepAliveTimeout_2384_);
v_currentTimeout_2385_ = lean_ctor_get(v_state_2376_, 3);
lean_inc(v_currentTimeout_2385_);
v_headerTimeout_2386_ = lean_ctor_get(v_state_2376_, 4);
lean_inc(v_headerTimeout_2386_);
v_response_2387_ = lean_ctor_get(v_state_2376_, 5);
lean_inc_ref(v_response_2387_);
v_respStream_2388_ = lean_ctor_get(v_state_2376_, 6);
lean_inc(v_respStream_2388_);
v_requiresData_2389_ = lean_ctor_get_uint8(v_state_2376_, sizeof(void*)*9);
v_expectData_2390_ = lean_ctor_get(v_state_2376_, 7);
lean_inc(v_expectData_2390_);
lean_dec_ref(v_state_2376_);
v_val_2391_ = lean_ctor_get(v_pendingHead_2380_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_pendingHead_2380_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2393_ = v_pendingHead_2380_;
v_isShared_2394_ = v_isSharedCheck_2413_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v_pendingHead_2380_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2413_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_onRequest_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___f_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v_onRequest_2395_ = lean_ctor_get(v_inst_2372_, 1);
lean_inc_ref(v_onRequest_2395_);
lean_dec_ref(v_inst_2372_);
v___f_2396_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2397_ = lean_box(v_requiresData_2389_);
lean_inc_ref(v_response_2387_);
lean_inc_ref(v_requestStream_2383_);
v___f_2398_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2398_, 0, v_machine_2382_);
lean_closure_set(v___f_2398_, 1, v_requestStream_2383_);
lean_closure_set(v___f_2398_, 2, v_keepAliveTimeout_2384_);
lean_closure_set(v___f_2398_, 3, v_currentTimeout_2385_);
lean_closure_set(v___f_2398_, 4, v_headerTimeout_2386_);
lean_closure_set(v___f_2398_, 5, v_response_2387_);
lean_closure_set(v___f_2398_, 6, v_respStream_2388_);
lean_closure_set(v___f_2398_, 7, v___x_2397_);
lean_closure_set(v___f_2398_, 8, v_expectData_2390_);
v___x_2399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2399_, 0, v_val_2391_);
lean_ctor_set(v___x_2399_, 1, v_requestStream_2383_);
lean_ctor_set(v___x_2399_, 2, v_extensions_2374_);
v___x_2400_ = lean_apply_3(v_onRequest_2395_, v_handler_2373_, v___x_2399_, v_connectionContext_2375_);
v___x_2401_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2381_);
v___f_2402_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2402_, 0, v_toFunctor_2381_);
lean_closure_set(v___f_2402_, 1, v_response_2387_);
lean_closure_set(v___f_2402_, 2, v___x_2401_);
lean_closure_set(v___f_2402_, 3, v___f_2398_);
v___x_2403_ = 0;
v___x_2404_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2404_, 0, lean_box(0));
lean_closure_set(v___x_2404_, 1, v___x_2400_);
v___x_2405_ = lean_io_as_task(v___x_2404_, v___x_2401_);
v___x_2406_ = 1;
v___x_2407_ = lean_task_bind(v___x_2405_, v___f_2396_, v___x_2401_, v___x_2406_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2407_);
v___x_2409_ = v___x_2393_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
v___x_2411_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2401_, v___x_2403_, v___x_2410_, v___f_2402_);
return v___x_2411_;
}
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec(v_pendingHead_2380_);
lean_dec_ref(v_connectionContext_2375_);
lean_dec(v_extensions_2374_);
lean_dec(v_handler_2373_);
lean_dec_ref(v_inst_2372_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_state_2376_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2416_, lean_object* v_handler_2417_, lean_object* v_extensions_2418_, lean_object* v_connectionContext_2419_, lean_object* v_state_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2416_, v_handler_2417_, v_extensions_2418_, v_connectionContext_2419_, v_state_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2423_, lean_object* v_inst_2424_, lean_object* v_handler_2425_, lean_object* v_extensions_2426_, lean_object* v_connectionContext_2427_, lean_object* v_state_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2424_, v_handler_2425_, v_extensions_2426_, v_connectionContext_2427_, v_state_2428_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2431_, lean_object* v_inst_2432_, lean_object* v_handler_2433_, lean_object* v_extensions_2434_, lean_object* v_connectionContext_2435_, lean_object* v_state_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2431_, v_inst_2432_, v_handler_2433_, v_extensions_2434_, v_connectionContext_2435_, v_state_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2439_, lean_object* v_____r_2440_){
_start:
{
lean_object* v_writer_2442_; lean_object* v_reader_2443_; lean_object* v_config_2444_; lean_object* v_events_2445_; lean_object* v_error_2446_; lean_object* v_instant_2447_; uint8_t v_keepAlive_2448_; uint8_t v_forcedFlush_2449_; uint8_t v_pullBodyStalled_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2477_; 
v_writer_2442_ = lean_ctor_get(v_machine_2439_, 1);
v_reader_2443_ = lean_ctor_get(v_machine_2439_, 0);
v_config_2444_ = lean_ctor_get(v_machine_2439_, 2);
v_events_2445_ = lean_ctor_get(v_machine_2439_, 3);
v_error_2446_ = lean_ctor_get(v_machine_2439_, 4);
v_instant_2447_ = lean_ctor_get(v_machine_2439_, 5);
v_keepAlive_2448_ = lean_ctor_get_uint8(v_machine_2439_, sizeof(void*)*6);
v_forcedFlush_2449_ = lean_ctor_get_uint8(v_machine_2439_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2450_ = lean_ctor_get_uint8(v_machine_2439_, sizeof(void*)*6 + 2);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_machine_2439_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2452_ = v_machine_2439_;
v_isShared_2453_ = v_isSharedCheck_2477_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_instant_2447_);
lean_inc(v_error_2446_);
lean_inc(v_events_2445_);
lean_inc(v_config_2444_);
lean_inc(v_writer_2442_);
lean_inc(v_reader_2443_);
lean_dec(v_machine_2439_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2477_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_userData_2454_; lean_object* v_outputData_2455_; lean_object* v_state_2456_; lean_object* v_knownSize_2457_; lean_object* v_messageHead_2458_; uint8_t v_sentMessage_2459_; uint8_t v_omitBody_2460_; lean_object* v_userDataBytes_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2476_; 
v_userData_2454_ = lean_ctor_get(v_writer_2442_, 0);
v_outputData_2455_ = lean_ctor_get(v_writer_2442_, 1);
v_state_2456_ = lean_ctor_get(v_writer_2442_, 2);
v_knownSize_2457_ = lean_ctor_get(v_writer_2442_, 3);
v_messageHead_2458_ = lean_ctor_get(v_writer_2442_, 4);
v_sentMessage_2459_ = lean_ctor_get_uint8(v_writer_2442_, sizeof(void*)*6);
v_omitBody_2460_ = lean_ctor_get_uint8(v_writer_2442_, sizeof(void*)*6 + 2);
v_userDataBytes_2461_ = lean_ctor_get(v_writer_2442_, 5);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_writer_2442_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2463_ = v_writer_2442_;
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_userDataBytes_2461_);
lean_inc(v_messageHead_2458_);
lean_inc(v_knownSize_2457_);
lean_inc(v_state_2456_);
lean_inc(v_outputData_2455_);
lean_inc(v_userData_2454_);
lean_dec(v_writer_2442_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
uint8_t v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = 1;
if (v_isShared_2464_ == 0)
{
v___x_2467_ = v___x_2463_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_userData_2454_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_outputData_2455_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_state_2456_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_knownSize_2457_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_messageHead_2458_);
lean_ctor_set(v_reuseFailAlloc_2475_, 5, v_userDataBytes_2461_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, sizeof(void*)*6, v_sentMessage_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, sizeof(void*)*6 + 2, v_omitBody_2460_);
v___x_2467_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2469_; 
lean_ctor_set_uint8(v___x_2467_, sizeof(void*)*6 + 1, v___x_2465_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2467_);
v___x_2469_ = v___x_2452_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_reader_2443_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_config_2444_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_events_2445_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_error_2446_);
lean_ctor_set(v_reuseFailAlloc_2474_, 5, v_instant_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*6, v_keepAlive_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*6 + 1, v_forcedFlush_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*6 + 2, v_pullBodyStalled_2450_);
v___x_2469_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
return v___x_2473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2478_, lean_object* v_____r_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2478_, v_____r_2479_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2482_, lean_object* v_x2_2483_){
_start:
{
lean_object* v_data_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_data_2484_ = lean_ctor_get(v_x2_2483_, 0);
v___x_2485_ = lean_byte_array_size(v_data_2484_);
v___x_2486_ = lean_nat_add(v_x1_2482_, v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2487_, lean_object* v_x2_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2487_, v_x2_2488_);
lean_dec_ref(v_x2_2488_);
lean_dec(v_x1_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2490_, lean_object* v_machine_2491_, lean_object* v_isClosed_2492_, lean_object* v___f_2493_, lean_object* v___f_2494_, lean_object* v_x_2495_){
_start:
{
lean_object* v___y_2498_; 
if (lean_obj_tag(v_x_2495_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___f_2493_);
lean_dec_ref(v_isClosed_2492_);
lean_dec_ref(v_machine_2491_);
lean_dec(v_body_2490_);
v_a_2503_ = lean_ctor_get(v_x_2495_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_x_2495_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2505_ = v_x_2495_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v_x_2495_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2575_; 
v_a_2512_ = lean_ctor_get(v_x_2495_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_x_2495_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2514_ = v_x_2495_;
v_isShared_2515_ = v_isSharedCheck_2575_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v_x_2495_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2575_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
if (lean_obj_tag(v_a_2512_) == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___f_2493_);
lean_dec_ref(v_isClosed_2492_);
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_body_2490_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_machine_2491_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2517_);
v___x_2519_ = v___x_2514_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
else
{
lean_object* v_val_2522_; 
lean_del_object(v___x_2514_);
v_val_2522_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v_a_2512_, 1);
if (lean_obj_tag(v_val_2522_) == 0)
{
lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v___f_2494_);
lean_dec_ref(v_machine_2491_);
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = 0;
v___x_2525_ = lean_apply_2(v_isClosed_2492_, v_body_2490_, lean_box(0));
v___x_2526_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2523_, v___x_2524_, v___x_2525_, v___f_2493_);
return v___x_2526_;
}
else
{
lean_object* v_val_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
lean_dec_ref(v___f_2493_);
lean_dec_ref(v_isClosed_2492_);
v_val_2527_ = lean_ctor_get(v_val_2522_, 0);
lean_inc(v_val_2527_);
lean_dec_ref_known(v_val_2522_, 1);
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_mk_empty_array_with_capacity(v___x_2528_);
v___x_2530_ = lean_array_push(v___x_2529_, v_val_2527_);
v___x_2531_ = lean_array_get_size(v___x_2530_);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = lean_nat_dec_eq(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v_reader_2534_; lean_object* v_writer_2535_; lean_object* v_config_2536_; lean_object* v_events_2537_; lean_object* v_error_2538_; lean_object* v_instant_2539_; uint8_t v_keepAlive_2540_; uint8_t v_forcedFlush_2541_; uint8_t v_pullBodyStalled_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2574_; 
v_reader_2534_ = lean_ctor_get(v_machine_2491_, 0);
v_writer_2535_ = lean_ctor_get(v_machine_2491_, 1);
v_config_2536_ = lean_ctor_get(v_machine_2491_, 2);
v_events_2537_ = lean_ctor_get(v_machine_2491_, 3);
v_error_2538_ = lean_ctor_get(v_machine_2491_, 4);
v_instant_2539_ = lean_ctor_get(v_machine_2491_, 5);
v_keepAlive_2540_ = lean_ctor_get_uint8(v_machine_2491_, sizeof(void*)*6);
v_forcedFlush_2541_ = lean_ctor_get_uint8(v_machine_2491_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2542_ = lean_ctor_get_uint8(v_machine_2491_, sizeof(void*)*6 + 2);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_machine_2491_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2544_ = v_machine_2491_;
v_isShared_2545_ = v_isSharedCheck_2574_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_instant_2539_);
lean_inc(v_error_2538_);
lean_inc(v_events_2537_);
lean_inc(v_config_2536_);
lean_inc(v_writer_2535_);
lean_inc(v_reader_2534_);
lean_dec(v_machine_2491_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2574_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___y_2547_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_2570_ = lean_nat_dec_lt(v___x_2532_, v___x_2531_);
if (v___x_2570_ == 0)
{
lean_dec_ref(v___f_2494_);
v___y_2547_ = v___x_2532_;
goto v___jp_2546_;
}
else
{
size_t v___x_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = lean_usize_of_nat(v___x_2531_);
lean_inc_ref(v___x_2530_);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2569_, v___f_2494_, v___x_2530_, v___x_2571_, v___x_2572_, v___x_2532_);
v___y_2547_ = v___x_2573_;
goto v___jp_2546_;
}
v___jp_2546_:
{
lean_object* v_userData_2548_; lean_object* v_outputData_2549_; lean_object* v_state_2550_; lean_object* v_knownSize_2551_; lean_object* v_messageHead_2552_; uint8_t v_sentMessage_2553_; uint8_t v_userClosedBody_2554_; uint8_t v_omitBody_2555_; lean_object* v_userDataBytes_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2568_; 
v_userData_2548_ = lean_ctor_get(v_writer_2535_, 0);
v_outputData_2549_ = lean_ctor_get(v_writer_2535_, 1);
v_state_2550_ = lean_ctor_get(v_writer_2535_, 2);
v_knownSize_2551_ = lean_ctor_get(v_writer_2535_, 3);
v_messageHead_2552_ = lean_ctor_get(v_writer_2535_, 4);
v_sentMessage_2553_ = lean_ctor_get_uint8(v_writer_2535_, sizeof(void*)*6);
v_userClosedBody_2554_ = lean_ctor_get_uint8(v_writer_2535_, sizeof(void*)*6 + 1);
v_omitBody_2555_ = lean_ctor_get_uint8(v_writer_2535_, sizeof(void*)*6 + 2);
v_userDataBytes_2556_ = lean_ctor_get(v_writer_2535_, 5);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_writer_2535_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2558_ = v_writer_2535_;
v_isShared_2559_ = v_isSharedCheck_2568_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_userDataBytes_2556_);
lean_inc(v_messageHead_2552_);
lean_inc(v_knownSize_2551_);
lean_inc(v_state_2550_);
lean_inc(v_outputData_2549_);
lean_inc(v_userData_2548_);
lean_dec(v_writer_2535_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2568_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2560_ = l_Array_append___redArg(v_userData_2548_, v___x_2530_);
lean_dec_ref(v___x_2530_);
v___x_2561_ = lean_nat_add(v_userDataBytes_2556_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec(v_userDataBytes_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 5, v___x_2561_);
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2563_ = v___x_2558_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_outputData_2549_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_state_2550_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_knownSize_2551_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_messageHead_2552_);
lean_ctor_set(v_reuseFailAlloc_2567_, 5, v___x_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2567_, sizeof(void*)*6, v_sentMessage_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2567_, sizeof(void*)*6 + 1, v_userClosedBody_2554_);
lean_ctor_set_uint8(v_reuseFailAlloc_2567_, sizeof(void*)*6 + 2, v_omitBody_2555_);
v___x_2563_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v___x_2565_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 1, v___x_2563_);
v___x_2565_ = v___x_2544_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_reader_2534_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_config_2536_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_events_2537_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v_error_2538_);
lean_ctor_set(v_reuseFailAlloc_2566_, 5, v_instant_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*6, v_keepAlive_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*6 + 1, v_forcedFlush_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*6 + 2, v_pullBodyStalled_2542_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
v___y_2498_ = v___x_2565_;
goto v___jp_2497_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___f_2494_);
v___y_2498_ = v_machine_2491_;
goto v___jp_2497_;
}
}
}
}
}
v___jp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_body_2490_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___y_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2576_, lean_object* v_machine_2577_, lean_object* v_isClosed_2578_, lean_object* v___f_2579_, lean_object* v___f_2580_, lean_object* v_x_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2576_, v_machine_2577_, v_isClosed_2578_, v___f_2579_, v___f_2580_, v_x_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2585_, lean_object* v_machine_2586_, lean_object* v_body_2587_){
_start:
{
lean_object* v_close_2589_; lean_object* v_isClosed_2590_; lean_object* v_tryRecv_2591_; lean_object* v___f_2592_; lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_close_2589_ = lean_ctor_get(v_inst_2585_, 1);
lean_inc_ref(v_close_2589_);
v_isClosed_2590_ = lean_ctor_get(v_inst_2585_, 2);
lean_inc_ref(v_isClosed_2590_);
v_tryRecv_2591_ = lean_ctor_get(v_inst_2585_, 4);
lean_inc_ref(v_tryRecv_2591_);
lean_dec_ref(v_inst_2585_);
lean_inc_ref(v_machine_2586_);
v___f_2592_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2592_, 0, v_machine_2586_);
lean_inc_ref(v___f_2592_);
v___f_2593_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2593_, 0, v___f_2592_);
lean_inc_n(v_body_2587_, 2);
v___f_2594_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2594_, 0, v_close_2589_);
lean_closure_set(v___f_2594_, 1, v_body_2587_);
lean_closure_set(v___f_2594_, 2, v___f_2593_);
lean_closure_set(v___f_2594_, 3, v___f_2592_);
v___f_2595_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2596_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2596_, 0, v_body_2587_);
lean_closure_set(v___f_2596_, 1, v_machine_2586_);
lean_closure_set(v___f_2596_, 2, v_isClosed_2590_);
lean_closure_set(v___f_2596_, 3, v___f_2594_);
lean_closure_set(v___f_2596_, 4, v___f_2595_);
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = 0;
v___x_2599_ = lean_apply_2(v_tryRecv_2591_, v_body_2587_, lean_box(0));
v___x_2600_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2597_, v___x_2598_, v___x_2599_, v___f_2596_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2601_, lean_object* v_machine_2602_, lean_object* v_body_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2601_, v_machine_2602_, v_body_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2606_, lean_object* v_inst_2607_, lean_object* v_machine_2608_, lean_object* v_body_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2607_, v_machine_2608_, v_body_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2612_, lean_object* v_inst_2613_, lean_object* v_machine_2614_, lean_object* v_body_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2612_, v_inst_2613_, v_machine_2614_, v_body_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2624_, lean_object* v_____r_2625_, lean_object* v_st_2626_){
_start:
{
lean_object* v_machine_2628_; lean_object* v_requestStream_2629_; lean_object* v_keepAliveTimeout_2630_; lean_object* v_currentTimeout_2631_; lean_object* v_headerTimeout_2632_; lean_object* v_response_2633_; lean_object* v_respStream_2634_; uint8_t v_requiresData_2635_; lean_object* v_expectData_2636_; uint8_t v_handlerDispatched_2637_; lean_object* v_pendingHead_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2720_; 
v_machine_2628_ = lean_ctor_get(v_st_2626_, 0);
v_requestStream_2629_ = lean_ctor_get(v_st_2626_, 1);
v_keepAliveTimeout_2630_ = lean_ctor_get(v_st_2626_, 2);
v_currentTimeout_2631_ = lean_ctor_get(v_st_2626_, 3);
v_headerTimeout_2632_ = lean_ctor_get(v_st_2626_, 4);
v_response_2633_ = lean_ctor_get(v_st_2626_, 5);
v_respStream_2634_ = lean_ctor_get(v_st_2626_, 6);
v_requiresData_2635_ = lean_ctor_get_uint8(v_st_2626_, sizeof(void*)*9);
v_expectData_2636_ = lean_ctor_get(v_st_2626_, 7);
v_handlerDispatched_2637_ = lean_ctor_get_uint8(v_st_2626_, sizeof(void*)*9 + 1);
v_pendingHead_2638_ = lean_ctor_get(v_st_2626_, 8);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_st_2626_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2640_ = v_st_2626_;
v_isShared_2641_ = v_isSharedCheck_2720_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_pendingHead_2638_);
lean_inc(v_expectData_2636_);
lean_inc(v_respStream_2634_);
lean_inc(v_response_2633_);
lean_inc(v_headerTimeout_2632_);
lean_inc(v_currentTimeout_2631_);
lean_inc(v_keepAliveTimeout_2630_);
lean_inc(v_requestStream_2629_);
lean_inc(v_machine_2628_);
lean_dec(v_st_2626_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2720_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___y_2643_; lean_object* v_reader_2652_; lean_object* v_state_2653_; 
v_reader_2652_ = lean_ctor_get(v_machine_2628_, 0);
lean_inc_ref(v_reader_2652_);
v_state_2653_ = lean_ctor_get(v_reader_2652_, 0);
lean_inc(v_state_2653_);
if (lean_obj_tag(v_state_2653_) == 6)
{
lean_dec_ref(v_reader_2652_);
lean_dec_ref(v_val_2624_);
v___y_2643_ = v_machine_2628_;
goto v___jp_2642_;
}
else
{
if (lean_obj_tag(v_state_2653_) == 7)
{
lean_dec_ref_known(v_state_2653_, 1);
lean_dec_ref(v_reader_2652_);
lean_dec_ref(v_val_2624_);
v___y_2643_ = v_machine_2628_;
goto v___jp_2642_;
}
else
{
lean_object* v_input_2654_; lean_object* v_writer_2655_; lean_object* v_config_2656_; lean_object* v_events_2657_; lean_object* v_error_2658_; lean_object* v_instant_2659_; uint8_t v_keepAlive_2660_; uint8_t v_forcedFlush_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2718_; 
v_input_2654_ = lean_ctor_get(v_reader_2652_, 1);
lean_inc_ref(v_input_2654_);
v_writer_2655_ = lean_ctor_get(v_machine_2628_, 1);
v_config_2656_ = lean_ctor_get(v_machine_2628_, 2);
v_events_2657_ = lean_ctor_get(v_machine_2628_, 3);
v_error_2658_ = lean_ctor_get(v_machine_2628_, 4);
v_instant_2659_ = lean_ctor_get(v_machine_2628_, 5);
v_keepAlive_2660_ = lean_ctor_get_uint8(v_machine_2628_, sizeof(void*)*6);
v_forcedFlush_2661_ = lean_ctor_get_uint8(v_machine_2628_, sizeof(void*)*6 + 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_machine_2628_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_machine_2628_, 0);
lean_dec(v_unused_2719_);
v___x_2663_ = v_machine_2628_;
v_isShared_2664_ = v_isSharedCheck_2718_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_instant_2659_);
lean_inc(v_error_2658_);
lean_inc(v_events_2657_);
lean_inc(v_config_2656_);
lean_inc(v_writer_2655_);
lean_dec(v_machine_2628_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2718_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v_messageHead_2665_; lean_object* v_messageCount_2666_; lean_object* v_bodyBytesRead_2667_; lean_object* v_headerBytesRead_2668_; uint8_t v_noMoreInput_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2715_; 
v_messageHead_2665_ = lean_ctor_get(v_reader_2652_, 2);
v_messageCount_2666_ = lean_ctor_get(v_reader_2652_, 3);
v_bodyBytesRead_2667_ = lean_ctor_get(v_reader_2652_, 4);
v_headerBytesRead_2668_ = lean_ctor_get(v_reader_2652_, 5);
v_noMoreInput_2669_ = lean_ctor_get_uint8(v_reader_2652_, sizeof(void*)*6);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_reader_2652_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; lean_object* v_unused_2717_; 
v_unused_2716_ = lean_ctor_get(v_reader_2652_, 1);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_reader_2652_, 0);
lean_dec(v_unused_2717_);
v___x_2671_ = v_reader_2652_;
v_isShared_2672_ = v_isSharedCheck_2715_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_headerBytesRead_2668_);
lean_inc(v_bodyBytesRead_2667_);
lean_inc(v_messageCount_2666_);
lean_inc(v_messageHead_2665_);
lean_dec(v_reader_2652_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2715_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_array_2673_; lean_object* v_idx_2674_; uint8_t v___x_2675_; lean_object* v___y_2677_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_array_2673_ = lean_ctor_get(v_input_2654_, 0);
lean_inc_ref(v_array_2673_);
v_idx_2674_ = lean_ctor_get(v_input_2654_, 1);
lean_inc(v_idx_2674_);
lean_dec_ref(v_input_2654_);
v___x_2675_ = 0;
v___x_2706_ = lean_byte_array_size(v_array_2673_);
v___x_2707_ = lean_nat_dec_le(v___x_2706_, v_idx_2674_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2708_ = l_ByteArray_extract(v_array_2673_, v_idx_2674_, v___x_2706_);
lean_dec_ref(v_array_2673_);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_byte_array_size(v___x_2708_);
v___x_2711_ = lean_byte_array_size(v_val_2624_);
v___x_2712_ = lean_byte_array_copy_slice(v_val_2624_, v___x_2709_, v___x_2708_, v___x_2710_, v___x_2711_, v___x_2707_);
lean_dec_ref(v_val_2624_);
v___x_2713_ = l_ByteArray_mkIterator(v___x_2712_);
v___y_2677_ = v___x_2713_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2714_; 
lean_dec(v_idx_2674_);
lean_dec_ref(v_array_2673_);
v___x_2714_ = l_ByteArray_mkIterator(v_val_2624_);
v___y_2677_ = v___x_2714_;
goto v___jp_2676_;
}
v___jp_2676_:
{
lean_object* v_maxHeaderBytes_2678_; lean_object* v_maxStartLineLength_2679_; lean_object* v_maxChunkLineLength_2680_; lean_object* v_maxBodySize_2681_; lean_object* v_array_2682_; lean_object* v_idx_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_maxHeaderBytes_2678_ = lean_ctor_get(v_config_2656_, 2);
v_maxStartLineLength_2679_ = lean_ctor_get(v_config_2656_, 5);
v_maxChunkLineLength_2680_ = lean_ctor_get(v_config_2656_, 13);
v_maxBodySize_2681_ = lean_ctor_get(v_config_2656_, 15);
v_array_2682_ = lean_ctor_get(v___y_2677_, 0);
v_idx_2683_ = lean_ctor_get(v___y_2677_, 1);
v___x_2684_ = lean_nat_add(v_maxBodySize_2681_, v_maxHeaderBytes_2678_);
v___x_2685_ = lean_nat_add(v___x_2684_, v_maxStartLineLength_2679_);
lean_dec(v___x_2684_);
v___x_2686_ = lean_nat_add(v___x_2685_, v_maxChunkLineLength_2680_);
lean_dec(v___x_2685_);
v___x_2687_ = lean_byte_array_size(v_array_2682_);
v___x_2688_ = lean_nat_sub(v___x_2687_, v_idx_2683_);
v___x_2689_ = lean_nat_dec_lt(v___x_2686_, v___x_2688_);
lean_dec(v___x_2688_);
lean_dec(v___x_2686_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2691_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___y_2677_);
v___x_2691_ = v___x_2671_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_state_2653_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___y_2677_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_messageHead_2665_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v_messageCount_2666_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v_bodyBytesRead_2667_);
lean_ctor_set(v_reuseFailAlloc_2695_, 5, v_headerBytesRead_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2695_, sizeof(void*)*6, v_noMoreInput_2669_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v_machine_2693_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2691_);
v_machine_2693_ = v___x_2663_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_writer_2655_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_config_2656_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_events_2657_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v_error_2658_);
lean_ctor_set(v_reuseFailAlloc_2694_, 5, v_instant_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2694_, sizeof(void*)*6, v_keepAlive_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2694_, sizeof(void*)*6 + 1, v_forcedFlush_2661_);
v_machine_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_ctor_set_uint8(v_machine_2693_, sizeof(void*)*6 + 2, v___x_2675_);
v___y_2643_ = v_machine_2693_;
goto v___jp_2642_;
}
}
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec(v_error_2658_);
lean_dec(v_state_2653_);
v___x_2696_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2697_ = lean_array_push(v_events_2657_, v___x_2696_);
v___x_2698_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___y_2677_);
lean_ctor_set(v___x_2671_, 0, v___x_2698_);
v___x_2700_ = v___x_2671_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___y_2677_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_messageHead_2665_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_messageCount_2666_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_bodyBytesRead_2667_);
lean_ctor_set(v_reuseFailAlloc_2705_, 5, v_headerBytesRead_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2705_, sizeof(void*)*6, v_noMoreInput_2669_);
v___x_2700_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 4, v___x_2701_);
lean_ctor_set(v___x_2663_, 3, v___x_2697_);
lean_ctor_set(v___x_2663_, 0, v___x_2700_);
v___x_2703_ = v___x_2663_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_writer_2655_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_config_2656_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2704_, 5, v_instant_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, sizeof(void*)*6, v_keepAlive_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, sizeof(void*)*6 + 1, v_forcedFlush_2661_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*6 + 2, v___x_2675_);
v___y_2643_ = v___x_2703_;
goto v___jp_2642_;
}
}
}
}
}
}
}
}
v___jp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___y_2643_);
v___x_2645_ = v___x_2640_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___y_2643_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_requestStream_2629_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_keepAliveTimeout_2630_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_currentTimeout_2631_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v_headerTimeout_2632_);
lean_ctor_set(v_reuseFailAlloc_2651_, 5, v_response_2633_);
lean_ctor_set(v_reuseFailAlloc_2651_, 6, v_respStream_2634_);
lean_ctor_set(v_reuseFailAlloc_2651_, 7, v_expectData_2636_);
lean_ctor_set(v_reuseFailAlloc_2651_, 8, v_pendingHead_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*9, v_requiresData_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*9 + 1, v_handlerDispatched_2637_);
v___x_2645_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2646_ = 0;
v___x_2647_ = lean_box(v___x_2646_);
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2645_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2721_, lean_object* v_____r_2722_, lean_object* v_st_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2721_, v_____r_2722_, v_st_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2726_, lean_object* v_machine_2727_, lean_object* v_requestStream_2728_, lean_object* v_currentTimeout_2729_, lean_object* v_response_2730_, lean_object* v_respStream_2731_, uint8_t v_requiresData_2732_, lean_object* v_expectData_2733_, uint8_t v_handlerDispatched_2734_, lean_object* v_pendingHead_2735_, lean_object* v___f_2736_, lean_object* v_x_2737_){
_start:
{
if (lean_obj_tag(v_x_2737_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v___f_2736_);
lean_dec(v_pendingHead_2735_);
lean_dec(v_expectData_2733_);
lean_dec(v_respStream_2731_);
lean_dec_ref(v_response_2730_);
lean_dec(v_currentTimeout_2729_);
lean_dec_ref(v_requestStream_2728_);
lean_dec_ref(v_machine_2727_);
v_a_2739_ = lean_ctor_get(v_x_2737_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_x_2737_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2741_ = v_x_2737_;
v_isShared_2742_ = v_isSharedCheck_2747_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v_x_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2747_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v_headerTimeout_2749_; lean_object* v_second_2750_; lean_object* v_nano_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_second_2755_; lean_object* v_nano_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v_nanos_2760_; lean_object* v___x_2761_; lean_object* v_nanos_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_a_2748_ = lean_ctor_get(v_x_2737_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v_x_2737_, 1);
v_headerTimeout_2749_ = lean_ctor_get(v_config_2726_, 6);
v_second_2750_ = lean_ctor_get(v_a_2748_, 0);
lean_inc(v_second_2750_);
v_nano_2751_ = lean_ctor_get(v_a_2748_, 1);
lean_inc(v_nano_2751_);
lean_dec(v_a_2748_);
v___x_2752_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2753_ = lean_int_mul(v_headerTimeout_2749_, v___x_2752_);
v___x_2754_ = l_Std_Time_Duration_ofNanoseconds(v___x_2753_);
lean_dec(v___x_2753_);
v_second_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_second_2755_);
v_nano_2756_ = lean_ctor_get(v___x_2754_, 1);
lean_inc(v_nano_2756_);
lean_dec_ref(v___x_2754_);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2759_ = lean_int_mul(v_second_2750_, v___x_2758_);
lean_dec(v_second_2750_);
v_nanos_2760_ = lean_int_add(v___x_2759_, v_nano_2751_);
lean_dec(v_nano_2751_);
lean_dec(v___x_2759_);
v___x_2761_ = lean_int_mul(v_second_2755_, v___x_2758_);
lean_dec(v_second_2755_);
v_nanos_2762_ = lean_int_add(v___x_2761_, v_nano_2756_);
lean_dec(v_nano_2756_);
lean_dec(v___x_2761_);
v___x_2763_ = lean_int_add(v_nanos_2760_, v_nanos_2762_);
lean_dec(v_nanos_2762_);
lean_dec(v_nanos_2760_);
v___x_2764_ = l_Std_Time_Duration_ofNanoseconds(v___x_2763_);
lean_dec(v___x_2763_);
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2766_, 0, v_machine_2727_);
lean_ctor_set(v___x_2766_, 1, v_requestStream_2728_);
lean_ctor_set(v___x_2766_, 2, v___x_2757_);
lean_ctor_set(v___x_2766_, 3, v_currentTimeout_2729_);
lean_ctor_set(v___x_2766_, 4, v___x_2765_);
lean_ctor_set(v___x_2766_, 5, v_response_2730_);
lean_ctor_set(v___x_2766_, 6, v_respStream_2731_);
lean_ctor_set(v___x_2766_, 7, v_expectData_2733_);
lean_ctor_set(v___x_2766_, 8, v_pendingHead_2735_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*9, v_requiresData_2732_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*9 + 1, v_handlerDispatched_2734_);
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_apply_3(v___f_2736_, v___x_2767_, v___x_2766_, lean_box(0));
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2769_, lean_object* v_machine_2770_, lean_object* v_requestStream_2771_, lean_object* v_currentTimeout_2772_, lean_object* v_response_2773_, lean_object* v_respStream_2774_, lean_object* v_requiresData_2775_, lean_object* v_expectData_2776_, lean_object* v_handlerDispatched_2777_, lean_object* v_pendingHead_2778_, lean_object* v___f_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v_requiresData_boxed_2782_; uint8_t v_handlerDispatched_boxed_2783_; lean_object* v_res_2784_; 
v_requiresData_boxed_2782_ = lean_unbox(v_requiresData_2775_);
v_handlerDispatched_boxed_2783_ = lean_unbox(v_handlerDispatched_2777_);
v_res_2784_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2769_, v_machine_2770_, v_requestStream_2771_, v_currentTimeout_2772_, v_response_2773_, v_respStream_2774_, v_requiresData_boxed_2782_, v_expectData_2776_, v_handlerDispatched_boxed_2783_, v_pendingHead_2778_, v___f_2779_, v_x_2780_);
lean_dec_ref(v_config_2769_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2785_, lean_object* v_requestStream_2786_, lean_object* v_keepAliveTimeout_2787_, lean_object* v_currentTimeout_2788_, lean_object* v_headerTimeout_2789_, lean_object* v_response_2790_, uint8_t v_requiresData_2791_, lean_object* v_expectData_2792_, uint8_t v_handlerDispatched_2793_, lean_object* v_pendingHead_2794_, lean_object* v_____r_2795_){
_start:
{
lean_object* v_writer_2797_; lean_object* v_reader_2798_; lean_object* v_config_2799_; lean_object* v_events_2800_; lean_object* v_error_2801_; lean_object* v_instant_2802_; uint8_t v_keepAlive_2803_; uint8_t v_forcedFlush_2804_; uint8_t v_pullBodyStalled_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2835_; 
v_writer_2797_ = lean_ctor_get(v_machine_2785_, 1);
v_reader_2798_ = lean_ctor_get(v_machine_2785_, 0);
v_config_2799_ = lean_ctor_get(v_machine_2785_, 2);
v_events_2800_ = lean_ctor_get(v_machine_2785_, 3);
v_error_2801_ = lean_ctor_get(v_machine_2785_, 4);
v_instant_2802_ = lean_ctor_get(v_machine_2785_, 5);
v_keepAlive_2803_ = lean_ctor_get_uint8(v_machine_2785_, sizeof(void*)*6);
v_forcedFlush_2804_ = lean_ctor_get_uint8(v_machine_2785_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2805_ = lean_ctor_get_uint8(v_machine_2785_, sizeof(void*)*6 + 2);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_machine_2785_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2807_ = v_machine_2785_;
v_isShared_2808_ = v_isSharedCheck_2835_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_instant_2802_);
lean_inc(v_error_2801_);
lean_inc(v_events_2800_);
lean_inc(v_config_2799_);
lean_inc(v_writer_2797_);
lean_inc(v_reader_2798_);
lean_dec(v_machine_2785_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2835_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_userData_2809_; lean_object* v_outputData_2810_; lean_object* v_state_2811_; lean_object* v_knownSize_2812_; lean_object* v_messageHead_2813_; uint8_t v_sentMessage_2814_; uint8_t v_omitBody_2815_; lean_object* v_userDataBytes_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2834_; 
v_userData_2809_ = lean_ctor_get(v_writer_2797_, 0);
v_outputData_2810_ = lean_ctor_get(v_writer_2797_, 1);
v_state_2811_ = lean_ctor_get(v_writer_2797_, 2);
v_knownSize_2812_ = lean_ctor_get(v_writer_2797_, 3);
v_messageHead_2813_ = lean_ctor_get(v_writer_2797_, 4);
v_sentMessage_2814_ = lean_ctor_get_uint8(v_writer_2797_, sizeof(void*)*6);
v_omitBody_2815_ = lean_ctor_get_uint8(v_writer_2797_, sizeof(void*)*6 + 2);
v_userDataBytes_2816_ = lean_ctor_get(v_writer_2797_, 5);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_writer_2797_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2818_ = v_writer_2797_;
v_isShared_2819_ = v_isSharedCheck_2834_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_userDataBytes_2816_);
lean_inc(v_messageHead_2813_);
lean_inc(v_knownSize_2812_);
lean_inc(v_state_2811_);
lean_inc(v_outputData_2810_);
lean_inc(v_userData_2809_);
lean_dec(v_writer_2797_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2834_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
uint8_t v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = 1;
if (v_isShared_2819_ == 0)
{
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_userData_2809_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_outputData_2810_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_state_2811_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_knownSize_2812_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_messageHead_2813_);
lean_ctor_set(v_reuseFailAlloc_2833_, 5, v_userDataBytes_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*6, v_sentMessage_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*6 + 2, v_omitBody_2815_);
v___x_2822_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; 
lean_ctor_set_uint8(v___x_2822_, sizeof(void*)*6 + 1, v___x_2820_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v___x_2822_);
v___x_2824_ = v___x_2807_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_reader_2798_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_config_2799_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_events_2800_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_error_2801_);
lean_ctor_set(v_reuseFailAlloc_2832_, 5, v_instant_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*6, v_keepAlive_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*6 + 1, v_forcedFlush_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*6 + 2, v_pullBodyStalled_2805_);
v___x_2824_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v_requestStream_2786_);
lean_ctor_set(v___x_2826_, 2, v_keepAliveTimeout_2787_);
lean_ctor_set(v___x_2826_, 3, v_currentTimeout_2788_);
lean_ctor_set(v___x_2826_, 4, v_headerTimeout_2789_);
lean_ctor_set(v___x_2826_, 5, v_response_2790_);
lean_ctor_set(v___x_2826_, 6, v___x_2825_);
lean_ctor_set(v___x_2826_, 7, v_expectData_2792_);
lean_ctor_set(v___x_2826_, 8, v_pendingHead_2794_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*9, v_requiresData_2791_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*9 + 1, v_handlerDispatched_2793_);
v___x_2827_ = 0;
v___x_2828_ = lean_box(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2836_, lean_object* v_requestStream_2837_, lean_object* v_keepAliveTimeout_2838_, lean_object* v_currentTimeout_2839_, lean_object* v_headerTimeout_2840_, lean_object* v_response_2841_, lean_object* v_requiresData_2842_, lean_object* v_expectData_2843_, lean_object* v_handlerDispatched_2844_, lean_object* v_pendingHead_2845_, lean_object* v_____r_2846_, lean_object* v___y_2847_){
_start:
{
uint8_t v_requiresData_boxed_2848_; uint8_t v_handlerDispatched_boxed_2849_; lean_object* v_res_2850_; 
v_requiresData_boxed_2848_ = lean_unbox(v_requiresData_2842_);
v_handlerDispatched_boxed_2849_ = lean_unbox(v_handlerDispatched_2844_);
v_res_2850_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2836_, v_requestStream_2837_, v_keepAliveTimeout_2838_, v_currentTimeout_2839_, v_headerTimeout_2840_, v_response_2841_, v_requiresData_boxed_2848_, v_expectData_2843_, v_handlerDispatched_boxed_2849_, v_pendingHead_2845_, v_____r_2846_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2851_, lean_object* v_x_2852_){
_start:
{
if (lean_obj_tag(v_x_2852_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref(v___f_2851_);
v_a_2854_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2856_ = v_x_2852_;
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v_x_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v_x_2852_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v_x_2852_, 1);
v___x_2864_ = lean_apply_2(v___f_2851_, v_a_2863_, lean_box(0));
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2865_, v_x_2866_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2869_, lean_object* v_val_2870_, lean_object* v___f_2871_, lean_object* v___f_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v___f_2872_);
lean_dec_ref(v___f_2871_);
lean_dec(v_val_2870_);
lean_dec_ref(v_close_2869_);
v_a_2875_ = lean_ctor_get(v_x_2873_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2877_ = v_x_2873_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v_x_2873_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2884_; uint8_t v___x_2885_; 
v_a_2884_ = lean_ctor_get(v_x_2873_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v_x_2873_, 1);
v___x_2885_ = lean_unbox(v_a_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; 
lean_dec_ref(v___f_2872_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_apply_2(v_close_2869_, v_val_2870_, lean_box(0));
v___x_2888_ = lean_unbox(v_a_2884_);
lean_dec(v_a_2884_);
v___x_2889_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2886_, v___x_2888_, v___x_2887_, v___f_2871_);
return v___x_2889_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v_a_2884_);
lean_dec_ref(v___f_2871_);
lean_dec(v_val_2870_);
lean_dec_ref(v_close_2869_);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_apply_2(v___f_2872_, v___x_2890_, lean_box(0));
return v___x_2891_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2892_, lean_object* v_val_2893_, lean_object* v___f_2894_, lean_object* v___f_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2892_, v_val_2893_, v___f_2894_, v___f_2895_, v_x_2896_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_2899_, lean_object* v_handler_2900_, lean_object* v_x_2901_){
_start:
{
if (lean_obj_tag(v_x_2901_) == 0)
{
lean_object* v_a_2903_; lean_object* v_onFailure_2904_; lean_object* v___x_2905_; 
v_a_2903_ = lean_ctor_get(v_x_2901_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v_x_2901_, 1);
v_onFailure_2904_ = lean_ctor_get(v_inst_2899_, 2);
lean_inc_ref(v_onFailure_2904_);
lean_dec_ref(v_inst_2899_);
v___x_2905_ = lean_apply_3(v_onFailure_2904_, v_handler_2900_, v_a_2903_, lean_box(0));
return v___x_2905_;
}
else
{
lean_object* v___x_2906_; 
lean_dec(v_handler_2900_);
lean_dec_ref(v_inst_2899_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_x_2901_);
return v___x_2906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_2907_, lean_object* v_handler_2908_, lean_object* v_x_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2907_, v_handler_2908_, v_x_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_2912_, lean_object* v_____r_2913_){
_start:
{
uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2915_ = 0;
v___x_2916_ = lean_box(v___x_2915_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v_st_2912_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_2920_, lean_object* v_____r_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2920_, v_____r_2921_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2924_, lean_object* v___f_2925_, lean_object* v___f_2926_, lean_object* v_x_2927_){
_start:
{
if (lean_obj_tag(v_x_2927_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v___f_2926_);
lean_dec_ref(v___f_2925_);
lean_dec_ref(v_requestStream_2924_);
v_a_2929_ = lean_ctor_get(v_x_2927_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_x_2927_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2931_ = v_x_2927_;
v_isShared_2932_ = v_isSharedCheck_2937_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v_x_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2937_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
}
}
else
{
lean_object* v_a_2938_; uint8_t v___x_2939_; 
v_a_2938_ = lean_ctor_get(v_x_2927_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v_x_2927_, 1);
v___x_2939_ = lean_unbox(v_a_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; 
lean_dec_ref(v___f_2926_);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = l_Std_Http_Body_Stream_close(v_requestStream_2924_);
v___x_2942_ = lean_unbox(v_a_2938_);
lean_dec(v_a_2938_);
v___x_2943_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2940_, v___x_2942_, v___x_2941_, v___f_2925_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v_a_2938_);
lean_dec_ref(v___f_2925_);
lean_dec_ref(v_requestStream_2924_);
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_apply_2(v___f_2926_, v___x_2944_, lean_box(0));
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2946_, lean_object* v___f_2947_, lean_object* v___f_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2946_, v___f_2947_, v___f_2948_, v_x_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t v_final_2952_, lean_object* v___f_2953_, lean_object* v___f_2954_, lean_object* v_requestStream_2955_, lean_object* v___f_2956_, lean_object* v_x_2957_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v___f_2956_);
lean_dec_ref(v_requestStream_2955_);
lean_dec_ref(v___f_2954_);
lean_dec_ref(v___f_2953_);
v_a_2959_ = lean_ctor_get(v_x_2957_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_x_2957_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2961_ = v_x_2957_;
v_isShared_2962_ = v_isSharedCheck_2967_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v_x_2957_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2967_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
}
else
{
lean_dec_ref_known(v_x_2957_, 1);
if (v_final_2952_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec_ref(v___f_2956_);
lean_dec_ref(v_requestStream_2955_);
lean_dec_ref(v___f_2954_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_apply_2(v___f_2953_, v___x_2968_, lean_box(0));
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_6684__overap_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref(v___f_2953_);
v___x_2970_ = lean_unsigned_to_nat(0u);
v___x_2971_ = 0;
v___x_2972_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2973_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2974_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2975_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2976_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2976_, 0, lean_box(0));
lean_closure_set(v___x_2976_, 1, lean_box(0));
lean_closure_set(v___x_2976_, 2, v___x_2972_);
lean_closure_set(v___x_2976_, 3, lean_box(0));
lean_closure_set(v___x_2976_, 4, lean_box(0));
lean_closure_set(v___x_2976_, 5, v___x_2975_);
lean_closure_set(v___x_2976_, 6, v___f_2954_);
v___x_6684__overap_2977_ = l_Std_Mutex_atomically___redArg(v___x_2972_, v___f_2973_, v___f_2974_, v_requestStream_2955_, v___x_2976_);
v___x_2978_ = lean_apply_1(v___x_6684__overap_2977_, lean_box(0));
v___x_2979_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2970_, v___x_2971_, v___x_2978_, v___f_2956_);
return v___x_2979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_final_2980_, lean_object* v___f_2981_, lean_object* v___f_2982_, lean_object* v_requestStream_2983_, lean_object* v___f_2984_, lean_object* v_x_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v_final_boxed_2987_; lean_object* v_res_2988_; 
v_final_boxed_2987_ = lean_unbox(v_final_2980_);
v_res_2988_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_boxed_2987_, v___f_2981_, v___f_2982_, v_requestStream_2983_, v___f_2984_, v_x_2985_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2989_, lean_object* v_x_2990_){
_start:
{
if (lean_obj_tag(v_x_2990_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v_state_2989_);
v_a_2992_ = lean_ctor_get(v_x_2990_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_x_2990_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2994_ = v_x_2990_;
v_isShared_2995_ = v_isSharedCheck_3000_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v_x_2990_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3000_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
}
else
{
lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3030_; 
v_isSharedCheck_3030_ = !lean_is_exclusive(v_x_2990_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v_x_2990_, 0);
lean_dec(v_unused_3031_);
v___x_3002_ = v_x_2990_;
v_isShared_3003_ = v_isSharedCheck_3030_;
goto v_resetjp_3001_;
}
else
{
lean_dec(v_x_2990_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3030_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v_machine_3004_; lean_object* v_requestStream_3005_; lean_object* v_keepAliveTimeout_3006_; lean_object* v_currentTimeout_3007_; lean_object* v_headerTimeout_3008_; lean_object* v_response_3009_; lean_object* v_respStream_3010_; uint8_t v_requiresData_3011_; lean_object* v_expectData_3012_; lean_object* v_pendingHead_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3029_; 
v_machine_3004_ = lean_ctor_get(v_state_2989_, 0);
v_requestStream_3005_ = lean_ctor_get(v_state_2989_, 1);
v_keepAliveTimeout_3006_ = lean_ctor_get(v_state_2989_, 2);
v_currentTimeout_3007_ = lean_ctor_get(v_state_2989_, 3);
v_headerTimeout_3008_ = lean_ctor_get(v_state_2989_, 4);
v_response_3009_ = lean_ctor_get(v_state_2989_, 5);
v_respStream_3010_ = lean_ctor_get(v_state_2989_, 6);
v_requiresData_3011_ = lean_ctor_get_uint8(v_state_2989_, sizeof(void*)*9);
v_expectData_3012_ = lean_ctor_get(v_state_2989_, 7);
v_pendingHead_3013_ = lean_ctor_get(v_state_2989_, 8);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_state_2989_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3015_ = v_state_2989_;
v_isShared_3016_ = v_isSharedCheck_3029_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_pendingHead_3013_);
lean_inc(v_expectData_3012_);
lean_inc(v_respStream_3010_);
lean_inc(v_response_3009_);
lean_inc(v_headerTimeout_3008_);
lean_inc(v_currentTimeout_3007_);
lean_inc(v_keepAliveTimeout_3006_);
lean_inc(v_requestStream_3005_);
lean_inc(v_machine_3004_);
lean_dec(v_state_2989_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3029_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3021_; 
v___x_3017_ = lean_box(52);
v___x_3018_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3004_, v___x_3017_);
v___x_3019_ = 0;
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3018_);
v___x_3021_ = v___x_3015_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_requestStream_3005_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_keepAliveTimeout_3006_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_currentTimeout_3007_);
lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_headerTimeout_3008_);
lean_ctor_set(v_reuseFailAlloc_3028_, 5, v_response_3009_);
lean_ctor_set(v_reuseFailAlloc_3028_, 6, v_respStream_3010_);
lean_ctor_set(v_reuseFailAlloc_3028_, 7, v_expectData_3012_);
lean_ctor_set(v_reuseFailAlloc_3028_, 8, v_pendingHead_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3028_, sizeof(void*)*9, v_requiresData_3011_);
v___x_3021_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*9 + 1, v___x_3019_);
v___x_3022_ = lean_box(v___x_3019_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3023_);
v___x_3025_ = v___x_3002_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3032_, lean_object* v_x_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3032_, v_x_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3036_, lean_object* v_requestStream_3037_, lean_object* v_keepAliveTimeout_3038_, lean_object* v_currentTimeout_3039_, lean_object* v_headerTimeout_3040_, lean_object* v_response_3041_, lean_object* v_respStream_3042_, uint8_t v_requiresData_3043_, lean_object* v_expectData_3044_, lean_object* v_pendingHead_3045_, lean_object* v_____r_3046_){
_start:
{
uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3048_ = 0;
v___x_3049_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3049_, 0, v_machine_3036_);
lean_ctor_set(v___x_3049_, 1, v_requestStream_3037_);
lean_ctor_set(v___x_3049_, 2, v_keepAliveTimeout_3038_);
lean_ctor_set(v___x_3049_, 3, v_currentTimeout_3039_);
lean_ctor_set(v___x_3049_, 4, v_headerTimeout_3040_);
lean_ctor_set(v___x_3049_, 5, v_response_3041_);
lean_ctor_set(v___x_3049_, 6, v_respStream_3042_);
lean_ctor_set(v___x_3049_, 7, v_expectData_3044_);
lean_ctor_set(v___x_3049_, 8, v_pendingHead_3045_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*9, v_requiresData_3043_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*9 + 1, v___x_3048_);
v___x_3050_ = lean_box(v___x_3048_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3054_, lean_object* v_requestStream_3055_, lean_object* v_keepAliveTimeout_3056_, lean_object* v_currentTimeout_3057_, lean_object* v_headerTimeout_3058_, lean_object* v_response_3059_, lean_object* v_respStream_3060_, lean_object* v_requiresData_3061_, lean_object* v_expectData_3062_, lean_object* v_pendingHead_3063_, lean_object* v_____r_3064_, lean_object* v___y_3065_){
_start:
{
uint8_t v_requiresData_boxed_3066_; lean_object* v_res_3067_; 
v_requiresData_boxed_3066_ = lean_unbox(v_requiresData_3061_);
v_res_3067_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3054_, v_requestStream_3055_, v_keepAliveTimeout_3056_, v_currentTimeout_3057_, v_headerTimeout_3058_, v_response_3059_, v_respStream_3060_, v_requiresData_boxed_3066_, v_expectData_3062_, v_pendingHead_3063_, v_____r_3064_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3068_, lean_object* v_body_3069_, lean_object* v___f_3070_, lean_object* v___f_3071_, lean_object* v_x_3072_){
_start:
{
if (lean_obj_tag(v_x_3072_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v___f_3071_);
lean_dec_ref(v___f_3070_);
lean_dec(v_body_3069_);
lean_dec_ref(v_close_3068_);
v_a_3074_ = lean_ctor_get(v_x_3072_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_x_3072_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3076_ = v_x_3072_;
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v_x_3072_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
}
}
else
{
lean_object* v_a_3083_; uint8_t v___x_3084_; 
v_a_3083_ = lean_ctor_get(v_x_3072_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v_x_3072_, 1);
v___x_3084_ = lean_unbox(v_a_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref(v___f_3071_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_apply_2(v_close_3068_, v_body_3069_, lean_box(0));
v___x_3087_ = lean_unbox(v_a_3083_);
lean_dec(v_a_3083_);
v___x_3088_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3085_, v___x_3087_, v___x_3086_, v___f_3070_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec(v_a_3083_);
lean_dec_ref(v___f_3070_);
lean_dec(v_body_3069_);
lean_dec_ref(v_close_3068_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_apply_2(v___f_3071_, v___x_3089_, lean_box(0));
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3091_, lean_object* v_body_3092_, lean_object* v___f_3093_, lean_object* v___f_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3091_, v_body_3092_, v___f_3093_, v___f_3094_, v_x_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3098_, lean_object* v_keepAliveTimeout_3099_, lean_object* v_currentTimeout_3100_, lean_object* v_headerTimeout_3101_, lean_object* v_response_3102_, uint8_t v_requiresData_3103_, lean_object* v_expectData_3104_, uint8_t v___x_3105_, lean_object* v_pendingHead_3106_, lean_object* v_____x_3107_){
_start:
{
lean_object* v_snd_3109_; lean_object* v_fst_3110_; lean_object* v_fst_3111_; lean_object* v_snd_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3122_; 
v_snd_3109_ = lean_ctor_get(v_____x_3107_, 1);
lean_inc(v_snd_3109_);
v_fst_3110_ = lean_ctor_get(v_____x_3107_, 0);
lean_inc(v_fst_3110_);
lean_dec_ref(v_____x_3107_);
v_fst_3111_ = lean_ctor_get(v_snd_3109_, 0);
v_snd_3112_ = lean_ctor_get(v_snd_3109_, 1);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_snd_3109_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3114_ = v_snd_3109_;
v_isShared_3115_ = v_isSharedCheck_3122_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_snd_3112_);
lean_inc(v_fst_3111_);
lean_dec(v_snd_3109_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3122_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3116_, 0, v_fst_3110_);
lean_ctor_set(v___x_3116_, 1, v_requestStream_3098_);
lean_ctor_set(v___x_3116_, 2, v_keepAliveTimeout_3099_);
lean_ctor_set(v___x_3116_, 3, v_currentTimeout_3100_);
lean_ctor_set(v___x_3116_, 4, v_headerTimeout_3101_);
lean_ctor_set(v___x_3116_, 5, v_response_3102_);
lean_ctor_set(v___x_3116_, 6, v_fst_3111_);
lean_ctor_set(v___x_3116_, 7, v_expectData_3104_);
lean_ctor_set(v___x_3116_, 8, v_pendingHead_3106_);
lean_ctor_set_uint8(v___x_3116_, sizeof(void*)*9, v_requiresData_3103_);
lean_ctor_set_uint8(v___x_3116_, sizeof(void*)*9 + 1, v___x_3105_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_snd_3112_);
v___x_3118_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3123_, lean_object* v_keepAliveTimeout_3124_, lean_object* v_currentTimeout_3125_, lean_object* v_headerTimeout_3126_, lean_object* v_response_3127_, lean_object* v_requiresData_3128_, lean_object* v_expectData_3129_, lean_object* v___x_3130_, lean_object* v_pendingHead_3131_, lean_object* v_____x_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v_requiresData_boxed_3134_; uint8_t v___x_7494__boxed_3135_; lean_object* v_res_3136_; 
v_requiresData_boxed_3134_ = lean_unbox(v_requiresData_3128_);
v___x_7494__boxed_3135_ = lean_unbox(v___x_3130_);
v_res_3136_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3123_, v_keepAliveTimeout_3124_, v_currentTimeout_3125_, v_headerTimeout_3126_, v_response_3127_, v_requiresData_boxed_3134_, v_expectData_3129_, v___x_7494__boxed_3135_, v_pendingHead_3131_, v_____x_3132_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3137_, lean_object* v_x_3138_){
_start:
{
if (lean_obj_tag(v_x_3138_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v___f_3137_);
v_a_3140_ = lean_ctor_get(v_x_3138_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_x_3138_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3142_ = v_x_3138_;
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v_x_3138_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3150_; 
v_a_3149_ = lean_ctor_get(v_x_3138_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v_x_3138_, 1);
v___x_3150_ = lean_apply_2(v___f_3137_, v_a_3149_, lean_box(0));
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3151_, lean_object* v_x_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3151_, v_x_3152_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3155_, lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3166_; 
v_a_3158_ = lean_ctor_get(v_x_3156_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_x_3156_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3160_ = v_x_3156_;
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v_x_3156_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3186_; 
v_a_3167_ = lean_ctor_get(v_x_3156_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_x_3156_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3169_ = v_x_3156_;
v_isShared_3170_ = v_isSharedCheck_3186_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v_x_3156_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3186_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_fst_3171_; lean_object* v_snd_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3185_; 
v_fst_3171_ = lean_ctor_get(v_a_3167_, 0);
v_snd_3172_ = lean_ctor_get(v_a_3167_, 1);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_a_3167_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3174_ = v_a_3167_;
v_isShared_3175_ = v_isSharedCheck_3185_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_snd_3172_);
lean_inc(v_fst_3171_);
lean_dec(v_a_3167_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3185_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = lean_box(v___x_3155_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v___x_3176_);
lean_ctor_set(v___x_3174_, 0, v_snd_3172_);
v___x_3178_ = v___x_3174_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_snd_3172_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_fst_3171_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3179_);
v___x_3181_ = v___x_3169_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3187_, lean_object* v_x_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v___x_7562__boxed_3190_; lean_object* v_res_3191_; 
v___x_7562__boxed_3190_ = lean_unbox(v___x_3187_);
v_res_3191_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7562__boxed_3190_, v_x_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3192_, uint8_t v___x_3193_, lean_object* v_fst_3194_, lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3195_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v_fst_3194_);
lean_dec(v_snd_3192_);
v_a_3197_ = lean_ctor_get(v_x_3195_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_x_3195_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3199_ = v_x_3195_;
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v_x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3197_);
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
else
{
lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3216_; 
v_isSharedCheck_3216_ = !lean_is_exclusive(v_x_3195_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v_x_3195_, 0);
lean_dec(v_unused_3217_);
v___x_3207_ = v_x_3195_;
v_isShared_3208_ = v_isSharedCheck_3216_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v_x_3195_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3216_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3209_ = lean_box(v___x_3193_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v_snd_3192_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_fst_3194_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3211_);
v___x_3213_ = v___x_3207_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3218_, lean_object* v___x_3219_, lean_object* v_fst_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v___x_7630__boxed_3223_; lean_object* v_res_3224_; 
v___x_7630__boxed_3223_ = lean_unbox(v___x_3219_);
v_res_3224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3218_, v___x_7630__boxed_3223_, v_fst_3220_, v_x_3221_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3225_, lean_object* v_handler_3226_, uint8_t v___x_3227_, lean_object* v___f_3228_, lean_object* v_x_3229_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 0)
{
lean_object* v_a_3231_; lean_object* v_onFailure_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_a_3231_ = lean_ctor_get(v_x_3229_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v_x_3229_, 1);
v_onFailure_3232_ = lean_ctor_get(v_inst_3225_, 2);
lean_inc_ref(v_onFailure_3232_);
lean_dec_ref(v_inst_3225_);
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = lean_apply_3(v_onFailure_3232_, v_handler_3226_, v_a_3231_, lean_box(0));
v___x_3235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3233_, v___x_3227_, v___x_3234_, v___f_3228_);
return v___x_3235_;
}
else
{
lean_object* v___x_3236_; 
lean_dec_ref(v___f_3228_);
lean_dec(v_handler_3226_);
lean_dec_ref(v_inst_3225_);
v___x_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3236_, 0, v_x_3229_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3237_, lean_object* v_handler_3238_, lean_object* v___x_3239_, lean_object* v___f_3240_, lean_object* v_x_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v___x_7688__boxed_3243_; lean_object* v_res_3244_; 
v___x_7688__boxed_3243_ = lean_unbox(v___x_3239_);
v_res_3244_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3237_, v_handler_3238_, v___x_7688__boxed_3243_, v___f_3240_, v_x_3241_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3245_, lean_object* v___f_3246_, uint8_t v___x_3247_, lean_object* v_inst_3248_, lean_object* v_handler_3249_, lean_object* v_inst_3250_, lean_object* v___f_3251_, lean_object* v___f_3252_, lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3253_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v___f_3252_);
lean_dec_ref(v___f_3251_);
lean_dec_ref(v_inst_3250_);
lean_dec(v_handler_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec_ref(v___f_3246_);
v_a_3255_ = lean_ctor_get(v_x_3253_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_x_3253_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3257_ = v_x_3253_;
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v_x_3253_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
return v___x_3261_;
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3297_; 
v_a_3264_ = lean_ctor_get(v_x_3253_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_x_3253_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3266_ = v_x_3253_;
v_isShared_3267_ = v_isSharedCheck_3297_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v_x_3253_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3297_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_snd_3268_; 
v_snd_3268_ = lean_ctor_get(v_a_3264_, 1);
lean_inc(v_snd_3268_);
if (lean_obj_tag(v_snd_3268_) == 0)
{
lean_object* v_fst_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3284_; 
lean_dec_ref(v___f_3252_);
lean_dec_ref(v___f_3251_);
lean_dec_ref(v_inst_3250_);
lean_dec(v_handler_3249_);
lean_dec_ref(v_inst_3248_);
v_fst_3269_ = lean_ctor_get(v_a_3264_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_a_3264_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; 
v_unused_3285_ = lean_ctor_get(v_a_3264_, 1);
lean_dec(v_unused_3285_);
v___x_3271_ = v_a_3264_;
v_isShared_3272_ = v_isSharedCheck_3284_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_fst_3269_);
lean_dec(v_a_3264_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3284_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = lean_box(v___x_3245_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 1, v___x_3273_);
lean_ctor_set(v___x_3271_, 0, v_snd_3268_);
v___x_3275_ = v___x_3271_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_snd_3268_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_fst_3269_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_unsigned_to_nat(0u);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3276_);
v___x_3279_ = v___x_3266_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3276_);
v___x_3279_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
v___x_3281_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3277_, v___x_3245_, v___x_3280_, v___f_3246_);
return v___x_3281_;
}
}
}
}
else
{
lean_object* v_fst_3286_; lean_object* v_val_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_del_object(v___x_3266_);
lean_dec_ref(v___f_3246_);
v_fst_3286_ = lean_ctor_get(v_a_3264_, 0);
lean_inc_n(v_fst_3286_, 2);
lean_dec(v_a_3264_);
v_val_3287_ = lean_ctor_get(v_snd_3268_, 0);
lean_inc(v_val_3287_);
v___x_3288_ = lean_box(v___x_3247_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3289_, 0, v_snd_3268_);
lean_closure_set(v___f_3289_, 1, v___x_3288_);
lean_closure_set(v___f_3289_, 2, v_fst_3286_);
v___x_3290_ = lean_box(v___x_3245_);
v___f_3291_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3291_, 0, v_inst_3248_);
lean_closure_set(v___f_3291_, 1, v_handler_3249_);
lean_closure_set(v___f_3291_, 2, v___x_3290_);
lean_closure_set(v___f_3291_, 3, v___f_3289_);
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3250_, v_fst_3286_, v_val_3287_);
v___x_3294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3292_, v___x_3245_, v___x_3293_, v___f_3251_);
v___x_3295_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3292_, v___x_3245_, v___x_3294_, v___f_3291_);
v___x_3296_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3292_, v___x_3245_, v___x_3295_, v___f_3252_);
return v___x_3296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3298_, lean_object* v___f_3299_, lean_object* v___x_3300_, lean_object* v_inst_3301_, lean_object* v_handler_3302_, lean_object* v_inst_3303_, lean_object* v___f_3304_, lean_object* v___f_3305_, lean_object* v_x_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v___x_7713__boxed_3308_; uint8_t v___x_7715__boxed_3309_; lean_object* v_res_3310_; 
v___x_7713__boxed_3308_ = lean_unbox(v___x_3298_);
v___x_7715__boxed_3309_ = lean_unbox(v___x_3300_);
v_res_3310_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_7713__boxed_3308_, v___f_3299_, v___x_7715__boxed_3309_, v_inst_3301_, v_handler_3302_, v_inst_3303_, v___f_3304_, v___f_3305_, v_x_3306_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3311_, lean_object* v_x_3312_){
_start:
{
if (lean_obj_tag(v_x_3312_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v_state_3311_);
v_a_3314_ = lean_ctor_get(v_x_3312_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_x_3312_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3316_ = v_x_3312_;
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v_x_3312_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
else
{
lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3352_; 
v_isSharedCheck_3352_ = !lean_is_exclusive(v_x_3312_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v_x_3312_, 0);
lean_dec(v_unused_3353_);
v___x_3324_ = v_x_3312_;
v_isShared_3325_ = v_isSharedCheck_3352_;
goto v_resetjp_3323_;
}
else
{
lean_dec(v_x_3312_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3352_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_machine_3326_; lean_object* v_requestStream_3327_; lean_object* v_keepAliveTimeout_3328_; lean_object* v_currentTimeout_3329_; lean_object* v_headerTimeout_3330_; lean_object* v_response_3331_; lean_object* v_respStream_3332_; uint8_t v_requiresData_3333_; lean_object* v_expectData_3334_; lean_object* v_pendingHead_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3351_; 
v_machine_3326_ = lean_ctor_get(v_state_3311_, 0);
v_requestStream_3327_ = lean_ctor_get(v_state_3311_, 1);
v_keepAliveTimeout_3328_ = lean_ctor_get(v_state_3311_, 2);
v_currentTimeout_3329_ = lean_ctor_get(v_state_3311_, 3);
v_headerTimeout_3330_ = lean_ctor_get(v_state_3311_, 4);
v_response_3331_ = lean_ctor_get(v_state_3311_, 5);
v_respStream_3332_ = lean_ctor_get(v_state_3311_, 6);
v_requiresData_3333_ = lean_ctor_get_uint8(v_state_3311_, sizeof(void*)*9);
v_expectData_3334_ = lean_ctor_get(v_state_3311_, 7);
v_pendingHead_3335_ = lean_ctor_get(v_state_3311_, 8);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_state_3311_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3337_ = v_state_3311_;
v_isShared_3338_ = v_isSharedCheck_3351_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_pendingHead_3335_);
lean_inc(v_expectData_3334_);
lean_inc(v_respStream_3332_);
lean_inc(v_response_3331_);
lean_inc(v_headerTimeout_3330_);
lean_inc(v_currentTimeout_3329_);
lean_inc(v_keepAliveTimeout_3328_);
lean_inc(v_requestStream_3327_);
lean_inc(v_machine_3326_);
lean_dec(v_state_3311_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3351_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; lean_object* v___x_3343_; 
v___x_3339_ = lean_box(31);
v___x_3340_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3326_, v___x_3339_);
v___x_3341_ = 0;
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3340_);
v___x_3343_ = v___x_3337_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_requestStream_3327_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_keepAliveTimeout_3328_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_currentTimeout_3329_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_headerTimeout_3330_);
lean_ctor_set(v_reuseFailAlloc_3350_, 5, v_response_3331_);
lean_ctor_set(v_reuseFailAlloc_3350_, 6, v_respStream_3332_);
lean_ctor_set(v_reuseFailAlloc_3350_, 7, v_expectData_3334_);
lean_ctor_set(v_reuseFailAlloc_3350_, 8, v_pendingHead_3335_);
lean_ctor_set_uint8(v_reuseFailAlloc_3350_, sizeof(void*)*9, v_requiresData_3333_);
v___x_3343_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*9 + 1, v___x_3341_);
v___x_3344_ = lean_box(v___x_3341_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3345_);
v___x_3347_ = v___x_3324_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3354_, v_x_3355_);
return v_res_3357_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3363_ = lean_mk_io_user_error(v___x_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_handler_3366_, lean_object* v_config_3367_, lean_object* v_event_3368_, lean_object* v_state_3369_){
_start:
{
switch(lean_obj_tag(v_event_3368_))
{
case 0:
{
lean_object* v_x_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_handler_3366_);
lean_dec_ref(v_inst_3365_);
lean_dec_ref(v_inst_3364_);
v_x_3371_ = lean_ctor_get(v_event_3368_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_event_3368_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3373_ = v_event_3368_;
v_isShared_3374_ = v_isSharedCheck_3478_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_x_3371_);
lean_dec(v_event_3368_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3478_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
if (lean_obj_tag(v_x_3371_) == 0)
{
lean_object* v_machine_3375_; lean_object* v_reader_3376_; lean_object* v_requestStream_3377_; lean_object* v_keepAliveTimeout_3378_; lean_object* v_currentTimeout_3379_; lean_object* v_headerTimeout_3380_; lean_object* v_response_3381_; lean_object* v_respStream_3382_; uint8_t v_requiresData_3383_; lean_object* v_expectData_3384_; uint8_t v_handlerDispatched_3385_; lean_object* v_pendingHead_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_config_3367_);
v_machine_3375_ = lean_ctor_get(v_state_3369_, 0);
lean_inc_ref(v_machine_3375_);
v_reader_3376_ = lean_ctor_get(v_machine_3375_, 0);
lean_inc_ref(v_reader_3376_);
v_requestStream_3377_ = lean_ctor_get(v_state_3369_, 1);
v_keepAliveTimeout_3378_ = lean_ctor_get(v_state_3369_, 2);
v_currentTimeout_3379_ = lean_ctor_get(v_state_3369_, 3);
v_headerTimeout_3380_ = lean_ctor_get(v_state_3369_, 4);
v_response_3381_ = lean_ctor_get(v_state_3369_, 5);
v_respStream_3382_ = lean_ctor_get(v_state_3369_, 6);
v_requiresData_3383_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3384_ = lean_ctor_get(v_state_3369_, 7);
v_handlerDispatched_3385_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9 + 1);
v_pendingHead_3386_ = lean_ctor_get(v_state_3369_, 8);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_state_3369_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v_state_3369_, 0);
lean_dec(v_unused_3430_);
v___x_3388_ = v_state_3369_;
v_isShared_3389_ = v_isSharedCheck_3429_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_pendingHead_3386_);
lean_inc(v_expectData_3384_);
lean_inc(v_respStream_3382_);
lean_inc(v_response_3381_);
lean_inc(v_headerTimeout_3380_);
lean_inc(v_currentTimeout_3379_);
lean_inc(v_keepAliveTimeout_3378_);
lean_inc(v_requestStream_3377_);
lean_dec(v_state_3369_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3429_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_writer_3390_; lean_object* v_config_3391_; lean_object* v_events_3392_; lean_object* v_error_3393_; lean_object* v_instant_3394_; uint8_t v_keepAlive_3395_; uint8_t v_forcedFlush_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3427_; 
v_writer_3390_ = lean_ctor_get(v_machine_3375_, 1);
v_config_3391_ = lean_ctor_get(v_machine_3375_, 2);
v_events_3392_ = lean_ctor_get(v_machine_3375_, 3);
v_error_3393_ = lean_ctor_get(v_machine_3375_, 4);
v_instant_3394_ = lean_ctor_get(v_machine_3375_, 5);
v_keepAlive_3395_ = lean_ctor_get_uint8(v_machine_3375_, sizeof(void*)*6);
v_forcedFlush_3396_ = lean_ctor_get_uint8(v_machine_3375_, sizeof(void*)*6 + 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_machine_3375_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v_machine_3375_, 0);
lean_dec(v_unused_3428_);
v___x_3398_ = v_machine_3375_;
v_isShared_3399_ = v_isSharedCheck_3427_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_instant_3394_);
lean_inc(v_error_3393_);
lean_inc(v_events_3392_);
lean_inc(v_config_3391_);
lean_inc(v_writer_3390_);
lean_dec(v_machine_3375_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3427_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_state_3400_; lean_object* v_input_3401_; lean_object* v_messageHead_3402_; lean_object* v_messageCount_3403_; lean_object* v_bodyBytesRead_3404_; lean_object* v_headerBytesRead_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3426_; 
v_state_3400_ = lean_ctor_get(v_reader_3376_, 0);
v_input_3401_ = lean_ctor_get(v_reader_3376_, 1);
v_messageHead_3402_ = lean_ctor_get(v_reader_3376_, 2);
v_messageCount_3403_ = lean_ctor_get(v_reader_3376_, 3);
v_bodyBytesRead_3404_ = lean_ctor_get(v_reader_3376_, 4);
v_headerBytesRead_3405_ = lean_ctor_get(v_reader_3376_, 5);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_reader_3376_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3407_ = v_reader_3376_;
v_isShared_3408_ = v_isSharedCheck_3426_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_headerBytesRead_3405_);
lean_inc(v_bodyBytesRead_3404_);
lean_inc(v_messageCount_3403_);
lean_inc(v_messageHead_3402_);
lean_inc(v_input_3401_);
lean_inc(v_state_3400_);
lean_dec(v_reader_3376_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3426_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
uint8_t v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = 1;
if (v_isShared_3408_ == 0)
{
v___x_3411_ = v___x_3407_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_state_3400_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_input_3401_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_messageHead_3402_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_messageCount_3403_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_bodyBytesRead_3404_);
lean_ctor_set(v_reuseFailAlloc_3425_, 5, v_headerBytesRead_3405_);
v___x_3411_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
uint8_t v___x_3412_; lean_object* v___x_3414_; 
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*6, v___x_3409_);
v___x_3412_ = 0;
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3411_);
v___x_3414_ = v___x_3398_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_writer_3390_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_config_3391_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_events_3392_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_error_3393_);
lean_ctor_set(v_reuseFailAlloc_3424_, 5, v_instant_3394_);
lean_ctor_set_uint8(v_reuseFailAlloc_3424_, sizeof(void*)*6, v_keepAlive_3395_);
lean_ctor_set_uint8(v_reuseFailAlloc_3424_, sizeof(void*)*6 + 1, v_forcedFlush_3396_);
v___x_3414_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3416_; 
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*6 + 2, v___x_3412_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3414_);
v___x_3416_ = v___x_3388_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_requestStream_3377_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_keepAliveTimeout_3378_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_currentTimeout_3379_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_headerTimeout_3380_);
lean_ctor_set(v_reuseFailAlloc_3423_, 5, v_response_3381_);
lean_ctor_set(v_reuseFailAlloc_3423_, 6, v_respStream_3382_);
lean_ctor_set(v_reuseFailAlloc_3423_, 7, v_expectData_3384_);
lean_ctor_set(v_reuseFailAlloc_3423_, 8, v_pendingHead_3386_);
lean_ctor_set_uint8(v_reuseFailAlloc_3423_, sizeof(void*)*9, v_requiresData_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3423_, sizeof(void*)*9 + 1, v_handlerDispatched_3385_);
v___x_3416_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3417_ = lean_box(v___x_3412_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set_tag(v___x_3373_, 1);
lean_ctor_set(v___x_3373_, 0, v___x_3418_);
v___x_3420_ = v___x_3373_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
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
lean_object* v_val_3431_; lean_object* v_machine_3432_; lean_object* v_requestStream_3433_; lean_object* v_keepAliveTimeout_3434_; lean_object* v_currentTimeout_3435_; lean_object* v_response_3436_; lean_object* v_respStream_3437_; uint8_t v_requiresData_3438_; lean_object* v_expectData_3439_; uint8_t v_handlerDispatched_3440_; lean_object* v_pendingHead_3441_; lean_object* v___f_3442_; 
lean_del_object(v___x_3373_);
v_val_3431_ = lean_ctor_get(v_x_3371_, 0);
lean_inc_n(v_val_3431_, 2);
lean_dec_ref_known(v_x_3371_, 1);
v_machine_3432_ = lean_ctor_get(v_state_3369_, 0);
v_requestStream_3433_ = lean_ctor_get(v_state_3369_, 1);
v_keepAliveTimeout_3434_ = lean_ctor_get(v_state_3369_, 2);
lean_inc(v_keepAliveTimeout_3434_);
v_currentTimeout_3435_ = lean_ctor_get(v_state_3369_, 3);
v_response_3436_ = lean_ctor_get(v_state_3369_, 5);
v_respStream_3437_ = lean_ctor_get(v_state_3369_, 6);
v_requiresData_3438_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3439_ = lean_ctor_get(v_state_3369_, 7);
v_handlerDispatched_3440_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9 + 1);
v_pendingHead_3441_ = lean_ctor_get(v_state_3369_, 8);
v___f_3442_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3442_, 0, v_val_3431_);
if (lean_obj_tag(v_keepAliveTimeout_3434_) == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v___f_3442_);
lean_dec_ref(v_config_3367_);
v___x_3443_ = lean_box(0);
v___x_3444_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3431_, v___x_3443_, v_state_3369_);
return v___x_3444_;
}
else
{
lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3476_; 
lean_inc(v_pendingHead_3441_);
lean_inc(v_expectData_3439_);
lean_inc(v_respStream_3437_);
lean_inc_ref(v_response_3436_);
lean_inc(v_currentTimeout_3435_);
lean_inc_ref(v_requestStream_3433_);
lean_inc_ref(v_machine_3432_);
lean_dec(v_val_3431_);
lean_dec_ref(v_state_3369_);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_keepAliveTimeout_3434_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v_keepAliveTimeout_3434_, 0);
lean_dec(v_unused_3477_);
v___x_3446_ = v_keepAliveTimeout_3434_;
v_isShared_3447_ = v_isSharedCheck_3476_;
goto v_resetjp_3445_;
}
else
{
lean_dec(v_keepAliveTimeout_3434_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3476_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; lean_object* v_val_3454_; lean_object* v___x_3459_; 
v___x_3448_ = lean_box(v_requiresData_3438_);
v___x_3449_ = lean_box(v_handlerDispatched_3440_);
v___f_3450_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3450_, 0, v_config_3367_);
lean_closure_set(v___f_3450_, 1, v_machine_3432_);
lean_closure_set(v___f_3450_, 2, v_requestStream_3433_);
lean_closure_set(v___f_3450_, 3, v_currentTimeout_3435_);
lean_closure_set(v___f_3450_, 4, v_response_3436_);
lean_closure_set(v___f_3450_, 5, v_respStream_3437_);
lean_closure_set(v___f_3450_, 6, v___x_3448_);
lean_closure_set(v___f_3450_, 7, v_expectData_3439_);
lean_closure_set(v___f_3450_, 8, v___x_3449_);
lean_closure_set(v___f_3450_, 9, v_pendingHead_3441_);
lean_closure_set(v___f_3450_, 10, v___f_3442_);
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = 0;
v___x_3459_ = lean_get_current_time();
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 1);
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
v_val_3454_ = v___x_3465_;
goto v___jp_3453_;
}
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
v_a_3468_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3459_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3459_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 0);
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
v_val_3454_ = v___x_3473_;
goto v___jp_3453_;
}
}
}
v___jp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 0);
lean_ctor_set(v___x_3446_, 0, v_val_3454_);
v___x_3456_ = v___x_3446_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_val_3454_);
v___x_3456_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; 
v___x_3457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3451_, v___x_3452_, v___x_3456_, v___f_3450_);
return v___x_3457_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v_config_3367_);
lean_dec(v_handler_3366_);
lean_dec_ref(v_inst_3364_);
v_x_3479_ = lean_ctor_get(v_event_3368_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_event_3368_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3481_ = v_event_3368_;
v_isShared_3482_ = v_isSharedCheck_3590_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_x_3479_);
lean_dec(v_event_3368_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3590_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
if (lean_obj_tag(v_x_3479_) == 0)
{
lean_object* v_machine_3483_; lean_object* v_requestStream_3484_; lean_object* v_keepAliveTimeout_3485_; lean_object* v_currentTimeout_3486_; lean_object* v_headerTimeout_3487_; lean_object* v_response_3488_; lean_object* v_respStream_3489_; uint8_t v_requiresData_3490_; lean_object* v_expectData_3491_; uint8_t v_handlerDispatched_3492_; lean_object* v_pendingHead_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___f_3496_; 
lean_del_object(v___x_3481_);
v_machine_3483_ = lean_ctor_get(v_state_3369_, 0);
lean_inc_ref_n(v_machine_3483_, 2);
v_requestStream_3484_ = lean_ctor_get(v_state_3369_, 1);
lean_inc_ref_n(v_requestStream_3484_, 2);
v_keepAliveTimeout_3485_ = lean_ctor_get(v_state_3369_, 2);
lean_inc_n(v_keepAliveTimeout_3485_, 2);
v_currentTimeout_3486_ = lean_ctor_get(v_state_3369_, 3);
lean_inc_n(v_currentTimeout_3486_, 2);
v_headerTimeout_3487_ = lean_ctor_get(v_state_3369_, 4);
lean_inc_n(v_headerTimeout_3487_, 2);
v_response_3488_ = lean_ctor_get(v_state_3369_, 5);
lean_inc_ref_n(v_response_3488_, 2);
v_respStream_3489_ = lean_ctor_get(v_state_3369_, 6);
lean_inc(v_respStream_3489_);
v_requiresData_3490_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3491_ = lean_ctor_get(v_state_3369_, 7);
lean_inc_n(v_expectData_3491_, 2);
v_handlerDispatched_3492_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9 + 1);
v_pendingHead_3493_ = lean_ctor_get(v_state_3369_, 8);
lean_inc_n(v_pendingHead_3493_, 2);
lean_dec_ref(v_state_3369_);
v___x_3494_ = lean_box(v_requiresData_3490_);
v___x_3495_ = lean_box(v_handlerDispatched_3492_);
v___f_3496_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3496_, 0, v_machine_3483_);
lean_closure_set(v___f_3496_, 1, v_requestStream_3484_);
lean_closure_set(v___f_3496_, 2, v_keepAliveTimeout_3485_);
lean_closure_set(v___f_3496_, 3, v_currentTimeout_3486_);
lean_closure_set(v___f_3496_, 4, v_headerTimeout_3487_);
lean_closure_set(v___f_3496_, 5, v_response_3488_);
lean_closure_set(v___f_3496_, 6, v___x_3494_);
lean_closure_set(v___f_3496_, 7, v_expectData_3491_);
lean_closure_set(v___f_3496_, 8, v___x_3495_);
lean_closure_set(v___f_3496_, 9, v_pendingHead_3493_);
if (lean_obj_tag(v_respStream_3489_) == 1)
{
lean_object* v_val_3497_; lean_object* v_close_3498_; lean_object* v_isClosed_3499_; lean_object* v___f_3500_; lean_object* v___f_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec(v_pendingHead_3493_);
lean_dec(v_expectData_3491_);
lean_dec_ref(v_response_3488_);
lean_dec(v_headerTimeout_3487_);
lean_dec(v_currentTimeout_3486_);
lean_dec(v_keepAliveTimeout_3485_);
lean_dec_ref(v_requestStream_3484_);
lean_dec_ref(v_machine_3483_);
v_val_3497_ = lean_ctor_get(v_respStream_3489_, 0);
lean_inc_n(v_val_3497_, 2);
lean_dec_ref_known(v_respStream_3489_, 1);
v_close_3498_ = lean_ctor_get(v_inst_3365_, 1);
lean_inc_ref(v_close_3498_);
v_isClosed_3499_ = lean_ctor_get(v_inst_3365_, 2);
lean_inc_ref(v_isClosed_3499_);
lean_dec_ref(v_inst_3365_);
lean_inc_ref(v___f_3496_);
v___f_3500_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3500_, 0, v___f_3496_);
v___f_3501_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3501_, 0, v_close_3498_);
lean_closure_set(v___f_3501_, 1, v_val_3497_);
lean_closure_set(v___f_3501_, 2, v___f_3500_);
lean_closure_set(v___f_3501_, 3, v___f_3496_);
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = 0;
v___x_3504_ = lean_apply_2(v_isClosed_3499_, v_val_3497_, lean_box(0));
v___x_3505_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3502_, v___x_3503_, v___x_3504_, v___f_3501_);
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec_ref(v___f_3496_);
lean_dec(v_respStream_3489_);
lean_dec_ref(v_inst_3365_);
v___x_3506_ = lean_box(0);
v___x_3507_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3483_, v_requestStream_3484_, v_keepAliveTimeout_3485_, v_currentTimeout_3486_, v_headerTimeout_3487_, v_response_3488_, v_requiresData_3490_, v_expectData_3491_, v_handlerDispatched_3492_, v_pendingHead_3493_, v___x_3506_);
return v___x_3507_;
}
}
else
{
lean_object* v_val_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v_inst_3365_);
v_val_3508_ = lean_ctor_get(v_x_3479_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_x_3479_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3510_ = v_x_3479_;
v_isShared_3511_ = v_isSharedCheck_3589_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_val_3508_);
lean_dec(v_x_3479_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3589_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_machine_3512_; lean_object* v_requestStream_3513_; lean_object* v_keepAliveTimeout_3514_; lean_object* v_currentTimeout_3515_; lean_object* v_headerTimeout_3516_; lean_object* v_response_3517_; lean_object* v_respStream_3518_; uint8_t v_requiresData_3519_; lean_object* v_expectData_3520_; uint8_t v_handlerDispatched_3521_; lean_object* v_pendingHead_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3588_; 
v_machine_3512_ = lean_ctor_get(v_state_3369_, 0);
v_requestStream_3513_ = lean_ctor_get(v_state_3369_, 1);
v_keepAliveTimeout_3514_ = lean_ctor_get(v_state_3369_, 2);
v_currentTimeout_3515_ = lean_ctor_get(v_state_3369_, 3);
v_headerTimeout_3516_ = lean_ctor_get(v_state_3369_, 4);
v_response_3517_ = lean_ctor_get(v_state_3369_, 5);
v_respStream_3518_ = lean_ctor_get(v_state_3369_, 6);
v_requiresData_3519_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3520_ = lean_ctor_get(v_state_3369_, 7);
v_handlerDispatched_3521_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9 + 1);
v_pendingHead_3522_ = lean_ctor_get(v_state_3369_, 8);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_state_3369_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3524_ = v_state_3369_;
v_isShared_3525_ = v_isSharedCheck_3588_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_pendingHead_3522_);
lean_inc(v_expectData_3520_);
lean_inc(v_respStream_3518_);
lean_inc(v_response_3517_);
lean_inc(v_headerTimeout_3516_);
lean_inc(v_currentTimeout_3515_);
lean_inc(v_keepAliveTimeout_3514_);
lean_inc(v_requestStream_3513_);
lean_inc(v_machine_3512_);
lean_dec(v_state_3369_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3588_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___y_3527_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3540_ = lean_unsigned_to_nat(1u);
v___x_3541_ = lean_mk_empty_array_with_capacity(v___x_3540_);
v___x_3542_ = lean_array_push(v___x_3541_, v_val_3508_);
v___x_3543_ = lean_array_get_size(v___x_3542_);
v___x_3544_ = lean_unsigned_to_nat(0u);
v___x_3545_ = lean_nat_dec_eq(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v_reader_3546_; lean_object* v_writer_3547_; lean_object* v_config_3548_; lean_object* v_events_3549_; lean_object* v_error_3550_; lean_object* v_instant_3551_; uint8_t v_keepAlive_3552_; uint8_t v_forcedFlush_3553_; uint8_t v_pullBodyStalled_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3587_; 
v_reader_3546_ = lean_ctor_get(v_machine_3512_, 0);
v_writer_3547_ = lean_ctor_get(v_machine_3512_, 1);
v_config_3548_ = lean_ctor_get(v_machine_3512_, 2);
v_events_3549_ = lean_ctor_get(v_machine_3512_, 3);
v_error_3550_ = lean_ctor_get(v_machine_3512_, 4);
v_instant_3551_ = lean_ctor_get(v_machine_3512_, 5);
v_keepAlive_3552_ = lean_ctor_get_uint8(v_machine_3512_, sizeof(void*)*6);
v_forcedFlush_3553_ = lean_ctor_get_uint8(v_machine_3512_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3554_ = lean_ctor_get_uint8(v_machine_3512_, sizeof(void*)*6 + 2);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_machine_3512_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3556_ = v_machine_3512_;
v_isShared_3557_ = v_isSharedCheck_3587_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_instant_3551_);
lean_inc(v_error_3550_);
lean_inc(v_events_3549_);
lean_inc(v_config_3548_);
lean_inc(v_writer_3547_);
lean_inc(v_reader_3546_);
lean_dec(v_machine_3512_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3587_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___y_3559_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_3582_ = lean_nat_dec_lt(v___x_3544_, v___x_3543_);
if (v___x_3582_ == 0)
{
v___y_3559_ = v___x_3544_;
goto v___jp_3558_;
}
else
{
lean_object* v___f_3583_; size_t v___x_3584_; size_t v___x_3585_; lean_object* v___x_3586_; 
v___f_3583_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3584_ = ((size_t)0ULL);
v___x_3585_ = lean_usize_of_nat(v___x_3543_);
lean_inc_ref(v___x_3542_);
v___x_3586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3581_, v___f_3583_, v___x_3542_, v___x_3584_, v___x_3585_, v___x_3544_);
v___y_3559_ = v___x_3586_;
goto v___jp_3558_;
}
v___jp_3558_:
{
lean_object* v_userData_3560_; lean_object* v_outputData_3561_; lean_object* v_state_3562_; lean_object* v_knownSize_3563_; lean_object* v_messageHead_3564_; uint8_t v_sentMessage_3565_; uint8_t v_userClosedBody_3566_; uint8_t v_omitBody_3567_; lean_object* v_userDataBytes_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3580_; 
v_userData_3560_ = lean_ctor_get(v_writer_3547_, 0);
v_outputData_3561_ = lean_ctor_get(v_writer_3547_, 1);
v_state_3562_ = lean_ctor_get(v_writer_3547_, 2);
v_knownSize_3563_ = lean_ctor_get(v_writer_3547_, 3);
v_messageHead_3564_ = lean_ctor_get(v_writer_3547_, 4);
v_sentMessage_3565_ = lean_ctor_get_uint8(v_writer_3547_, sizeof(void*)*6);
v_userClosedBody_3566_ = lean_ctor_get_uint8(v_writer_3547_, sizeof(void*)*6 + 1);
v_omitBody_3567_ = lean_ctor_get_uint8(v_writer_3547_, sizeof(void*)*6 + 2);
v_userDataBytes_3568_ = lean_ctor_get(v_writer_3547_, 5);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_writer_3547_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3570_ = v_writer_3547_;
v_isShared_3571_ = v_isSharedCheck_3580_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_userDataBytes_3568_);
lean_inc(v_messageHead_3564_);
lean_inc(v_knownSize_3563_);
lean_inc(v_state_3562_);
lean_inc(v_outputData_3561_);
lean_inc(v_userData_3560_);
lean_dec(v_writer_3547_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3580_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = l_Array_append___redArg(v_userData_3560_, v___x_3542_);
lean_dec_ref(v___x_3542_);
v___x_3573_ = lean_nat_add(v_userDataBytes_3568_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec(v_userDataBytes_3568_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 5, v___x_3573_);
lean_ctor_set(v___x_3570_, 0, v___x_3572_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_outputData_3561_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_state_3562_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_knownSize_3563_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_messageHead_3564_);
lean_ctor_set(v_reuseFailAlloc_3579_, 5, v___x_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*6, v_sentMessage_3565_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*6 + 1, v_userClosedBody_3566_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*6 + 2, v_omitBody_3567_);
v___x_3575_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3577_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 1, v___x_3575_);
v___x_3577_ = v___x_3556_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_reader_3546_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_config_3548_);
lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_events_3549_);
lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_error_3550_);
lean_ctor_set(v_reuseFailAlloc_3578_, 5, v_instant_3551_);
lean_ctor_set_uint8(v_reuseFailAlloc_3578_, sizeof(void*)*6, v_keepAlive_3552_);
lean_ctor_set_uint8(v_reuseFailAlloc_3578_, sizeof(void*)*6 + 1, v_forcedFlush_3553_);
lean_ctor_set_uint8(v_reuseFailAlloc_3578_, sizeof(void*)*6 + 2, v_pullBodyStalled_3554_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
v___y_3527_ = v___x_3577_;
goto v___jp_3526_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3542_);
v___y_3527_ = v_machine_3512_;
goto v___jp_3526_;
}
v___jp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___y_3527_);
v___x_3529_ = v___x_3524_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___y_3527_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_requestStream_3513_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_keepAliveTimeout_3514_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v_currentTimeout_3515_);
lean_ctor_set(v_reuseFailAlloc_3539_, 4, v_headerTimeout_3516_);
lean_ctor_set(v_reuseFailAlloc_3539_, 5, v_response_3517_);
lean_ctor_set(v_reuseFailAlloc_3539_, 6, v_respStream_3518_);
lean_ctor_set(v_reuseFailAlloc_3539_, 7, v_expectData_3520_);
lean_ctor_set(v_reuseFailAlloc_3539_, 8, v_pendingHead_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3539_, sizeof(void*)*9, v_requiresData_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3539_, sizeof(void*)*9 + 1, v_handlerDispatched_3521_);
v___x_3529_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
uint8_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3530_ = 0;
v___x_3531_ = lean_box(v___x_3530_);
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3529_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3532_);
v___x_3534_ = v___x_3510_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set_tag(v___x_3481_, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3534_);
v___x_3536_ = v___x_3481_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
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
uint8_t v_x_3591_; 
lean_dec_ref(v_config_3367_);
lean_dec_ref(v_inst_3365_);
v_x_3591_ = lean_ctor_get_uint8(v_event_3368_, 0);
lean_dec_ref_known(v_event_3368_, 0);
if (v_x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec(v_handler_3366_);
lean_dec_ref(v_inst_3364_);
v___x_3592_ = lean_box(v_x_3591_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v_state_3369_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
else
{
lean_object* v_machine_3596_; lean_object* v_requestStream_3597_; lean_object* v_keepAliveTimeout_3598_; lean_object* v_currentTimeout_3599_; lean_object* v_headerTimeout_3600_; lean_object* v_response_3601_; lean_object* v_respStream_3602_; uint8_t v_requiresData_3603_; lean_object* v_expectData_3604_; uint8_t v_handlerDispatched_3605_; lean_object* v_pendingHead_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3656_; 
v_machine_3596_ = lean_ctor_get(v_state_3369_, 0);
v_requestStream_3597_ = lean_ctor_get(v_state_3369_, 1);
v_keepAliveTimeout_3598_ = lean_ctor_get(v_state_3369_, 2);
v_currentTimeout_3599_ = lean_ctor_get(v_state_3369_, 3);
v_headerTimeout_3600_ = lean_ctor_get(v_state_3369_, 4);
v_response_3601_ = lean_ctor_get(v_state_3369_, 5);
v_respStream_3602_ = lean_ctor_get(v_state_3369_, 6);
v_requiresData_3603_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3604_ = lean_ctor_get(v_state_3369_, 7);
v_handlerDispatched_3605_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9 + 1);
v_pendingHead_3606_ = lean_ctor_get(v_state_3369_, 8);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_state_3369_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3608_ = v_state_3369_;
v_isShared_3609_ = v_isSharedCheck_3656_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_pendingHead_3606_);
lean_inc(v_expectData_3604_);
lean_inc(v_respStream_3602_);
lean_inc(v_response_3601_);
lean_inc(v_headerTimeout_3600_);
lean_inc(v_currentTimeout_3599_);
lean_inc(v_keepAliveTimeout_3598_);
lean_inc(v_requestStream_3597_);
lean_inc(v_machine_3596_);
lean_dec(v_state_3369_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3656_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
uint8_t v___x_3610_; lean_object* v___x_3611_; lean_object* v_fst_3612_; lean_object* v_snd_3613_; lean_object* v_reader_3614_; lean_object* v_writer_3615_; lean_object* v_config_3616_; lean_object* v_events_3617_; lean_object* v_error_3618_; lean_object* v_instant_3619_; uint8_t v_keepAlive_3620_; uint8_t v_forcedFlush_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3655_; 
v___x_3610_ = 0;
v___x_3611_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3610_, v_machine_3596_);
v_fst_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_fst_3612_);
v_snd_3613_ = lean_ctor_get(v___x_3611_, 1);
lean_inc(v_snd_3613_);
lean_dec_ref(v___x_3611_);
v_reader_3614_ = lean_ctor_get(v_fst_3612_, 0);
v_writer_3615_ = lean_ctor_get(v_fst_3612_, 1);
v_config_3616_ = lean_ctor_get(v_fst_3612_, 2);
v_events_3617_ = lean_ctor_get(v_fst_3612_, 3);
v_error_3618_ = lean_ctor_get(v_fst_3612_, 4);
v_instant_3619_ = lean_ctor_get(v_fst_3612_, 5);
v_keepAlive_3620_ = lean_ctor_get_uint8(v_fst_3612_, sizeof(void*)*6);
v_forcedFlush_3621_ = lean_ctor_get_uint8(v_fst_3612_, sizeof(void*)*6 + 1);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_fst_3612_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3623_ = v_fst_3612_;
v_isShared_3624_ = v_isSharedCheck_3655_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_instant_3619_);
lean_inc(v_error_3618_);
lean_inc(v_events_3617_);
lean_inc(v_config_3616_);
lean_inc(v_writer_3615_);
lean_inc(v_reader_3614_);
lean_dec(v_fst_3612_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3655_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___f_3625_; lean_object* v___f_3626_; uint8_t v___y_3628_; 
v___f_3625_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_3626_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_3626_, 0, v_inst_3364_);
lean_closure_set(v___f_3626_, 1, v_handler_3366_);
if (lean_obj_tag(v_snd_3613_) == 0)
{
uint8_t v_sentMessage_3651_; 
v_sentMessage_3651_ = lean_ctor_get_uint8(v_writer_3615_, sizeof(void*)*6);
if (v_sentMessage_3651_ == 0)
{
lean_object* v_state_3652_; 
v_state_3652_ = lean_ctor_get(v_reader_3614_, 0);
if (lean_obj_tag(v_state_3652_) == 2)
{
v___y_3628_ = v_x_3591_;
goto v___jp_3627_;
}
else
{
v___y_3628_ = v_sentMessage_3651_;
goto v___jp_3627_;
}
}
else
{
uint8_t v___x_3653_; 
v___x_3653_ = 0;
v___y_3628_ = v___x_3653_;
goto v___jp_3627_;
}
}
else
{
uint8_t v___x_3654_; 
v___x_3654_ = 0;
v___y_3628_ = v___x_3654_;
goto v___jp_3627_;
}
v___jp_3627_:
{
lean_object* v___x_3630_; 
if (v_isShared_3624_ == 0)
{
v___x_3630_ = v___x_3623_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_reader_3614_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_writer_3615_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_config_3616_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_events_3617_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_error_3618_);
lean_ctor_set(v_reuseFailAlloc_3650_, 5, v_instant_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3650_, sizeof(void*)*6, v_keepAlive_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3650_, sizeof(void*)*6 + 1, v_forcedFlush_3621_);
v___x_3630_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v_st_3632_; 
lean_ctor_set_uint8(v___x_3630_, sizeof(void*)*6 + 2, v___y_3628_);
lean_inc_ref(v_requestStream_3597_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3630_);
v_st_3632_ = v___x_3608_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_requestStream_3597_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_keepAliveTimeout_3598_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v_currentTimeout_3599_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v_headerTimeout_3600_);
lean_ctor_set(v_reuseFailAlloc_3649_, 5, v_response_3601_);
lean_ctor_set(v_reuseFailAlloc_3649_, 6, v_respStream_3602_);
lean_ctor_set(v_reuseFailAlloc_3649_, 7, v_expectData_3604_);
lean_ctor_set(v_reuseFailAlloc_3649_, 8, v_pendingHead_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3649_, sizeof(void*)*9, v_requiresData_3603_);
lean_ctor_set_uint8(v_reuseFailAlloc_3649_, sizeof(void*)*9 + 1, v_handlerDispatched_3605_);
v_st_3632_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___f_3633_; 
lean_inc_ref(v_st_3632_);
v___f_3633_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3633_, 0, v_st_3632_);
if (lean_obj_tag(v_snd_3613_) == 1)
{
lean_object* v_val_3634_; uint8_t v_final_3635_; uint8_t v_incomplete_3636_; lean_object* v_chunk_3637_; lean_object* v___f_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_dec_ref(v_st_3632_);
v_val_3634_ = lean_ctor_get(v_snd_3613_, 0);
lean_inc(v_val_3634_);
lean_dec_ref_known(v_snd_3613_, 1);
v_final_3635_ = lean_ctor_get_uint8(v_val_3634_, sizeof(void*)*1);
v_incomplete_3636_ = lean_ctor_get_uint8(v_val_3634_, sizeof(void*)*1 + 1);
v_chunk_3637_ = lean_ctor_get(v_val_3634_, 0);
lean_inc_ref(v_chunk_3637_);
lean_dec(v_val_3634_);
lean_inc_ref_n(v___f_3633_, 2);
v___f_3638_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3638_, 0, v___f_3633_);
lean_inc_ref_n(v_requestStream_3597_, 2);
v___f_3639_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3639_, 0, v_requestStream_3597_);
lean_closure_set(v___f_3639_, 1, v___f_3638_);
lean_closure_set(v___f_3639_, 2, v___f_3633_);
v___x_3640_ = lean_box(v_final_3635_);
v___f_3641_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_3641_, 0, v___x_3640_);
lean_closure_set(v___f_3641_, 1, v___f_3633_);
lean_closure_set(v___f_3641_, 2, v___f_3625_);
lean_closure_set(v___f_3641_, 3, v_requestStream_3597_);
lean_closure_set(v___f_3641_, 4, v___f_3639_);
v___x_3642_ = lean_unsigned_to_nat(0u);
v___x_3643_ = 0;
v___x_3644_ = l_Std_Http_Body_Stream_send(v_requestStream_3597_, v_chunk_3637_, v_incomplete_3636_);
v___x_3645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3642_, v___x_3643_, v___x_3644_, v___f_3626_);
v___x_3646_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3642_, v___x_3643_, v___x_3645_, v___f_3641_);
return v___x_3646_;
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec_ref(v___f_3633_);
lean_dec_ref(v___f_3626_);
lean_dec(v_snd_3613_);
lean_dec_ref(v_requestStream_3597_);
v___x_3647_ = lean_box(0);
v___x_3648_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3632_, v___x_3647_);
return v___x_3648_;
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
lean_object* v_x_3657_; 
v_x_3657_ = lean_ctor_get(v_event_3368_, 0);
lean_inc_ref(v_x_3657_);
lean_dec_ref_known(v_event_3368_, 1);
if (lean_obj_tag(v_x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v_onFailure_3659_; lean_object* v___f_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec_ref(v_config_3367_);
lean_dec_ref(v_inst_3365_);
v_a_3658_ = lean_ctor_get(v_x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v_x_3657_, 1);
v_onFailure_3659_ = lean_ctor_get(v_inst_3364_, 2);
lean_inc_ref(v_onFailure_3659_);
lean_dec_ref(v_inst_3364_);
v___f_3660_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3660_, 0, v_state_3369_);
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = 0;
v___x_3663_ = lean_apply_3(v_onFailure_3659_, v_handler_3366_, v_a_3658_, lean_box(0));
v___x_3664_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3661_, v___x_3662_, v___x_3663_, v___f_3660_);
return v___x_3664_;
}
else
{
lean_object* v_machine_3665_; lean_object* v_reader_3666_; lean_object* v_state_3667_; 
v_machine_3665_ = lean_ctor_get(v_state_3369_, 0);
lean_inc_ref(v_machine_3665_);
v_reader_3666_ = lean_ctor_get(v_machine_3665_, 0);
v_state_3667_ = lean_ctor_get(v_reader_3666_, 0);
if (lean_obj_tag(v_state_3667_) == 7)
{
lean_object* v_a_3668_; lean_object* v_requestStream_3669_; lean_object* v_keepAliveTimeout_3670_; lean_object* v_currentTimeout_3671_; lean_object* v_headerTimeout_3672_; lean_object* v_response_3673_; lean_object* v_respStream_3674_; uint8_t v_requiresData_3675_; lean_object* v_expectData_3676_; lean_object* v_pendingHead_3677_; lean_object* v_close_3678_; lean_object* v_isClosed_3679_; lean_object* v_body_3680_; lean_object* v___x_3681_; lean_object* v___f_3682_; lean_object* v___f_3683_; lean_object* v___f_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
lean_dec_ref(v_config_3367_);
lean_dec(v_handler_3366_);
lean_dec_ref(v_inst_3364_);
v_a_3668_ = lean_ctor_get(v_x_3657_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v_x_3657_, 1);
v_requestStream_3669_ = lean_ctor_get(v_state_3369_, 1);
lean_inc_ref(v_requestStream_3669_);
v_keepAliveTimeout_3670_ = lean_ctor_get(v_state_3369_, 2);
lean_inc(v_keepAliveTimeout_3670_);
v_currentTimeout_3671_ = lean_ctor_get(v_state_3369_, 3);
lean_inc(v_currentTimeout_3671_);
v_headerTimeout_3672_ = lean_ctor_get(v_state_3369_, 4);
lean_inc(v_headerTimeout_3672_);
v_response_3673_ = lean_ctor_get(v_state_3369_, 5);
lean_inc_ref(v_response_3673_);
v_respStream_3674_ = lean_ctor_get(v_state_3369_, 6);
lean_inc(v_respStream_3674_);
v_requiresData_3675_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3676_ = lean_ctor_get(v_state_3369_, 7);
lean_inc(v_expectData_3676_);
v_pendingHead_3677_ = lean_ctor_get(v_state_3369_, 8);
lean_inc(v_pendingHead_3677_);
lean_dec_ref(v_state_3369_);
v_close_3678_ = lean_ctor_get(v_inst_3365_, 1);
lean_inc_ref(v_close_3678_);
v_isClosed_3679_ = lean_ctor_get(v_inst_3365_, 2);
lean_inc_ref(v_isClosed_3679_);
lean_dec_ref(v_inst_3365_);
v_body_3680_ = lean_ctor_get(v_a_3668_, 1);
lean_inc_n(v_body_3680_, 2);
lean_dec(v_a_3668_);
v___x_3681_ = lean_box(v_requiresData_3675_);
v___f_3682_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3682_, 0, v_machine_3665_);
lean_closure_set(v___f_3682_, 1, v_requestStream_3669_);
lean_closure_set(v___f_3682_, 2, v_keepAliveTimeout_3670_);
lean_closure_set(v___f_3682_, 3, v_currentTimeout_3671_);
lean_closure_set(v___f_3682_, 4, v_headerTimeout_3672_);
lean_closure_set(v___f_3682_, 5, v_response_3673_);
lean_closure_set(v___f_3682_, 6, v_respStream_3674_);
lean_closure_set(v___f_3682_, 7, v___x_3681_);
lean_closure_set(v___f_3682_, 8, v_expectData_3676_);
lean_closure_set(v___f_3682_, 9, v_pendingHead_3677_);
lean_inc_ref(v___f_3682_);
v___f_3683_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3683_, 0, v___f_3682_);
v___f_3684_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3684_, 0, v_close_3678_);
lean_closure_set(v___f_3684_, 1, v_body_3680_);
lean_closure_set(v___f_3684_, 2, v___f_3683_);
lean_closure_set(v___f_3684_, 3, v___f_3682_);
v___x_3685_ = lean_unsigned_to_nat(0u);
v___x_3686_ = 0;
v___x_3687_ = lean_apply_2(v_isClosed_3679_, v_body_3680_, lean_box(0));
v___x_3688_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3685_, v___x_3686_, v___x_3687_, v___f_3684_);
return v___x_3688_;
}
else
{
lean_object* v_a_3689_; lean_object* v_requestStream_3690_; lean_object* v_keepAliveTimeout_3691_; lean_object* v_currentTimeout_3692_; lean_object* v_headerTimeout_3693_; lean_object* v_response_3694_; uint8_t v_requiresData_3695_; lean_object* v_expectData_3696_; lean_object* v_pendingHead_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___f_3703_; uint8_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_a_3689_ = lean_ctor_get(v_x_3657_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v_x_3657_, 1);
v_requestStream_3690_ = lean_ctor_get(v_state_3369_, 1);
lean_inc_ref(v_requestStream_3690_);
v_keepAliveTimeout_3691_ = lean_ctor_get(v_state_3369_, 2);
lean_inc(v_keepAliveTimeout_3691_);
v_currentTimeout_3692_ = lean_ctor_get(v_state_3369_, 3);
lean_inc(v_currentTimeout_3692_);
v_headerTimeout_3693_ = lean_ctor_get(v_state_3369_, 4);
lean_inc(v_headerTimeout_3693_);
v_response_3694_ = lean_ctor_get(v_state_3369_, 5);
lean_inc_ref(v_response_3694_);
v_requiresData_3695_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3696_ = lean_ctor_get(v_state_3369_, 7);
lean_inc(v_expectData_3696_);
v_pendingHead_3697_ = lean_ctor_get(v_state_3369_, 8);
lean_inc(v_pendingHead_3697_);
lean_dec_ref(v_state_3369_);
v___x_3698_ = 0;
v___x_3699_ = lean_box(v_requiresData_3695_);
v___x_3700_ = lean_box(v___x_3698_);
v___f_3701_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3701_, 0, v_requestStream_3690_);
lean_closure_set(v___f_3701_, 1, v_keepAliveTimeout_3691_);
lean_closure_set(v___f_3701_, 2, v_currentTimeout_3692_);
lean_closure_set(v___f_3701_, 3, v_headerTimeout_3693_);
lean_closure_set(v___f_3701_, 4, v_response_3694_);
lean_closure_set(v___f_3701_, 5, v___x_3699_);
lean_closure_set(v___f_3701_, 6, v_expectData_3696_);
lean_closure_set(v___f_3701_, 7, v___x_3700_);
lean_closure_set(v___f_3701_, 8, v_pendingHead_3697_);
v___f_3702_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3702_, 0, v___f_3701_);
v___f_3703_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3704_ = 1;
v___x_3705_ = lean_box(v___x_3698_);
v___x_3706_ = lean_box(v___x_3704_);
lean_inc_ref(v_inst_3365_);
lean_inc_ref(v___f_3702_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3707_, 0, v___x_3705_);
lean_closure_set(v___f_3707_, 1, v___f_3702_);
lean_closure_set(v___f_3707_, 2, v___x_3706_);
lean_closure_set(v___f_3707_, 3, v_inst_3364_);
lean_closure_set(v___f_3707_, 4, v_handler_3366_);
lean_closure_set(v___f_3707_, 5, v_inst_3365_);
lean_closure_set(v___f_3707_, 6, v___f_3703_);
lean_closure_set(v___f_3707_, 7, v___f_3702_);
v___x_3708_ = lean_unsigned_to_nat(0u);
v___x_3709_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3365_, v_config_3367_, v_machine_3665_, v_a_3689_);
v___x_3710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3708_, v___x_3698_, v___x_3709_, v___f_3707_);
return v___x_3710_;
}
}
}
case 4:
{
lean_object* v_onFailure_3711_; lean_object* v___f_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec_ref(v_config_3367_);
lean_dec_ref(v_inst_3365_);
v_onFailure_3711_ = lean_ctor_get(v_inst_3364_, 2);
lean_inc_ref(v_onFailure_3711_);
lean_dec_ref(v_inst_3364_);
v___f_3712_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3712_, 0, v_state_3369_);
v___x_3713_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = 0;
v___x_3716_ = lean_apply_3(v_onFailure_3711_, v_handler_3366_, v___x_3713_, lean_box(0));
v___x_3717_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3714_, v___x_3715_, v___x_3716_, v___f_3712_);
return v___x_3717_;
}
case 5:
{
lean_object* v_machine_3718_; lean_object* v_requestStream_3719_; lean_object* v_keepAliveTimeout_3720_; lean_object* v_currentTimeout_3721_; lean_object* v_headerTimeout_3722_; lean_object* v_response_3723_; lean_object* v_respStream_3724_; uint8_t v_requiresData_3725_; lean_object* v_expectData_3726_; lean_object* v_pendingHead_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v_config_3367_);
lean_dec(v_handler_3366_);
lean_dec_ref(v_inst_3365_);
lean_dec_ref(v_inst_3364_);
v_machine_3718_ = lean_ctor_get(v_state_3369_, 0);
v_requestStream_3719_ = lean_ctor_get(v_state_3369_, 1);
v_keepAliveTimeout_3720_ = lean_ctor_get(v_state_3369_, 2);
v_currentTimeout_3721_ = lean_ctor_get(v_state_3369_, 3);
v_headerTimeout_3722_ = lean_ctor_get(v_state_3369_, 4);
v_response_3723_ = lean_ctor_get(v_state_3369_, 5);
v_respStream_3724_ = lean_ctor_get(v_state_3369_, 6);
v_requiresData_3725_ = lean_ctor_get_uint8(v_state_3369_, sizeof(void*)*9);
v_expectData_3726_ = lean_ctor_get(v_state_3369_, 7);
v_pendingHead_3727_ = lean_ctor_get(v_state_3369_, 8);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_state_3369_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3729_ = v_state_3369_;
v_isShared_3730_ = v_isSharedCheck_3741_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_pendingHead_3727_);
lean_inc(v_expectData_3726_);
lean_inc(v_respStream_3724_);
lean_inc(v_response_3723_);
lean_inc(v_headerTimeout_3722_);
lean_inc(v_currentTimeout_3721_);
lean_inc(v_keepAliveTimeout_3720_);
lean_inc(v_requestStream_3719_);
lean_inc(v_machine_3718_);
lean_dec(v_state_3369_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3741_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3735_; 
v___x_3731_ = lean_box(55);
v___x_3732_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3718_, v___x_3731_);
v___x_3733_ = 0;
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3732_);
v___x_3735_ = v___x_3729_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_requestStream_3719_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_keepAliveTimeout_3720_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v_currentTimeout_3721_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v_headerTimeout_3722_);
lean_ctor_set(v_reuseFailAlloc_3740_, 5, v_response_3723_);
lean_ctor_set(v_reuseFailAlloc_3740_, 6, v_respStream_3724_);
lean_ctor_set(v_reuseFailAlloc_3740_, 7, v_expectData_3726_);
lean_ctor_set(v_reuseFailAlloc_3740_, 8, v_pendingHead_3727_);
lean_ctor_set_uint8(v_reuseFailAlloc_3740_, sizeof(void*)*9, v_requiresData_3725_);
v___x_3735_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_ctor_set_uint8(v___x_3735_, sizeof(void*)*9 + 1, v___x_3733_);
v___x_3736_ = lean_box(v___x_3733_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
}
}
default: 
{
uint8_t v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec_ref(v_config_3367_);
lean_dec(v_handler_3366_);
lean_dec_ref(v_inst_3365_);
lean_dec_ref(v_inst_3364_);
v___x_3742_ = 1;
v___x_3743_ = lean_box(v___x_3742_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v_state_3369_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
return v___x_3746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3747_, lean_object* v_inst_3748_, lean_object* v_handler_3749_, lean_object* v_config_3750_, lean_object* v_event_3751_, lean_object* v_state_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3747_, v_inst_3748_, v_handler_3749_, v_config_3750_, v_event_3751_, v_state_3752_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3755_, lean_object* v_00_u03b2_3756_, lean_object* v_inst_3757_, lean_object* v_inst_3758_, lean_object* v_handler_3759_, lean_object* v_config_3760_, lean_object* v_event_3761_, lean_object* v_state_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3757_, v_inst_3758_, v_handler_3759_, v_config_3760_, v_event_3761_, v_state_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3765_, lean_object* v_00_u03b2_3766_, lean_object* v_inst_3767_, lean_object* v_inst_3768_, lean_object* v_handler_3769_, lean_object* v_config_3770_, lean_object* v_event_3771_, lean_object* v_state_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3765_, v_00_u03b2_3766_, v_inst_3767_, v_inst_3768_, v_handler_3769_, v_config_3770_, v_event_3771_, v_state_3772_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3775_, uint8_t v_handlerDispatched_3776_, lean_object* v_keepAliveTimeout_3777_, lean_object* v_headerTimeout_3778_, lean_object* v_expectData_3779_, lean_object* v_respStream_3780_, lean_object* v_currentTimeout_3781_, lean_object* v_response_3782_, lean_object* v_socket_3783_, uint8_t v_requiresData_3784_, uint8_t v_sentMessage_3785_, lean_object* v_reader_3786_, uint8_t v_requestBodyInterested_3787_, lean_object* v_requestBody_3788_){
_start:
{
lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3802_; 
if (v_requiresData_3784_ == 0)
{
if (v_handlerDispatched_3776_ == 0)
{
goto v___jp_3805_;
}
else
{
if (lean_obj_tag(v_respStream_3780_) == 0)
{
if (v_sentMessage_3785_ == 0)
{
lean_object* v_state_3809_; 
v_state_3809_ = lean_ctor_get(v_reader_3786_, 0);
if (lean_obj_tag(v_state_3809_) == 2)
{
if (v_requestBodyInterested_3787_ == 0)
{
lean_dec(v_socket_3783_);
goto v___jp_3807_;
}
else
{
goto v___jp_3805_;
}
}
else
{
lean_dec(v_socket_3783_);
goto v___jp_3807_;
}
}
else
{
goto v___jp_3805_;
}
}
else
{
goto v___jp_3805_;
}
}
}
else
{
goto v___jp_3805_;
}
v___jp_3790_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3798_, 0, v___y_3792_);
lean_ctor_set(v___x_3798_, 1, v___y_3794_);
lean_ctor_set(v___x_3798_, 2, v___y_3797_);
lean_ctor_set(v___x_3798_, 3, v___y_3795_);
lean_ctor_set(v___x_3798_, 4, v_requestBody_3788_);
lean_ctor_set(v___x_3798_, 5, v___y_3796_);
lean_ctor_set(v___x_3798_, 6, v___y_3791_);
lean_ctor_set(v___x_3798_, 7, v___y_3793_);
lean_ctor_set(v___x_3798_, 8, v_connectionContext_3775_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
return v___x_3800_;
}
v___jp_3801_:
{
if (v_handlerDispatched_3776_ == 0)
{
lean_object* v___x_3803_; 
lean_dec_ref(v_response_3782_);
v___x_3803_ = lean_box(0);
v___y_3791_ = v_keepAliveTimeout_3777_;
v___y_3792_ = v___y_3802_;
v___y_3793_ = v_headerTimeout_3778_;
v___y_3794_ = v_expectData_3779_;
v___y_3795_ = v_respStream_3780_;
v___y_3796_ = v_currentTimeout_3781_;
v___y_3797_ = v___x_3803_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3804_, 0, v_response_3782_);
v___y_3791_ = v_keepAliveTimeout_3777_;
v___y_3792_ = v___y_3802_;
v___y_3793_ = v_headerTimeout_3778_;
v___y_3794_ = v_expectData_3779_;
v___y_3795_ = v_respStream_3780_;
v___y_3796_ = v_currentTimeout_3781_;
v___y_3797_ = v___x_3804_;
goto v___jp_3790_;
}
}
v___jp_3805_:
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_socket_3783_);
v___y_3802_ = v___x_3806_;
goto v___jp_3801_;
}
v___jp_3807_:
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_box(0);
v___y_3802_ = v___x_3808_;
goto v___jp_3801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3810_, lean_object* v_handlerDispatched_3811_, lean_object* v_keepAliveTimeout_3812_, lean_object* v_headerTimeout_3813_, lean_object* v_expectData_3814_, lean_object* v_respStream_3815_, lean_object* v_currentTimeout_3816_, lean_object* v_response_3817_, lean_object* v_socket_3818_, lean_object* v_requiresData_3819_, lean_object* v_sentMessage_3820_, lean_object* v_reader_3821_, lean_object* v_requestBodyInterested_3822_, lean_object* v_requestBody_3823_, lean_object* v___y_3824_){
_start:
{
uint8_t v_handlerDispatched_boxed_3825_; uint8_t v_requiresData_boxed_3826_; uint8_t v_sentMessage_boxed_3827_; uint8_t v_requestBodyInterested_boxed_3828_; lean_object* v_res_3829_; 
v_handlerDispatched_boxed_3825_ = lean_unbox(v_handlerDispatched_3811_);
v_requiresData_boxed_3826_ = lean_unbox(v_requiresData_3819_);
v_sentMessage_boxed_3827_ = lean_unbox(v_sentMessage_3820_);
v_requestBodyInterested_boxed_3828_ = lean_unbox(v_requestBodyInterested_3822_);
v_res_3829_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3810_, v_handlerDispatched_boxed_3825_, v_keepAliveTimeout_3812_, v_headerTimeout_3813_, v_expectData_3814_, v_respStream_3815_, v_currentTimeout_3816_, v_response_3817_, v_socket_3818_, v_requiresData_boxed_3826_, v_sentMessage_boxed_3827_, v_reader_3821_, v_requestBodyInterested_boxed_3828_, v_requestBody_3823_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3852_, uint8_t v_handlerDispatched_3853_, lean_object* v_keepAliveTimeout_3854_, lean_object* v_headerTimeout_3855_, lean_object* v_expectData_3856_, lean_object* v_respStream_3857_, lean_object* v_currentTimeout_3858_, lean_object* v_response_3859_, lean_object* v_socket_3860_, uint8_t v_requiresData_3861_, uint8_t v_sentMessage_3862_, lean_object* v_reader_3863_, uint8_t v_pullBodyStalled_3864_, uint8_t v_requestBodyOpen_3865_, lean_object* v_requestStream_3866_, uint8_t v_requestBodyInterested_3867_){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; uint8_t v___y_3876_; 
v___x_3869_ = lean_box(v_handlerDispatched_3853_);
v___x_3870_ = lean_box(v_requiresData_3861_);
v___x_3871_ = lean_box(v_sentMessage_3862_);
v___x_3872_ = lean_box(v_requestBodyInterested_3867_);
lean_inc_ref(v_reader_3863_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3873_, 0, v_connectionContext_3852_);
lean_closure_set(v___f_3873_, 1, v___x_3869_);
lean_closure_set(v___f_3873_, 2, v_keepAliveTimeout_3854_);
lean_closure_set(v___f_3873_, 3, v_headerTimeout_3855_);
lean_closure_set(v___f_3873_, 4, v_expectData_3856_);
lean_closure_set(v___f_3873_, 5, v_respStream_3857_);
lean_closure_set(v___f_3873_, 6, v_currentTimeout_3858_);
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
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
v___x_3889_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3886_, v_pullBodyStalled_3864_, v___x_3888_, v___f_3874_);
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
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3877_, v___y_3876_, v___x_3878_, v___f_3874_);
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3894_ = _args[0];
lean_object* v_handlerDispatched_3895_ = _args[1];
lean_object* v_keepAliveTimeout_3896_ = _args[2];
lean_object* v_headerTimeout_3897_ = _args[3];
lean_object* v_expectData_3898_ = _args[4];
lean_object* v_respStream_3899_ = _args[5];
lean_object* v_currentTimeout_3900_ = _args[6];
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
v_handlerDispatched_boxed_3911_ = lean_unbox(v_handlerDispatched_3895_);
v_requiresData_boxed_3912_ = lean_unbox(v_requiresData_3903_);
v_sentMessage_boxed_3913_ = lean_unbox(v_sentMessage_3904_);
v_pullBodyStalled_boxed_3914_ = lean_unbox(v_pullBodyStalled_3906_);
v_requestBodyOpen_boxed_3915_ = lean_unbox(v_requestBodyOpen_3907_);
v_requestBodyInterested_boxed_3916_ = lean_unbox(v_requestBodyInterested_3909_);
v_res_3917_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3894_, v_handlerDispatched_boxed_3911_, v_keepAliveTimeout_3896_, v_headerTimeout_3897_, v_expectData_3898_, v_respStream_3899_, v_currentTimeout_3900_, v_response_3901_, v_socket_3902_, v_requiresData_boxed_3912_, v_sentMessage_boxed_3913_, v_reader_3905_, v_pullBodyStalled_boxed_3914_, v_requestBodyOpen_boxed_3915_, v_requestStream_3908_, v_requestBodyInterested_boxed_3916_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3936_, uint8_t v_handlerDispatched_3937_, lean_object* v_keepAliveTimeout_3938_, lean_object* v_headerTimeout_3939_, lean_object* v_expectData_3940_, lean_object* v_respStream_3941_, lean_object* v_currentTimeout_3942_, lean_object* v_response_3943_, lean_object* v_socket_3944_, uint8_t v_requiresData_3945_, uint8_t v_sentMessage_3946_, lean_object* v_reader_3947_, uint8_t v_pullBodyStalled_3948_, lean_object* v_requestStream_3949_, uint8_t v_requestBodyOpen_3950_){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; lean_object* v___f_3958_; uint8_t v___y_3960_; 
v___x_3952_ = lean_box(v_handlerDispatched_3937_);
v___x_3953_ = lean_box(v_requiresData_3945_);
v___x_3954_ = lean_box(v_sentMessage_3946_);
v___x_3955_ = lean_box(v_pullBodyStalled_3948_);
v___x_3956_ = lean_box(v_requestBodyOpen_3950_);
lean_inc_ref(v_requestStream_3949_);
lean_inc_ref(v_reader_3947_);
v___f_3957_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3957_, 0, v_connectionContext_3936_);
lean_closure_set(v___f_3957_, 1, v___x_3952_);
lean_closure_set(v___f_3957_, 2, v_keepAliveTimeout_3938_);
lean_closure_set(v___f_3957_, 3, v_headerTimeout_3939_);
lean_closure_set(v___f_3957_, 4, v_expectData_3940_);
lean_closure_set(v___f_3957_, 5, v_respStream_3941_);
lean_closure_set(v___f_3957_, 6, v_currentTimeout_3942_);
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
v___x_3967_ = lean_unsigned_to_nat(0u);
v___x_3968_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3949_);
v___x_3969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3967_, v_sentMessage_3946_, v___x_3968_, v___f_3958_);
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
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = lean_box(v___y_3960_);
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v___x_3965_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3961_, v___y_3960_, v___x_3964_, v___f_3958_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3971_, lean_object* v_handlerDispatched_3972_, lean_object* v_keepAliveTimeout_3973_, lean_object* v_headerTimeout_3974_, lean_object* v_expectData_3975_, lean_object* v_respStream_3976_, lean_object* v_currentTimeout_3977_, lean_object* v_response_3978_, lean_object* v_socket_3979_, lean_object* v_requiresData_3980_, lean_object* v_sentMessage_3981_, lean_object* v_reader_3982_, lean_object* v_pullBodyStalled_3983_, lean_object* v_requestStream_3984_, lean_object* v_requestBodyOpen_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v_handlerDispatched_boxed_3987_; uint8_t v_requiresData_boxed_3988_; uint8_t v_sentMessage_boxed_3989_; uint8_t v_pullBodyStalled_boxed_3990_; uint8_t v_requestBodyOpen_boxed_3991_; lean_object* v_res_3992_; 
v_handlerDispatched_boxed_3987_ = lean_unbox(v_handlerDispatched_3972_);
v_requiresData_boxed_3988_ = lean_unbox(v_requiresData_3980_);
v_sentMessage_boxed_3989_ = lean_unbox(v_sentMessage_3981_);
v_pullBodyStalled_boxed_3990_ = lean_unbox(v_pullBodyStalled_3983_);
v_requestBodyOpen_boxed_3991_ = lean_unbox(v_requestBodyOpen_3985_);
v_res_3992_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3971_, v_handlerDispatched_boxed_3987_, v_keepAliveTimeout_3973_, v_headerTimeout_3974_, v_expectData_3975_, v_respStream_3976_, v_currentTimeout_3977_, v_response_3978_, v_socket_3979_, v_requiresData_boxed_3988_, v_sentMessage_boxed_3989_, v_reader_3982_, v_pullBodyStalled_boxed_3990_, v_requestStream_3984_, v_requestBodyOpen_boxed_3991_);
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
v___x_4000_ = lean_unsigned_to_nat(0u);
v___x_4001_ = lean_box(v___y_3999_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
v___x_4004_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4000_, v_sentMessage_3993_, v___x_4003_, v___f_3994_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4016_, lean_object* v___f_4017_, lean_object* v___x_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_){
_start:
{
uint8_t v_sentMessage_boxed_4021_; uint8_t v___x_2892__boxed_4022_; lean_object* v_res_4023_; 
v_sentMessage_boxed_4021_ = lean_unbox(v_sentMessage_4016_);
v___x_2892__boxed_4022_ = lean_unbox(v___x_4018_);
v_res_4023_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4021_, v___f_4017_, v___x_2892__boxed_4022_, v_x_4019_);
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
lean_closure_set(v___f_4050_, 0, v_connectionContext_4029_);
lean_closure_set(v___f_4050_, 1, v___x_4046_);
lean_closure_set(v___f_4050_, 2, v_keepAliveTimeout_4035_);
lean_closure_set(v___f_4050_, 3, v_headerTimeout_4037_);
lean_closure_set(v___f_4050_, 4, v_expectData_4041_);
lean_closure_set(v___f_4050_, 5, v_respStream_4039_);
lean_closure_set(v___f_4050_, 6, v_currentTimeout_4036_);
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
uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___f_4066_; lean_object* v___f_4067_; lean_object* v___x_4068_; lean_object* v___x_2542__overap_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec_ref_known(v_state_4059_, 1);
v___x_4060_ = 1;
v___x_4061_ = lean_box(v_sentMessage_4045_);
v___x_4062_ = lean_box(v___x_4060_);
v___f_4063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4063_, 0, v___x_4061_);
lean_closure_set(v___f_4063_, 1, v___f_4051_);
lean_closure_set(v___f_4063_, 2, v___x_4062_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4066_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4067_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4068_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2542__overap_4069_ = l_Std_Mutex_atomically___redArg(v___x_4065_, v___f_4066_, v___f_4067_, v_requestStream_4034_, v___x_4068_);
v___x_4070_ = lean_apply_1(v___x_2542__overap_4069_, lean_box(0));
v___x_4071_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4064_, v_sentMessage_4045_, v___x_4070_, v___f_4063_);
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
v___x_4054_ = lean_unsigned_to_nat(0u);
v___x_4055_ = lean_box(v___y_4053_);
v___x_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
v___x_4058_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4054_, v___y_4053_, v___x_4057_, v___f_4051_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4094_){
_start:
{
if (lean_obj_tag(v_x_4094_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4104_; 
v_a_4096_ = lean_ctor_get(v_x_4094_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_x_4094_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4098_ = v_x_4094_;
v_isShared_4099_ = v_isSharedCheck_4104_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v_x_4094_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4104_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4114_; 
v_a_4105_ = lean_ctor_get(v_x_4094_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_x_4094_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4107_ = v_x_4094_;
v_isShared_4108_ = v_isSharedCheck_4114_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v_x_4094_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4114_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_a_4105_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v___x_4109_);
v___x_4111_ = v___x_4107_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
return v___x_4112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4115_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4122_){
_start:
{
if (lean_obj_tag(v_x_4122_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4132_; 
v_a_4124_ = lean_ctor_get(v_x_4122_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_x_4122_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4126_ = v_x_4122_;
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v_x_4122_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec_ref_known(v_x_4122_, 1);
v___x_4133_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_4137_, lean_object* v_handler_4138_, lean_object* v___f_4139_, lean_object* v_x_4140_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_a_4142_ = lean_ctor_get(v_x_4140_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v_x_4140_, 1);
v___x_4143_ = lean_unsigned_to_nat(0u);
v___x_4144_ = 0;
v___x_4145_ = lean_apply_3(v_onFailure_4137_, v_handler_4138_, v_a_4142_, lean_box(0));
v___x_4146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4143_, v___x_4144_, v___x_4145_, v___f_4139_);
return v___x_4146_;
}
else
{
lean_object* v___x_4147_; 
lean_dec_ref(v___f_4139_);
lean_dec(v_handler_4138_);
lean_dec_ref(v_onFailure_4137_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_x_4140_);
return v___x_4147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_4148_, lean_object* v_handler_4149_, lean_object* v___f_4150_, lean_object* v_x_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_4148_, v_handler_4149_, v___f_4150_, v_x_4151_);
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
v___x_4244_ = lean_unsigned_to_nat(0u);
v___x_4245_ = lean_apply_2(v_close_4227_, v_val_4228_, lean_box(0));
v___x_4246_ = lean_unbox(v_a_4242_);
lean_dec(v_a_4242_);
v___x_4247_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4244_, v___x_4246_, v___x_4245_, v___f_4229_);
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
lean_object* v_val_4263_; lean_object* v_close_4264_; lean_object* v_isClosed_4265_; lean_object* v___f_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v_val_4263_ = lean_ctor_get(v_respStream_4257_, 0);
lean_inc_n(v_val_4263_, 2);
lean_dec_ref_known(v_respStream_4257_, 1);
v_close_4264_ = lean_ctor_get(v_responseBodyInstance_4258_, 1);
lean_inc_ref(v_close_4264_);
v_isClosed_4265_ = lean_ctor_get(v_responseBodyInstance_4258_, 2);
lean_inc_ref(v_isClosed_4265_);
lean_dec_ref(v_responseBodyInstance_4258_);
v___f_4266_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4266_, 0, v_close_4264_);
lean_closure_set(v___f_4266_, 1, v_val_4263_);
lean_closure_set(v___f_4266_, 2, v___f_4259_);
lean_closure_set(v___f_4266_, 3, v___f_4260_);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = 0;
v___x_4269_ = lean_apply_2(v_isClosed_4265_, v_val_4263_, lean_box(0));
v___x_4270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4267_, v___x_4268_, v___x_4269_, v___f_4266_);
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
v___x_4296_ = lean_unsigned_to_nat(0u);
v___x_4297_ = l_Std_Http_Body_Stream_close(v_requestStream_4280_);
v___x_4298_ = lean_unbox(v_a_4294_);
lean_dec(v_a_4294_);
v___x_4299_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4296_, v___x_4298_, v___x_4297_, v___f_4281_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4308_, lean_object* v___f_4309_, lean_object* v___f_4310_, lean_object* v___f_4311_, lean_object* v_x_4312_){
_start:
{
if (lean_obj_tag(v_x_4312_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4322_; 
lean_dec_ref(v___f_4311_);
lean_dec_ref(v___f_4310_);
lean_dec_ref(v___f_4309_);
lean_dec_ref(v_responseBodyInstance_4308_);
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
lean_object* v_a_4323_; lean_object* v_requestStream_4324_; lean_object* v_respStream_4325_; lean_object* v___f_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___f_4332_; lean_object* v___f_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4542__overap_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_a_4323_ = lean_ctor_get(v_x_4312_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v_x_4312_, 1);
v_requestStream_4324_ = lean_ctor_get(v_a_4323_, 1);
lean_inc_ref_n(v_requestStream_4324_, 2);
v_respStream_4325_ = lean_ctor_get(v_a_4323_, 6);
lean_inc(v_respStream_4325_);
lean_dec(v_a_4323_);
v___f_4326_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4326_, 0, v_respStream_4325_);
lean_closure_set(v___f_4326_, 1, v_responseBodyInstance_4308_);
lean_closure_set(v___f_4326_, 2, v___f_4309_);
lean_closure_set(v___f_4326_, 3, v___f_4310_);
lean_inc_ref(v___f_4326_);
v___f_4327_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4327_, 0, v___f_4326_);
v___f_4328_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4328_, 0, v_requestStream_4324_);
lean_closure_set(v___f_4328_, 1, v___f_4327_);
lean_closure_set(v___f_4328_, 2, v___f_4326_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = 0;
v___x_4331_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4332_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4333_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4334_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4335_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4335_, 0, lean_box(0));
lean_closure_set(v___x_4335_, 1, lean_box(0));
lean_closure_set(v___x_4335_, 2, v___x_4331_);
lean_closure_set(v___x_4335_, 3, lean_box(0));
lean_closure_set(v___x_4335_, 4, lean_box(0));
lean_closure_set(v___x_4335_, 5, v___x_4334_);
lean_closure_set(v___x_4335_, 6, v___f_4311_);
v___x_4542__overap_4336_ = l_Std_Mutex_atomically___redArg(v___x_4331_, v___f_4332_, v___f_4333_, v_requestStream_4324_, v___x_4335_);
v___x_4337_ = lean_apply_1(v___x_4542__overap_4336_, lean_box(0));
v___x_4338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4329_, v___x_4330_, v___x_4337_, v___f_4328_);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4339_, lean_object* v___f_4340_, lean_object* v___f_4341_, lean_object* v___f_4342_, lean_object* v_x_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4339_, v___f_4340_, v___f_4341_, v___f_4342_, v_x_4343_);
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
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4346_, v_responseBodyInstance_4347_, v_handler_4348_, v_config_4349_, v_a_4364_, v___x_4350_);
v___x_4367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4365_, v___x_4351_, v___x_4366_, v___f_4352_);
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4368_, lean_object* v_responseBodyInstance_4369_, lean_object* v_handler_4370_, lean_object* v_config_4371_, lean_object* v___x_4372_, lean_object* v___x_4373_, lean_object* v___f_4374_, lean_object* v_x_4375_, lean_object* v___y_4376_){
_start:
{
uint8_t v___x_5208__boxed_4377_; lean_object* v_res_4378_; 
v___x_5208__boxed_4377_ = lean_unbox(v___x_4373_);
v_res_4378_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4368_, v_responseBodyInstance_4369_, v_handler_4370_, v_config_4371_, v___x_4372_, v___x_5208__boxed_4377_, v___f_4374_, v_x_4375_);
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
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4379_, v_h_4380_, v_responseBodyInstance_4381_, v_config_4382_, v_handler_4383_, v_a_4397_);
v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4398_, v___x_4384_, v___x_4399_, v___f_4385_);
return v___x_4400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4401_, lean_object* v_h_4402_, lean_object* v_responseBodyInstance_4403_, lean_object* v_config_4404_, lean_object* v_handler_4405_, lean_object* v___x_4406_, lean_object* v___f_4407_, lean_object* v_x_4408_, lean_object* v___y_4409_){
_start:
{
uint8_t v___x_5249__boxed_4410_; lean_object* v_res_4411_; 
v___x_5249__boxed_4410_ = lean_unbox(v___x_4406_);
v_res_4411_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4401_, v_h_4402_, v_responseBodyInstance_4403_, v_config_4404_, v_handler_4405_, v___x_5249__boxed_4410_, v___f_4407_, v_x_4408_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4412_, lean_object* v_h_4413_, lean_object* v_responseBodyInstance_4414_, lean_object* v_handler_4415_, lean_object* v_config_4416_, lean_object* v___f_4417_, lean_object* v_inst_4418_, lean_object* v_socket_4419_, lean_object* v_connectionContext_4420_, lean_object* v_x_4421_){
_start:
{
if (lean_obj_tag(v_x_4421_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4431_; 
lean_dec_ref(v_connectionContext_4420_);
lean_dec(v_socket_4419_);
lean_dec_ref(v_inst_4418_);
lean_dec_ref(v___f_4417_);
lean_dec_ref(v_config_4416_);
lean_dec(v_handler_4415_);
lean_dec_ref(v_responseBodyInstance_4414_);
lean_dec_ref(v_h_4413_);
v_a_4423_ = lean_ctor_get(v_x_4421_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_x_4421_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4425_ = v_x_4421_;
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v_x_4421_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4466_; 
v_a_4432_ = lean_ctor_get(v_x_4421_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_x_4421_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4434_ = v_x_4421_;
v_isShared_4435_ = v_isSharedCheck_4466_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v_x_4421_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4466_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v_machine_4442_; lean_object* v_requestStream_4443_; lean_object* v_keepAliveTimeout_4444_; lean_object* v_currentTimeout_4445_; lean_object* v_headerTimeout_4446_; lean_object* v_response_4447_; lean_object* v_respStream_4448_; uint8_t v_requiresData_4449_; lean_object* v_expectData_4450_; uint8_t v_handlerDispatched_4451_; lean_object* v_pendingHead_4452_; 
v_machine_4442_ = lean_ctor_get(v_a_4432_, 0);
v_requestStream_4443_ = lean_ctor_get(v_a_4432_, 1);
v_keepAliveTimeout_4444_ = lean_ctor_get(v_a_4432_, 2);
v_currentTimeout_4445_ = lean_ctor_get(v_a_4432_, 3);
v_headerTimeout_4446_ = lean_ctor_get(v_a_4432_, 4);
v_response_4447_ = lean_ctor_get(v_a_4432_, 5);
v_respStream_4448_ = lean_ctor_get(v_a_4432_, 6);
v_requiresData_4449_ = lean_ctor_get_uint8(v_a_4432_, sizeof(void*)*9);
v_expectData_4450_ = lean_ctor_get(v_a_4432_, 7);
v_handlerDispatched_4451_ = lean_ctor_get_uint8(v_a_4432_, sizeof(void*)*9 + 1);
v_pendingHead_4452_ = lean_ctor_get(v_a_4432_, 8);
if (v_requiresData_4449_ == 0)
{
if (v_handlerDispatched_4451_ == 0)
{
if (lean_obj_tag(v_respStream_4448_) == 0)
{
lean_object* v_writer_4462_; uint8_t v_sentMessage_4463_; 
v_writer_4462_ = lean_ctor_get(v_machine_4442_, 1);
v_sentMessage_4463_ = lean_ctor_get_uint8(v_writer_4462_, sizeof(void*)*6);
if (v_sentMessage_4463_ == 0)
{
lean_object* v_reader_4464_; lean_object* v_state_4465_; 
v_reader_4464_ = lean_ctor_get(v_machine_4442_, 0);
v_state_4465_ = lean_ctor_get(v_reader_4464_, 0);
if (lean_obj_tag(v_state_4465_) == 2)
{
lean_inc(v_respStream_4448_);
lean_inc(v_pendingHead_4452_);
lean_inc(v_expectData_4450_);
lean_inc_ref(v_response_4447_);
lean_inc(v_headerTimeout_4446_);
lean_inc(v_currentTimeout_4445_);
lean_inc(v_keepAliveTimeout_4444_);
lean_inc_ref(v_requestStream_4443_);
lean_inc_ref(v_machine_4442_);
lean_del_object(v___x_4434_);
lean_dec(v_a_4432_);
goto v___jp_4453_;
}
else
{
lean_dec_ref(v_connectionContext_4420_);
lean_dec(v_socket_4419_);
lean_dec_ref(v_inst_4418_);
lean_dec_ref(v___f_4417_);
lean_dec_ref(v_config_4416_);
lean_dec(v_handler_4415_);
lean_dec_ref(v_responseBodyInstance_4414_);
lean_dec_ref(v_h_4413_);
goto v___jp_4436_;
}
}
else
{
lean_dec_ref(v_connectionContext_4420_);
lean_dec(v_socket_4419_);
lean_dec_ref(v_inst_4418_);
lean_dec_ref(v___f_4417_);
lean_dec_ref(v_config_4416_);
lean_dec(v_handler_4415_);
lean_dec_ref(v_responseBodyInstance_4414_);
lean_dec_ref(v_h_4413_);
goto v___jp_4436_;
}
}
else
{
lean_inc_ref(v_respStream_4448_);
lean_inc(v_pendingHead_4452_);
lean_inc(v_expectData_4450_);
lean_inc_ref(v_response_4447_);
lean_inc(v_headerTimeout_4446_);
lean_inc(v_currentTimeout_4445_);
lean_inc(v_keepAliveTimeout_4444_);
lean_inc_ref(v_requestStream_4443_);
lean_inc_ref(v_machine_4442_);
lean_del_object(v___x_4434_);
lean_dec(v_a_4432_);
goto v___jp_4453_;
}
}
else
{
lean_inc(v_pendingHead_4452_);
lean_inc(v_expectData_4450_);
lean_inc(v_respStream_4448_);
lean_inc_ref(v_response_4447_);
lean_inc(v_headerTimeout_4446_);
lean_inc(v_currentTimeout_4445_);
lean_inc(v_keepAliveTimeout_4444_);
lean_inc_ref(v_requestStream_4443_);
lean_inc_ref(v_machine_4442_);
lean_del_object(v___x_4434_);
lean_dec(v_a_4432_);
goto v___jp_4453_;
}
}
else
{
lean_inc(v_pendingHead_4452_);
lean_inc(v_expectData_4450_);
lean_inc(v_respStream_4448_);
lean_inc_ref(v_response_4447_);
lean_inc(v_headerTimeout_4446_);
lean_inc(v_currentTimeout_4445_);
lean_inc(v_keepAliveTimeout_4444_);
lean_inc_ref(v_requestStream_4443_);
lean_inc_ref(v_machine_4442_);
lean_del_object(v___x_4434_);
lean_dec(v_a_4432_);
goto v___jp_4453_;
}
v___jp_4436_:
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4437_, 0, v_a_4432_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4437_);
v___x_4439_ = v___x_4434_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
return v___x_4440_;
}
}
v___jp_4453_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; lean_object* v___f_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4454_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4454_, 0, v_machine_4442_);
lean_ctor_set(v___x_4454_, 1, v_requestStream_4443_);
lean_ctor_set(v___x_4454_, 2, v_keepAliveTimeout_4444_);
lean_ctor_set(v___x_4454_, 3, v_currentTimeout_4445_);
lean_ctor_set(v___x_4454_, 4, v_headerTimeout_4446_);
lean_ctor_set(v___x_4454_, 5, v_response_4447_);
lean_ctor_set(v___x_4454_, 6, v_respStream_4448_);
lean_ctor_set(v___x_4454_, 7, v_expectData_4450_);
lean_ctor_set(v___x_4454_, 8, v_pendingHead_4452_);
lean_ctor_set_uint8(v___x_4454_, sizeof(void*)*9, v___x_4412_);
lean_ctor_set_uint8(v___x_4454_, sizeof(void*)*9 + 1, v_handlerDispatched_4451_);
v___x_4455_ = lean_box(v___x_4412_);
lean_inc_ref(v___x_4454_);
lean_inc_ref(v_config_4416_);
lean_inc(v_handler_4415_);
lean_inc_ref(v_responseBodyInstance_4414_);
lean_inc_ref(v_h_4413_);
v___f_4456_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4456_, 0, v_h_4413_);
lean_closure_set(v___f_4456_, 1, v_responseBodyInstance_4414_);
lean_closure_set(v___f_4456_, 2, v_handler_4415_);
lean_closure_set(v___f_4456_, 3, v_config_4416_);
lean_closure_set(v___f_4456_, 4, v___x_4454_);
lean_closure_set(v___f_4456_, 5, v___x_4455_);
lean_closure_set(v___f_4456_, 6, v___f_4417_);
v___x_4457_ = lean_box(v___x_4412_);
v___f_4458_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4458_, 0, v_inst_4418_);
lean_closure_set(v___f_4458_, 1, v_h_4413_);
lean_closure_set(v___f_4458_, 2, v_responseBodyInstance_4414_);
lean_closure_set(v___f_4458_, 3, v_config_4416_);
lean_closure_set(v___f_4458_, 4, v_handler_4415_);
lean_closure_set(v___f_4458_, 5, v___x_4457_);
lean_closure_set(v___f_4458_, 6, v___f_4456_);
v___x_4459_ = lean_unsigned_to_nat(0u);
v___x_4460_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4419_, v_connectionContext_4420_, v___x_4454_);
v___x_4461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4459_, v___x_4412_, v___x_4460_, v___f_4458_);
return v___x_4461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4467_, lean_object* v_h_4468_, lean_object* v_responseBodyInstance_4469_, lean_object* v_handler_4470_, lean_object* v_config_4471_, lean_object* v___f_4472_, lean_object* v_inst_4473_, lean_object* v_socket_4474_, lean_object* v_connectionContext_4475_, lean_object* v_x_4476_, lean_object* v___y_4477_){
_start:
{
uint8_t v___x_5289__boxed_4478_; lean_object* v_res_4479_; 
v___x_5289__boxed_4478_ = lean_unbox(v___x_4467_);
v_res_4479_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5289__boxed_4478_, v_h_4468_, v_responseBodyInstance_4469_, v_handler_4470_, v_config_4471_, v___f_4472_, v_inst_4473_, v_socket_4474_, v_connectionContext_4475_, v_x_4476_);
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
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4480_, v_handler_4481_, v_extensions_4482_, v_connectionContext_4483_, v_a_4497_);
v___x_4500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4498_, v___x_4484_, v___x_4499_, v___f_4485_);
return v___x_4500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4501_, lean_object* v_handler_4502_, lean_object* v_extensions_4503_, lean_object* v_connectionContext_4504_, lean_object* v___x_4505_, lean_object* v___f_4506_, lean_object* v_x_4507_, lean_object* v___y_4508_){
_start:
{
uint8_t v___x_5364__boxed_4509_; lean_object* v_res_4510_; 
v___x_5364__boxed_4509_ = lean_unbox(v___x_4505_);
v_res_4510_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4501_, v_handler_4502_, v_extensions_4503_, v_connectionContext_4504_, v___x_5364__boxed_4509_, v___f_4506_, v_x_4507_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4511_, lean_object* v_responseBodyInstance_4512_, lean_object* v_handler_4513_, lean_object* v_config_4514_, lean_object* v_connectionContext_4515_, lean_object* v_events_4516_, lean_object* v___x_4517_, uint8_t v___x_4518_, lean_object* v___f_4519_, lean_object* v_____r_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4511_, v_responseBodyInstance_4512_, v_handler_4513_, v_config_4514_, v_connectionContext_4515_, v_events_4516_, v___x_4517_);
v___x_4524_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4522_, v___x_4518_, v___x_4523_, v___f_4519_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4525_, lean_object* v_responseBodyInstance_4526_, lean_object* v_handler_4527_, lean_object* v_config_4528_, lean_object* v_connectionContext_4529_, lean_object* v_events_4530_, lean_object* v___x_4531_, lean_object* v___x_4532_, lean_object* v___f_4533_, lean_object* v_____r_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___x_5403__boxed_4536_; lean_object* v_res_4537_; 
v___x_5403__boxed_4536_ = lean_unbox(v___x_4532_);
v_res_4537_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4525_, v_responseBodyInstance_4526_, v_handler_4527_, v_config_4528_, v_connectionContext_4529_, v_events_4530_, v___x_4531_, v___x_5403__boxed_4536_, v___f_4533_, v_____r_4534_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4568_, lean_object* v_responseBodyInstance_4569_, lean_object* v_handler_4570_, lean_object* v_config_4571_, lean_object* v_connectionContext_4572_, uint8_t v___x_4573_, lean_object* v___f_4574_, lean_object* v_inst_4575_, lean_object* v_socket_4576_, lean_object* v___f_4577_, lean_object* v___f_4578_, lean_object* v_x_4579_, lean_object* v_____s_4580_){
_start:
{
lean_object* v_machine_4582_; lean_object* v_reader_4583_; lean_object* v_requestStream_4584_; lean_object* v_keepAliveTimeout_4585_; lean_object* v_currentTimeout_4586_; lean_object* v_headerTimeout_4587_; lean_object* v_response_4588_; lean_object* v_respStream_4589_; uint8_t v_requiresData_4590_; lean_object* v_expectData_4591_; uint8_t v_handlerDispatched_4592_; lean_object* v_pendingHead_4593_; lean_object* v_writer_4594_; lean_object* v_state_4595_; uint8_t v___x_4596_; 
v_machine_4582_ = lean_ctor_get(v_____s_4580_, 0);
v_reader_4583_ = lean_ctor_get(v_machine_4582_, 0);
v_requestStream_4584_ = lean_ctor_get(v_____s_4580_, 1);
v_keepAliveTimeout_4585_ = lean_ctor_get(v_____s_4580_, 2);
v_currentTimeout_4586_ = lean_ctor_get(v_____s_4580_, 3);
v_headerTimeout_4587_ = lean_ctor_get(v_____s_4580_, 4);
v_response_4588_ = lean_ctor_get(v_____s_4580_, 5);
v_respStream_4589_ = lean_ctor_get(v_____s_4580_, 6);
v_requiresData_4590_ = lean_ctor_get_uint8(v_____s_4580_, sizeof(void*)*9);
v_expectData_4591_ = lean_ctor_get(v_____s_4580_, 7);
v_handlerDispatched_4592_ = lean_ctor_get_uint8(v_____s_4580_, sizeof(void*)*9 + 1);
v_pendingHead_4593_ = lean_ctor_get(v_____s_4580_, 8);
v_writer_4594_ = lean_ctor_get(v_machine_4582_, 1);
v_state_4595_ = lean_ctor_get(v_reader_4583_, 0);
v___x_4596_ = 0;
if (lean_obj_tag(v_state_4595_) == 6)
{
lean_object* v_state_4618_; 
v_state_4618_ = lean_ctor_get(v_writer_4594_, 2);
if (lean_obj_tag(v_state_4618_) == 7)
{
lean_object* v_outputData_4619_; lean_object* v_size_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; 
v_outputData_4619_ = lean_ctor_get(v_writer_4594_, 1);
v_size_4620_ = lean_ctor_get(v_outputData_4619_, 1);
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = lean_nat_dec_eq(v_size_4620_, v___x_4621_);
if (v___x_4622_ == 0)
{
lean_inc(v_pendingHead_4593_);
lean_inc(v_expectData_4591_);
lean_inc(v_respStream_4589_);
lean_inc_ref(v_response_4588_);
lean_inc(v_headerTimeout_4587_);
lean_inc(v_currentTimeout_4586_);
lean_inc(v_keepAliveTimeout_4585_);
lean_inc_ref(v_requestStream_4584_);
lean_inc_ref(v_machine_4582_);
lean_dec_ref(v_____s_4580_);
goto v___jp_4597_;
}
else
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
lean_dec_ref(v___f_4578_);
lean_dec_ref(v___f_4577_);
lean_dec(v_socket_4576_);
lean_dec_ref(v_inst_4575_);
lean_dec_ref(v___f_4574_);
lean_dec_ref(v_connectionContext_4572_);
lean_dec_ref(v_config_4571_);
lean_dec(v_handler_4570_);
lean_dec_ref(v_responseBodyInstance_4569_);
lean_dec_ref(v_h_4568_);
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v_____s_4580_);
v___x_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
return v___x_4625_;
}
}
else
{
lean_inc(v_pendingHead_4593_);
lean_inc(v_expectData_4591_);
lean_inc(v_respStream_4589_);
lean_inc_ref(v_response_4588_);
lean_inc(v_headerTimeout_4587_);
lean_inc(v_currentTimeout_4586_);
lean_inc(v_keepAliveTimeout_4585_);
lean_inc_ref(v_requestStream_4584_);
lean_inc_ref(v_machine_4582_);
lean_dec_ref(v_____s_4580_);
goto v___jp_4597_;
}
}
else
{
lean_inc(v_pendingHead_4593_);
lean_inc(v_expectData_4591_);
lean_inc(v_respStream_4589_);
lean_inc_ref(v_response_4588_);
lean_inc(v_headerTimeout_4587_);
lean_inc(v_currentTimeout_4586_);
lean_inc(v_keepAliveTimeout_4585_);
lean_inc_ref(v_requestStream_4584_);
lean_inc_ref(v_machine_4582_);
lean_dec_ref(v_____s_4580_);
goto v___jp_4597_;
}
v___jp_4597_:
{
lean_object* v___x_4598_; lean_object* v_snd_4599_; lean_object* v_output_4600_; lean_object* v_fst_4601_; lean_object* v_events_4602_; lean_object* v_data_4603_; lean_object* v_size_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___f_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4598_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4596_, v_machine_4582_);
v_snd_4599_ = lean_ctor_get(v___x_4598_, 1);
lean_inc(v_snd_4599_);
v_output_4600_ = lean_ctor_get(v_snd_4599_, 1);
lean_inc_ref(v_output_4600_);
v_fst_4601_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_fst_4601_);
lean_dec_ref(v___x_4598_);
v_events_4602_ = lean_ctor_get(v_snd_4599_, 0);
lean_inc_ref_n(v_events_4602_, 2);
lean_dec(v_snd_4599_);
v_data_4603_ = lean_ctor_get(v_output_4600_, 0);
lean_inc_ref(v_data_4603_);
v_size_4604_ = lean_ctor_get(v_output_4600_, 1);
lean_inc(v_size_4604_);
lean_dec_ref(v_output_4600_);
v___x_4605_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4605_, 0, v_fst_4601_);
lean_ctor_set(v___x_4605_, 1, v_requestStream_4584_);
lean_ctor_set(v___x_4605_, 2, v_keepAliveTimeout_4585_);
lean_ctor_set(v___x_4605_, 3, v_currentTimeout_4586_);
lean_ctor_set(v___x_4605_, 4, v_headerTimeout_4587_);
lean_ctor_set(v___x_4605_, 5, v_response_4588_);
lean_ctor_set(v___x_4605_, 6, v_respStream_4589_);
lean_ctor_set(v___x_4605_, 7, v_expectData_4591_);
lean_ctor_set(v___x_4605_, 8, v_pendingHead_4593_);
lean_ctor_set_uint8(v___x_4605_, sizeof(void*)*9, v_requiresData_4590_);
lean_ctor_set_uint8(v___x_4605_, sizeof(void*)*9 + 1, v_handlerDispatched_4592_);
v___x_4606_ = lean_box(v___x_4573_);
lean_inc_ref(v___f_4574_);
lean_inc_ref(v___x_4605_);
lean_inc_ref(v_connectionContext_4572_);
lean_inc_ref(v_config_4571_);
lean_inc(v_handler_4570_);
lean_inc_ref(v_responseBodyInstance_4569_);
lean_inc_ref(v_h_4568_);
v___f_4607_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4607_, 0, v_h_4568_);
lean_closure_set(v___f_4607_, 1, v_responseBodyInstance_4569_);
lean_closure_set(v___f_4607_, 2, v_handler_4570_);
lean_closure_set(v___f_4607_, 3, v_config_4571_);
lean_closure_set(v___f_4607_, 4, v_connectionContext_4572_);
lean_closure_set(v___f_4607_, 5, v_events_4602_);
lean_closure_set(v___f_4607_, 6, v___x_4605_);
lean_closure_set(v___f_4607_, 7, v___x_4606_);
lean_closure_set(v___f_4607_, 8, v___f_4574_);
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = lean_nat_dec_lt(v___x_4608_, v_size_4604_);
lean_dec(v_size_4604_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
lean_dec_ref(v___f_4607_);
lean_dec_ref(v_data_4603_);
lean_dec_ref(v___f_4578_);
lean_dec_ref(v___f_4577_);
lean_dec(v_socket_4576_);
lean_dec_ref(v_inst_4575_);
v___x_4610_ = lean_box(0);
v___x_4611_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4568_, v_responseBodyInstance_4569_, v_handler_4570_, v_config_4571_, v_connectionContext_4572_, v_events_4602_, v___x_4605_, v___x_4573_, v___f_4574_, v___x_4610_);
return v___x_4611_;
}
else
{
lean_object* v_sendAll_4612_; lean_object* v___f_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
lean_dec_ref(v_events_4602_);
lean_dec_ref(v___f_4574_);
lean_dec_ref(v_connectionContext_4572_);
lean_dec_ref(v_config_4571_);
lean_dec(v_handler_4570_);
lean_dec_ref(v_responseBodyInstance_4569_);
lean_dec_ref(v_h_4568_);
v_sendAll_4612_ = lean_ctor_get(v_inst_4575_, 1);
lean_inc_ref(v_sendAll_4612_);
lean_dec_ref(v_inst_4575_);
v___f_4613_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4613_, 0, v___x_4605_);
lean_closure_set(v___f_4613_, 1, v___f_4607_);
v___x_4614_ = lean_apply_3(v_sendAll_4612_, v_socket_4576_, v_data_4603_, lean_box(0));
v___x_4615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4608_, v___x_4573_, v___x_4614_, v___f_4577_);
v___x_4616_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4608_, v___x_4573_, v___x_4615_, v___f_4578_);
v___x_4617_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4608_, v___x_4573_, v___x_4616_, v___f_4613_);
return v___x_4617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4626_, lean_object* v_responseBodyInstance_4627_, lean_object* v_handler_4628_, lean_object* v_config_4629_, lean_object* v_connectionContext_4630_, lean_object* v___x_4631_, lean_object* v___f_4632_, lean_object* v_inst_4633_, lean_object* v_socket_4634_, lean_object* v___f_4635_, lean_object* v___f_4636_, lean_object* v_x_4637_, lean_object* v_____s_4638_, lean_object* v___y_4639_){
_start:
{
uint8_t v___x_5477__boxed_4640_; lean_object* v_res_4641_; 
v___x_5477__boxed_4640_ = lean_unbox(v___x_4631_);
v_res_4641_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4626_, v_responseBodyInstance_4627_, v_handler_4628_, v_config_4629_, v_connectionContext_4630_, v___x_5477__boxed_4640_, v___f_4632_, v_inst_4633_, v_socket_4634_, v___f_4635_, v___f_4636_, v_x_4637_, v_____s_4638_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4642_, lean_object* v_x_4643_){
_start:
{
if (lean_obj_tag(v_x_4643_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4653_; 
v_a_4645_ = lean_ctor_get(v_x_4643_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_x_4643_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4647_ = v_x_4643_;
v_isShared_4648_ = v_isSharedCheck_4653_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v_x_4643_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4653_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
lean_object* v___x_4651_; 
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
return v___x_4651_;
}
}
}
else
{
lean_object* v___x_4654_; lean_object* v___x_4655_; 
lean_dec_ref_known(v_x_4643_, 1);
v___x_4654_ = l_IO_Promise_result_x21___redArg(v_a_4642_);
v___x_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
return v___x_4655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4656_, lean_object* v_x_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4656_, v_x_4657_);
lean_dec(v_a_4656_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4660_, lean_object* v___x_4661_, lean_object* v___x_4662_, uint8_t v___x_4663_, lean_object* v_x_4664_){
_start:
{
if (lean_obj_tag(v_x_4664_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4674_; 
lean_dec_ref(v___x_4662_);
lean_dec(v___x_4661_);
lean_dec_ref(v___f_4660_);
v_a_4666_ = lean_ctor_get(v_x_4664_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v_x_4664_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4668_ = v_x_4664_;
v_isShared_4669_ = v_isSharedCheck_4674_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v_x_4664_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4674_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4672_; 
v___x_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
return v___x_4672_;
}
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4686_; 
v_a_4675_ = lean_ctor_get(v_x_4664_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_x_4664_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4677_ = v_x_4664_;
v_isShared_4678_ = v_isSharedCheck_4686_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v_x_4664_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4686_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___f_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
lean_inc(v_a_4675_);
v___f_4679_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4679_, 0, v_a_4675_);
lean_inc(v___x_4661_);
v___x_4680_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4660_, v___x_4661_, v_a_4675_, v___x_4662_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 0, v___x_4680_);
v___x_4682_ = v___x_4677_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
v___x_4684_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4661_, v___x_4663_, v___x_4683_, v___f_4679_);
return v___x_4684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4687_, lean_object* v___x_4688_, lean_object* v___x_4689_, lean_object* v___x_4690_, lean_object* v_x_4691_, lean_object* v___y_4692_){
_start:
{
uint8_t v___x_5580__boxed_4693_; lean_object* v_res_4694_; 
v___x_5580__boxed_4693_ = lean_unbox(v___x_4690_);
v_res_4694_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4687_, v___x_4688_, v___x_4689_, v___x_5580__boxed_4693_, v_x_4691_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4695_, lean_object* v_h_4696_, lean_object* v_responseBodyInstance_4697_, lean_object* v_handler_4698_, lean_object* v___f_4699_, lean_object* v_inst_4700_, lean_object* v_socket_4701_, lean_object* v_connectionContext_4702_, lean_object* v_extensions_4703_, lean_object* v___f_4704_, lean_object* v___f_4705_, lean_object* v_machine_4706_, lean_object* v_a_4707_, lean_object* v___x_4708_, lean_object* v___f_4709_, lean_object* v_x_4710_){
_start:
{
if (lean_obj_tag(v_x_4710_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref(v___f_4709_);
lean_dec(v___x_4708_);
lean_dec_ref(v_a_4707_);
lean_dec_ref(v_machine_4706_);
lean_dec_ref(v___f_4705_);
lean_dec_ref(v___f_4704_);
lean_dec(v_extensions_4703_);
lean_dec_ref(v_connectionContext_4702_);
lean_dec(v_socket_4701_);
lean_dec_ref(v_inst_4700_);
lean_dec_ref(v___f_4699_);
lean_dec(v_handler_4698_);
lean_dec_ref(v_responseBodyInstance_4697_);
lean_dec_ref(v_h_4696_);
lean_dec_ref(v_config_4695_);
v_a_4712_ = lean_ctor_get(v_x_4710_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v_x_4710_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4714_ = v_x_4710_;
v_isShared_4715_ = v_isSharedCheck_4720_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v_x_4710_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4720_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; 
v___x_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4717_);
return v___x_4718_;
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4746_; 
v_a_4721_ = lean_ctor_get(v_x_4710_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v_x_4710_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4723_ = v_x_4710_;
v_isShared_4724_ = v_isSharedCheck_4746_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v_x_4710_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4746_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_keepAliveTimeout_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___x_4729_; lean_object* v___f_4730_; lean_object* v___x_4731_; lean_object* v___f_4732_; lean_object* v___x_4733_; lean_object* v___f_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___f_4738_; lean_object* v___x_4739_; lean_object* v___x_4741_; 
v_keepAliveTimeout_4725_ = lean_ctor_get(v_config_4695_, 5);
lean_inc_n(v_keepAliveTimeout_4725_, 2);
v___x_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4726_, 0, v_keepAliveTimeout_4725_);
v___x_4727_ = lean_box(0);
v___x_4728_ = 0;
v___x_4729_ = lean_box(v___x_4728_);
lean_inc_ref_n(v_connectionContext_4702_, 2);
lean_inc(v_socket_4701_);
lean_inc_ref(v_inst_4700_);
lean_inc_ref(v_config_4695_);
lean_inc_n(v_handler_4698_, 2);
lean_inc_ref(v_responseBodyInstance_4697_);
lean_inc_ref_n(v_h_4696_, 2);
v___f_4730_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4730_, 0, v___x_4729_);
lean_closure_set(v___f_4730_, 1, v_h_4696_);
lean_closure_set(v___f_4730_, 2, v_responseBodyInstance_4697_);
lean_closure_set(v___f_4730_, 3, v_handler_4698_);
lean_closure_set(v___f_4730_, 4, v_config_4695_);
lean_closure_set(v___f_4730_, 5, v___f_4699_);
lean_closure_set(v___f_4730_, 6, v_inst_4700_);
lean_closure_set(v___f_4730_, 7, v_socket_4701_);
lean_closure_set(v___f_4730_, 8, v_connectionContext_4702_);
v___x_4731_ = lean_box(v___x_4728_);
v___f_4732_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4732_, 0, v_h_4696_);
lean_closure_set(v___f_4732_, 1, v_handler_4698_);
lean_closure_set(v___f_4732_, 2, v_extensions_4703_);
lean_closure_set(v___f_4732_, 3, v_connectionContext_4702_);
lean_closure_set(v___f_4732_, 4, v___x_4731_);
lean_closure_set(v___f_4732_, 5, v___f_4730_);
v___x_4733_ = lean_box(v___x_4728_);
v___f_4734_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4734_, 0, v_h_4696_);
lean_closure_set(v___f_4734_, 1, v_responseBodyInstance_4697_);
lean_closure_set(v___f_4734_, 2, v_handler_4698_);
lean_closure_set(v___f_4734_, 3, v_config_4695_);
lean_closure_set(v___f_4734_, 4, v_connectionContext_4702_);
lean_closure_set(v___f_4734_, 5, v___x_4733_);
lean_closure_set(v___f_4734_, 6, v___f_4732_);
lean_closure_set(v___f_4734_, 7, v_inst_4700_);
lean_closure_set(v___f_4734_, 8, v_socket_4701_);
lean_closure_set(v___f_4734_, 9, v___f_4704_);
lean_closure_set(v___f_4734_, 10, v___f_4705_);
v___x_4735_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4735_, 0, v_machine_4706_);
lean_ctor_set(v___x_4735_, 1, v_a_4707_);
lean_ctor_set(v___x_4735_, 2, v___x_4726_);
lean_ctor_set(v___x_4735_, 3, v_keepAliveTimeout_4725_);
lean_ctor_set(v___x_4735_, 4, v___x_4727_);
lean_ctor_set(v___x_4735_, 5, v_a_4721_);
lean_ctor_set(v___x_4735_, 6, v___x_4727_);
lean_ctor_set(v___x_4735_, 7, v___x_4708_);
lean_ctor_set(v___x_4735_, 8, v___x_4727_);
lean_ctor_set_uint8(v___x_4735_, sizeof(void*)*9, v___x_4728_);
lean_ctor_set_uint8(v___x_4735_, sizeof(void*)*9 + 1, v___x_4728_);
v___x_4736_ = lean_unsigned_to_nat(0u);
v___x_4737_ = lean_box(v___x_4728_);
v___f_4738_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4738_, 0, v___f_4734_);
lean_closure_set(v___f_4738_, 1, v___x_4736_);
lean_closure_set(v___f_4738_, 2, v___x_4735_);
lean_closure_set(v___f_4738_, 3, v___x_4737_);
v___x_4739_ = lean_io_promise_new();
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v___x_4739_);
v___x_4741_ = v___x_4723_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4739_);
v___x_4741_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
v___x_4743_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4736_, v___x_4728_, v___x_4742_, v___f_4738_);
v___x_4744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4736_, v___x_4728_, v___x_4743_, v___f_4709_);
return v___x_4744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4747_ = _args[0];
lean_object* v_h_4748_ = _args[1];
lean_object* v_responseBodyInstance_4749_ = _args[2];
lean_object* v_handler_4750_ = _args[3];
lean_object* v___f_4751_ = _args[4];
lean_object* v_inst_4752_ = _args[5];
lean_object* v_socket_4753_ = _args[6];
lean_object* v_connectionContext_4754_ = _args[7];
lean_object* v_extensions_4755_ = _args[8];
lean_object* v___f_4756_ = _args[9];
lean_object* v___f_4757_ = _args[10];
lean_object* v_machine_4758_ = _args[11];
lean_object* v_a_4759_ = _args[12];
lean_object* v___x_4760_ = _args[13];
lean_object* v___f_4761_ = _args[14];
lean_object* v_x_4762_ = _args[15];
lean_object* v___y_4763_ = _args[16];
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4747_, v_h_4748_, v_responseBodyInstance_4749_, v_handler_4750_, v___f_4751_, v_inst_4752_, v_socket_4753_, v_connectionContext_4754_, v_extensions_4755_, v___f_4756_, v___f_4757_, v_machine_4758_, v_a_4759_, v___x_4760_, v___f_4761_, v_x_4762_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4765_, lean_object* v_h_4766_, lean_object* v_responseBodyInstance_4767_, lean_object* v_handler_4768_, lean_object* v___f_4769_, lean_object* v_inst_4770_, lean_object* v_socket_4771_, lean_object* v_connectionContext_4772_, lean_object* v_extensions_4773_, lean_object* v___f_4774_, lean_object* v___f_4775_, lean_object* v_machine_4776_, lean_object* v___f_4777_, lean_object* v_x_4778_){
_start:
{
if (lean_obj_tag(v_x_4778_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4788_; 
lean_dec_ref(v___f_4777_);
lean_dec_ref(v_machine_4776_);
lean_dec_ref(v___f_4775_);
lean_dec_ref(v___f_4774_);
lean_dec(v_extensions_4773_);
lean_dec_ref(v_connectionContext_4772_);
lean_dec(v_socket_4771_);
lean_dec_ref(v_inst_4770_);
lean_dec_ref(v___f_4769_);
lean_dec(v_handler_4768_);
lean_dec_ref(v_responseBodyInstance_4767_);
lean_dec_ref(v_h_4766_);
lean_dec_ref(v_config_4765_);
v_a_4780_ = lean_ctor_get(v_x_4778_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_x_4778_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4782_ = v_x_4778_;
v_isShared_4783_ = v_isSharedCheck_4788_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v_x_4778_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4788_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
return v___x_4786_;
}
}
}
else
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4803_; 
v_a_4789_ = lean_ctor_get(v_x_4778_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_x_4778_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4791_ = v_x_4778_;
v_isShared_4792_ = v_isSharedCheck_4803_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v_x_4778_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4803_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4793_; lean_object* v___f_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v___x_4793_ = lean_box(0);
v___f_4794_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4794_, 0, v_config_4765_);
lean_closure_set(v___f_4794_, 1, v_h_4766_);
lean_closure_set(v___f_4794_, 2, v_responseBodyInstance_4767_);
lean_closure_set(v___f_4794_, 3, v_handler_4768_);
lean_closure_set(v___f_4794_, 4, v___f_4769_);
lean_closure_set(v___f_4794_, 5, v_inst_4770_);
lean_closure_set(v___f_4794_, 6, v_socket_4771_);
lean_closure_set(v___f_4794_, 7, v_connectionContext_4772_);
lean_closure_set(v___f_4794_, 8, v_extensions_4773_);
lean_closure_set(v___f_4794_, 9, v___f_4774_);
lean_closure_set(v___f_4794_, 10, v___f_4775_);
lean_closure_set(v___f_4794_, 11, v_machine_4776_);
lean_closure_set(v___f_4794_, 12, v_a_4789_);
lean_closure_set(v___f_4794_, 13, v___x_4793_);
lean_closure_set(v___f_4794_, 14, v___f_4777_);
v___x_4795_ = lean_unsigned_to_nat(0u);
v___x_4796_ = 0;
v___x_4797_ = l_Std_CloseableChannel_new___redArg(v___x_4793_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4797_);
v___x_4799_ = v___x_4791_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
v___x_4801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4795_, v___x_4796_, v___x_4800_, v___f_4794_);
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4804_, lean_object* v_h_4805_, lean_object* v_responseBodyInstance_4806_, lean_object* v_handler_4807_, lean_object* v___f_4808_, lean_object* v_inst_4809_, lean_object* v_socket_4810_, lean_object* v_connectionContext_4811_, lean_object* v_extensions_4812_, lean_object* v___f_4813_, lean_object* v___f_4814_, lean_object* v_machine_4815_, lean_object* v___f_4816_, lean_object* v_x_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4804_, v_h_4805_, v_responseBodyInstance_4806_, v_handler_4807_, v___f_4808_, v_inst_4809_, v_socket_4810_, v_connectionContext_4811_, v_extensions_4812_, v___f_4813_, v___f_4814_, v_machine_4815_, v___f_4816_, v_x_4817_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4823_, lean_object* v_h_4824_, lean_object* v_connection_4825_, lean_object* v_config_4826_, lean_object* v_connectionContext_4827_, lean_object* v_handler_4828_){
_start:
{
lean_object* v_responseBodyInstance_4830_; lean_object* v_onFailure_4831_; lean_object* v_socket_4832_; lean_object* v_machine_4833_; lean_object* v_extensions_4834_; lean_object* v___f_4835_; lean_object* v___f_4836_; lean_object* v___f_4837_; lean_object* v___f_4838_; lean_object* v___f_4839_; lean_object* v___f_4840_; lean_object* v___f_4841_; lean_object* v___f_4842_; lean_object* v___f_4843_; lean_object* v___x_4844_; uint8_t v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v_responseBodyInstance_4830_ = lean_ctor_get(v_h_4824_, 0);
lean_inc_ref_n(v_responseBodyInstance_4830_, 2);
v_onFailure_4831_ = lean_ctor_get(v_h_4824_, 2);
v_socket_4832_ = lean_ctor_get(v_connection_4825_, 0);
lean_inc_n(v_socket_4832_, 2);
v_machine_4833_ = lean_ctor_get(v_connection_4825_, 1);
lean_inc_ref(v_machine_4833_);
v_extensions_4834_ = lean_ctor_get(v_connection_4825_, 2);
lean_inc(v_extensions_4834_);
lean_dec_ref(v_connection_4825_);
v___f_4835_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4836_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4837_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4828_);
lean_inc_ref(v_onFailure_4831_);
v___f_4838_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4838_, 0, v_onFailure_4831_);
lean_closure_set(v___f_4838_, 1, v_handler_4828_);
lean_closure_set(v___f_4838_, 2, v___f_4837_);
v___f_4839_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4823_);
v___f_4840_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4840_, 0, v_inst_4823_);
lean_closure_set(v___f_4840_, 1, v_socket_4832_);
lean_inc_ref(v___f_4840_);
v___f_4841_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4841_, 0, v___f_4840_);
v___f_4842_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4842_, 0, v_responseBodyInstance_4830_);
lean_closure_set(v___f_4842_, 1, v___f_4841_);
lean_closure_set(v___f_4842_, 2, v___f_4840_);
lean_closure_set(v___f_4842_, 3, v___f_4835_);
v___f_4843_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4843_, 0, v_config_4826_);
lean_closure_set(v___f_4843_, 1, v_h_4824_);
lean_closure_set(v___f_4843_, 2, v_responseBodyInstance_4830_);
lean_closure_set(v___f_4843_, 3, v_handler_4828_);
lean_closure_set(v___f_4843_, 4, v___f_4839_);
lean_closure_set(v___f_4843_, 5, v_inst_4823_);
lean_closure_set(v___f_4843_, 6, v_socket_4832_);
lean_closure_set(v___f_4843_, 7, v_connectionContext_4827_);
lean_closure_set(v___f_4843_, 8, v_extensions_4834_);
lean_closure_set(v___f_4843_, 9, v___f_4836_);
lean_closure_set(v___f_4843_, 10, v___f_4838_);
lean_closure_set(v___f_4843_, 11, v_machine_4833_);
lean_closure_set(v___f_4843_, 12, v___f_4842_);
v___x_4844_ = lean_unsigned_to_nat(0u);
v___x_4845_ = 0;
v___x_4846_ = l_Std_Http_Body_mkStream();
v___x_4847_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4844_, v___x_4845_, v___x_4846_, v___f_4843_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4848_, lean_object* v_h_4849_, lean_object* v_connection_4850_, lean_object* v_config_4851_, lean_object* v_connectionContext_4852_, lean_object* v_handler_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4848_, v_h_4849_, v_connection_4850_, v_config_4851_, v_connectionContext_4852_, v_handler_4853_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4856_, lean_object* v_00_u03c3_4857_, lean_object* v_inst_4858_, lean_object* v_h_4859_, lean_object* v_connection_4860_, lean_object* v_config_4861_, lean_object* v_connectionContext_4862_, lean_object* v_handler_4863_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4858_, v_h_4859_, v_connection_4860_, v_config_4861_, v_connectionContext_4862_, v_handler_4863_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4866_, lean_object* v_00_u03c3_4867_, lean_object* v_inst_4868_, lean_object* v_h_4869_, lean_object* v_connection_4870_, lean_object* v_config_4871_, lean_object* v_connectionContext_4872_, lean_object* v_handler_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4866_, v_00_u03c3_4867_, v_inst_4868_, v_h_4869_, v_connection_4870_, v_config_4871_, v_connectionContext_4872_, v_handler_4873_);
return v_res_4875_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = 0;
v___x_4877_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4876_);
return v___x_4877_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = lean_unsigned_to_nat(4096u);
v___x_4879_ = lean_mk_empty_byte_array(v___x_4878_);
return v___x_4879_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4881_ = l_ByteArray_mkIterator(v___x_4880_);
return v___x_4881_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4882_ = 0;
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4885_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4886_ = lean_box(0);
v___x_4887_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v___x_4885_);
lean_ctor_set(v___x_4887_, 2, v___x_4884_);
lean_ctor_set(v___x_4887_, 3, v___x_4883_);
lean_ctor_set(v___x_4887_, 4, v___x_4883_);
lean_ctor_set(v___x_4887_, 5, v___x_4883_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*6, v___x_4882_);
return v___x_4887_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = 1;
v___x_4896_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4895_);
return v___x_4896_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4897_; uint8_t v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4897_ = lean_unsigned_to_nat(0u);
v___x_4898_ = 0;
v___x_4899_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4900_ = lean_box(0);
v___x_4901_ = lean_box(0);
v___x_4902_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4903_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4904_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
lean_ctor_set(v___x_4904_, 1, v___x_4902_);
lean_ctor_set(v___x_4904_, 2, v___x_4901_);
lean_ctor_set(v___x_4904_, 3, v___x_4900_);
lean_ctor_set(v___x_4904_, 4, v___x_4899_);
lean_ctor_set(v___x_4904_, 5, v___x_4897_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*6, v___x_4898_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*6 + 1, v___x_4898_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*6 + 2, v___x_4898_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4905_, lean_object* v_client_4906_, lean_object* v_extensions_4907_, lean_object* v_inst_4908_, lean_object* v_inst_4909_, lean_object* v_handler_4910_, lean_object* v_x_4911_){
_start:
{
if (lean_obj_tag(v_x_4911_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4921_; 
lean_dec(v_handler_4910_);
lean_dec_ref(v_inst_4909_);
lean_dec_ref(v_inst_4908_);
lean_dec(v_extensions_4907_);
lean_dec(v_client_4906_);
lean_dec_ref(v_config_4905_);
v_a_4913_ = lean_ctor_get(v_x_4911_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v_x_4911_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4915_ = v_x_4911_;
v_isShared_4916_ = v_isSharedCheck_4921_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v_x_4911_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4921_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4919_; 
v___x_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
return v___x_4919_;
}
}
}
else
{
lean_object* v_a_4922_; uint8_t v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; uint8_t v_enableKeepAlive_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v_a_4922_ = lean_ctor_get(v_x_4911_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v_x_4911_, 1);
v___x_4923_ = 0;
v___x_4924_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4925_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4926_ = lean_box(0);
v___x_4927_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4928_ = l_Std_Http_Config_toH1Config(v_config_4905_);
v_enableKeepAlive_4929_ = lean_ctor_get_uint8(v___x_4928_, sizeof(void*)*18);
v___x_4930_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4930_, 0, v___x_4924_);
lean_ctor_set(v___x_4930_, 1, v___x_4927_);
lean_ctor_set(v___x_4930_, 2, v___x_4928_);
lean_ctor_set(v___x_4930_, 3, v___x_4925_);
lean_ctor_set(v___x_4930_, 4, v___x_4926_);
lean_ctor_set(v___x_4930_, 5, v___x_4926_);
lean_ctor_set_uint8(v___x_4930_, sizeof(void*)*6, v_enableKeepAlive_4929_);
lean_ctor_set_uint8(v___x_4930_, sizeof(void*)*6 + 1, v___x_4923_);
lean_ctor_set_uint8(v___x_4930_, sizeof(void*)*6 + 2, v___x_4923_);
v___x_4931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4931_, 0, v_client_4906_);
lean_ctor_set(v___x_4931_, 1, v___x_4930_);
lean_ctor_set(v___x_4931_, 2, v_extensions_4907_);
v___x_4932_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4908_, v_inst_4909_, v___x_4931_, v_config_4905_, v_a_4922_, v_handler_4910_);
return v___x_4932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4933_, lean_object* v_client_4934_, lean_object* v_extensions_4935_, lean_object* v_inst_4936_, lean_object* v_inst_4937_, lean_object* v_handler_4938_, lean_object* v_x_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4933_, v_client_4934_, v_extensions_4935_, v_inst_4936_, v_inst_4937_, v_handler_4938_, v_x_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4942_, lean_object* v_inst_4943_, lean_object* v_client_4944_, lean_object* v_handler_4945_, lean_object* v_config_4946_, lean_object* v_extensions_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v___f_4950_; lean_object* v___x_4951_; uint8_t v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___f_4950_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4950_, 0, v_config_4946_);
lean_closure_set(v___f_4950_, 1, v_client_4944_);
lean_closure_set(v___f_4950_, 2, v_extensions_4947_);
lean_closure_set(v___f_4950_, 3, v_inst_4942_);
lean_closure_set(v___f_4950_, 4, v_inst_4943_);
lean_closure_set(v___f_4950_, 5, v_handler_4945_);
v___x_4951_ = lean_unsigned_to_nat(0u);
v___x_4952_ = 0;
lean_inc_ref(v_a_4948_);
v___x_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_a_4948_);
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
v___x_4955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4951_, v___x_4952_, v___x_4954_, v___f_4950_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4956_, lean_object* v_inst_4957_, lean_object* v_client_4958_, lean_object* v_handler_4959_, lean_object* v_config_4960_, lean_object* v_extensions_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4956_, v_inst_4957_, v_client_4958_, v_handler_4959_, v_config_4960_, v_extensions_4961_, v_a_4962_);
lean_dec_ref(v_a_4962_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4965_, lean_object* v_00_u03c3_4966_, lean_object* v_inst_4967_, lean_object* v_inst_4968_, lean_object* v_client_4969_, lean_object* v_handler_4970_, lean_object* v_config_4971_, lean_object* v_extensions_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4967_, v_inst_4968_, v_client_4969_, v_handler_4970_, v_config_4971_, v_extensions_4972_, v_a_4973_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4976_, lean_object* v_00_u03c3_4977_, lean_object* v_inst_4978_, lean_object* v_inst_4979_, lean_object* v_client_4980_, lean_object* v_handler_4981_, lean_object* v_config_4982_, lean_object* v_extensions_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Std_Http_Server_serveConnection(v_t_4976_, v_00_u03c3_4977_, v_inst_4978_, v_inst_4979_, v_client_4980_, v_handler_4981_, v_config_4982_, v_extensions_4983_, v_a_4984_);
lean_dec_ref(v_a_4984_);
return v_res_4986_;
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
