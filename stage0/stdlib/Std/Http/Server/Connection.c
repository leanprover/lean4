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
lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_402_; uint8_t v___y_403_; lean_object* v___y_404_; lean_object* v_val_405_; lean_object* v_socket_408_; lean_object* v_expect_409_; lean_object* v_response_410_; lean_object* v_responseBody_411_; lean_object* v_requestBody_412_; lean_object* v_timeout_413_; lean_object* v_keepAliveTimeout_414_; lean_object* v_headerTimeout_415_; lean_object* v_connectionContext_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___y_429_; lean_object* v___y_479_; 
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
v___x_407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_402_, v___y_403_, v___x_406_, v___y_404_);
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
v___y_402_ = v___x_447_;
v___y_403_ = v___x_448_;
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
v___y_402_ = v___x_447_;
v___y_403_ = v___x_448_;
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
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_a_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Rat_ofInt(v_a_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
return v_x_814_;
}
else
{
lean_object* v_key_816_; lean_object* v_value_817_; lean_object* v_tail_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_841_; 
v_key_816_ = lean_ctor_get(v_x_815_, 0);
v_value_817_ = lean_ctor_get(v_x_815_, 1);
v_tail_818_ = lean_ctor_get(v_x_815_, 2);
v_isSharedCheck_841_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_841_ == 0)
{
v___x_820_ = v_x_815_;
v_isShared_821_ = v_isSharedCheck_841_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_tail_818_);
lean_inc(v_value_817_);
lean_inc(v_key_816_);
lean_dec(v_x_815_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_841_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v_fold_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_822_ = lean_array_get_size(v_x_814_);
v___x_823_ = lean_string_hash(v_key_816_);
v___x_824_ = 32ULL;
v___x_825_ = lean_uint64_shift_right(v___x_823_, v___x_824_);
v_fold_826_ = lean_uint64_xor(v___x_823_, v___x_825_);
v___x_827_ = 16ULL;
v___x_828_ = lean_uint64_shift_right(v_fold_826_, v___x_827_);
v___x_829_ = lean_uint64_xor(v_fold_826_, v___x_828_);
v___x_830_ = lean_uint64_to_usize(v___x_829_);
v___x_831_ = lean_usize_of_nat(v___x_822_);
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_sub(v___x_831_, v___x_832_);
v___x_834_ = lean_usize_land(v___x_830_, v___x_833_);
v___x_835_ = lean_array_uget_borrowed(v_x_814_, v___x_834_);
lean_inc(v___x_835_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 2, v___x_835_);
v___x_837_ = v___x_820_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_key_816_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_value_817_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v___x_835_);
v___x_837_ = v_reuseFailAlloc_840_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; 
v___x_838_ = lean_array_uset(v_x_814_, v___x_834_, v___x_837_);
v_x_814_ = v___x_838_;
v_x_815_ = v_tail_818_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(lean_object* v_i_842_, lean_object* v_source_843_, lean_object* v_target_844_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_array_get_size(v_source_843_);
v___x_846_ = lean_nat_dec_lt(v_i_842_, v___x_845_);
if (v___x_846_ == 0)
{
lean_dec_ref(v_source_843_);
lean_dec(v_i_842_);
return v_target_844_;
}
else
{
lean_object* v_es_847_; lean_object* v___x_848_; lean_object* v_source_849_; lean_object* v_target_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_es_847_ = lean_array_fget(v_source_843_, v_i_842_);
v___x_848_ = lean_box(0);
v_source_849_ = lean_array_fset(v_source_843_, v_i_842_, v___x_848_);
v_target_850_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_target_844_, v_es_847_);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v_i_842_, v___x_851_);
lean_dec(v_i_842_);
v_i_842_ = v___x_852_;
v_source_843_ = v_source_849_;
v_target_844_ = v_target_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(lean_object* v_data_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_nbuckets_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_855_ = lean_array_get_size(v_data_854_);
v___x_856_ = lean_unsigned_to_nat(2u);
v_nbuckets_857_ = lean_nat_mul(v___x_855_, v___x_856_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_box(0);
v___x_860_ = lean_mk_array(v_nbuckets_857_, v___x_859_);
v___x_861_ = lean_array_propagate_mark(v_data_854_, v___x_860_);
v___x_862_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v___x_858_, v_data_854_, v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(lean_object* v_i_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_mk_empty_array_with_capacity(v___x_865_);
v___x_867_ = lean_array_push(v___x_866_, v_i_863_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
else
{
lean_object* v_val_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_val_869_ = lean_ctor_get(v_x_864_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v_x_864_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_val_869_);
lean_dec(v_x_864_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_array_push(v_val_869_, v_i_863_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(lean_object* v_i_878_, lean_object* v_a_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_val_883_; lean_object* v___x_884_; 
v___x_881_ = lean_box(0);
v___x_882_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_878_, v___x_881_);
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec(v___x_882_);
v___x_884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_884_, 0, v_a_879_);
lean_ctor_set(v___x_884_, 1, v_val_883_);
lean_ctor_set(v___x_884_, 2, v_x_880_);
return v___x_884_;
}
else
{
lean_object* v_key_885_; lean_object* v_value_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_902_; 
v_key_885_ = lean_ctor_get(v_x_880_, 0);
v_value_886_ = lean_ctor_get(v_x_880_, 1);
v_tail_887_ = lean_ctor_get(v_x_880_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_880_);
if (v_isSharedCheck_902_ == 0)
{
v___x_889_ = v_x_880_;
v_isShared_890_ = v_isSharedCheck_902_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_value_886_);
lean_inc(v_key_885_);
lean_dec(v_x_880_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_902_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; 
v___x_891_ = lean_string_dec_eq(v_key_885_, v_a_879_);
if (v___x_891_ == 0)
{
lean_object* v_tail_892_; lean_object* v___x_894_; 
v_tail_892_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_878_, v_a_879_, v_tail_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 2, v_tail_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_key_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_value_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_tail_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_val_898_; lean_object* v___x_900_; 
lean_dec(v_key_885_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_value_886_);
v___x_897_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0(v_i_878_, v___x_896_);
v_val_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_val_898_);
lean_dec(v___x_897_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v_val_898_);
lean_ctor_set(v___x_889_, 0, v_a_879_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_879_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_val_898_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_tail_887_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(lean_object* v_a_903_, lean_object* v_x_904_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
uint8_t v___x_905_; 
v___x_905_ = 0;
return v___x_905_;
}
else
{
lean_object* v_key_906_; lean_object* v_tail_907_; uint8_t v___x_908_; 
v_key_906_ = lean_ctor_get(v_x_904_, 0);
v_tail_907_ = lean_ctor_get(v_x_904_, 2);
v___x_908_ = lean_string_dec_eq(v_key_906_, v_a_903_);
if (v___x_908_ == 0)
{
v_x_904_ = v_tail_907_;
goto _start;
}
else
{
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg___boxed(lean_object* v_a_910_, lean_object* v_x_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_910_, v_x_911_);
lean_dec(v_x_911_);
lean_dec_ref(v_a_910_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_i_914_, lean_object* v_m_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_size_917_; lean_object* v_buckets_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_968_; 
v_size_917_ = lean_ctor_get(v_m_915_, 0);
v_buckets_918_ = lean_ctor_get(v_m_915_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_m_915_);
if (v_isSharedCheck_968_ == 0)
{
v___x_920_ = v_m_915_;
v_isShared_921_ = v_isSharedCheck_968_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_buckets_918_);
lean_inc(v_size_917_);
lean_dec(v_m_915_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_968_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; uint64_t v___x_923_; uint64_t v___x_924_; uint64_t v___x_925_; uint64_t v_fold_926_; uint64_t v___x_927_; uint64_t v___x_928_; uint64_t v___x_929_; size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v_bkt_935_; uint8_t v___x_936_; 
v___x_922_ = lean_array_get_size(v_buckets_918_);
v___x_923_ = lean_string_hash(v_a_916_);
v___x_924_ = 32ULL;
v___x_925_ = lean_uint64_shift_right(v___x_923_, v___x_924_);
v_fold_926_ = lean_uint64_xor(v___x_923_, v___x_925_);
v___x_927_ = 16ULL;
v___x_928_ = lean_uint64_shift_right(v_fold_926_, v___x_927_);
v___x_929_ = lean_uint64_xor(v_fold_926_, v___x_928_);
v___x_930_ = lean_uint64_to_usize(v___x_929_);
v___x_931_ = lean_usize_of_nat(v___x_922_);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_sub(v___x_931_, v___x_932_);
v___x_934_ = lean_usize_land(v___x_930_, v___x_933_);
v_bkt_935_ = lean_array_uget_borrowed(v_buckets_918_, v___x_934_);
v___x_936_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_916_, v_bkt_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_size_x27_940_; lean_object* v___x_941_; lean_object* v_buckets_x27_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___x_939_ = lean_array_push(v___x_938_, v_i_914_);
v_size_x27_940_ = lean_nat_add(v_size_917_, v___x_937_);
lean_dec(v_size_917_);
lean_inc(v_bkt_935_);
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v_a_916_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v_bkt_935_);
v_buckets_x27_942_ = lean_array_uset(v_buckets_918_, v___x_934_, v___x_941_);
v___x_943_ = lean_unsigned_to_nat(4u);
v___x_944_ = lean_nat_mul(v_size_x27_940_, v___x_943_);
v___x_945_ = lean_unsigned_to_nat(3u);
v___x_946_ = lean_nat_div(v___x_944_, v___x_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_array_get_size(v_buckets_x27_942_);
v___x_948_ = lean_nat_dec_le(v___x_946_, v___x_947_);
lean_dec(v___x_946_);
if (v___x_948_ == 0)
{
lean_object* v_val_949_; lean_object* v___x_951_; 
v_val_949_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_buckets_x27_942_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v_val_949_);
lean_ctor_set(v___x_920_, 0, v_size_x27_940_);
v___x_951_ = v___x_920_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_size_x27_940_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_val_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v___x_954_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v_buckets_x27_942_);
lean_ctor_set(v___x_920_, 0, v_size_x27_940_);
v___x_954_ = v___x_920_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_size_x27_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_buckets_x27_942_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v___x_956_; lean_object* v_buckets_x27_957_; lean_object* v_bkt_x27_958_; lean_object* v___y_960_; uint8_t v___x_965_; 
lean_inc(v_bkt_935_);
v___x_956_ = lean_box(0);
v_buckets_x27_957_ = lean_array_uset(v_buckets_918_, v___x_934_, v___x_956_);
lean_inc_ref(v_a_916_);
v_bkt_x27_958_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2(v_i_914_, v_a_916_, v_bkt_935_);
v___x_965_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_916_, v_bkt_x27_958_);
lean_dec_ref(v_a_916_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_sub(v_size_917_, v___x_966_);
lean_dec(v_size_917_);
v___y_960_ = v___x_967_;
goto v___jp_959_;
}
else
{
v___y_960_ = v_size_917_;
goto v___jp_959_;
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_array_uset(v_buckets_x27_957_, v___x_934_, v_bkt_x27_958_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_961_);
lean_ctor_set(v___x_920_, 0, v___y_960_);
v___x_963_ = v___x_920_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___y_960_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_entries_969_, lean_object* v_indexes_970_, lean_object* v_status_971_, uint8_t v_version_972_, lean_object* v_x_973_){
_start:
{
if (lean_obj_tag(v_x_973_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_status_971_);
lean_dec_ref(v_indexes_970_);
lean_dec_ref(v_entries_969_);
v_a_975_ = lean_ctor_get(v_x_973_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_973_);
if (v_isSharedCheck_983_ == 0)
{
v___x_977_ = v_x_973_;
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v_x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1001_; 
v_a_984_ = lean_ctor_get(v_x_973_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_x_973_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_986_ = v_x_973_;
v_isShared_987_ = v_isSharedCheck_1001_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v_x_973_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1001_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_i_991_; lean_object* v___x_992_; lean_object* v_entries_993_; lean_object* v_indexes_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_988_ = l_Std_Http_Header_Name_date;
v___x_989_ = l_Std_Time_DateTime_toRFC822String(v_a_984_);
v___x_990_ = l_Std_Http_Header_Value_ofString_x21(v___x_989_);
v_i_991_ = lean_array_get_size(v_entries_969_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_988_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
v_entries_993_ = lean_array_push(v_entries_969_, v___x_992_);
v_indexes_994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(v_i_991_, v_indexes_970_, v___x_988_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_entries_993_);
lean_ctor_set(v___x_995_, 1, v_indexes_994_);
v___x_996_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_996_, 0, v_status_971_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*2, v_version_972_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_996_);
v___x_998_ = v___x_986_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_1000_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_entries_1002_, lean_object* v_indexes_1003_, lean_object* v_status_1004_, lean_object* v_version_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v_version_boxed_1008_; lean_object* v_res_1009_; 
v_version_boxed_1008_ = lean_unbox(v_version_1005_);
v_res_1009_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_entries_1002_, v_indexes_1003_, v_status_1004_, v_version_boxed_1008_, v_x_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_tz_1010_, lean_object* v_a_1011_, lean_object* v___x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_offset_1014_; lean_object* v_second_1015_; lean_object* v_nano_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_nanos_1020_; lean_object* v___x_1021_; lean_object* v_nanos_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_offset_1014_ = lean_ctor_get(v_tz_1010_, 0);
v_second_1015_ = lean_ctor_get(v_a_1011_, 0);
v_nano_1016_ = lean_ctor_get(v_a_1011_, 1);
v___x_1017_ = lean_nat_to_int(v___x_1012_);
v___x_1018_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_1019_ = lean_int_mul(v_second_1015_, v___x_1018_);
v_nanos_1020_ = lean_int_add(v___x_1019_, v_nano_1016_);
lean_dec(v___x_1019_);
v___x_1021_ = lean_int_mul(v_offset_1014_, v___x_1018_);
v_nanos_1022_ = lean_int_add(v___x_1021_, v___x_1017_);
lean_dec(v___x_1017_);
lean_dec(v___x_1021_);
v___x_1023_ = lean_int_add(v_nanos_1020_, v_nanos_1022_);
lean_dec(v_nanos_1022_);
lean_dec(v_nanos_1020_);
v___x_1024_ = l_Std_Time_Duration_ofNanoseconds(v___x_1023_);
lean_dec(v___x_1023_);
v___x_1025_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_tz_1026_, lean_object* v_a_1027_, lean_object* v___x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_tz_1026_, v_a_1027_, v___x_1028_, v_x_1029_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_tz_1026_);
return v_res_1030_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(lean_object* v_m_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_buckets_1033_; lean_object* v___x_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; uint64_t v_fold_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_buckets_1033_ = lean_ctor_get(v_m_1031_, 1);
v___x_1034_ = lean_array_get_size(v_buckets_1033_);
v___x_1035_ = lean_string_hash(v_a_1032_);
v___x_1036_ = 32ULL;
v___x_1037_ = lean_uint64_shift_right(v___x_1035_, v___x_1036_);
v_fold_1038_ = lean_uint64_xor(v___x_1035_, v___x_1037_);
v___x_1039_ = 16ULL;
v___x_1040_ = lean_uint64_shift_right(v_fold_1038_, v___x_1039_);
v___x_1041_ = lean_uint64_xor(v_fold_1038_, v___x_1040_);
v___x_1042_ = lean_uint64_to_usize(v___x_1041_);
v___x_1043_ = lean_usize_of_nat(v___x_1034_);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_sub(v___x_1043_, v___x_1044_);
v___x_1046_ = lean_usize_land(v___x_1042_, v___x_1045_);
v___x_1047_ = lean_array_uget_borrowed(v_buckets_1033_, v___x_1046_);
v___x_1048_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1032_, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg___boxed(lean_object* v_m_1049_, lean_object* v_a_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1049_, v_a_1050_);
lean_dec_ref(v_a_1050_);
lean_dec_ref(v_m_1049_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_1054_, lean_object* v_head_1055_){
_start:
{
uint8_t v_generateDate_1060_; 
v_generateDate_1060_ = lean_ctor_get_uint8(v_config_1054_, sizeof(void*)*24 + 1);
if (v_generateDate_1060_ == 0)
{
goto v___jp_1057_;
}
else
{
lean_object* v_headers_1061_; lean_object* v_status_1062_; uint8_t v_version_1063_; lean_object* v_entries_1064_; lean_object* v_indexes_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_headers_1061_ = lean_ctor_get(v_head_1055_, 1);
v_status_1062_ = lean_ctor_get(v_head_1055_, 0);
v_version_1063_ = lean_ctor_get_uint8(v_head_1055_, sizeof(void*)*2);
v_entries_1064_ = lean_ctor_get(v_headers_1061_, 0);
v_indexes_1065_ = lean_ctor_get(v_headers_1061_, 1);
v___x_1066_ = l_Std_Http_Header_Name_date;
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_indexes_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_val_1073_; lean_object* v_a_1077_; lean_object* v___x_1079_; 
lean_inc_ref(v_indexes_1065_);
lean_inc_ref(v_entries_1064_);
lean_inc(v_status_1062_);
lean_dec_ref(v_head_1055_);
v___x_1068_ = lean_box(v_version_1063_);
v___f_1069_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1069_, 0, v_entries_1064_);
lean_closure_set(v___f_1069_, 1, v_indexes_1065_);
lean_closure_set(v___f_1069_, 2, v_status_1062_);
lean_closure_set(v___f_1069_, 3, v___x_1068_);
v___x_1070_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___closed__0));
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_get_current_time();
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = l_Std_Time_Database_defaultGetZoneRules(v___x_1070_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1093_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_tz_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_inc(v_a_1082_);
v_tz_1086_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_1082_, v_a_1080_);
lean_inc(v_a_1080_);
lean_inc_ref(v_tz_1086_);
v___f_1087_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1087_, 0, v_tz_1086_);
lean_closure_set(v___f_1087_, 1, v_a_1080_);
lean_closure_set(v___f_1087_, 2, v___x_1071_);
v___x_1088_ = lean_mk_thunk(v___f_1087_);
v___x_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1080_);
lean_ctor_set(v___x_1089_, 2, v_a_1082_);
lean_ctor_set(v___x_1089_, 3, v_tz_1086_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1089_);
v___x_1091_ = v___x_1084_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
v_val_1073_ = v___x_1091_;
goto v___jp_1072_;
}
}
}
else
{
lean_object* v_a_1094_; 
lean_dec(v_a_1080_);
v_a_1094_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1081_, 1);
v_a_1077_ = v_a_1094_;
goto v___jp_1076_;
}
}
else
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1079_, 1);
v_a_1077_ = v_a_1095_;
goto v___jp_1076_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_val_1073_);
v___x_1075_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1071_, v___x_1067_, v___x_1074_, v___f_1069_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_a_1077_);
v_val_1073_ = v___x_1078_;
goto v___jp_1072_;
}
}
else
{
goto v___jp_1057_;
}
}
v___jp_1057_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_head_1055_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_1096_, lean_object* v_head_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1096_, v_head_1097_);
lean_dec_ref(v_config_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_00_u03b2_1100_, lean_object* v_m_1101_, lean_object* v_a_1102_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___redArg(v_m_1101_, v_a_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1___boxed(lean_object* v_00_u03b2_1104_, lean_object* v_m_1105_, lean_object* v_a_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(v_00_u03b2_1104_, v_m_1105_, v_a_1106_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_m_1105_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2_spec__5(lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_nat_to_int(v_a_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_nat_to_int(v_a_1111_);
v___x_1113_ = l_Rat_ofInt(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___redArg(v_a_1115_, v_x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1118_, lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__0(v_00_u03b2_1118_, v_a_1119_, v_x_1120_);
lean_dec(v_x_1120_);
lean_dec_ref(v_a_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1(lean_object* v_00_u03b2_1123_, lean_object* v_data_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1___redArg(v_data_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1126_, lean_object* v_i_1127_, lean_object* v_source_1128_, lean_object* v_target_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3___redArg(v_i_1127_, v_source_1128_, v_target_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__1_spec__3_spec__7___redArg(v_x_1132_, v_x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v___y_1135_, lean_object* v_____r_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1135_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v___y_1142_, lean_object* v_____r_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v___y_1142_, v_____r_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___f_1146_, lean_object* v_x_1147_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v___f_1146_);
v_a_1149_ = lean_ctor_get(v_x_1147_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1151_ = v_x_1147_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v_x_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1159_; 
v_a_1158_ = lean_ctor_get(v_x_1147_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v_x_1147_, 1);
v___x_1159_ = lean_apply_2(v___f_1146_, v_a_1158_, lean_box(0));
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___f_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___f_1160_, v_x_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v_close_1164_, lean_object* v_body_1165_, lean_object* v___f_1166_, lean_object* v___f_1167_, lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___f_1167_);
lean_dec_ref(v___f_1166_);
lean_dec(v_body_1165_);
lean_dec_ref(v_close_1164_);
v_a_1170_ = lean_ctor_get(v_x_1168_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v_x_1168_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v_x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; uint8_t v___x_1180_; 
v_a_1179_ = lean_ctor_get(v_x_1168_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v_x_1168_, 1);
v___x_1180_ = lean_unbox(v_a_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
lean_dec_ref(v___f_1167_);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_apply_2(v_close_1164_, v_body_1165_, lean_box(0));
v___x_1183_ = lean_unbox(v_a_1179_);
lean_dec(v_a_1179_);
v___x_1184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1181_, v___x_1183_, v___x_1182_, v___f_1166_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_a_1179_);
lean_dec_ref(v___f_1166_);
lean_dec(v_body_1165_);
lean_dec_ref(v_close_1164_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_apply_2(v___f_1167_, v___x_1185_, lean_box(0));
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v_close_1187_, lean_object* v_body_1188_, lean_object* v___f_1189_, lean_object* v___f_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v_close_1187_, v_body_1188_, v___f_1189_, v___f_1190_, v_x_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1194_, uint8_t v___x_1195_, lean_object* v___f_1196_, lean_object* v___f_1197_, lean_object* v_x1_1198_, lean_object* v_x2_1199_){
_start:
{
lean_object* v_fst_1200_; uint8_t v___x_1201_; 
v_fst_1200_ = lean_ctor_get(v_x2_1199_, 0);
lean_inc(v_fst_1200_);
v___x_1201_ = lean_string_dec_eq(v___x_1194_, v_fst_1200_);
if (v___x_1201_ == 0)
{
if (v___x_1195_ == 0)
{
lean_dec(v_fst_1200_);
lean_dec_ref(v_x2_1199_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v___f_1196_);
return v_x1_1198_;
}
else
{
lean_object* v_entries_1202_; lean_object* v_indexes_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1214_; 
v_entries_1202_ = lean_ctor_get(v_x1_1198_, 0);
v_indexes_1203_ = lean_ctor_get(v_x1_1198_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x1_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1205_ = v_x1_1198_;
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_indexes_1203_);
lean_inc(v_entries_1202_);
lean_dec(v_x1_1198_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_i_1207_; lean_object* v_f_1208_; lean_object* v_entries_1209_; lean_object* v_indexes_1210_; lean_object* v___x_1212_; 
v_i_1207_ = lean_array_get_size(v_entries_1202_);
v_f_1208_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(v_f_1208_, 0, v_i_1207_);
v_entries_1209_ = lean_array_push(v_entries_1202_, v_x2_1199_);
v_indexes_1210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1196_, v___f_1197_, v_indexes_1203_, v_fst_1200_, v_f_1208_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v_indexes_1210_);
lean_ctor_set(v___x_1205_, 0, v_entries_1209_);
v___x_1212_ = v___x_1205_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_entries_1209_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_indexes_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_dec(v_fst_1200_);
lean_dec_ref(v_x2_1199_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v___f_1196_);
return v_x1_1198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v___f_1217_, lean_object* v___f_1218_, lean_object* v_x1_1219_, lean_object* v_x2_1220_){
_start:
{
uint8_t v___x_2240__boxed_1221_; lean_object* v_res_1222_; 
v___x_2240__boxed_1221_ = lean_unbox(v___x_1216_);
v_res_1222_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1215_, v___x_2240__boxed_1221_, v___f_1217_, v___f_1218_, v_x1_1219_, v_x2_1220_);
lean_dec_ref(v___x_1215_);
return v_res_1222_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v___y_1245_, lean_object* v_body_1246_, lean_object* v_close_1247_, lean_object* v_isClosed_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___y_1252_; uint8_t v_omitBody_1253_; lean_object* v___y_1266_; lean_object* v___y_1301_; uint8_t v___y_1305_; uint8_t v___y_1306_; lean_object* v___y_1307_; uint8_t v___y_1308_; 
if (lean_obj_tag(v_x_1249_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_isClosed_1248_);
lean_dec_ref(v_close_1247_);
lean_dec(v_body_1246_);
lean_dec_ref(v___y_1245_);
v_a_1309_ = lean_ctor_get(v_x_1249_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_x_1249_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v_x_1249_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v_x_1249_);
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
lean_object* v_writer_1318_; lean_object* v_a_1319_; lean_object* v_reader_1320_; lean_object* v_config_1321_; lean_object* v_events_1322_; lean_object* v_error_1323_; lean_object* v_instant_1324_; uint8_t v_keepAlive_1325_; uint8_t v_forcedFlush_1326_; uint8_t v_pullBodyStalled_1327_; lean_object* v_userData_1328_; lean_object* v_outputData_1329_; lean_object* v_state_1330_; lean_object* v_knownSize_1331_; lean_object* v_messageHead_1332_; uint8_t v_sentMessage_1333_; uint8_t v_userClosedBody_1334_; uint8_t v_omitBody_1335_; lean_object* v_userDataBytes_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1439_; 
v_writer_1318_ = lean_ctor_get(v___y_1245_, 1);
lean_inc_ref(v_writer_1318_);
v_a_1319_ = lean_ctor_get(v_x_1249_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v_x_1249_, 1);
v_reader_1320_ = lean_ctor_get(v___y_1245_, 0);
v_config_1321_ = lean_ctor_get(v___y_1245_, 2);
v_events_1322_ = lean_ctor_get(v___y_1245_, 3);
v_error_1323_ = lean_ctor_get(v___y_1245_, 4);
v_instant_1324_ = lean_ctor_get(v___y_1245_, 5);
v_keepAlive_1325_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*6);
v_forcedFlush_1326_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1327_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*6 + 2);
v_userData_1328_ = lean_ctor_get(v_writer_1318_, 0);
v_outputData_1329_ = lean_ctor_get(v_writer_1318_, 1);
v_state_1330_ = lean_ctor_get(v_writer_1318_, 2);
v_knownSize_1331_ = lean_ctor_get(v_writer_1318_, 3);
v_messageHead_1332_ = lean_ctor_get(v_writer_1318_, 4);
v_sentMessage_1333_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6);
v_userClosedBody_1334_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6 + 1);
v_omitBody_1335_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6 + 2);
v_userDataBytes_1336_ = lean_ctor_get(v_writer_1318_, 5);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_writer_1318_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1338_ = v_writer_1318_;
v_isShared_1339_ = v_isSharedCheck_1439_;
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
v_isShared_1339_ = v_isSharedCheck_1439_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1364_; uint8_t v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1375_; uint8_t v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; uint8_t v___x_1389_; uint8_t v___y_1391_; uint8_t v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; uint8_t v___y_1403_; uint8_t v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1422_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1389_ = 0;
v___x_1437_ = lean_box(1);
v___x_1438_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1330_, v___x_1437_);
if (v___x_1438_ == 0)
{
v___y_1422_ = v___x_1438_;
goto v___jp_1421_;
}
else
{
if (v_sentMessage_1333_ == 0)
{
v___y_1422_ = v___x_1438_;
goto v___jp_1421_;
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
v___y_1252_ = v___y_1245_;
v_omitBody_1253_ = v_omitBody_1335_;
goto v___jp_1251_;
}
}
v___jp_1340_:
{
lean_object* v_message_1343_; lean_object* v___x_2029__overap_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_message_1343_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1341_, v_a_1319_, v___y_1342_);
v___x_2029__overap_1344_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1341_);
v___x_1345_ = lean_apply_2(v___x_2029__overap_1344_, v_outputData_1329_, v_message_1343_);
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
v___y_1252_ = v___x_1348_;
v_omitBody_1253_ = v_omitBody_1335_;
goto v___jp_1251_;
}
}
v___jp_1350_:
{
lean_object* v_entries_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_entries_1354_ = lean_ctor_get(v___y_1351_, 0);
lean_inc_ref(v_entries_1354_);
lean_dec_ref(v___y_1351_);
v___x_1355_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_array_get_size(v_entries_1354_);
v___x_1358_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_1359_ = lean_nat_dec_lt(v___x_1356_, v___x_1357_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v_entries_1354_);
lean_dec_ref(v___y_1353_);
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___x_1355_;
goto v___jp_1340_;
}
else
{
size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = lean_usize_of_nat(v___x_1357_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1358_, v___y_1353_, v_entries_1354_, v___x_1360_, v___x_1361_, v___x_1355_);
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___x_1362_;
goto v___jp_1340_;
}
}
v___jp_1363_:
{
lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; lean_object* v___f_1372_; uint8_t v___x_1373_; 
v___x_1368_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1369_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1370_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1371_ = lean_box(v___y_1364_);
v___f_1372_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1372_, 0, v___x_1368_);
lean_closure_set(v___f_1372_, 1, v___x_1371_);
lean_closure_set(v___f_1372_, 2, v___f_1369_);
lean_closure_set(v___f_1372_, 3, v___f_1370_);
v___x_1373_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1369_, v___f_1370_, v___x_1368_, v___y_1367_);
if (v___x_1373_ == 0)
{
if (v___y_1365_ == 0)
{
v___y_1351_ = v___y_1367_;
v___y_1352_ = v___y_1366_;
v___y_1353_ = v___f_1372_;
goto v___jp_1350_;
}
else
{
lean_dec_ref(v___f_1372_);
v___y_1341_ = v___y_1366_;
v___y_1342_ = v___y_1367_;
goto v___jp_1340_;
}
}
else
{
v___y_1351_ = v___y_1367_;
v___y_1352_ = v___y_1366_;
v___y_1353_ = v___f_1372_;
goto v___jp_1350_;
}
}
v___jp_1374_:
{
lean_object* v_entries_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_entries_1380_ = lean_ctor_get(v___y_1379_, 0);
lean_inc_ref(v_entries_1380_);
lean_dec_ref(v___y_1379_);
v___x_1381_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__0);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = lean_array_get_size(v_entries_1380_);
v___x_1384_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_1385_ = lean_nat_dec_lt(v___x_1382_, v___x_1383_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_entries_1380_);
lean_dec_ref(v___y_1377_);
v___y_1364_ = v___y_1375_;
v___y_1365_ = v___y_1376_;
v___y_1366_ = v___y_1378_;
v___y_1367_ = v___x_1381_;
goto v___jp_1363_;
}
else
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = lean_usize_of_nat(v___x_1383_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1384_, v___y_1377_, v_entries_1380_, v___x_1386_, v___x_1387_, v___x_1381_);
v___y_1364_ = v___y_1375_;
v___y_1365_ = v___y_1376_;
v___y_1366_ = v___y_1378_;
v___y_1367_ = v___x_1388_;
goto v___jp_1363_;
}
}
v___jp_1390_:
{
lean_object* v_headerSize_1397_; lean_object* v_machine_1398_; lean_object* v_machine_1399_; lean_object* v_reader_1400_; lean_object* v_state_1401_; 
v_headerSize_1397_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___y_1393_, v_a_1319_, v___y_1391_);
v_machine_1398_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1389_, v___y_1395_, v_headerSize_1397_, v___y_1396_);
v_machine_1399_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1389_, v_machine_1398_, v_a_1319_);
lean_dec(v_a_1319_);
v_reader_1400_ = lean_ctor_get(v_machine_1399_, 0);
v_state_1401_ = lean_ctor_get(v_reader_1400_, 0);
if (lean_obj_tag(v_state_1401_) == 7)
{
v___y_1305_ = v___y_1391_;
v___y_1306_ = v___y_1392_;
v___y_1307_ = v_machine_1399_;
v___y_1308_ = v___y_1394_;
goto v___jp_1304_;
}
else
{
v___y_1305_ = v___y_1391_;
v___y_1306_ = v___y_1392_;
v___y_1307_ = v_machine_1399_;
v___y_1308_ = v___y_1391_;
goto v___jp_1304_;
}
}
v___jp_1402_:
{
uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v_indexes_1408_; lean_object* v___x_1409_; lean_object* v_machine_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___f_1413_; uint8_t v___x_1414_; 
v___x_1406_ = 1;
v___x_1407_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1406_, v_a_1319_);
v_indexes_1408_ = lean_ctor_get(v___x_1407_, 1);
lean_inc_ref(v_indexes_1408_);
lean_dec_ref(v___x_1407_);
lean_inc(v_a_1319_);
v___x_1409_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1409_, 0, v_userData_1328_);
lean_ctor_set(v___x_1409_, 1, v_outputData_1329_);
lean_ctor_set(v___x_1409_, 2, v_state_1330_);
lean_ctor_set(v___x_1409_, 3, v_knownSize_1331_);
lean_ctor_set(v___x_1409_, 4, v_a_1319_);
lean_ctor_set(v___x_1409_, 5, v_userDataBytes_1336_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*6, v___y_1404_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*6 + 1, v_userClosedBody_1334_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*6 + 2, v_omitBody_1335_);
v_machine_1410_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_machine_1410_, 0, v_reader_1320_);
lean_ctor_set(v_machine_1410_, 1, v___x_1409_);
lean_ctor_set(v_machine_1410_, 2, v_config_1321_);
lean_ctor_set(v_machine_1410_, 3, v_events_1322_);
lean_ctor_set(v_machine_1410_, 4, v_error_1323_);
lean_ctor_set(v_machine_1410_, 5, v_instant_1324_);
lean_ctor_set_uint8(v_machine_1410_, sizeof(void*)*6, v_keepAlive_1325_);
lean_ctor_set_uint8(v_machine_1410_, sizeof(void*)*6 + 1, v_forcedFlush_1326_);
lean_ctor_set_uint8(v_machine_1410_, sizeof(void*)*6 + 2, v_pullBodyStalled_1327_);
v___x_1411_ = l_Std_Http_Header_Name_contentLength;
v___f_1412_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1413_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1412_, v___f_1413_, v_indexes_1408_, v___x_1411_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = l_Std_Http_Header_Name_transferEncoding;
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1412_, v___f_1413_, v_indexes_1408_, v___x_1415_);
lean_dec_ref(v_indexes_1408_);
v___y_1391_ = v___y_1403_;
v___y_1392_ = v___y_1405_;
v___y_1393_ = v___x_1406_;
v___y_1394_ = v___y_1404_;
v___y_1395_ = v_machine_1410_;
v___y_1396_ = v___x_1416_;
goto v___jp_1390_;
}
else
{
lean_dec_ref(v_indexes_1408_);
v___y_1391_ = v___y_1403_;
v___y_1392_ = v___y_1405_;
v___y_1393_ = v___x_1406_;
v___y_1394_ = v___y_1404_;
v___y_1395_ = v_machine_1410_;
v___y_1396_ = v___x_1414_;
goto v___jp_1390_;
}
}
v___jp_1417_:
{
lean_object* v_state_1420_; 
v_state_1420_ = lean_ctor_get(v_reader_1320_, 0);
if (lean_obj_tag(v_state_1420_) == 7)
{
v___y_1403_ = v___y_1419_;
v___y_1404_ = v___y_1418_;
v___y_1405_ = v___y_1418_;
goto v___jp_1402_;
}
else
{
v___y_1403_ = v___y_1419_;
v___y_1404_ = v___y_1418_;
v___y_1405_ = v___y_1419_;
goto v___jp_1402_;
}
}
v___jp_1421_:
{
if (v___y_1422_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_userDataBytes_1336_);
lean_dec(v_messageHead_1332_);
lean_dec(v_knownSize_1331_);
lean_dec(v_state_1330_);
lean_dec_ref(v_outputData_1329_);
lean_dec_ref(v_userData_1328_);
lean_dec(v_a_1319_);
v___y_1252_ = v___y_1245_;
v_omitBody_1253_ = v_omitBody_1335_;
goto v___jp_1251_;
}
else
{
lean_object* v_status_1423_; uint16_t v___x_1424_; uint16_t v___x_1425_; uint8_t v___x_1426_; 
lean_inc(v_instant_1324_);
lean_inc(v_error_1323_);
lean_inc_ref(v_events_1322_);
lean_inc_ref(v_config_1321_);
lean_inc_ref(v_reader_1320_);
lean_dec_ref(v___y_1245_);
v_status_1423_ = lean_ctor_get(v_a_1319_, 0);
v___x_1424_ = 100;
v___x_1425_ = l_Std_Http_Status_toCode(v_status_1423_);
v___x_1426_ = lean_uint16_dec_le(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_messageHead_1332_);
v___y_1418_ = v___y_1422_;
v___y_1419_ = v___x_1426_;
goto v___jp_1417_;
}
else
{
uint16_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = 200;
v___x_1428_ = lean_uint16_dec_lt(v___x_1425_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_messageHead_1332_);
v___y_1418_ = v___y_1422_;
v___y_1419_ = v___x_1428_;
goto v___jp_1417_;
}
else
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; uint8_t v___x_1436_; 
v___x_1429_ = 1;
v___x_1430_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1429_, v_a_1319_);
v___x_1431_ = l_Std_Http_Header_Name_contentLength;
v___f_1432_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__11));
v___f_1433_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__12));
v___x_1434_ = lean_box(v___x_1428_);
v___f_1435_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1435_, 0, v___x_1431_);
lean_closure_set(v___f_1435_, 1, v___x_1434_);
lean_closure_set(v___f_1435_, 2, v___f_1432_);
lean_closure_set(v___f_1435_, 3, v___f_1433_);
v___x_1436_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1432_, v___f_1433_, v___x_1431_, v___x_1430_);
if (v___x_1436_ == 0)
{
if (v___x_1428_ == 0)
{
v___y_1375_ = v___x_1428_;
v___y_1376_ = v___x_1428_;
v___y_1377_ = v___f_1435_;
v___y_1378_ = v___x_1429_;
v___y_1379_ = v___x_1430_;
goto v___jp_1374_;
}
else
{
lean_dec_ref(v___f_1435_);
v___y_1364_ = v___x_1428_;
v___y_1365_ = v___x_1428_;
v___y_1366_ = v___x_1429_;
v___y_1367_ = v___x_1430_;
goto v___jp_1363_;
}
}
else
{
v___y_1375_ = v___x_1428_;
v___y_1376_ = v___x_1428_;
v___y_1377_ = v___f_1435_;
v___y_1378_ = v___x_1429_;
v___y_1379_ = v___x_1430_;
goto v___jp_1374_;
}
}
}
}
}
}
}
v___jp_1251_:
{
if (v_omitBody_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v_isClosed_1248_);
lean_dec_ref(v_close_1247_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_body_1246_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___y_1252_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
else
{
lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___f_1258_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1258_, 0, v___y_1252_);
lean_inc_ref(v___f_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1259_, 0, v___f_1258_);
lean_inc(v_body_1246_);
v___f_1260_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1260_, 0, v_close_1247_);
lean_closure_set(v___f_1260_, 1, v_body_1246_);
lean_closure_set(v___f_1260_, 2, v___f_1259_);
lean_closure_set(v___f_1260_, 3, v___f_1258_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = 0;
v___x_1263_ = lean_apply_2(v_isClosed_1248_, v_body_1246_, lean_box(0));
v___x_1264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1261_, v___x_1262_, v___x_1263_, v___f_1260_);
return v___x_1264_;
}
}
v___jp_1265_:
{
lean_object* v_writer_1267_; lean_object* v_reader_1268_; lean_object* v_config_1269_; lean_object* v_events_1270_; lean_object* v_error_1271_; lean_object* v_instant_1272_; uint8_t v_keepAlive_1273_; uint8_t v_forcedFlush_1274_; uint8_t v_pullBodyStalled_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1299_; 
v_writer_1267_ = lean_ctor_get(v___y_1266_, 1);
v_reader_1268_ = lean_ctor_get(v___y_1266_, 0);
v_config_1269_ = lean_ctor_get(v___y_1266_, 2);
v_events_1270_ = lean_ctor_get(v___y_1266_, 3);
v_error_1271_ = lean_ctor_get(v___y_1266_, 4);
v_instant_1272_ = lean_ctor_get(v___y_1266_, 5);
v_keepAlive_1273_ = lean_ctor_get_uint8(v___y_1266_, sizeof(void*)*6);
v_forcedFlush_1274_ = lean_ctor_get_uint8(v___y_1266_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1275_ = lean_ctor_get_uint8(v___y_1266_, sizeof(void*)*6 + 2);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___y_1266_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1277_ = v___y_1266_;
v_isShared_1278_ = v_isSharedCheck_1299_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_instant_1272_);
lean_inc(v_error_1271_);
lean_inc(v_events_1270_);
lean_inc(v_config_1269_);
lean_inc(v_writer_1267_);
lean_inc(v_reader_1268_);
lean_dec(v___y_1266_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1299_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_userData_1279_; lean_object* v_outputData_1280_; lean_object* v_knownSize_1281_; lean_object* v_messageHead_1282_; uint8_t v_sentMessage_1283_; uint8_t v_userClosedBody_1284_; uint8_t v_omitBody_1285_; lean_object* v_userDataBytes_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1297_; 
v_userData_1279_ = lean_ctor_get(v_writer_1267_, 0);
v_outputData_1280_ = lean_ctor_get(v_writer_1267_, 1);
v_knownSize_1281_ = lean_ctor_get(v_writer_1267_, 3);
v_messageHead_1282_ = lean_ctor_get(v_writer_1267_, 4);
v_sentMessage_1283_ = lean_ctor_get_uint8(v_writer_1267_, sizeof(void*)*6);
v_userClosedBody_1284_ = lean_ctor_get_uint8(v_writer_1267_, sizeof(void*)*6 + 1);
v_omitBody_1285_ = lean_ctor_get_uint8(v_writer_1267_, sizeof(void*)*6 + 2);
v_userDataBytes_1286_ = lean_ctor_get(v_writer_1267_, 5);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_writer_1267_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_writer_1267_, 2);
lean_dec(v_unused_1298_);
v___x_1288_ = v_writer_1267_;
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_userDataBytes_1286_);
lean_inc(v_messageHead_1282_);
lean_inc(v_knownSize_1281_);
lean_inc(v_outputData_1280_);
lean_inc(v_userData_1279_);
lean_dec(v_writer_1267_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(2);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 2, v___x_1290_);
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_userData_1279_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_outputData_1280_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_knownSize_1281_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_messageHead_1282_);
lean_ctor_set(v_reuseFailAlloc_1296_, 5, v_userDataBytes_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*6, v_sentMessage_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*6 + 1, v_userClosedBody_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*6 + 2, v_omitBody_1285_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1292_);
v___x_1294_ = v___x_1277_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_reader_1268_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_config_1269_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_events_1270_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_error_1271_);
lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_instant_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*6, v_keepAlive_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*6 + 1, v_forcedFlush_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*6 + 2, v_pullBodyStalled_1275_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
v___y_1252_ = v___x_1294_;
v_omitBody_1253_ = v_omitBody_1285_;
goto v___jp_1251_;
}
}
}
}
}
v___jp_1300_:
{
lean_object* v_writer_1302_; uint8_t v_omitBody_1303_; 
v_writer_1302_ = lean_ctor_get(v___y_1301_, 1);
v_omitBody_1303_ = lean_ctor_get_uint8(v_writer_1302_, sizeof(void*)*6 + 2);
v___y_1252_ = v___y_1301_;
v_omitBody_1253_ = v_omitBody_1303_;
goto v___jp_1251_;
}
v___jp_1304_:
{
if (v___y_1308_ == 0)
{
v___y_1266_ = v___y_1307_;
goto v___jp_1265_;
}
else
{
if (v___y_1306_ == 0)
{
v___y_1301_ = v___y_1307_;
goto v___jp_1300_;
}
else
{
if (v___y_1305_ == 0)
{
v___y_1266_ = v___y_1307_;
goto v___jp_1265_;
}
else
{
v___y_1301_ = v___y_1307_;
goto v___jp_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v___y_1440_, lean_object* v_body_1441_, lean_object* v_close_1442_, lean_object* v_isClosed_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v___y_1440_, v_body_1441_, v_close_1442_, v_isClosed_1443_, v_x_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_body_1447_, lean_object* v_close_1448_, lean_object* v_isClosed_1449_, lean_object* v_config_1450_, lean_object* v_line_1451_, lean_object* v_machine_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v___y_1456_; 
if (lean_obj_tag(v_x_1453_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_machine_1452_);
lean_dec_ref(v_line_1451_);
lean_dec_ref(v_isClosed_1449_);
lean_dec_ref(v_close_1448_);
lean_dec(v_body_1447_);
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
lean_object* v___f_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___f_1457_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1457_, 0, v___y_1456_);
lean_closure_set(v___f_1457_, 1, v_body_1447_);
lean_closure_set(v___f_1457_, 2, v_close_1448_);
lean_closure_set(v___f_1457_, 3, v_isClosed_1449_);
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = 0;
v___x_1460_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1450_, v_line_1451_);
v___x_1461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1458_, v___x_1459_, v___x_1460_, v___f_1457_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_body_1504_, lean_object* v_close_1505_, lean_object* v_isClosed_1506_, lean_object* v_config_1507_, lean_object* v_line_1508_, lean_object* v_machine_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_body_1504_, v_close_1505_, v_isClosed_1506_, v_config_1507_, v_line_1508_, v_machine_1509_, v_x_1510_);
lean_dec_ref(v_config_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1513_, lean_object* v_config_1514_, lean_object* v_machine_1515_, lean_object* v_res_1516_){
_start:
{
lean_object* v_close_1518_; lean_object* v_isClosed_1519_; lean_object* v_getKnownSize_1520_; lean_object* v_line_1521_; lean_object* v_body_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
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
v___f_1523_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_1523_, 0, v_body_1522_);
lean_closure_set(v___f_1523_, 1, v_close_1518_);
lean_closure_set(v___f_1523_, 2, v_isClosed_1519_);
lean_closure_set(v___f_1523_, 3, v_config_1514_);
lean_closure_set(v___f_1523_, 4, v_line_1521_);
lean_closure_set(v___f_1523_, 5, v_machine_1515_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = 0;
v___x_1526_ = lean_apply_2(v_getKnownSize_1520_, v_body_1522_, lean_box(0));
v___x_1527_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1524_, v___x_1525_, v___x_1526_, v___f_1523_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1559_, lean_object* v_x_1560_){
_start:
{
if (lean_obj_tag(v_x_1560_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v___x_1559_);
v_a_1562_ = lean_ctor_get(v_x_1560_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_x_1560_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1564_ = v_x_1560_;
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v_x_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
}
else
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1560_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_x_1560_, 0);
lean_dec(v_unused_1580_);
v___x_1572_ = v_x_1560_;
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_x_1560_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1559_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1574_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1581_, v_x_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_pendingProducer_1593_; lean_object* v_pendingConsumer_1594_; lean_object* v_interestWaiter_1595_; uint8_t v_closed_1596_; lean_object* v_pendingIncompleteChunk_1597_; lean_object* v_closeError_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1607_; 
v___x_1592_ = lean_st_ref_take(v___y_1590_);
v_pendingProducer_1593_ = lean_ctor_get(v___x_1592_, 0);
v_pendingConsumer_1594_ = lean_ctor_get(v___x_1592_, 1);
v_interestWaiter_1595_ = lean_ctor_get(v___x_1592_, 2);
v_closed_1596_ = lean_ctor_get_uint8(v___x_1592_, sizeof(void*)*6);
v_pendingIncompleteChunk_1597_ = lean_ctor_get(v___x_1592_, 4);
v_closeError_1598_ = lean_ctor_get(v___x_1592_, 5);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1592_, 3);
lean_dec(v_unused_1608_);
v___x_1600_ = v___x_1592_;
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_closeError_1598_);
lean_inc(v_pendingIncompleteChunk_1597_);
lean_inc(v_interestWaiter_1595_);
lean_inc(v_pendingConsumer_1594_);
lean_inc(v_pendingProducer_1593_);
lean_dec(v___x_1592_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 3, v___x_1589_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_pendingProducer_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_pendingConsumer_1594_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_interestWaiter_1595_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_pendingIncompleteChunk_1597_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v_closeError_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*6, v_closed_1596_);
v___x_1603_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_st_ref_put(v___y_1590_, v___x_1603_);
v___x_1605_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1609_, v___y_1610_);
lean_dec(v___y_1610_);
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
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = l_Std_Http_Body_Stream_close(v_requestStream_1661_);
v___x_1679_ = lean_unbox(v_a_1675_);
lean_dec(v_a_1675_);
v___x_1680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1677_, v___x_1679_, v___x_1678_, v___f_1662_);
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
v___x_1689_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1689_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
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
lean_object* v_machine_1725_; lean_object* v_requestStream_1726_; lean_object* v_keepAliveTimeout_1727_; lean_object* v_currentTimeout_1728_; lean_object* v_headerTimeout_1729_; lean_object* v_response_1730_; lean_object* v_respStream_1731_; lean_object* v_expectData_1732_; uint8_t v_handlerDispatched_1733_; lean_object* v___x_1734_; lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_4870__overap_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
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
v___x_1734_ = lean_box(v_handlerDispatched_1733_);
v___f_1735_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1735_, 0, v_machine_1725_);
lean_closure_set(v___f_1735_, 1, v_requestStream_1726_);
lean_closure_set(v___f_1735_, 2, v_keepAliveTimeout_1727_);
lean_closure_set(v___f_1735_, 3, v_currentTimeout_1728_);
lean_closure_set(v___f_1735_, 4, v_headerTimeout_1729_);
lean_closure_set(v___f_1735_, 5, v_response_1730_);
lean_closure_set(v___f_1735_, 6, v_respStream_1731_);
lean_closure_set(v___f_1735_, 7, v_expectData_1732_);
lean_closure_set(v___f_1735_, 8, v___x_1734_);
lean_inc_ref(v___f_1735_);
v___f_1736_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1736_, 0, v___f_1735_);
v___f_1737_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1737_, 0, v_requestStream_1726_);
lean_closure_set(v___f_1737_, 1, v___f_1736_);
lean_closure_set(v___f_1737_, 2, v___f_1735_);
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = 0;
v___x_1740_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1741_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1742_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1743_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1744_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1744_, 0, lean_box(0));
lean_closure_set(v___x_1744_, 1, lean_box(0));
lean_closure_set(v___x_1744_, 2, v___x_1740_);
lean_closure_set(v___x_1744_, 3, lean_box(0));
lean_closure_set(v___x_1744_, 4, lean_box(0));
lean_closure_set(v___x_1744_, 5, v___x_1743_);
lean_closure_set(v___x_1744_, 6, v___f_1713_);
v___x_4870__overap_1745_ = l_Std_Mutex_atomically___redArg(v___x_1740_, v___f_1741_, v___f_1742_, v_requestStream_1726_, v___x_1744_);
v___x_1746_ = lean_apply_1(v___x_4870__overap_1745_, lean_box(0));
v___x_1747_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1738_, v___x_1739_, v___x_1746_, v___f_1737_);
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
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = l_Std_Http_Body_Stream_close(v_requestStream_1779_);
v___x_1800_ = lean_unbox(v_a_1793_);
lean_dec(v_a_1793_);
v___x_1801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1798_, v___x_1800_, v___x_1799_, v___f_1780_);
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
lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1876_ = lean_box(v_requiresData_1858_);
v___f_1877_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1877_, 0, v_config_1856_);
lean_closure_set(v___f_1877_, 1, v_machine_1857_);
lean_closure_set(v___f_1877_, 2, v_a_1872_);
lean_closure_set(v___f_1877_, 3, v___x_1876_);
lean_closure_set(v___f_1877_, 4, v_expectData_1859_);
lean_closure_set(v___f_1877_, 5, v_pendingHead_1860_);
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = 0;
v___x_1881_ = l_Std_CloseableChannel_new___redArg(v___x_1878_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
v___x_1885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1879_, v___x_1880_, v___x_1884_, v___f_1877_);
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
lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = 0;
v___x_1902_ = l_Std_Http_Body_mkStream();
v___x_1903_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1900_, v___x_1901_, v___x_1902_, v___f_1897_);
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
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_apply_2(v_close_1908_, v_val_1909_, lean_box(0));
v___x_1927_ = lean_unbox(v_a_1923_);
lean_dec(v_a_1923_);
v___x_1928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1925_, v___x_1927_, v___x_1926_, v___f_1910_);
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
lean_object* v_val_1944_; lean_object* v_close_1945_; lean_object* v_isClosed_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_val_1944_ = lean_ctor_get(v_respStream_1938_, 0);
lean_inc_n(v_val_1944_, 2);
lean_dec_ref_known(v_respStream_1938_, 1);
v_close_1945_ = lean_ctor_get(v_inst_1939_, 1);
lean_inc_ref(v_close_1945_);
v_isClosed_1946_ = lean_ctor_get(v_inst_1939_, 2);
lean_inc_ref(v_isClosed_1946_);
lean_dec_ref(v_inst_1939_);
v___f_1947_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1947_, 0, v_close_1945_);
lean_closure_set(v___f_1947_, 1, v_val_1944_);
lean_closure_set(v___f_1947_, 2, v___f_1940_);
lean_closure_set(v___f_1947_, 3, v___f_1941_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = 0;
v___x_1950_ = lean_apply_2(v_isClosed_1946_, v_val_1944_, lean_box(0));
v___x_1951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1948_, v___x_1949_, v___x_1950_, v___f_1947_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_2031_, lean_object* v_inst_2032_, lean_object* v___f_2033_, lean_object* v_handler_2034_, lean_object* v___f_2035_, lean_object* v_inst_2036_, lean_object* v___f_2037_, lean_object* v_connectionContext_2038_, lean_object* v_a_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_){
_start:
{
switch(lean_obj_tag(v_a_2039_))
{
case 0:
{
lean_object* v_head_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_inst_2036_);
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
lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___x_5061__overap_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___f_2066_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2066_, 0, v___x_2062_);
v___f_2067_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2067_, 0, v___x_2065_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = 0;
v___x_2070_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2071_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2072_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_2073_ = l_Std_Mutex_atomically___redArg(v___x_2070_, v___f_2071_, v___f_2072_, v_requestStream_2048_, v___f_2067_);
v___x_2074_ = lean_apply_1(v___x_5061__overap_2073_, lean_box(0));
v___x_2075_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2068_, v___x_2069_, v___x_2074_, v___f_2066_);
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
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_inst_2036_);
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
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_inst_2036_);
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
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2120_ = lean_mk_io_user_error(v___y_2119_);
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = 0;
v___x_2123_ = lean_apply_3(v_onFailure_2116_, v_handler_2034_, v___x_2120_, lean_box(0));
v___x_2124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2121_, v___x_2122_, v___x_2123_, v___f_2117_);
return v___x_2124_;
}
}
case 4:
{
lean_object* v_requestStream_2139_; lean_object* v___f_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_5118__overap_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_connectionContext_2038_);
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec(v_handler_2034_);
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_config_2031_);
v_requestStream_2139_ = lean_ctor_get(v___y_2041_, 1);
lean_inc_ref_n(v_requestStream_2139_, 2);
lean_inc_ref(v___y_2041_);
v___f_2140_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2140_, 0, v___y_2041_);
v___f_2141_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2141_, 0, v_requestStream_2139_);
lean_closure_set(v___f_2141_, 1, v___f_2140_);
lean_closure_set(v___f_2141_, 2, v___y_2041_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = 0;
v___x_2144_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2145_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2146_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2147_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2148_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2148_, 0, lean_box(0));
lean_closure_set(v___x_2148_, 1, lean_box(0));
lean_closure_set(v___x_2148_, 2, v___x_2144_);
lean_closure_set(v___x_2148_, 3, lean_box(0));
lean_closure_set(v___x_2148_, 4, lean_box(0));
lean_closure_set(v___x_2148_, 5, v___x_2147_);
lean_closure_set(v___x_2148_, 6, v___f_2035_);
v___x_5118__overap_2149_ = l_Std_Mutex_atomically___redArg(v___x_2144_, v___f_2145_, v___f_2146_, v_requestStream_2139_, v___x_2148_);
v___x_2150_ = lean_apply_1(v___x_5118__overap_2149_, lean_box(0));
v___x_2151_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2142_, v___x_2143_, v___x_2150_, v___f_2141_);
return v___x_2151_;
}
case 6:
{
lean_object* v_machine_2152_; lean_object* v_requestStream_2153_; lean_object* v_respStream_2154_; uint8_t v_requiresData_2155_; lean_object* v_expectData_2156_; lean_object* v_pendingHead_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___f_2163_; lean_object* v___f_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_5143__overap_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
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
v___x_2158_ = lean_box(v_requiresData_2155_);
v___f_2159_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2159_, 0, v_config_2031_);
lean_closure_set(v___f_2159_, 1, v_machine_2152_);
lean_closure_set(v___f_2159_, 2, v___x_2158_);
lean_closure_set(v___f_2159_, 3, v_expectData_2156_);
lean_closure_set(v___f_2159_, 4, v_pendingHead_2157_);
v___f_2160_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2160_, 0, v___f_2159_);
lean_inc_ref(v___f_2160_);
v___f_2161_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2161_, 0, v___f_2160_);
v___f_2162_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2162_, 0, v_respStream_2154_);
lean_closure_set(v___f_2162_, 1, v_inst_2036_);
lean_closure_set(v___f_2162_, 2, v___f_2161_);
lean_closure_set(v___f_2162_, 3, v___f_2160_);
lean_inc_ref(v___f_2162_);
v___f_2163_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2163_, 0, v___f_2162_);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2164_, 0, v_requestStream_2153_);
lean_closure_set(v___f_2164_, 1, v___f_2163_);
lean_closure_set(v___f_2164_, 2, v___f_2162_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = 0;
v___x_2167_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2168_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2169_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2170_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2171_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2171_, 0, lean_box(0));
lean_closure_set(v___x_2171_, 1, lean_box(0));
lean_closure_set(v___x_2171_, 2, v___x_2167_);
lean_closure_set(v___x_2171_, 3, lean_box(0));
lean_closure_set(v___x_2171_, 4, lean_box(0));
lean_closure_set(v___x_2171_, 5, v___x_2170_);
lean_closure_set(v___x_2171_, 6, v___f_2037_);
v___x_5143__overap_2172_ = l_Std_Mutex_atomically___redArg(v___x_2167_, v___f_2168_, v___f_2169_, v_requestStream_2153_, v___x_2171_);
v___x_2173_ = lean_apply_1(v___x_5143__overap_2172_, lean_box(0));
v___x_2174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2165_, v___x_2166_, v___x_2173_, v___f_2164_);
return v___x_2174_;
}
case 7:
{
lean_object* v_pendingHead_2175_; 
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2033_);
v_pendingHead_2175_ = lean_ctor_get(v___y_2041_, 8);
if (lean_obj_tag(v_pendingHead_2175_) == 1)
{
lean_object* v_machine_2176_; lean_object* v_requestStream_2177_; lean_object* v_keepAliveTimeout_2178_; lean_object* v_currentTimeout_2179_; lean_object* v_headerTimeout_2180_; lean_object* v_response_2181_; lean_object* v_respStream_2182_; uint8_t v_requiresData_2183_; lean_object* v_expectData_2184_; uint8_t v_handlerDispatched_2185_; lean_object* v_val_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
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
v___x_2187_ = lean_box(v_requiresData_2183_);
v___x_2188_ = lean_box(v_handlerDispatched_2185_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2189_, 0, v_requestStream_2177_);
lean_closure_set(v___f_2189_, 1, v_keepAliveTimeout_2178_);
lean_closure_set(v___f_2189_, 2, v_currentTimeout_2179_);
lean_closure_set(v___f_2189_, 3, v_headerTimeout_2180_);
lean_closure_set(v___f_2189_, 4, v_response_2181_);
lean_closure_set(v___f_2189_, 5, v_respStream_2182_);
lean_closure_set(v___f_2189_, 6, v___x_2187_);
lean_closure_set(v___f_2189_, 7, v_expectData_2184_);
lean_closure_set(v___f_2189_, 8, v___x_2188_);
lean_closure_set(v___f_2189_, 9, v_pendingHead_2175_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = 0;
v___x_2192_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2032_, v_handler_2034_, v_machine_2176_, v_val_2186_, v_config_2031_, v_connectionContext_2038_);
v___x_2193_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2190_, v___x_2191_, v___x_2192_, v___f_2189_);
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
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_inst_2036_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2200_, lean_object* v_inst_2201_, lean_object* v___f_2202_, lean_object* v_handler_2203_, lean_object* v___f_2204_, lean_object* v_inst_2205_, lean_object* v___f_2206_, lean_object* v_connectionContext_2207_, lean_object* v_a_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2200_, v_inst_2201_, v___f_2202_, v_handler_2203_, v___f_2204_, v_inst_2205_, v___f_2206_, v_connectionContext_2207_, v_a_2208_, v_x_2209_, v___y_2210_);
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
lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___f_2231_; lean_object* v___x_2232_; size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_4072__overap_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___f_2229_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2230_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2230_, 0, v_config_2224_);
lean_closure_set(v___f_2230_, 1, v_inst_2221_);
lean_closure_set(v___f_2230_, 2, v___f_2229_);
lean_closure_set(v___f_2230_, 3, v_handler_2223_);
lean_closure_set(v___f_2230_, 4, v___f_2229_);
lean_closure_set(v___f_2230_, 5, v_inst_2222_);
lean_closure_set(v___f_2230_, 6, v___f_2229_);
lean_closure_set(v___f_2230_, 7, v_connectionContext_2225_);
v___f_2231_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2232_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2233_ = lean_array_size(v_events_2226_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = 0;
v___x_4072__overap_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2232_, v_events_2226_, v___f_2230_, v_sz_2233_, v___x_2234_, v_state_2227_);
v___x_2238_ = lean_apply_1(v___x_4072__overap_2237_, lean_box(0));
v___x_2239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2235_, v___x_2236_, v___x_2238_, v___f_2231_);
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
lean_object* v_onRequest_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v_onRequest_2381_ = lean_ctor_get(v_inst_2358_, 1);
lean_inc_ref(v_onRequest_2381_);
lean_dec_ref(v_inst_2358_);
v___f_2382_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2383_ = lean_box(v_requiresData_2375_);
lean_inc_ref(v_response_2373_);
lean_inc_ref(v_requestStream_2369_);
v___f_2384_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2384_, 0, v_machine_2368_);
lean_closure_set(v___f_2384_, 1, v_requestStream_2369_);
lean_closure_set(v___f_2384_, 2, v_keepAliveTimeout_2370_);
lean_closure_set(v___f_2384_, 3, v_currentTimeout_2371_);
lean_closure_set(v___f_2384_, 4, v_headerTimeout_2372_);
lean_closure_set(v___f_2384_, 5, v_response_2373_);
lean_closure_set(v___f_2384_, 6, v_respStream_2374_);
lean_closure_set(v___f_2384_, 7, v___x_2383_);
lean_closure_set(v___f_2384_, 8, v_expectData_2376_);
v___x_2385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2385_, 0, v_val_2377_);
lean_ctor_set(v___x_2385_, 1, v_requestStream_2369_);
lean_ctor_set(v___x_2385_, 2, v_extensions_2360_);
v___x_2386_ = lean_apply_3(v_onRequest_2381_, v_handler_2359_, v___x_2385_, v_connectionContext_2361_);
v___x_2387_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2367_);
v___f_2388_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2388_, 0, v_toFunctor_2367_);
lean_closure_set(v___f_2388_, 1, v_response_2373_);
lean_closure_set(v___f_2388_, 2, v___x_2387_);
lean_closure_set(v___f_2388_, 3, v___f_2384_);
v___x_2389_ = 0;
v___x_2390_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2390_, 0, lean_box(0));
lean_closure_set(v___x_2390_, 1, v___x_2386_);
v___x_2391_ = lean_io_as_task(v___x_2390_, v___x_2387_);
v___x_2392_ = 1;
v___x_2393_ = lean_task_bind(v___x_2391_, v___f_2382_, v___x_2387_, v___x_2392_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2393_);
v___x_2395_ = v___x_2379_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
v___x_2397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2387_, v___x_2389_, v___x_2396_, v___f_2388_);
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
lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec_ref(v___f_2480_);
lean_dec_ref(v_machine_2477_);
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = 0;
v___x_2511_ = lean_apply_2(v_isClosed_2478_, v_body_2476_, lean_box(0));
v___x_2512_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2509_, v___x_2510_, v___x_2511_, v___f_2479_);
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
v___x_2555_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
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
lean_object* v_close_2575_; lean_object* v_isClosed_2576_; lean_object* v_tryRecv_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_close_2575_ = lean_ctor_get(v_inst_2571_, 1);
lean_inc_ref(v_close_2575_);
v_isClosed_2576_ = lean_ctor_get(v_inst_2571_, 2);
lean_inc_ref(v_isClosed_2576_);
v_tryRecv_2577_ = lean_ctor_get(v_inst_2571_, 4);
lean_inc_ref(v_tryRecv_2577_);
lean_dec_ref(v_inst_2571_);
lean_inc_ref(v_machine_2572_);
v___f_2578_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2578_, 0, v_machine_2572_);
lean_inc_ref(v___f_2578_);
v___f_2579_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2579_, 0, v___f_2578_);
lean_inc_n(v_body_2573_, 2);
v___f_2580_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2580_, 0, v_close_2575_);
lean_closure_set(v___f_2580_, 1, v_body_2573_);
lean_closure_set(v___f_2580_, 2, v___f_2579_);
lean_closure_set(v___f_2580_, 3, v___f_2578_);
v___f_2581_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2582_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2582_, 0, v_body_2573_);
lean_closure_set(v___f_2582_, 1, v_machine_2572_);
lean_closure_set(v___f_2582_, 2, v_isClosed_2576_);
lean_closure_set(v___f_2582_, 3, v___f_2580_);
lean_closure_set(v___f_2582_, 4, v___f_2581_);
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = 0;
v___x_2585_ = lean_apply_2(v_tryRecv_2577_, v_body_2573_, lean_box(0));
v___x_2586_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2583_, v___x_2584_, v___x_2585_, v___f_2582_);
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
lean_object* v_machine_2614_; lean_object* v_requestStream_2615_; lean_object* v_keepAliveTimeout_2616_; lean_object* v_currentTimeout_2617_; lean_object* v_headerTimeout_2618_; lean_object* v_response_2619_; lean_object* v_respStream_2620_; uint8_t v_requiresData_2621_; lean_object* v_expectData_2622_; uint8_t v_handlerDispatched_2623_; lean_object* v_pendingHead_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2706_; 
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
v_isSharedCheck_2706_ = !lean_is_exclusive(v_st_2612_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2626_ = v_st_2612_;
v_isShared_2627_ = v_isSharedCheck_2706_;
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
v_isShared_2627_ = v_isSharedCheck_2706_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___y_2629_; lean_object* v_reader_2638_; lean_object* v_state_2639_; 
v_reader_2638_ = lean_ctor_get(v_machine_2614_, 0);
lean_inc_ref(v_reader_2638_);
v_state_2639_ = lean_ctor_get(v_reader_2638_, 0);
lean_inc(v_state_2639_);
if (lean_obj_tag(v_state_2639_) == 6)
{
lean_dec_ref(v_reader_2638_);
lean_dec_ref(v_val_2610_);
v___y_2629_ = v_machine_2614_;
goto v___jp_2628_;
}
else
{
if (lean_obj_tag(v_state_2639_) == 7)
{
lean_dec_ref_known(v_state_2639_, 1);
lean_dec_ref(v_reader_2638_);
lean_dec_ref(v_val_2610_);
v___y_2629_ = v_machine_2614_;
goto v___jp_2628_;
}
else
{
lean_object* v_input_2640_; lean_object* v_writer_2641_; lean_object* v_config_2642_; lean_object* v_events_2643_; lean_object* v_error_2644_; lean_object* v_instant_2645_; uint8_t v_keepAlive_2646_; uint8_t v_forcedFlush_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2704_; 
v_input_2640_ = lean_ctor_get(v_reader_2638_, 1);
lean_inc_ref(v_input_2640_);
v_writer_2641_ = lean_ctor_get(v_machine_2614_, 1);
v_config_2642_ = lean_ctor_get(v_machine_2614_, 2);
v_events_2643_ = lean_ctor_get(v_machine_2614_, 3);
v_error_2644_ = lean_ctor_get(v_machine_2614_, 4);
v_instant_2645_ = lean_ctor_get(v_machine_2614_, 5);
v_keepAlive_2646_ = lean_ctor_get_uint8(v_machine_2614_, sizeof(void*)*6);
v_forcedFlush_2647_ = lean_ctor_get_uint8(v_machine_2614_, sizeof(void*)*6 + 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_machine_2614_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_machine_2614_, 0);
lean_dec(v_unused_2705_);
v___x_2649_ = v_machine_2614_;
v_isShared_2650_ = v_isSharedCheck_2704_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_instant_2645_);
lean_inc(v_error_2644_);
lean_inc(v_events_2643_);
lean_inc(v_config_2642_);
lean_inc(v_writer_2641_);
lean_dec(v_machine_2614_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2704_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_messageHead_2651_; lean_object* v_messageCount_2652_; lean_object* v_bodyBytesRead_2653_; lean_object* v_headerBytesRead_2654_; uint8_t v_noMoreInput_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2701_; 
v_messageHead_2651_ = lean_ctor_get(v_reader_2638_, 2);
v_messageCount_2652_ = lean_ctor_get(v_reader_2638_, 3);
v_bodyBytesRead_2653_ = lean_ctor_get(v_reader_2638_, 4);
v_headerBytesRead_2654_ = lean_ctor_get(v_reader_2638_, 5);
v_noMoreInput_2655_ = lean_ctor_get_uint8(v_reader_2638_, sizeof(void*)*6);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_reader_2638_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; 
v_unused_2702_ = lean_ctor_get(v_reader_2638_, 1);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_reader_2638_, 0);
lean_dec(v_unused_2703_);
v___x_2657_ = v_reader_2638_;
v_isShared_2658_ = v_isSharedCheck_2701_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_headerBytesRead_2654_);
lean_inc(v_bodyBytesRead_2653_);
lean_inc(v_messageCount_2652_);
lean_inc(v_messageHead_2651_);
lean_dec(v_reader_2638_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2701_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_array_2659_; lean_object* v_idx_2660_; uint8_t v___x_2661_; lean_object* v___y_2663_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_array_2659_ = lean_ctor_get(v_input_2640_, 0);
lean_inc_ref(v_array_2659_);
v_idx_2660_ = lean_ctor_get(v_input_2640_, 1);
lean_inc(v_idx_2660_);
lean_dec_ref(v_input_2640_);
v___x_2661_ = 0;
v___x_2692_ = lean_byte_array_size(v_array_2659_);
v___x_2693_ = lean_nat_dec_le(v___x_2692_, v_idx_2660_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2694_ = l_ByteArray_extract(v_array_2659_, v_idx_2660_, v___x_2692_);
lean_dec_ref(v_array_2659_);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_byte_array_size(v___x_2694_);
v___x_2697_ = lean_byte_array_size(v_val_2610_);
v___x_2698_ = lean_byte_array_copy_slice(v_val_2610_, v___x_2695_, v___x_2694_, v___x_2696_, v___x_2697_, v___x_2693_);
lean_dec_ref(v_val_2610_);
v___x_2699_ = l_ByteArray_mkIterator(v___x_2698_);
v___y_2663_ = v___x_2699_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2700_; 
lean_dec(v_idx_2660_);
lean_dec_ref(v_array_2659_);
v___x_2700_ = l_ByteArray_mkIterator(v_val_2610_);
v___y_2663_ = v___x_2700_;
goto v___jp_2662_;
}
v___jp_2662_:
{
lean_object* v_maxHeaderBytes_2664_; lean_object* v_maxStartLineLength_2665_; lean_object* v_maxChunkLineLength_2666_; lean_object* v_maxBodySize_2667_; lean_object* v_array_2668_; lean_object* v_idx_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_maxHeaderBytes_2664_ = lean_ctor_get(v_config_2642_, 2);
v_maxStartLineLength_2665_ = lean_ctor_get(v_config_2642_, 5);
v_maxChunkLineLength_2666_ = lean_ctor_get(v_config_2642_, 13);
v_maxBodySize_2667_ = lean_ctor_get(v_config_2642_, 15);
v_array_2668_ = lean_ctor_get(v___y_2663_, 0);
v_idx_2669_ = lean_ctor_get(v___y_2663_, 1);
v___x_2670_ = lean_nat_add(v_maxBodySize_2667_, v_maxHeaderBytes_2664_);
v___x_2671_ = lean_nat_add(v___x_2670_, v_maxStartLineLength_2665_);
lean_dec(v___x_2670_);
v___x_2672_ = lean_nat_add(v___x_2671_, v_maxChunkLineLength_2666_);
lean_dec(v___x_2671_);
v___x_2673_ = lean_byte_array_size(v_array_2668_);
v___x_2674_ = lean_nat_sub(v___x_2673_, v_idx_2669_);
v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2674_);
lean_dec(v___x_2674_);
lean_dec(v___x_2672_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2677_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___y_2663_);
v___x_2677_ = v___x_2657_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_state_2639_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___y_2663_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v_messageHead_2651_);
lean_ctor_set(v_reuseFailAlloc_2681_, 3, v_messageCount_2652_);
lean_ctor_set(v_reuseFailAlloc_2681_, 4, v_bodyBytesRead_2653_);
lean_ctor_set(v_reuseFailAlloc_2681_, 5, v_headerBytesRead_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2681_, sizeof(void*)*6, v_noMoreInput_2655_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v_machine_2679_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2677_);
v_machine_2679_ = v___x_2649_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_writer_2641_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_config_2642_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_events_2643_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_error_2644_);
lean_ctor_set(v_reuseFailAlloc_2680_, 5, v_instant_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2680_, sizeof(void*)*6, v_keepAlive_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2680_, sizeof(void*)*6 + 1, v_forcedFlush_2647_);
v_machine_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_ctor_set_uint8(v_machine_2679_, sizeof(void*)*6 + 2, v___x_2661_);
v___y_2629_ = v_machine_2679_;
goto v___jp_2628_;
}
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec(v_error_2644_);
lean_dec(v_state_2639_);
v___x_2682_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2683_ = lean_array_push(v_events_2643_, v___x_2682_);
v___x_2684_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___y_2663_);
lean_ctor_set(v___x_2657_, 0, v___x_2684_);
v___x_2686_ = v___x_2657_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___y_2663_);
lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_messageHead_2651_);
lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_messageCount_2652_);
lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_bodyBytesRead_2653_);
lean_ctor_set(v_reuseFailAlloc_2691_, 5, v_headerBytesRead_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2691_, sizeof(void*)*6, v_noMoreInput_2655_);
v___x_2686_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 4, v___x_2687_);
lean_ctor_set(v___x_2649_, 3, v___x_2683_);
lean_ctor_set(v___x_2649_, 0, v___x_2686_);
v___x_2689_ = v___x_2649_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_writer_2641_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_config_2642_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v_instant_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2690_, sizeof(void*)*6, v_keepAlive_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2690_, sizeof(void*)*6 + 1, v_forcedFlush_2647_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*6 + 2, v___x_2661_);
v___y_2629_ = v___x_2689_;
goto v___jp_2628_;
}
}
}
}
}
}
}
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2707_, lean_object* v_____r_2708_, lean_object* v_st_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2707_, v_____r_2708_, v_st_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2712_, lean_object* v_machine_2713_, lean_object* v_requestStream_2714_, lean_object* v_currentTimeout_2715_, lean_object* v_response_2716_, lean_object* v_respStream_2717_, uint8_t v_requiresData_2718_, lean_object* v_expectData_2719_, uint8_t v_handlerDispatched_2720_, lean_object* v_pendingHead_2721_, lean_object* v___f_2722_, lean_object* v_x_2723_){
_start:
{
if (lean_obj_tag(v_x_2723_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2733_; 
lean_dec_ref(v___f_2722_);
lean_dec(v_pendingHead_2721_);
lean_dec(v_expectData_2719_);
lean_dec(v_respStream_2717_);
lean_dec_ref(v_response_2716_);
lean_dec(v_currentTimeout_2715_);
lean_dec_ref(v_requestStream_2714_);
lean_dec_ref(v_machine_2713_);
v_a_2725_ = lean_ctor_get(v_x_2723_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_x_2723_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2727_ = v_x_2723_;
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v_x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; 
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v_headerTimeout_2735_; lean_object* v_second_2736_; lean_object* v_nano_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v_second_2741_; lean_object* v_nano_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v_nanos_2746_; lean_object* v___x_2747_; lean_object* v_nanos_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_a_2734_ = lean_ctor_get(v_x_2723_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v_x_2723_, 1);
v_headerTimeout_2735_ = lean_ctor_get(v_config_2712_, 6);
v_second_2736_ = lean_ctor_get(v_a_2734_, 0);
lean_inc(v_second_2736_);
v_nano_2737_ = lean_ctor_get(v_a_2734_, 1);
lean_inc(v_nano_2737_);
lean_dec(v_a_2734_);
v___x_2738_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2739_ = lean_int_mul(v_headerTimeout_2735_, v___x_2738_);
v___x_2740_ = l_Std_Time_Duration_ofNanoseconds(v___x_2739_);
lean_dec(v___x_2739_);
v_second_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_second_2741_);
v_nano_2742_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_nano_2742_);
lean_dec_ref(v___x_2740_);
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2745_ = lean_int_mul(v_second_2736_, v___x_2744_);
lean_dec(v_second_2736_);
v_nanos_2746_ = lean_int_add(v___x_2745_, v_nano_2737_);
lean_dec(v_nano_2737_);
lean_dec(v___x_2745_);
v___x_2747_ = lean_int_mul(v_second_2741_, v___x_2744_);
lean_dec(v_second_2741_);
v_nanos_2748_ = lean_int_add(v___x_2747_, v_nano_2742_);
lean_dec(v_nano_2742_);
lean_dec(v___x_2747_);
v___x_2749_ = lean_int_add(v_nanos_2746_, v_nanos_2748_);
lean_dec(v_nanos_2748_);
lean_dec(v_nanos_2746_);
v___x_2750_ = l_Std_Time_Duration_ofNanoseconds(v___x_2749_);
lean_dec(v___x_2749_);
v___x_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2752_, 0, v_machine_2713_);
lean_ctor_set(v___x_2752_, 1, v_requestStream_2714_);
lean_ctor_set(v___x_2752_, 2, v___x_2743_);
lean_ctor_set(v___x_2752_, 3, v_currentTimeout_2715_);
lean_ctor_set(v___x_2752_, 4, v___x_2751_);
lean_ctor_set(v___x_2752_, 5, v_response_2716_);
lean_ctor_set(v___x_2752_, 6, v_respStream_2717_);
lean_ctor_set(v___x_2752_, 7, v_expectData_2719_);
lean_ctor_set(v___x_2752_, 8, v_pendingHead_2721_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*9, v_requiresData_2718_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*9 + 1, v_handlerDispatched_2720_);
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_apply_3(v___f_2722_, v___x_2753_, v___x_2752_, lean_box(0));
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2755_, lean_object* v_machine_2756_, lean_object* v_requestStream_2757_, lean_object* v_currentTimeout_2758_, lean_object* v_response_2759_, lean_object* v_respStream_2760_, lean_object* v_requiresData_2761_, lean_object* v_expectData_2762_, lean_object* v_handlerDispatched_2763_, lean_object* v_pendingHead_2764_, lean_object* v___f_2765_, lean_object* v_x_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v_requiresData_boxed_2768_; uint8_t v_handlerDispatched_boxed_2769_; lean_object* v_res_2770_; 
v_requiresData_boxed_2768_ = lean_unbox(v_requiresData_2761_);
v_handlerDispatched_boxed_2769_ = lean_unbox(v_handlerDispatched_2763_);
v_res_2770_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2755_, v_machine_2756_, v_requestStream_2757_, v_currentTimeout_2758_, v_response_2759_, v_respStream_2760_, v_requiresData_boxed_2768_, v_expectData_2762_, v_handlerDispatched_boxed_2769_, v_pendingHead_2764_, v___f_2765_, v_x_2766_);
lean_dec_ref(v_config_2755_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2771_, lean_object* v_requestStream_2772_, lean_object* v_keepAliveTimeout_2773_, lean_object* v_currentTimeout_2774_, lean_object* v_headerTimeout_2775_, lean_object* v_response_2776_, uint8_t v_requiresData_2777_, lean_object* v_expectData_2778_, uint8_t v_handlerDispatched_2779_, lean_object* v_pendingHead_2780_, lean_object* v_____r_2781_){
_start:
{
lean_object* v_writer_2783_; lean_object* v_reader_2784_; lean_object* v_config_2785_; lean_object* v_events_2786_; lean_object* v_error_2787_; lean_object* v_instant_2788_; uint8_t v_keepAlive_2789_; uint8_t v_forcedFlush_2790_; uint8_t v_pullBodyStalled_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2821_; 
v_writer_2783_ = lean_ctor_get(v_machine_2771_, 1);
v_reader_2784_ = lean_ctor_get(v_machine_2771_, 0);
v_config_2785_ = lean_ctor_get(v_machine_2771_, 2);
v_events_2786_ = lean_ctor_get(v_machine_2771_, 3);
v_error_2787_ = lean_ctor_get(v_machine_2771_, 4);
v_instant_2788_ = lean_ctor_get(v_machine_2771_, 5);
v_keepAlive_2789_ = lean_ctor_get_uint8(v_machine_2771_, sizeof(void*)*6);
v_forcedFlush_2790_ = lean_ctor_get_uint8(v_machine_2771_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2791_ = lean_ctor_get_uint8(v_machine_2771_, sizeof(void*)*6 + 2);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_machine_2771_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2793_ = v_machine_2771_;
v_isShared_2794_ = v_isSharedCheck_2821_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_instant_2788_);
lean_inc(v_error_2787_);
lean_inc(v_events_2786_);
lean_inc(v_config_2785_);
lean_inc(v_writer_2783_);
lean_inc(v_reader_2784_);
lean_dec(v_machine_2771_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2821_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_userData_2795_; lean_object* v_outputData_2796_; lean_object* v_state_2797_; lean_object* v_knownSize_2798_; lean_object* v_messageHead_2799_; uint8_t v_sentMessage_2800_; uint8_t v_omitBody_2801_; lean_object* v_userDataBytes_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2820_; 
v_userData_2795_ = lean_ctor_get(v_writer_2783_, 0);
v_outputData_2796_ = lean_ctor_get(v_writer_2783_, 1);
v_state_2797_ = lean_ctor_get(v_writer_2783_, 2);
v_knownSize_2798_ = lean_ctor_get(v_writer_2783_, 3);
v_messageHead_2799_ = lean_ctor_get(v_writer_2783_, 4);
v_sentMessage_2800_ = lean_ctor_get_uint8(v_writer_2783_, sizeof(void*)*6);
v_omitBody_2801_ = lean_ctor_get_uint8(v_writer_2783_, sizeof(void*)*6 + 2);
v_userDataBytes_2802_ = lean_ctor_get(v_writer_2783_, 5);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_writer_2783_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2804_ = v_writer_2783_;
v_isShared_2805_ = v_isSharedCheck_2820_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_userDataBytes_2802_);
lean_inc(v_messageHead_2799_);
lean_inc(v_knownSize_2798_);
lean_inc(v_state_2797_);
lean_inc(v_outputData_2796_);
lean_inc(v_userData_2795_);
lean_dec(v_writer_2783_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2820_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
uint8_t v___x_2806_; lean_object* v___x_2808_; 
v___x_2806_ = 1;
if (v_isShared_2805_ == 0)
{
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_userData_2795_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_outputData_2796_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_state_2797_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_knownSize_2798_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v_messageHead_2799_);
lean_ctor_set(v_reuseFailAlloc_2819_, 5, v_userDataBytes_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2819_, sizeof(void*)*6, v_sentMessage_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2819_, sizeof(void*)*6 + 2, v_omitBody_2801_);
v___x_2808_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2810_; 
lean_ctor_set_uint8(v___x_2808_, sizeof(void*)*6 + 1, v___x_2806_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 1, v___x_2808_);
v___x_2810_ = v___x_2793_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_reader_2784_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2818_, 2, v_config_2785_);
lean_ctor_set(v_reuseFailAlloc_2818_, 3, v_events_2786_);
lean_ctor_set(v_reuseFailAlloc_2818_, 4, v_error_2787_);
lean_ctor_set(v_reuseFailAlloc_2818_, 5, v_instant_2788_);
lean_ctor_set_uint8(v_reuseFailAlloc_2818_, sizeof(void*)*6, v_keepAlive_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2818_, sizeof(void*)*6 + 1, v_forcedFlush_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2818_, sizeof(void*)*6 + 2, v_pullBodyStalled_2791_);
v___x_2810_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v_requestStream_2772_);
lean_ctor_set(v___x_2812_, 2, v_keepAliveTimeout_2773_);
lean_ctor_set(v___x_2812_, 3, v_currentTimeout_2774_);
lean_ctor_set(v___x_2812_, 4, v_headerTimeout_2775_);
lean_ctor_set(v___x_2812_, 5, v_response_2776_);
lean_ctor_set(v___x_2812_, 6, v___x_2811_);
lean_ctor_set(v___x_2812_, 7, v_expectData_2778_);
lean_ctor_set(v___x_2812_, 8, v_pendingHead_2780_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*9, v_requiresData_2777_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*9 + 1, v_handlerDispatched_2779_);
v___x_2813_ = 0;
v___x_2814_ = lean_box(v___x_2813_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2812_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
return v___x_2817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2822_, lean_object* v_requestStream_2823_, lean_object* v_keepAliveTimeout_2824_, lean_object* v_currentTimeout_2825_, lean_object* v_headerTimeout_2826_, lean_object* v_response_2827_, lean_object* v_requiresData_2828_, lean_object* v_expectData_2829_, lean_object* v_handlerDispatched_2830_, lean_object* v_pendingHead_2831_, lean_object* v_____r_2832_, lean_object* v___y_2833_){
_start:
{
uint8_t v_requiresData_boxed_2834_; uint8_t v_handlerDispatched_boxed_2835_; lean_object* v_res_2836_; 
v_requiresData_boxed_2834_ = lean_unbox(v_requiresData_2828_);
v_handlerDispatched_boxed_2835_ = lean_unbox(v_handlerDispatched_2830_);
v_res_2836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2822_, v_requestStream_2823_, v_keepAliveTimeout_2824_, v_currentTimeout_2825_, v_headerTimeout_2826_, v_response_2827_, v_requiresData_boxed_2834_, v_expectData_2829_, v_handlerDispatched_boxed_2835_, v_pendingHead_2831_, v_____r_2832_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref(v___f_2837_);
v_a_2840_ = lean_ctor_get(v_x_2838_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_x_2838_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2842_ = v_x_2838_;
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v_x_2838_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v_x_2838_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v_x_2838_, 1);
v___x_2850_ = lean_apply_2(v___f_2837_, v_a_2849_, lean_box(0));
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2851_, lean_object* v_x_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2851_, v_x_2852_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2855_, lean_object* v_val_2856_, lean_object* v___f_2857_, lean_object* v___f_2858_, lean_object* v_x_2859_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v___f_2858_);
lean_dec_ref(v___f_2857_);
lean_dec(v_val_2856_);
lean_dec_ref(v_close_2855_);
v_a_2861_ = lean_ctor_get(v_x_2859_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_x_2859_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2863_ = v_x_2859_;
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v_x_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
else
{
lean_object* v_a_2870_; uint8_t v___x_2871_; 
v_a_2870_ = lean_ctor_get(v_x_2859_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v_x_2859_, 1);
v___x_2871_ = lean_unbox(v_a_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; 
lean_dec_ref(v___f_2858_);
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_apply_2(v_close_2855_, v_val_2856_, lean_box(0));
v___x_2874_ = lean_unbox(v_a_2870_);
lean_dec(v_a_2870_);
v___x_2875_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2872_, v___x_2874_, v___x_2873_, v___f_2857_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v_a_2870_);
lean_dec_ref(v___f_2857_);
lean_dec(v_val_2856_);
lean_dec_ref(v_close_2855_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_apply_2(v___f_2858_, v___x_2876_, lean_box(0));
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2878_, lean_object* v_val_2879_, lean_object* v___f_2880_, lean_object* v___f_2881_, lean_object* v_x_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2878_, v_val_2879_, v___f_2880_, v___f_2881_, v_x_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_2885_, lean_object* v_handler_2886_, lean_object* v_x_2887_){
_start:
{
if (lean_obj_tag(v_x_2887_) == 0)
{
lean_object* v_a_2889_; lean_object* v_onFailure_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v_x_2887_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v_x_2887_, 1);
v_onFailure_2890_ = lean_ctor_get(v_inst_2885_, 2);
lean_inc_ref(v_onFailure_2890_);
lean_dec_ref(v_inst_2885_);
v___x_2891_ = lean_apply_3(v_onFailure_2890_, v_handler_2886_, v_a_2889_, lean_box(0));
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_handler_2886_);
lean_dec_ref(v_inst_2885_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_x_2887_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_2893_, lean_object* v_handler_2894_, lean_object* v_x_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2893_, v_handler_2894_, v_x_2895_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_2898_, lean_object* v_____r_2899_){
_start:
{
uint8_t v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2901_ = 0;
v___x_2902_ = lean_box(v___x_2901_);
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v_st_2898_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_2906_, lean_object* v_____r_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2906_, v_____r_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2910_, lean_object* v___f_2911_, lean_object* v___f_2912_, lean_object* v_x_2913_){
_start:
{
if (lean_obj_tag(v_x_2913_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v___f_2912_);
lean_dec_ref(v___f_2911_);
lean_dec_ref(v_requestStream_2910_);
v_a_2915_ = lean_ctor_get(v_x_2913_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_x_2913_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2917_ = v_x_2913_;
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v_x_2913_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
}
else
{
lean_object* v_a_2924_; uint8_t v___x_2925_; 
v_a_2924_ = lean_ctor_get(v_x_2913_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v_x_2913_, 1);
v___x_2925_ = lean_unbox(v_a_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; 
lean_dec_ref(v___f_2912_);
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = l_Std_Http_Body_Stream_close(v_requestStream_2910_);
v___x_2928_ = lean_unbox(v_a_2924_);
lean_dec(v_a_2924_);
v___x_2929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2926_, v___x_2928_, v___x_2927_, v___f_2911_);
return v___x_2929_;
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_a_2924_);
lean_dec_ref(v___f_2911_);
lean_dec_ref(v_requestStream_2910_);
v___x_2930_ = lean_box(0);
v___x_2931_ = lean_apply_2(v___f_2912_, v___x_2930_, lean_box(0));
return v___x_2931_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2932_, lean_object* v___f_2933_, lean_object* v___f_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2932_, v___f_2933_, v___f_2934_, v_x_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t v_final_2938_, lean_object* v___f_2939_, lean_object* v___f_2940_, lean_object* v_requestStream_2941_, lean_object* v___f_2942_, lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v___f_2942_);
lean_dec_ref(v_requestStream_2941_);
lean_dec_ref(v___f_2940_);
lean_dec_ref(v___f_2939_);
v_a_2945_ = lean_ctor_get(v_x_2943_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2947_ = v_x_2943_;
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v_x_2943_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
}
else
{
lean_dec_ref_known(v_x_2943_, 1);
if (v_final_2938_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec_ref(v___f_2942_);
lean_dec_ref(v_requestStream_2941_);
lean_dec_ref(v___f_2940_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_apply_2(v___f_2939_, v___x_2954_, lean_box(0));
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; uint8_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___f_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_6684__overap_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v___f_2939_);
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = 0;
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
lean_closure_set(v___x_2962_, 6, v___f_2940_);
v___x_6684__overap_2963_ = l_Std_Mutex_atomically___redArg(v___x_2958_, v___f_2959_, v___f_2960_, v_requestStream_2941_, v___x_2962_);
v___x_2964_ = lean_apply_1(v___x_6684__overap_2963_, lean_box(0));
v___x_2965_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2956_, v___x_2957_, v___x_2964_, v___f_2942_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_final_2966_, lean_object* v___f_2967_, lean_object* v___f_2968_, lean_object* v_requestStream_2969_, lean_object* v___f_2970_, lean_object* v_x_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v_final_boxed_2973_; lean_object* v_res_2974_; 
v_final_boxed_2973_ = lean_unbox(v_final_2966_);
v_res_2974_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_boxed_2973_, v___f_2967_, v___f_2968_, v_requestStream_2969_, v___f_2970_, v_x_2971_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2975_, lean_object* v_x_2976_){
_start:
{
if (lean_obj_tag(v_x_2976_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2986_; 
lean_dec_ref(v_state_2975_);
v_a_2978_ = lean_ctor_get(v_x_2976_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_x_2976_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2980_ = v_x_2976_;
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v_x_2976_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
}
}
else
{
lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3016_; 
v_isSharedCheck_3016_ = !lean_is_exclusive(v_x_2976_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v_x_2976_, 0);
lean_dec(v_unused_3017_);
v___x_2988_ = v_x_2976_;
v_isShared_2989_ = v_isSharedCheck_3016_;
goto v_resetjp_2987_;
}
else
{
lean_dec(v_x_2976_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3016_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_machine_2990_; lean_object* v_requestStream_2991_; lean_object* v_keepAliveTimeout_2992_; lean_object* v_currentTimeout_2993_; lean_object* v_headerTimeout_2994_; lean_object* v_response_2995_; lean_object* v_respStream_2996_; uint8_t v_requiresData_2997_; lean_object* v_expectData_2998_; lean_object* v_pendingHead_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3015_; 
v_machine_2990_ = lean_ctor_get(v_state_2975_, 0);
v_requestStream_2991_ = lean_ctor_get(v_state_2975_, 1);
v_keepAliveTimeout_2992_ = lean_ctor_get(v_state_2975_, 2);
v_currentTimeout_2993_ = lean_ctor_get(v_state_2975_, 3);
v_headerTimeout_2994_ = lean_ctor_get(v_state_2975_, 4);
v_response_2995_ = lean_ctor_get(v_state_2975_, 5);
v_respStream_2996_ = lean_ctor_get(v_state_2975_, 6);
v_requiresData_2997_ = lean_ctor_get_uint8(v_state_2975_, sizeof(void*)*9);
v_expectData_2998_ = lean_ctor_get(v_state_2975_, 7);
v_pendingHead_2999_ = lean_ctor_get(v_state_2975_, 8);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_state_2975_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3001_ = v_state_2975_;
v_isShared_3002_ = v_isSharedCheck_3015_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_pendingHead_2999_);
lean_inc(v_expectData_2998_);
lean_inc(v_respStream_2996_);
lean_inc(v_response_2995_);
lean_inc(v_headerTimeout_2994_);
lean_inc(v_currentTimeout_2993_);
lean_inc(v_keepAliveTimeout_2992_);
lean_inc(v_requestStream_2991_);
lean_inc(v_machine_2990_);
lean_dec(v_state_2975_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3015_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; lean_object* v___x_3007_; 
v___x_3003_ = lean_box(52);
v___x_3004_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2990_, v___x_3003_);
v___x_3005_ = 0;
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3004_);
v___x_3007_ = v___x_3001_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_requestStream_2991_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_keepAliveTimeout_2992_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_currentTimeout_2993_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v_headerTimeout_2994_);
lean_ctor_set(v_reuseFailAlloc_3014_, 5, v_response_2995_);
lean_ctor_set(v_reuseFailAlloc_3014_, 6, v_respStream_2996_);
lean_ctor_set(v_reuseFailAlloc_3014_, 7, v_expectData_2998_);
lean_ctor_set(v_reuseFailAlloc_3014_, 8, v_pendingHead_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, sizeof(void*)*9, v_requiresData_2997_);
v___x_3007_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*9 + 1, v___x_3005_);
v___x_3008_ = lean_box(v___x_3005_);
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_3009_);
v___x_3011_ = v___x_2988_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_3018_, v_x_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_3022_, lean_object* v_requestStream_3023_, lean_object* v_keepAliveTimeout_3024_, lean_object* v_currentTimeout_3025_, lean_object* v_headerTimeout_3026_, lean_object* v_response_3027_, lean_object* v_respStream_3028_, uint8_t v_requiresData_3029_, lean_object* v_expectData_3030_, lean_object* v_pendingHead_3031_, lean_object* v_____r_3032_){
_start:
{
uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3034_ = 0;
v___x_3035_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3035_, 0, v_machine_3022_);
lean_ctor_set(v___x_3035_, 1, v_requestStream_3023_);
lean_ctor_set(v___x_3035_, 2, v_keepAliveTimeout_3024_);
lean_ctor_set(v___x_3035_, 3, v_currentTimeout_3025_);
lean_ctor_set(v___x_3035_, 4, v_headerTimeout_3026_);
lean_ctor_set(v___x_3035_, 5, v_response_3027_);
lean_ctor_set(v___x_3035_, 6, v_respStream_3028_);
lean_ctor_set(v___x_3035_, 7, v_expectData_3030_);
lean_ctor_set(v___x_3035_, 8, v_pendingHead_3031_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*9, v_requiresData_3029_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*9 + 1, v___x_3034_);
v___x_3036_ = lean_box(v___x_3034_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_3040_, lean_object* v_requestStream_3041_, lean_object* v_keepAliveTimeout_3042_, lean_object* v_currentTimeout_3043_, lean_object* v_headerTimeout_3044_, lean_object* v_response_3045_, lean_object* v_respStream_3046_, lean_object* v_requiresData_3047_, lean_object* v_expectData_3048_, lean_object* v_pendingHead_3049_, lean_object* v_____r_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v_requiresData_boxed_3052_; lean_object* v_res_3053_; 
v_requiresData_boxed_3052_ = lean_unbox(v_requiresData_3047_);
v_res_3053_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_3040_, v_requestStream_3041_, v_keepAliveTimeout_3042_, v_currentTimeout_3043_, v_headerTimeout_3044_, v_response_3045_, v_respStream_3046_, v_requiresData_boxed_3052_, v_expectData_3048_, v_pendingHead_3049_, v_____r_3050_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_3054_, lean_object* v_body_3055_, lean_object* v___f_3056_, lean_object* v___f_3057_, lean_object* v_x_3058_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___f_3057_);
lean_dec_ref(v___f_3056_);
lean_dec(v_body_3055_);
lean_dec_ref(v_close_3054_);
v_a_3060_ = lean_ctor_get(v_x_3058_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_x_3058_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3062_ = v_x_3058_;
v_isShared_3063_ = v_isSharedCheck_3068_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v_x_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3068_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
}
else
{
lean_object* v_a_3069_; uint8_t v___x_3070_; 
v_a_3069_ = lean_ctor_get(v_x_3058_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v_x_3058_, 1);
v___x_3070_ = lean_unbox(v_a_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; 
lean_dec_ref(v___f_3057_);
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = lean_apply_2(v_close_3054_, v_body_3055_, lean_box(0));
v___x_3073_ = lean_unbox(v_a_3069_);
lean_dec(v_a_3069_);
v___x_3074_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3071_, v___x_3073_, v___x_3072_, v___f_3056_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec(v_a_3069_);
lean_dec_ref(v___f_3056_);
lean_dec(v_body_3055_);
lean_dec_ref(v_close_3054_);
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_apply_2(v___f_3057_, v___x_3075_, lean_box(0));
return v___x_3076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_3077_, lean_object* v_body_3078_, lean_object* v___f_3079_, lean_object* v___f_3080_, lean_object* v_x_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_3077_, v_body_3078_, v___f_3079_, v___f_3080_, v_x_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_3084_, lean_object* v_keepAliveTimeout_3085_, lean_object* v_currentTimeout_3086_, lean_object* v_headerTimeout_3087_, lean_object* v_response_3088_, uint8_t v_requiresData_3089_, lean_object* v_expectData_3090_, uint8_t v___x_3091_, lean_object* v_pendingHead_3092_, lean_object* v_____x_3093_){
_start:
{
lean_object* v_snd_3095_; lean_object* v_fst_3096_; lean_object* v_fst_3097_; lean_object* v_snd_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3108_; 
v_snd_3095_ = lean_ctor_get(v_____x_3093_, 1);
lean_inc(v_snd_3095_);
v_fst_3096_ = lean_ctor_get(v_____x_3093_, 0);
lean_inc(v_fst_3096_);
lean_dec_ref(v_____x_3093_);
v_fst_3097_ = lean_ctor_get(v_snd_3095_, 0);
v_snd_3098_ = lean_ctor_get(v_snd_3095_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_snd_3095_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3100_ = v_snd_3095_;
v_isShared_3101_ = v_isSharedCheck_3108_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_snd_3098_);
lean_inc(v_fst_3097_);
lean_dec(v_snd_3095_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3108_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3102_, 0, v_fst_3096_);
lean_ctor_set(v___x_3102_, 1, v_requestStream_3084_);
lean_ctor_set(v___x_3102_, 2, v_keepAliveTimeout_3085_);
lean_ctor_set(v___x_3102_, 3, v_currentTimeout_3086_);
lean_ctor_set(v___x_3102_, 4, v_headerTimeout_3087_);
lean_ctor_set(v___x_3102_, 5, v_response_3088_);
lean_ctor_set(v___x_3102_, 6, v_fst_3097_);
lean_ctor_set(v___x_3102_, 7, v_expectData_3090_);
lean_ctor_set(v___x_3102_, 8, v_pendingHead_3092_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*9, v_requiresData_3089_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*9 + 1, v___x_3091_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3102_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_snd_3098_);
v___x_3104_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_3109_, lean_object* v_keepAliveTimeout_3110_, lean_object* v_currentTimeout_3111_, lean_object* v_headerTimeout_3112_, lean_object* v_response_3113_, lean_object* v_requiresData_3114_, lean_object* v_expectData_3115_, lean_object* v___x_3116_, lean_object* v_pendingHead_3117_, lean_object* v_____x_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v_requiresData_boxed_3120_; uint8_t v___x_7494__boxed_3121_; lean_object* v_res_3122_; 
v_requiresData_boxed_3120_ = lean_unbox(v_requiresData_3114_);
v___x_7494__boxed_3121_ = lean_unbox(v___x_3116_);
v_res_3122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_3109_, v_keepAliveTimeout_3110_, v_currentTimeout_3111_, v_headerTimeout_3112_, v_response_3113_, v_requiresData_boxed_3120_, v_expectData_3115_, v___x_7494__boxed_3121_, v_pendingHead_3117_, v_____x_3118_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_3123_, lean_object* v_x_3124_){
_start:
{
if (lean_obj_tag(v_x_3124_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v___f_3123_);
v_a_3126_ = lean_ctor_get(v_x_3124_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_x_3124_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3128_ = v_x_3124_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v_x_3124_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
v_a_3135_ = lean_ctor_get(v_x_3124_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v_x_3124_, 1);
v___x_3136_ = lean_apply_2(v___f_3123_, v_a_3135_, lean_box(0));
return v___x_3136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3137_, v_x_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3141_, lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3142_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3152_; 
v_a_3144_ = lean_ctor_get(v_x_3142_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_x_3142_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3146_ = v_x_3142_;
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v_x_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3172_; 
v_a_3153_ = lean_ctor_get(v_x_3142_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_x_3142_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3155_ = v_x_3142_;
v_isShared_3156_ = v_isSharedCheck_3172_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v_x_3142_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3172_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_fst_3157_; lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3171_; 
v_fst_3157_ = lean_ctor_get(v_a_3153_, 0);
v_snd_3158_ = lean_ctor_get(v_a_3153_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_a_3153_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3160_ = v_a_3153_;
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_inc(v_fst_3157_);
lean_dec(v_a_3153_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3162_ = lean_box(v___x_3141_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3162_);
lean_ctor_set(v___x_3160_, 0, v_snd_3158_);
v___x_3164_ = v___x_3160_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_snd_3158_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_fst_3157_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3165_);
v___x_3167_ = v___x_3155_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3173_, lean_object* v_x_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v___x_7562__boxed_3176_; lean_object* v_res_3177_; 
v___x_7562__boxed_3176_ = lean_unbox(v___x_3173_);
v_res_3177_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7562__boxed_3176_, v_x_3174_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3178_, uint8_t v___x_3179_, lean_object* v_fst_3180_, lean_object* v_x_3181_){
_start:
{
if (lean_obj_tag(v_x_3181_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_fst_3180_);
lean_dec(v_snd_3178_);
v_a_3183_ = lean_ctor_get(v_x_3181_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_x_3181_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3185_ = v_x_3181_;
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v_x_3181_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
}
else
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3202_; 
v_isSharedCheck_3202_ = !lean_is_exclusive(v_x_3181_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v_x_3181_, 0);
lean_dec(v_unused_3203_);
v___x_3193_ = v_x_3181_;
v_isShared_3194_ = v_isSharedCheck_3202_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_x_3181_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3202_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3195_ = lean_box(v___x_3179_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v_snd_3178_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_fst_3180_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3197_);
v___x_3199_ = v___x_3193_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
return v___x_3200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3204_, lean_object* v___x_3205_, lean_object* v_fst_3206_, lean_object* v_x_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v___x_7630__boxed_3209_; lean_object* v_res_3210_; 
v___x_7630__boxed_3209_ = lean_unbox(v___x_3205_);
v_res_3210_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3204_, v___x_7630__boxed_3209_, v_fst_3206_, v_x_3207_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3211_, lean_object* v_handler_3212_, uint8_t v___x_3213_, lean_object* v___f_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 0)
{
lean_object* v_a_3217_; lean_object* v_onFailure_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_a_3217_ = lean_ctor_get(v_x_3215_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v_x_3215_, 1);
v_onFailure_3218_ = lean_ctor_get(v_inst_3211_, 2);
lean_inc_ref(v_onFailure_3218_);
lean_dec_ref(v_inst_3211_);
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_apply_3(v_onFailure_3218_, v_handler_3212_, v_a_3217_, lean_box(0));
v___x_3221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3219_, v___x_3213_, v___x_3220_, v___f_3214_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; 
lean_dec_ref(v___f_3214_);
lean_dec(v_handler_3212_);
lean_dec_ref(v_inst_3211_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_x_3215_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3223_, lean_object* v_handler_3224_, lean_object* v___x_3225_, lean_object* v___f_3226_, lean_object* v_x_3227_, lean_object* v___y_3228_){
_start:
{
uint8_t v___x_7688__boxed_3229_; lean_object* v_res_3230_; 
v___x_7688__boxed_3229_ = lean_unbox(v___x_3225_);
v_res_3230_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3223_, v_handler_3224_, v___x_7688__boxed_3229_, v___f_3226_, v_x_3227_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3231_, lean_object* v___f_3232_, uint8_t v___x_3233_, lean_object* v_inst_3234_, lean_object* v_handler_3235_, lean_object* v_inst_3236_, lean_object* v___f_3237_, lean_object* v___f_3238_, lean_object* v_x_3239_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v___f_3238_);
lean_dec_ref(v___f_3237_);
lean_dec_ref(v_inst_3236_);
lean_dec(v_handler_3235_);
lean_dec_ref(v_inst_3234_);
lean_dec_ref(v___f_3232_);
v_a_3241_ = lean_ctor_get(v_x_3239_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_x_3239_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3243_ = v_x_3239_;
v_isShared_3244_ = v_isSharedCheck_3249_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v_x_3239_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3249_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3283_; 
v_a_3250_ = lean_ctor_get(v_x_3239_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_x_3239_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3252_ = v_x_3239_;
v_isShared_3253_ = v_isSharedCheck_3283_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v_x_3239_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3283_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v_snd_3254_; 
v_snd_3254_ = lean_ctor_get(v_a_3250_, 1);
lean_inc(v_snd_3254_);
if (lean_obj_tag(v_snd_3254_) == 0)
{
lean_object* v_fst_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v___f_3238_);
lean_dec_ref(v___f_3237_);
lean_dec_ref(v_inst_3236_);
lean_dec(v_handler_3235_);
lean_dec_ref(v_inst_3234_);
v_fst_3255_ = lean_ctor_get(v_a_3250_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_a_3250_);
if (v_isSharedCheck_3270_ == 0)
{
lean_object* v_unused_3271_; 
v_unused_3271_ = lean_ctor_get(v_a_3250_, 1);
lean_dec(v_unused_3271_);
v___x_3257_ = v_a_3250_;
v_isShared_3258_ = v_isSharedCheck_3270_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_fst_3255_);
lean_dec(v_a_3250_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3270_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_box(v___x_3231_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 1, v___x_3259_);
lean_ctor_set(v___x_3257_, 0, v_snd_3254_);
v___x_3261_ = v___x_3257_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_snd_3254_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_fst_3255_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = lean_unsigned_to_nat(0u);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3262_);
v___x_3265_ = v___x_3252_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3262_);
v___x_3265_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
v___x_3267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3263_, v___x_3231_, v___x_3266_, v___f_3232_);
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_fst_3272_; lean_object* v_val_3273_; lean_object* v___x_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; lean_object* v___f_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_del_object(v___x_3252_);
lean_dec_ref(v___f_3232_);
v_fst_3272_ = lean_ctor_get(v_a_3250_, 0);
lean_inc_n(v_fst_3272_, 2);
lean_dec(v_a_3250_);
v_val_3273_ = lean_ctor_get(v_snd_3254_, 0);
lean_inc(v_val_3273_);
v___x_3274_ = lean_box(v___x_3233_);
v___f_3275_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3275_, 0, v_snd_3254_);
lean_closure_set(v___f_3275_, 1, v___x_3274_);
lean_closure_set(v___f_3275_, 2, v_fst_3272_);
v___x_3276_ = lean_box(v___x_3231_);
v___f_3277_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3277_, 0, v_inst_3234_);
lean_closure_set(v___f_3277_, 1, v_handler_3235_);
lean_closure_set(v___f_3277_, 2, v___x_3276_);
lean_closure_set(v___f_3277_, 3, v___f_3275_);
v___x_3278_ = lean_unsigned_to_nat(0u);
v___x_3279_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3236_, v_fst_3272_, v_val_3273_);
v___x_3280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3278_, v___x_3231_, v___x_3279_, v___f_3237_);
v___x_3281_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3278_, v___x_3231_, v___x_3280_, v___f_3277_);
v___x_3282_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3278_, v___x_3231_, v___x_3281_, v___f_3238_);
return v___x_3282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3284_, lean_object* v___f_3285_, lean_object* v___x_3286_, lean_object* v_inst_3287_, lean_object* v_handler_3288_, lean_object* v_inst_3289_, lean_object* v___f_3290_, lean_object* v___f_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v___x_7713__boxed_3294_; uint8_t v___x_7715__boxed_3295_; lean_object* v_res_3296_; 
v___x_7713__boxed_3294_ = lean_unbox(v___x_3284_);
v___x_7715__boxed_3295_ = lean_unbox(v___x_3286_);
v_res_3296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_7713__boxed_3294_, v___f_3285_, v___x_7715__boxed_3295_, v_inst_3287_, v_handler_3288_, v_inst_3289_, v___f_3290_, v___f_3291_, v_x_3292_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3297_, lean_object* v_x_3298_){
_start:
{
if (lean_obj_tag(v_x_3298_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_state_3297_);
v_a_3300_ = lean_ctor_get(v_x_3298_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_x_3298_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3302_ = v_x_3298_;
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v_x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
}
else
{
lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3338_; 
v_isSharedCheck_3338_ = !lean_is_exclusive(v_x_3298_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_x_3298_, 0);
lean_dec(v_unused_3339_);
v___x_3310_ = v_x_3298_;
v_isShared_3311_ = v_isSharedCheck_3338_;
goto v_resetjp_3309_;
}
else
{
lean_dec(v_x_3298_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3338_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v_machine_3312_; lean_object* v_requestStream_3313_; lean_object* v_keepAliveTimeout_3314_; lean_object* v_currentTimeout_3315_; lean_object* v_headerTimeout_3316_; lean_object* v_response_3317_; lean_object* v_respStream_3318_; uint8_t v_requiresData_3319_; lean_object* v_expectData_3320_; lean_object* v_pendingHead_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3337_; 
v_machine_3312_ = lean_ctor_get(v_state_3297_, 0);
v_requestStream_3313_ = lean_ctor_get(v_state_3297_, 1);
v_keepAliveTimeout_3314_ = lean_ctor_get(v_state_3297_, 2);
v_currentTimeout_3315_ = lean_ctor_get(v_state_3297_, 3);
v_headerTimeout_3316_ = lean_ctor_get(v_state_3297_, 4);
v_response_3317_ = lean_ctor_get(v_state_3297_, 5);
v_respStream_3318_ = lean_ctor_get(v_state_3297_, 6);
v_requiresData_3319_ = lean_ctor_get_uint8(v_state_3297_, sizeof(void*)*9);
v_expectData_3320_ = lean_ctor_get(v_state_3297_, 7);
v_pendingHead_3321_ = lean_ctor_get(v_state_3297_, 8);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_state_3297_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3323_ = v_state_3297_;
v_isShared_3324_ = v_isSharedCheck_3337_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_pendingHead_3321_);
lean_inc(v_expectData_3320_);
lean_inc(v_respStream_3318_);
lean_inc(v_response_3317_);
lean_inc(v_headerTimeout_3316_);
lean_inc(v_currentTimeout_3315_);
lean_inc(v_keepAliveTimeout_3314_);
lean_inc(v_requestStream_3313_);
lean_inc(v_machine_3312_);
lean_dec(v_state_3297_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3337_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3329_; 
v___x_3325_ = lean_box(31);
v___x_3326_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3312_, v___x_3325_);
v___x_3327_ = 0;
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3326_);
v___x_3329_ = v___x_3323_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_requestStream_3313_);
lean_ctor_set(v_reuseFailAlloc_3336_, 2, v_keepAliveTimeout_3314_);
lean_ctor_set(v_reuseFailAlloc_3336_, 3, v_currentTimeout_3315_);
lean_ctor_set(v_reuseFailAlloc_3336_, 4, v_headerTimeout_3316_);
lean_ctor_set(v_reuseFailAlloc_3336_, 5, v_response_3317_);
lean_ctor_set(v_reuseFailAlloc_3336_, 6, v_respStream_3318_);
lean_ctor_set(v_reuseFailAlloc_3336_, 7, v_expectData_3320_);
lean_ctor_set(v_reuseFailAlloc_3336_, 8, v_pendingHead_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3336_, sizeof(void*)*9, v_requiresData_3319_);
v___x_3329_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*9 + 1, v___x_3327_);
v___x_3330_ = lean_box(v___x_3327_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3331_);
v___x_3333_ = v___x_3310_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3340_, v_x_3341_);
return v_res_3343_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3349_ = lean_mk_io_user_error(v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_handler_3352_, lean_object* v_config_3353_, lean_object* v_event_3354_, lean_object* v_state_3355_){
_start:
{
switch(lean_obj_tag(v_event_3354_))
{
case 0:
{
lean_object* v_x_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_handler_3352_);
lean_dec_ref(v_inst_3351_);
lean_dec_ref(v_inst_3350_);
v_x_3357_ = lean_ctor_get(v_event_3354_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_event_3354_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3359_ = v_event_3354_;
v_isShared_3360_ = v_isSharedCheck_3464_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_x_3357_);
lean_dec(v_event_3354_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3464_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
if (lean_obj_tag(v_x_3357_) == 0)
{
lean_object* v_machine_3361_; lean_object* v_reader_3362_; lean_object* v_requestStream_3363_; lean_object* v_keepAliveTimeout_3364_; lean_object* v_currentTimeout_3365_; lean_object* v_headerTimeout_3366_; lean_object* v_response_3367_; lean_object* v_respStream_3368_; uint8_t v_requiresData_3369_; lean_object* v_expectData_3370_; uint8_t v_handlerDispatched_3371_; lean_object* v_pendingHead_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_config_3353_);
v_machine_3361_ = lean_ctor_get(v_state_3355_, 0);
lean_inc_ref(v_machine_3361_);
v_reader_3362_ = lean_ctor_get(v_machine_3361_, 0);
lean_inc_ref(v_reader_3362_);
v_requestStream_3363_ = lean_ctor_get(v_state_3355_, 1);
v_keepAliveTimeout_3364_ = lean_ctor_get(v_state_3355_, 2);
v_currentTimeout_3365_ = lean_ctor_get(v_state_3355_, 3);
v_headerTimeout_3366_ = lean_ctor_get(v_state_3355_, 4);
v_response_3367_ = lean_ctor_get(v_state_3355_, 5);
v_respStream_3368_ = lean_ctor_get(v_state_3355_, 6);
v_requiresData_3369_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3370_ = lean_ctor_get(v_state_3355_, 7);
v_handlerDispatched_3371_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9 + 1);
v_pendingHead_3372_ = lean_ctor_get(v_state_3355_, 8);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_state_3355_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v_state_3355_, 0);
lean_dec(v_unused_3416_);
v___x_3374_ = v_state_3355_;
v_isShared_3375_ = v_isSharedCheck_3415_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_pendingHead_3372_);
lean_inc(v_expectData_3370_);
lean_inc(v_respStream_3368_);
lean_inc(v_response_3367_);
lean_inc(v_headerTimeout_3366_);
lean_inc(v_currentTimeout_3365_);
lean_inc(v_keepAliveTimeout_3364_);
lean_inc(v_requestStream_3363_);
lean_dec(v_state_3355_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3415_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_writer_3376_; lean_object* v_config_3377_; lean_object* v_events_3378_; lean_object* v_error_3379_; lean_object* v_instant_3380_; uint8_t v_keepAlive_3381_; uint8_t v_forcedFlush_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3413_; 
v_writer_3376_ = lean_ctor_get(v_machine_3361_, 1);
v_config_3377_ = lean_ctor_get(v_machine_3361_, 2);
v_events_3378_ = lean_ctor_get(v_machine_3361_, 3);
v_error_3379_ = lean_ctor_get(v_machine_3361_, 4);
v_instant_3380_ = lean_ctor_get(v_machine_3361_, 5);
v_keepAlive_3381_ = lean_ctor_get_uint8(v_machine_3361_, sizeof(void*)*6);
v_forcedFlush_3382_ = lean_ctor_get_uint8(v_machine_3361_, sizeof(void*)*6 + 1);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_machine_3361_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v_machine_3361_, 0);
lean_dec(v_unused_3414_);
v___x_3384_ = v_machine_3361_;
v_isShared_3385_ = v_isSharedCheck_3413_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_instant_3380_);
lean_inc(v_error_3379_);
lean_inc(v_events_3378_);
lean_inc(v_config_3377_);
lean_inc(v_writer_3376_);
lean_dec(v_machine_3361_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3413_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_state_3386_; lean_object* v_input_3387_; lean_object* v_messageHead_3388_; lean_object* v_messageCount_3389_; lean_object* v_bodyBytesRead_3390_; lean_object* v_headerBytesRead_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3412_; 
v_state_3386_ = lean_ctor_get(v_reader_3362_, 0);
v_input_3387_ = lean_ctor_get(v_reader_3362_, 1);
v_messageHead_3388_ = lean_ctor_get(v_reader_3362_, 2);
v_messageCount_3389_ = lean_ctor_get(v_reader_3362_, 3);
v_bodyBytesRead_3390_ = lean_ctor_get(v_reader_3362_, 4);
v_headerBytesRead_3391_ = lean_ctor_get(v_reader_3362_, 5);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_reader_3362_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3393_ = v_reader_3362_;
v_isShared_3394_ = v_isSharedCheck_3412_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_headerBytesRead_3391_);
lean_inc(v_bodyBytesRead_3390_);
lean_inc(v_messageCount_3389_);
lean_inc(v_messageHead_3388_);
lean_inc(v_input_3387_);
lean_inc(v_state_3386_);
lean_dec(v_reader_3362_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3412_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
uint8_t v___x_3395_; lean_object* v___x_3397_; 
v___x_3395_ = 1;
if (v_isShared_3394_ == 0)
{
v___x_3397_ = v___x_3393_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_state_3386_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_input_3387_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_messageHead_3388_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_messageCount_3389_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v_bodyBytesRead_3390_);
lean_ctor_set(v_reuseFailAlloc_3411_, 5, v_headerBytesRead_3391_);
v___x_3397_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
uint8_t v___x_3398_; lean_object* v___x_3400_; 
lean_ctor_set_uint8(v___x_3397_, sizeof(void*)*6, v___x_3395_);
v___x_3398_ = 0;
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3397_);
v___x_3400_ = v___x_3384_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_writer_3376_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_config_3377_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_events_3378_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_error_3379_);
lean_ctor_set(v_reuseFailAlloc_3410_, 5, v_instant_3380_);
lean_ctor_set_uint8(v_reuseFailAlloc_3410_, sizeof(void*)*6, v_keepAlive_3381_);
lean_ctor_set_uint8(v_reuseFailAlloc_3410_, sizeof(void*)*6 + 1, v_forcedFlush_3382_);
v___x_3400_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3402_; 
lean_ctor_set_uint8(v___x_3400_, sizeof(void*)*6 + 2, v___x_3398_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3400_);
v___x_3402_ = v___x_3374_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_requestStream_3363_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_keepAliveTimeout_3364_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_currentTimeout_3365_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v_headerTimeout_3366_);
lean_ctor_set(v_reuseFailAlloc_3409_, 5, v_response_3367_);
lean_ctor_set(v_reuseFailAlloc_3409_, 6, v_respStream_3368_);
lean_ctor_set(v_reuseFailAlloc_3409_, 7, v_expectData_3370_);
lean_ctor_set(v_reuseFailAlloc_3409_, 8, v_pendingHead_3372_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, sizeof(void*)*9, v_requiresData_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, sizeof(void*)*9 + 1, v_handlerDispatched_3371_);
v___x_3402_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3403_ = lean_box(v___x_3398_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set_tag(v___x_3359_, 1);
lean_ctor_set(v___x_3359_, 0, v___x_3404_);
v___x_3406_ = v___x_3359_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
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
lean_object* v_val_3417_; lean_object* v_machine_3418_; lean_object* v_requestStream_3419_; lean_object* v_keepAliveTimeout_3420_; lean_object* v_currentTimeout_3421_; lean_object* v_response_3422_; lean_object* v_respStream_3423_; uint8_t v_requiresData_3424_; lean_object* v_expectData_3425_; uint8_t v_handlerDispatched_3426_; lean_object* v_pendingHead_3427_; lean_object* v___f_3428_; 
lean_del_object(v___x_3359_);
v_val_3417_ = lean_ctor_get(v_x_3357_, 0);
lean_inc_n(v_val_3417_, 2);
lean_dec_ref_known(v_x_3357_, 1);
v_machine_3418_ = lean_ctor_get(v_state_3355_, 0);
v_requestStream_3419_ = lean_ctor_get(v_state_3355_, 1);
v_keepAliveTimeout_3420_ = lean_ctor_get(v_state_3355_, 2);
lean_inc(v_keepAliveTimeout_3420_);
v_currentTimeout_3421_ = lean_ctor_get(v_state_3355_, 3);
v_response_3422_ = lean_ctor_get(v_state_3355_, 5);
v_respStream_3423_ = lean_ctor_get(v_state_3355_, 6);
v_requiresData_3424_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3425_ = lean_ctor_get(v_state_3355_, 7);
v_handlerDispatched_3426_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9 + 1);
v_pendingHead_3427_ = lean_ctor_get(v_state_3355_, 8);
v___f_3428_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3428_, 0, v_val_3417_);
if (lean_obj_tag(v_keepAliveTimeout_3420_) == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec_ref(v___f_3428_);
lean_dec_ref(v_config_3353_);
v___x_3429_ = lean_box(0);
v___x_3430_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3417_, v___x_3429_, v_state_3355_);
return v___x_3430_;
}
else
{
lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3462_; 
lean_inc(v_pendingHead_3427_);
lean_inc(v_expectData_3425_);
lean_inc(v_respStream_3423_);
lean_inc_ref(v_response_3422_);
lean_inc(v_currentTimeout_3421_);
lean_inc_ref(v_requestStream_3419_);
lean_inc_ref(v_machine_3418_);
lean_dec(v_val_3417_);
lean_dec_ref(v_state_3355_);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_keepAliveTimeout_3420_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; 
v_unused_3463_ = lean_ctor_get(v_keepAliveTimeout_3420_, 0);
lean_dec(v_unused_3463_);
v___x_3432_ = v_keepAliveTimeout_3420_;
v_isShared_3433_ = v_isSharedCheck_3462_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v_keepAliveTimeout_3420_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3462_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___f_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; lean_object* v_val_3440_; lean_object* v___x_3445_; 
v___x_3434_ = lean_box(v_requiresData_3424_);
v___x_3435_ = lean_box(v_handlerDispatched_3426_);
v___f_3436_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3436_, 0, v_config_3353_);
lean_closure_set(v___f_3436_, 1, v_machine_3418_);
lean_closure_set(v___f_3436_, 2, v_requestStream_3419_);
lean_closure_set(v___f_3436_, 3, v_currentTimeout_3421_);
lean_closure_set(v___f_3436_, 4, v_response_3422_);
lean_closure_set(v___f_3436_, 5, v_respStream_3423_);
lean_closure_set(v___f_3436_, 6, v___x_3434_);
lean_closure_set(v___f_3436_, 7, v_expectData_3425_);
lean_closure_set(v___f_3436_, 8, v___x_3435_);
lean_closure_set(v___f_3436_, 9, v_pendingHead_3427_);
lean_closure_set(v___f_3436_, 10, v___f_3428_);
v___x_3437_ = lean_unsigned_to_nat(0u);
v___x_3438_ = 0;
v___x_3445_ = lean_get_current_time();
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 1);
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
v_val_3440_ = v___x_3451_;
goto v___jp_3439_;
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
v_a_3454_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3445_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3445_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set_tag(v___x_3456_, 0);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
v_val_3440_ = v___x_3459_;
goto v___jp_3439_;
}
}
}
v___jp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 0);
lean_ctor_set(v___x_3432_, 0, v_val_3440_);
v___x_3442_ = v___x_3432_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_val_3440_);
v___x_3442_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; 
v___x_3443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3437_, v___x_3438_, v___x_3442_, v___f_3436_);
return v___x_3443_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_config_3353_);
lean_dec(v_handler_3352_);
lean_dec_ref(v_inst_3350_);
v_x_3465_ = lean_ctor_get(v_event_3354_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_event_3354_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3467_ = v_event_3354_;
v_isShared_3468_ = v_isSharedCheck_3576_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_x_3465_);
lean_dec(v_event_3354_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3576_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
if (lean_obj_tag(v_x_3465_) == 0)
{
lean_object* v_machine_3469_; lean_object* v_requestStream_3470_; lean_object* v_keepAliveTimeout_3471_; lean_object* v_currentTimeout_3472_; lean_object* v_headerTimeout_3473_; lean_object* v_response_3474_; lean_object* v_respStream_3475_; uint8_t v_requiresData_3476_; lean_object* v_expectData_3477_; uint8_t v_handlerDispatched_3478_; lean_object* v_pendingHead_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___f_3482_; 
lean_del_object(v___x_3467_);
v_machine_3469_ = lean_ctor_get(v_state_3355_, 0);
lean_inc_ref_n(v_machine_3469_, 2);
v_requestStream_3470_ = lean_ctor_get(v_state_3355_, 1);
lean_inc_ref_n(v_requestStream_3470_, 2);
v_keepAliveTimeout_3471_ = lean_ctor_get(v_state_3355_, 2);
lean_inc_n(v_keepAliveTimeout_3471_, 2);
v_currentTimeout_3472_ = lean_ctor_get(v_state_3355_, 3);
lean_inc_n(v_currentTimeout_3472_, 2);
v_headerTimeout_3473_ = lean_ctor_get(v_state_3355_, 4);
lean_inc_n(v_headerTimeout_3473_, 2);
v_response_3474_ = lean_ctor_get(v_state_3355_, 5);
lean_inc_ref_n(v_response_3474_, 2);
v_respStream_3475_ = lean_ctor_get(v_state_3355_, 6);
lean_inc(v_respStream_3475_);
v_requiresData_3476_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3477_ = lean_ctor_get(v_state_3355_, 7);
lean_inc_n(v_expectData_3477_, 2);
v_handlerDispatched_3478_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9 + 1);
v_pendingHead_3479_ = lean_ctor_get(v_state_3355_, 8);
lean_inc_n(v_pendingHead_3479_, 2);
lean_dec_ref(v_state_3355_);
v___x_3480_ = lean_box(v_requiresData_3476_);
v___x_3481_ = lean_box(v_handlerDispatched_3478_);
v___f_3482_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3482_, 0, v_machine_3469_);
lean_closure_set(v___f_3482_, 1, v_requestStream_3470_);
lean_closure_set(v___f_3482_, 2, v_keepAliveTimeout_3471_);
lean_closure_set(v___f_3482_, 3, v_currentTimeout_3472_);
lean_closure_set(v___f_3482_, 4, v_headerTimeout_3473_);
lean_closure_set(v___f_3482_, 5, v_response_3474_);
lean_closure_set(v___f_3482_, 6, v___x_3480_);
lean_closure_set(v___f_3482_, 7, v_expectData_3477_);
lean_closure_set(v___f_3482_, 8, v___x_3481_);
lean_closure_set(v___f_3482_, 9, v_pendingHead_3479_);
if (lean_obj_tag(v_respStream_3475_) == 1)
{
lean_object* v_val_3483_; lean_object* v_close_3484_; lean_object* v_isClosed_3485_; lean_object* v___f_3486_; lean_object* v___f_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec(v_pendingHead_3479_);
lean_dec(v_expectData_3477_);
lean_dec_ref(v_response_3474_);
lean_dec(v_headerTimeout_3473_);
lean_dec(v_currentTimeout_3472_);
lean_dec(v_keepAliveTimeout_3471_);
lean_dec_ref(v_requestStream_3470_);
lean_dec_ref(v_machine_3469_);
v_val_3483_ = lean_ctor_get(v_respStream_3475_, 0);
lean_inc_n(v_val_3483_, 2);
lean_dec_ref_known(v_respStream_3475_, 1);
v_close_3484_ = lean_ctor_get(v_inst_3351_, 1);
lean_inc_ref(v_close_3484_);
v_isClosed_3485_ = lean_ctor_get(v_inst_3351_, 2);
lean_inc_ref(v_isClosed_3485_);
lean_dec_ref(v_inst_3351_);
lean_inc_ref(v___f_3482_);
v___f_3486_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3486_, 0, v___f_3482_);
v___f_3487_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3487_, 0, v_close_3484_);
lean_closure_set(v___f_3487_, 1, v_val_3483_);
lean_closure_set(v___f_3487_, 2, v___f_3486_);
lean_closure_set(v___f_3487_, 3, v___f_3482_);
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = 0;
v___x_3490_ = lean_apply_2(v_isClosed_3485_, v_val_3483_, lean_box(0));
v___x_3491_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3488_, v___x_3489_, v___x_3490_, v___f_3487_);
return v___x_3491_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec_ref(v___f_3482_);
lean_dec(v_respStream_3475_);
lean_dec_ref(v_inst_3351_);
v___x_3492_ = lean_box(0);
v___x_3493_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3469_, v_requestStream_3470_, v_keepAliveTimeout_3471_, v_currentTimeout_3472_, v_headerTimeout_3473_, v_response_3474_, v_requiresData_3476_, v_expectData_3477_, v_handlerDispatched_3478_, v_pendingHead_3479_, v___x_3492_);
return v___x_3493_;
}
}
else
{
lean_object* v_val_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3575_; 
lean_dec_ref(v_inst_3351_);
v_val_3494_ = lean_ctor_get(v_x_3465_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_x_3465_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3496_ = v_x_3465_;
v_isShared_3497_ = v_isSharedCheck_3575_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_val_3494_);
lean_dec(v_x_3465_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3575_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v_machine_3498_; lean_object* v_requestStream_3499_; lean_object* v_keepAliveTimeout_3500_; lean_object* v_currentTimeout_3501_; lean_object* v_headerTimeout_3502_; lean_object* v_response_3503_; lean_object* v_respStream_3504_; uint8_t v_requiresData_3505_; lean_object* v_expectData_3506_; uint8_t v_handlerDispatched_3507_; lean_object* v_pendingHead_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3574_; 
v_machine_3498_ = lean_ctor_get(v_state_3355_, 0);
v_requestStream_3499_ = lean_ctor_get(v_state_3355_, 1);
v_keepAliveTimeout_3500_ = lean_ctor_get(v_state_3355_, 2);
v_currentTimeout_3501_ = lean_ctor_get(v_state_3355_, 3);
v_headerTimeout_3502_ = lean_ctor_get(v_state_3355_, 4);
v_response_3503_ = lean_ctor_get(v_state_3355_, 5);
v_respStream_3504_ = lean_ctor_get(v_state_3355_, 6);
v_requiresData_3505_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3506_ = lean_ctor_get(v_state_3355_, 7);
v_handlerDispatched_3507_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9 + 1);
v_pendingHead_3508_ = lean_ctor_get(v_state_3355_, 8);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_state_3355_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3510_ = v_state_3355_;
v_isShared_3511_ = v_isSharedCheck_3574_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_pendingHead_3508_);
lean_inc(v_expectData_3506_);
lean_inc(v_respStream_3504_);
lean_inc(v_response_3503_);
lean_inc(v_headerTimeout_3502_);
lean_inc(v_currentTimeout_3501_);
lean_inc(v_keepAliveTimeout_3500_);
lean_inc(v_requestStream_3499_);
lean_inc(v_machine_3498_);
lean_dec(v_state_3355_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3574_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___y_3513_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_mk_empty_array_with_capacity(v___x_3526_);
v___x_3528_ = lean_array_push(v___x_3527_, v_val_3494_);
v___x_3529_ = lean_array_get_size(v___x_3528_);
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = lean_nat_dec_eq(v___x_3529_, v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v_reader_3532_; lean_object* v_writer_3533_; lean_object* v_config_3534_; lean_object* v_events_3535_; lean_object* v_error_3536_; lean_object* v_instant_3537_; uint8_t v_keepAlive_3538_; uint8_t v_forcedFlush_3539_; uint8_t v_pullBodyStalled_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3573_; 
v_reader_3532_ = lean_ctor_get(v_machine_3498_, 0);
v_writer_3533_ = lean_ctor_get(v_machine_3498_, 1);
v_config_3534_ = lean_ctor_get(v_machine_3498_, 2);
v_events_3535_ = lean_ctor_get(v_machine_3498_, 3);
v_error_3536_ = lean_ctor_get(v_machine_3498_, 4);
v_instant_3537_ = lean_ctor_get(v_machine_3498_, 5);
v_keepAlive_3538_ = lean_ctor_get_uint8(v_machine_3498_, sizeof(void*)*6);
v_forcedFlush_3539_ = lean_ctor_get_uint8(v_machine_3498_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3540_ = lean_ctor_get_uint8(v_machine_3498_, sizeof(void*)*6 + 2);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_machine_3498_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3542_ = v_machine_3498_;
v_isShared_3543_ = v_isSharedCheck_3573_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_instant_3537_);
lean_inc(v_error_3536_);
lean_inc(v_events_3535_);
lean_inc(v_config_3534_);
lean_inc(v_writer_3533_);
lean_inc(v_reader_3532_);
lean_dec(v_machine_3498_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3573_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___y_3545_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___closed__10));
v___x_3568_ = lean_nat_dec_lt(v___x_3530_, v___x_3529_);
if (v___x_3568_ == 0)
{
v___y_3545_ = v___x_3530_;
goto v___jp_3544_;
}
else
{
lean_object* v___f_3569_; size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___f_3569_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = lean_usize_of_nat(v___x_3529_);
lean_inc_ref(v___x_3528_);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3567_, v___f_3569_, v___x_3528_, v___x_3570_, v___x_3571_, v___x_3530_);
v___y_3545_ = v___x_3572_;
goto v___jp_3544_;
}
v___jp_3544_:
{
lean_object* v_userData_3546_; lean_object* v_outputData_3547_; lean_object* v_state_3548_; lean_object* v_knownSize_3549_; lean_object* v_messageHead_3550_; uint8_t v_sentMessage_3551_; uint8_t v_userClosedBody_3552_; uint8_t v_omitBody_3553_; lean_object* v_userDataBytes_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3566_; 
v_userData_3546_ = lean_ctor_get(v_writer_3533_, 0);
v_outputData_3547_ = lean_ctor_get(v_writer_3533_, 1);
v_state_3548_ = lean_ctor_get(v_writer_3533_, 2);
v_knownSize_3549_ = lean_ctor_get(v_writer_3533_, 3);
v_messageHead_3550_ = lean_ctor_get(v_writer_3533_, 4);
v_sentMessage_3551_ = lean_ctor_get_uint8(v_writer_3533_, sizeof(void*)*6);
v_userClosedBody_3552_ = lean_ctor_get_uint8(v_writer_3533_, sizeof(void*)*6 + 1);
v_omitBody_3553_ = lean_ctor_get_uint8(v_writer_3533_, sizeof(void*)*6 + 2);
v_userDataBytes_3554_ = lean_ctor_get(v_writer_3533_, 5);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_writer_3533_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3556_ = v_writer_3533_;
v_isShared_3557_ = v_isSharedCheck_3566_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_userDataBytes_3554_);
lean_inc(v_messageHead_3550_);
lean_inc(v_knownSize_3549_);
lean_inc(v_state_3548_);
lean_inc(v_outputData_3547_);
lean_inc(v_userData_3546_);
lean_dec(v_writer_3533_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3566_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3558_ = l_Array_append___redArg(v_userData_3546_, v___x_3528_);
lean_dec_ref(v___x_3528_);
v___x_3559_ = lean_nat_add(v_userDataBytes_3554_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec(v_userDataBytes_3554_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 5, v___x_3559_);
lean_ctor_set(v___x_3556_, 0, v___x_3558_);
v___x_3561_ = v___x_3556_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_outputData_3547_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_state_3548_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_knownSize_3549_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_messageHead_3550_);
lean_ctor_set(v_reuseFailAlloc_3565_, 5, v___x_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*6, v_sentMessage_3551_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*6 + 1, v_userClosedBody_3552_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*6 + 2, v_omitBody_3553_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3561_);
v___x_3563_ = v___x_3542_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_reader_3532_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_config_3534_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_events_3535_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_error_3536_);
lean_ctor_set(v_reuseFailAlloc_3564_, 5, v_instant_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*6, v_keepAlive_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*6 + 1, v_forcedFlush_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*6 + 2, v_pullBodyStalled_3540_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
v___y_3513_ = v___x_3563_;
goto v___jp_3512_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3528_);
v___y_3513_ = v_machine_3498_;
goto v___jp_3512_;
}
v___jp_3512_:
{
lean_object* v___x_3515_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___y_3513_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___y_3513_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_requestStream_3499_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_keepAliveTimeout_3500_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_currentTimeout_3501_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_headerTimeout_3502_);
lean_ctor_set(v_reuseFailAlloc_3525_, 5, v_response_3503_);
lean_ctor_set(v_reuseFailAlloc_3525_, 6, v_respStream_3504_);
lean_ctor_set(v_reuseFailAlloc_3525_, 7, v_expectData_3506_);
lean_ctor_set(v_reuseFailAlloc_3525_, 8, v_pendingHead_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, sizeof(void*)*9, v_requiresData_3505_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, sizeof(void*)*9 + 1, v_handlerDispatched_3507_);
v___x_3515_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
uint8_t v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3516_ = 0;
v___x_3517_ = lean_box(v___x_3516_);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3515_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3518_);
v___x_3520_ = v___x_3496_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3520_);
v___x_3522_ = v___x_3467_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
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
uint8_t v_x_3577_; 
lean_dec_ref(v_config_3353_);
lean_dec_ref(v_inst_3351_);
v_x_3577_ = lean_ctor_get_uint8(v_event_3354_, 0);
lean_dec_ref_known(v_event_3354_, 0);
if (v_x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec(v_handler_3352_);
lean_dec_ref(v_inst_3350_);
v___x_3578_ = lean_box(v_x_3577_);
v___x_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3579_, 0, v_state_3355_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
else
{
lean_object* v_machine_3582_; lean_object* v_requestStream_3583_; lean_object* v_keepAliveTimeout_3584_; lean_object* v_currentTimeout_3585_; lean_object* v_headerTimeout_3586_; lean_object* v_response_3587_; lean_object* v_respStream_3588_; uint8_t v_requiresData_3589_; lean_object* v_expectData_3590_; uint8_t v_handlerDispatched_3591_; lean_object* v_pendingHead_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3642_; 
v_machine_3582_ = lean_ctor_get(v_state_3355_, 0);
v_requestStream_3583_ = lean_ctor_get(v_state_3355_, 1);
v_keepAliveTimeout_3584_ = lean_ctor_get(v_state_3355_, 2);
v_currentTimeout_3585_ = lean_ctor_get(v_state_3355_, 3);
v_headerTimeout_3586_ = lean_ctor_get(v_state_3355_, 4);
v_response_3587_ = lean_ctor_get(v_state_3355_, 5);
v_respStream_3588_ = lean_ctor_get(v_state_3355_, 6);
v_requiresData_3589_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3590_ = lean_ctor_get(v_state_3355_, 7);
v_handlerDispatched_3591_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9 + 1);
v_pendingHead_3592_ = lean_ctor_get(v_state_3355_, 8);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_state_3355_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3594_ = v_state_3355_;
v_isShared_3595_ = v_isSharedCheck_3642_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_pendingHead_3592_);
lean_inc(v_expectData_3590_);
lean_inc(v_respStream_3588_);
lean_inc(v_response_3587_);
lean_inc(v_headerTimeout_3586_);
lean_inc(v_currentTimeout_3585_);
lean_inc(v_keepAliveTimeout_3584_);
lean_inc(v_requestStream_3583_);
lean_inc(v_machine_3582_);
lean_dec(v_state_3355_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3642_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
uint8_t v___x_3596_; lean_object* v___x_3597_; lean_object* v_fst_3598_; lean_object* v_snd_3599_; lean_object* v_reader_3600_; lean_object* v_writer_3601_; lean_object* v_config_3602_; lean_object* v_events_3603_; lean_object* v_error_3604_; lean_object* v_instant_3605_; uint8_t v_keepAlive_3606_; uint8_t v_forcedFlush_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3641_; 
v___x_3596_ = 0;
v___x_3597_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3596_, v_machine_3582_);
v_fst_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_fst_3598_);
v_snd_3599_ = lean_ctor_get(v___x_3597_, 1);
lean_inc(v_snd_3599_);
lean_dec_ref(v___x_3597_);
v_reader_3600_ = lean_ctor_get(v_fst_3598_, 0);
v_writer_3601_ = lean_ctor_get(v_fst_3598_, 1);
v_config_3602_ = lean_ctor_get(v_fst_3598_, 2);
v_events_3603_ = lean_ctor_get(v_fst_3598_, 3);
v_error_3604_ = lean_ctor_get(v_fst_3598_, 4);
v_instant_3605_ = lean_ctor_get(v_fst_3598_, 5);
v_keepAlive_3606_ = lean_ctor_get_uint8(v_fst_3598_, sizeof(void*)*6);
v_forcedFlush_3607_ = lean_ctor_get_uint8(v_fst_3598_, sizeof(void*)*6 + 1);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_fst_3598_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3609_ = v_fst_3598_;
v_isShared_3610_ = v_isSharedCheck_3641_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_instant_3605_);
lean_inc(v_error_3604_);
lean_inc(v_events_3603_);
lean_inc(v_config_3602_);
lean_inc(v_writer_3601_);
lean_inc(v_reader_3600_);
lean_dec(v_fst_3598_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3641_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___f_3611_; lean_object* v___f_3612_; uint8_t v___y_3614_; 
v___f_3611_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_3612_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_3612_, 0, v_inst_3350_);
lean_closure_set(v___f_3612_, 1, v_handler_3352_);
if (lean_obj_tag(v_snd_3599_) == 0)
{
uint8_t v_sentMessage_3637_; 
v_sentMessage_3637_ = lean_ctor_get_uint8(v_writer_3601_, sizeof(void*)*6);
if (v_sentMessage_3637_ == 0)
{
lean_object* v_state_3638_; 
v_state_3638_ = lean_ctor_get(v_reader_3600_, 0);
if (lean_obj_tag(v_state_3638_) == 2)
{
v___y_3614_ = v_x_3577_;
goto v___jp_3613_;
}
else
{
v___y_3614_ = v_sentMessage_3637_;
goto v___jp_3613_;
}
}
else
{
uint8_t v___x_3639_; 
v___x_3639_ = 0;
v___y_3614_ = v___x_3639_;
goto v___jp_3613_;
}
}
else
{
uint8_t v___x_3640_; 
v___x_3640_ = 0;
v___y_3614_ = v___x_3640_;
goto v___jp_3613_;
}
v___jp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3610_ == 0)
{
v___x_3616_ = v___x_3609_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_reader_3600_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_writer_3601_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_config_3602_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_events_3603_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v_error_3604_);
lean_ctor_set(v_reuseFailAlloc_3636_, 5, v_instant_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3636_, sizeof(void*)*6, v_keepAlive_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3636_, sizeof(void*)*6 + 1, v_forcedFlush_3607_);
v___x_3616_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v_st_3618_; 
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*6 + 2, v___y_3614_);
lean_inc_ref(v_requestStream_3583_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v___x_3616_);
v_st_3618_ = v___x_3594_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_requestStream_3583_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_keepAliveTimeout_3584_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_currentTimeout_3585_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_headerTimeout_3586_);
lean_ctor_set(v_reuseFailAlloc_3635_, 5, v_response_3587_);
lean_ctor_set(v_reuseFailAlloc_3635_, 6, v_respStream_3588_);
lean_ctor_set(v_reuseFailAlloc_3635_, 7, v_expectData_3590_);
lean_ctor_set(v_reuseFailAlloc_3635_, 8, v_pendingHead_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*9, v_requiresData_3589_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*9 + 1, v_handlerDispatched_3591_);
v_st_3618_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___f_3619_; 
lean_inc_ref(v_st_3618_);
v___f_3619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3619_, 0, v_st_3618_);
if (lean_obj_tag(v_snd_3599_) == 1)
{
lean_object* v_val_3620_; uint8_t v_final_3621_; uint8_t v_incomplete_3622_; lean_object* v_chunk_3623_; lean_object* v___f_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_dec_ref(v_st_3618_);
v_val_3620_ = lean_ctor_get(v_snd_3599_, 0);
lean_inc(v_val_3620_);
lean_dec_ref_known(v_snd_3599_, 1);
v_final_3621_ = lean_ctor_get_uint8(v_val_3620_, sizeof(void*)*1);
v_incomplete_3622_ = lean_ctor_get_uint8(v_val_3620_, sizeof(void*)*1 + 1);
v_chunk_3623_ = lean_ctor_get(v_val_3620_, 0);
lean_inc_ref(v_chunk_3623_);
lean_dec(v_val_3620_);
lean_inc_ref_n(v___f_3619_, 2);
v___f_3624_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3624_, 0, v___f_3619_);
lean_inc_ref_n(v_requestStream_3583_, 2);
v___f_3625_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3625_, 0, v_requestStream_3583_);
lean_closure_set(v___f_3625_, 1, v___f_3624_);
lean_closure_set(v___f_3625_, 2, v___f_3619_);
v___x_3626_ = lean_box(v_final_3621_);
v___f_3627_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_3627_, 0, v___x_3626_);
lean_closure_set(v___f_3627_, 1, v___f_3619_);
lean_closure_set(v___f_3627_, 2, v___f_3611_);
lean_closure_set(v___f_3627_, 3, v_requestStream_3583_);
lean_closure_set(v___f_3627_, 4, v___f_3625_);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = 0;
v___x_3630_ = l_Std_Http_Body_Stream_send(v_requestStream_3583_, v_chunk_3623_, v_incomplete_3622_);
v___x_3631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3628_, v___x_3629_, v___x_3630_, v___f_3612_);
v___x_3632_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3628_, v___x_3629_, v___x_3631_, v___f_3627_);
return v___x_3632_;
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
lean_dec_ref(v___f_3619_);
lean_dec_ref(v___f_3612_);
lean_dec(v_snd_3599_);
lean_dec_ref(v_requestStream_3583_);
v___x_3633_ = lean_box(0);
v___x_3634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3618_, v___x_3633_);
return v___x_3634_;
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
lean_object* v_x_3643_; 
v_x_3643_ = lean_ctor_get(v_event_3354_, 0);
lean_inc_ref(v_x_3643_);
lean_dec_ref_known(v_event_3354_, 1);
if (lean_obj_tag(v_x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v_onFailure_3645_; lean_object* v___f_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec_ref(v_config_3353_);
lean_dec_ref(v_inst_3351_);
v_a_3644_ = lean_ctor_get(v_x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v_x_3643_, 1);
v_onFailure_3645_ = lean_ctor_get(v_inst_3350_, 2);
lean_inc_ref(v_onFailure_3645_);
lean_dec_ref(v_inst_3350_);
v___f_3646_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3646_, 0, v_state_3355_);
v___x_3647_ = lean_unsigned_to_nat(0u);
v___x_3648_ = 0;
v___x_3649_ = lean_apply_3(v_onFailure_3645_, v_handler_3352_, v_a_3644_, lean_box(0));
v___x_3650_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3647_, v___x_3648_, v___x_3649_, v___f_3646_);
return v___x_3650_;
}
else
{
lean_object* v_machine_3651_; lean_object* v_reader_3652_; lean_object* v_state_3653_; 
v_machine_3651_ = lean_ctor_get(v_state_3355_, 0);
lean_inc_ref(v_machine_3651_);
v_reader_3652_ = lean_ctor_get(v_machine_3651_, 0);
v_state_3653_ = lean_ctor_get(v_reader_3652_, 0);
if (lean_obj_tag(v_state_3653_) == 7)
{
lean_object* v_a_3654_; lean_object* v_requestStream_3655_; lean_object* v_keepAliveTimeout_3656_; lean_object* v_currentTimeout_3657_; lean_object* v_headerTimeout_3658_; lean_object* v_response_3659_; lean_object* v_respStream_3660_; uint8_t v_requiresData_3661_; lean_object* v_expectData_3662_; lean_object* v_pendingHead_3663_; lean_object* v_close_3664_; lean_object* v_isClosed_3665_; lean_object* v_body_3666_; lean_object* v___x_3667_; lean_object* v___f_3668_; lean_object* v___f_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_dec_ref(v_config_3353_);
lean_dec(v_handler_3352_);
lean_dec_ref(v_inst_3350_);
v_a_3654_ = lean_ctor_get(v_x_3643_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v_x_3643_, 1);
v_requestStream_3655_ = lean_ctor_get(v_state_3355_, 1);
lean_inc_ref(v_requestStream_3655_);
v_keepAliveTimeout_3656_ = lean_ctor_get(v_state_3355_, 2);
lean_inc(v_keepAliveTimeout_3656_);
v_currentTimeout_3657_ = lean_ctor_get(v_state_3355_, 3);
lean_inc(v_currentTimeout_3657_);
v_headerTimeout_3658_ = lean_ctor_get(v_state_3355_, 4);
lean_inc(v_headerTimeout_3658_);
v_response_3659_ = lean_ctor_get(v_state_3355_, 5);
lean_inc_ref(v_response_3659_);
v_respStream_3660_ = lean_ctor_get(v_state_3355_, 6);
lean_inc(v_respStream_3660_);
v_requiresData_3661_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3662_ = lean_ctor_get(v_state_3355_, 7);
lean_inc(v_expectData_3662_);
v_pendingHead_3663_ = lean_ctor_get(v_state_3355_, 8);
lean_inc(v_pendingHead_3663_);
lean_dec_ref(v_state_3355_);
v_close_3664_ = lean_ctor_get(v_inst_3351_, 1);
lean_inc_ref(v_close_3664_);
v_isClosed_3665_ = lean_ctor_get(v_inst_3351_, 2);
lean_inc_ref(v_isClosed_3665_);
lean_dec_ref(v_inst_3351_);
v_body_3666_ = lean_ctor_get(v_a_3654_, 1);
lean_inc_n(v_body_3666_, 2);
lean_dec(v_a_3654_);
v___x_3667_ = lean_box(v_requiresData_3661_);
v___f_3668_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3668_, 0, v_machine_3651_);
lean_closure_set(v___f_3668_, 1, v_requestStream_3655_);
lean_closure_set(v___f_3668_, 2, v_keepAliveTimeout_3656_);
lean_closure_set(v___f_3668_, 3, v_currentTimeout_3657_);
lean_closure_set(v___f_3668_, 4, v_headerTimeout_3658_);
lean_closure_set(v___f_3668_, 5, v_response_3659_);
lean_closure_set(v___f_3668_, 6, v_respStream_3660_);
lean_closure_set(v___f_3668_, 7, v___x_3667_);
lean_closure_set(v___f_3668_, 8, v_expectData_3662_);
lean_closure_set(v___f_3668_, 9, v_pendingHead_3663_);
lean_inc_ref(v___f_3668_);
v___f_3669_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3669_, 0, v___f_3668_);
v___f_3670_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3670_, 0, v_close_3664_);
lean_closure_set(v___f_3670_, 1, v_body_3666_);
lean_closure_set(v___f_3670_, 2, v___f_3669_);
lean_closure_set(v___f_3670_, 3, v___f_3668_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = 0;
v___x_3673_ = lean_apply_2(v_isClosed_3665_, v_body_3666_, lean_box(0));
v___x_3674_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3671_, v___x_3672_, v___x_3673_, v___f_3670_);
return v___x_3674_;
}
else
{
lean_object* v_a_3675_; lean_object* v_requestStream_3676_; lean_object* v_keepAliveTimeout_3677_; lean_object* v_currentTimeout_3678_; lean_object* v_headerTimeout_3679_; lean_object* v_response_3680_; uint8_t v_requiresData_3681_; lean_object* v_expectData_3682_; lean_object* v_pendingHead_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___f_3687_; lean_object* v___f_3688_; lean_object* v___f_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___f_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_a_3675_ = lean_ctor_get(v_x_3643_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v_x_3643_, 1);
v_requestStream_3676_ = lean_ctor_get(v_state_3355_, 1);
lean_inc_ref(v_requestStream_3676_);
v_keepAliveTimeout_3677_ = lean_ctor_get(v_state_3355_, 2);
lean_inc(v_keepAliveTimeout_3677_);
v_currentTimeout_3678_ = lean_ctor_get(v_state_3355_, 3);
lean_inc(v_currentTimeout_3678_);
v_headerTimeout_3679_ = lean_ctor_get(v_state_3355_, 4);
lean_inc(v_headerTimeout_3679_);
v_response_3680_ = lean_ctor_get(v_state_3355_, 5);
lean_inc_ref(v_response_3680_);
v_requiresData_3681_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3682_ = lean_ctor_get(v_state_3355_, 7);
lean_inc(v_expectData_3682_);
v_pendingHead_3683_ = lean_ctor_get(v_state_3355_, 8);
lean_inc(v_pendingHead_3683_);
lean_dec_ref(v_state_3355_);
v___x_3684_ = 0;
v___x_3685_ = lean_box(v_requiresData_3681_);
v___x_3686_ = lean_box(v___x_3684_);
v___f_3687_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3687_, 0, v_requestStream_3676_);
lean_closure_set(v___f_3687_, 1, v_keepAliveTimeout_3677_);
lean_closure_set(v___f_3687_, 2, v_currentTimeout_3678_);
lean_closure_set(v___f_3687_, 3, v_headerTimeout_3679_);
lean_closure_set(v___f_3687_, 4, v_response_3680_);
lean_closure_set(v___f_3687_, 5, v___x_3685_);
lean_closure_set(v___f_3687_, 6, v_expectData_3682_);
lean_closure_set(v___f_3687_, 7, v___x_3686_);
lean_closure_set(v___f_3687_, 8, v_pendingHead_3683_);
v___f_3688_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3688_, 0, v___f_3687_);
v___f_3689_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3690_ = 1;
v___x_3691_ = lean_box(v___x_3684_);
v___x_3692_ = lean_box(v___x_3690_);
lean_inc_ref(v_inst_3351_);
lean_inc_ref(v___f_3688_);
v___f_3693_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3693_, 0, v___x_3691_);
lean_closure_set(v___f_3693_, 1, v___f_3688_);
lean_closure_set(v___f_3693_, 2, v___x_3692_);
lean_closure_set(v___f_3693_, 3, v_inst_3350_);
lean_closure_set(v___f_3693_, 4, v_handler_3352_);
lean_closure_set(v___f_3693_, 5, v_inst_3351_);
lean_closure_set(v___f_3693_, 6, v___f_3689_);
lean_closure_set(v___f_3693_, 7, v___f_3688_);
v___x_3694_ = lean_unsigned_to_nat(0u);
v___x_3695_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3351_, v_config_3353_, v_machine_3651_, v_a_3675_);
v___x_3696_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3694_, v___x_3684_, v___x_3695_, v___f_3693_);
return v___x_3696_;
}
}
}
case 4:
{
lean_object* v_onFailure_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec_ref(v_config_3353_);
lean_dec_ref(v_inst_3351_);
v_onFailure_3697_ = lean_ctor_get(v_inst_3350_, 2);
lean_inc_ref(v_onFailure_3697_);
lean_dec_ref(v_inst_3350_);
v___f_3698_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3698_, 0, v_state_3355_);
v___x_3699_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3700_ = lean_unsigned_to_nat(0u);
v___x_3701_ = 0;
v___x_3702_ = lean_apply_3(v_onFailure_3697_, v_handler_3352_, v___x_3699_, lean_box(0));
v___x_3703_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3700_, v___x_3701_, v___x_3702_, v___f_3698_);
return v___x_3703_;
}
case 5:
{
lean_object* v_machine_3704_; lean_object* v_requestStream_3705_; lean_object* v_keepAliveTimeout_3706_; lean_object* v_currentTimeout_3707_; lean_object* v_headerTimeout_3708_; lean_object* v_response_3709_; lean_object* v_respStream_3710_; uint8_t v_requiresData_3711_; lean_object* v_expectData_3712_; lean_object* v_pendingHead_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_config_3353_);
lean_dec(v_handler_3352_);
lean_dec_ref(v_inst_3351_);
lean_dec_ref(v_inst_3350_);
v_machine_3704_ = lean_ctor_get(v_state_3355_, 0);
v_requestStream_3705_ = lean_ctor_get(v_state_3355_, 1);
v_keepAliveTimeout_3706_ = lean_ctor_get(v_state_3355_, 2);
v_currentTimeout_3707_ = lean_ctor_get(v_state_3355_, 3);
v_headerTimeout_3708_ = lean_ctor_get(v_state_3355_, 4);
v_response_3709_ = lean_ctor_get(v_state_3355_, 5);
v_respStream_3710_ = lean_ctor_get(v_state_3355_, 6);
v_requiresData_3711_ = lean_ctor_get_uint8(v_state_3355_, sizeof(void*)*9);
v_expectData_3712_ = lean_ctor_get(v_state_3355_, 7);
v_pendingHead_3713_ = lean_ctor_get(v_state_3355_, 8);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_state_3355_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3715_ = v_state_3355_;
v_isShared_3716_ = v_isSharedCheck_3727_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_pendingHead_3713_);
lean_inc(v_expectData_3712_);
lean_inc(v_respStream_3710_);
lean_inc(v_response_3709_);
lean_inc(v_headerTimeout_3708_);
lean_inc(v_currentTimeout_3707_);
lean_inc(v_keepAliveTimeout_3706_);
lean_inc(v_requestStream_3705_);
lean_inc(v_machine_3704_);
lean_dec(v_state_3355_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3727_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; lean_object* v___x_3721_; 
v___x_3717_ = lean_box(55);
v___x_3718_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3704_, v___x_3717_);
v___x_3719_ = 0;
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3718_);
v___x_3721_ = v___x_3715_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_requestStream_3705_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_keepAliveTimeout_3706_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v_currentTimeout_3707_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v_headerTimeout_3708_);
lean_ctor_set(v_reuseFailAlloc_3726_, 5, v_response_3709_);
lean_ctor_set(v_reuseFailAlloc_3726_, 6, v_respStream_3710_);
lean_ctor_set(v_reuseFailAlloc_3726_, 7, v_expectData_3712_);
lean_ctor_set(v_reuseFailAlloc_3726_, 8, v_pendingHead_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, sizeof(void*)*9, v_requiresData_3711_);
v___x_3721_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
lean_ctor_set_uint8(v___x_3721_, sizeof(void*)*9 + 1, v___x_3719_);
v___x_3722_ = lean_box(v___x_3719_);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
return v___x_3725_;
}
}
}
default: 
{
uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_dec_ref(v_config_3353_);
lean_dec(v_handler_3352_);
lean_dec_ref(v_inst_3351_);
lean_dec_ref(v_inst_3350_);
v___x_3728_ = 1;
v___x_3729_ = lean_box(v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_state_3355_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3733_, lean_object* v_inst_3734_, lean_object* v_handler_3735_, lean_object* v_config_3736_, lean_object* v_event_3737_, lean_object* v_state_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3733_, v_inst_3734_, v_handler_3735_, v_config_3736_, v_event_3737_, v_state_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3741_, lean_object* v_00_u03b2_3742_, lean_object* v_inst_3743_, lean_object* v_inst_3744_, lean_object* v_handler_3745_, lean_object* v_config_3746_, lean_object* v_event_3747_, lean_object* v_state_3748_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3743_, v_inst_3744_, v_handler_3745_, v_config_3746_, v_event_3747_, v_state_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3751_, lean_object* v_00_u03b2_3752_, lean_object* v_inst_3753_, lean_object* v_inst_3754_, lean_object* v_handler_3755_, lean_object* v_config_3756_, lean_object* v_event_3757_, lean_object* v_state_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3751_, v_00_u03b2_3752_, v_inst_3753_, v_inst_3754_, v_handler_3755_, v_config_3756_, v_event_3757_, v_state_3758_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3761_, uint8_t v_handlerDispatched_3762_, lean_object* v_currentTimeout_3763_, lean_object* v_respStream_3764_, lean_object* v_expectData_3765_, lean_object* v_headerTimeout_3766_, lean_object* v_keepAliveTimeout_3767_, lean_object* v_response_3768_, lean_object* v_socket_3769_, uint8_t v_requiresData_3770_, uint8_t v_sentMessage_3771_, lean_object* v_reader_3772_, uint8_t v_requestBodyInterested_3773_, lean_object* v_requestBody_3774_){
_start:
{
lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3788_; 
if (v_requiresData_3770_ == 0)
{
if (v_handlerDispatched_3762_ == 0)
{
goto v___jp_3791_;
}
else
{
if (lean_obj_tag(v_respStream_3764_) == 0)
{
if (v_sentMessage_3771_ == 0)
{
lean_object* v_state_3795_; 
v_state_3795_ = lean_ctor_get(v_reader_3772_, 0);
if (lean_obj_tag(v_state_3795_) == 2)
{
if (v_requestBodyInterested_3773_ == 0)
{
lean_dec(v_socket_3769_);
goto v___jp_3793_;
}
else
{
goto v___jp_3791_;
}
}
else
{
lean_dec(v_socket_3769_);
goto v___jp_3793_;
}
}
else
{
goto v___jp_3791_;
}
}
else
{
goto v___jp_3791_;
}
}
}
else
{
goto v___jp_3791_;
}
v___jp_3776_:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3784_, 0, v___y_3779_);
lean_ctor_set(v___x_3784_, 1, v___y_3780_);
lean_ctor_set(v___x_3784_, 2, v___y_3783_);
lean_ctor_set(v___x_3784_, 3, v___y_3778_);
lean_ctor_set(v___x_3784_, 4, v_requestBody_3774_);
lean_ctor_set(v___x_3784_, 5, v___y_3777_);
lean_ctor_set(v___x_3784_, 6, v___y_3782_);
lean_ctor_set(v___x_3784_, 7, v___y_3781_);
lean_ctor_set(v___x_3784_, 8, v_connectionContext_3761_);
v___x_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
return v___x_3786_;
}
v___jp_3787_:
{
if (v_handlerDispatched_3762_ == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v_response_3768_);
v___x_3789_ = lean_box(0);
v___y_3777_ = v_currentTimeout_3763_;
v___y_3778_ = v_respStream_3764_;
v___y_3779_ = v___y_3788_;
v___y_3780_ = v_expectData_3765_;
v___y_3781_ = v_headerTimeout_3766_;
v___y_3782_ = v_keepAliveTimeout_3767_;
v___y_3783_ = v___x_3789_;
goto v___jp_3776_;
}
else
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v_response_3768_);
v___y_3777_ = v_currentTimeout_3763_;
v___y_3778_ = v_respStream_3764_;
v___y_3779_ = v___y_3788_;
v___y_3780_ = v_expectData_3765_;
v___y_3781_ = v_headerTimeout_3766_;
v___y_3782_ = v_keepAliveTimeout_3767_;
v___y_3783_ = v___x_3790_;
goto v___jp_3776_;
}
}
v___jp_3791_:
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3792_, 0, v_socket_3769_);
v___y_3788_ = v___x_3792_;
goto v___jp_3787_;
}
v___jp_3793_:
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_box(0);
v___y_3788_ = v___x_3794_;
goto v___jp_3787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3796_, lean_object* v_handlerDispatched_3797_, lean_object* v_currentTimeout_3798_, lean_object* v_respStream_3799_, lean_object* v_expectData_3800_, lean_object* v_headerTimeout_3801_, lean_object* v_keepAliveTimeout_3802_, lean_object* v_response_3803_, lean_object* v_socket_3804_, lean_object* v_requiresData_3805_, lean_object* v_sentMessage_3806_, lean_object* v_reader_3807_, lean_object* v_requestBodyInterested_3808_, lean_object* v_requestBody_3809_, lean_object* v___y_3810_){
_start:
{
uint8_t v_handlerDispatched_boxed_3811_; uint8_t v_requiresData_boxed_3812_; uint8_t v_sentMessage_boxed_3813_; uint8_t v_requestBodyInterested_boxed_3814_; lean_object* v_res_3815_; 
v_handlerDispatched_boxed_3811_ = lean_unbox(v_handlerDispatched_3797_);
v_requiresData_boxed_3812_ = lean_unbox(v_requiresData_3805_);
v_sentMessage_boxed_3813_ = lean_unbox(v_sentMessage_3806_);
v_requestBodyInterested_boxed_3814_ = lean_unbox(v_requestBodyInterested_3808_);
v_res_3815_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3796_, v_handlerDispatched_boxed_3811_, v_currentTimeout_3798_, v_respStream_3799_, v_expectData_3800_, v_headerTimeout_3801_, v_keepAliveTimeout_3802_, v_response_3803_, v_socket_3804_, v_requiresData_boxed_3812_, v_sentMessage_boxed_3813_, v_reader_3807_, v_requestBodyInterested_boxed_3814_, v_requestBody_3809_);
lean_dec_ref(v_reader_3807_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3816_, lean_object* v_x_3817_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v___f_3816_);
v_a_3819_ = lean_ctor_get(v_x_3817_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_x_3817_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3821_ = v_x_3817_;
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v_x_3817_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
return v___x_3825_;
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3829_; 
v_a_3828_ = lean_ctor_get(v_x_3817_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v_x_3817_, 1);
v___x_3829_ = lean_apply_2(v___f_3816_, v_a_3828_, lean_box(0));
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3830_, lean_object* v_x_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3830_, v_x_3831_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3838_, uint8_t v_handlerDispatched_3839_, lean_object* v_currentTimeout_3840_, lean_object* v_respStream_3841_, lean_object* v_expectData_3842_, lean_object* v_headerTimeout_3843_, lean_object* v_keepAliveTimeout_3844_, lean_object* v_response_3845_, lean_object* v_socket_3846_, uint8_t v_requiresData_3847_, uint8_t v_sentMessage_3848_, lean_object* v_reader_3849_, uint8_t v_pullBodyStalled_3850_, uint8_t v_requestBodyOpen_3851_, lean_object* v_requestStream_3852_, uint8_t v_requestBodyInterested_3853_){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___f_3859_; lean_object* v___f_3860_; uint8_t v___y_3862_; 
v___x_3855_ = lean_box(v_handlerDispatched_3839_);
v___x_3856_ = lean_box(v_requiresData_3847_);
v___x_3857_ = lean_box(v_sentMessage_3848_);
v___x_3858_ = lean_box(v_requestBodyInterested_3853_);
lean_inc_ref(v_reader_3849_);
v___f_3859_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3859_, 0, v_connectionContext_3838_);
lean_closure_set(v___f_3859_, 1, v___x_3855_);
lean_closure_set(v___f_3859_, 2, v_currentTimeout_3840_);
lean_closure_set(v___f_3859_, 3, v_respStream_3841_);
lean_closure_set(v___f_3859_, 4, v_expectData_3842_);
lean_closure_set(v___f_3859_, 5, v_headerTimeout_3843_);
lean_closure_set(v___f_3859_, 6, v_keepAliveTimeout_3844_);
lean_closure_set(v___f_3859_, 7, v_response_3845_);
lean_closure_set(v___f_3859_, 8, v_socket_3846_);
lean_closure_set(v___f_3859_, 9, v___x_3856_);
lean_closure_set(v___f_3859_, 10, v___x_3857_);
lean_closure_set(v___f_3859_, 11, v_reader_3849_);
lean_closure_set(v___f_3859_, 12, v___x_3858_);
v___f_3860_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3860_, 0, v___f_3859_);
if (v_sentMessage_3848_ == 0)
{
lean_object* v_state_3866_; 
v_state_3866_ = lean_ctor_get(v_reader_3849_, 0);
lean_inc(v_state_3866_);
lean_dec_ref(v_reader_3849_);
if (lean_obj_tag(v_state_3866_) == 2)
{
lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3877_; 
v_isSharedCheck_3877_ = !lean_is_exclusive(v_state_3866_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; 
v_unused_3878_ = lean_ctor_get(v_state_3866_, 0);
lean_dec(v_unused_3878_);
v___x_3868_ = v_state_3866_;
v_isShared_3869_ = v_isSharedCheck_3877_;
goto v_resetjp_3867_;
}
else
{
lean_dec(v_state_3866_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3877_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
if (v_pullBodyStalled_3850_ == 0)
{
if (v_requestBodyOpen_3851_ == 0)
{
lean_del_object(v___x_3868_);
lean_dec_ref(v_requestStream_3852_);
v___y_3862_ = v_requestBodyOpen_3851_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 1);
lean_ctor_set(v___x_3868_, 0, v_requestStream_3852_);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_requestStream_3852_);
v___x_3871_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3872_ = lean_unsigned_to_nat(0u);
v___x_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
v___x_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3872_, v_pullBodyStalled_3850_, v___x_3874_, v___f_3860_);
return v___x_3875_;
}
}
}
else
{
lean_del_object(v___x_3868_);
lean_dec_ref(v_requestStream_3852_);
v___y_3862_ = v_sentMessage_3848_;
goto v___jp_3861_;
}
}
}
else
{
lean_dec(v_state_3866_);
lean_dec_ref(v_requestStream_3852_);
v___y_3862_ = v_sentMessage_3848_;
goto v___jp_3861_;
}
}
else
{
uint8_t v___x_3879_; 
lean_dec_ref(v_requestStream_3852_);
lean_dec_ref(v_reader_3849_);
v___x_3879_ = 0;
v___y_3862_ = v___x_3879_;
goto v___jp_3861_;
}
v___jp_3861_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_unsigned_to_nat(0u);
v___x_3864_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3865_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3863_, v___y_3862_, v___x_3864_, v___f_3860_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3880_ = _args[0];
lean_object* v_handlerDispatched_3881_ = _args[1];
lean_object* v_currentTimeout_3882_ = _args[2];
lean_object* v_respStream_3883_ = _args[3];
lean_object* v_expectData_3884_ = _args[4];
lean_object* v_headerTimeout_3885_ = _args[5];
lean_object* v_keepAliveTimeout_3886_ = _args[6];
lean_object* v_response_3887_ = _args[7];
lean_object* v_socket_3888_ = _args[8];
lean_object* v_requiresData_3889_ = _args[9];
lean_object* v_sentMessage_3890_ = _args[10];
lean_object* v_reader_3891_ = _args[11];
lean_object* v_pullBodyStalled_3892_ = _args[12];
lean_object* v_requestBodyOpen_3893_ = _args[13];
lean_object* v_requestStream_3894_ = _args[14];
lean_object* v_requestBodyInterested_3895_ = _args[15];
lean_object* v___y_3896_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3897_; uint8_t v_requiresData_boxed_3898_; uint8_t v_sentMessage_boxed_3899_; uint8_t v_pullBodyStalled_boxed_3900_; uint8_t v_requestBodyOpen_boxed_3901_; uint8_t v_requestBodyInterested_boxed_3902_; lean_object* v_res_3903_; 
v_handlerDispatched_boxed_3897_ = lean_unbox(v_handlerDispatched_3881_);
v_requiresData_boxed_3898_ = lean_unbox(v_requiresData_3889_);
v_sentMessage_boxed_3899_ = lean_unbox(v_sentMessage_3890_);
v_pullBodyStalled_boxed_3900_ = lean_unbox(v_pullBodyStalled_3892_);
v_requestBodyOpen_boxed_3901_ = lean_unbox(v_requestBodyOpen_3893_);
v_requestBodyInterested_boxed_3902_ = lean_unbox(v_requestBodyInterested_3895_);
v_res_3903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3880_, v_handlerDispatched_boxed_3897_, v_currentTimeout_3882_, v_respStream_3883_, v_expectData_3884_, v_headerTimeout_3885_, v_keepAliveTimeout_3886_, v_response_3887_, v_socket_3888_, v_requiresData_boxed_3898_, v_sentMessage_boxed_3899_, v_reader_3891_, v_pullBodyStalled_boxed_3900_, v_requestBodyOpen_boxed_3901_, v_requestStream_3894_, v_requestBodyInterested_boxed_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3904_, lean_object* v_x_3905_){
_start:
{
if (lean_obj_tag(v_x_3905_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v___f_3904_);
v_a_3907_ = lean_ctor_get(v_x_3905_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_x_3905_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3909_ = v_x_3905_;
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v_x_3905_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3917_; 
v_a_3916_ = lean_ctor_get(v_x_3905_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v_x_3905_, 1);
v___x_3917_ = lean_apply_2(v___f_3904_, v_a_3916_, lean_box(0));
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3918_, lean_object* v_x_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3918_, v_x_3919_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3922_, uint8_t v_handlerDispatched_3923_, lean_object* v_currentTimeout_3924_, lean_object* v_respStream_3925_, lean_object* v_expectData_3926_, lean_object* v_headerTimeout_3927_, lean_object* v_keepAliveTimeout_3928_, lean_object* v_response_3929_, lean_object* v_socket_3930_, uint8_t v_requiresData_3931_, uint8_t v_sentMessage_3932_, lean_object* v_reader_3933_, uint8_t v_pullBodyStalled_3934_, lean_object* v_requestStream_3935_, uint8_t v_requestBodyOpen_3936_){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___f_3943_; lean_object* v___f_3944_; uint8_t v___y_3946_; 
v___x_3938_ = lean_box(v_handlerDispatched_3923_);
v___x_3939_ = lean_box(v_requiresData_3931_);
v___x_3940_ = lean_box(v_sentMessage_3932_);
v___x_3941_ = lean_box(v_pullBodyStalled_3934_);
v___x_3942_ = lean_box(v_requestBodyOpen_3936_);
lean_inc_ref(v_requestStream_3935_);
lean_inc_ref(v_reader_3933_);
v___f_3943_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3943_, 0, v_connectionContext_3922_);
lean_closure_set(v___f_3943_, 1, v___x_3938_);
lean_closure_set(v___f_3943_, 2, v_currentTimeout_3924_);
lean_closure_set(v___f_3943_, 3, v_respStream_3925_);
lean_closure_set(v___f_3943_, 4, v_expectData_3926_);
lean_closure_set(v___f_3943_, 5, v_headerTimeout_3927_);
lean_closure_set(v___f_3943_, 6, v_keepAliveTimeout_3928_);
lean_closure_set(v___f_3943_, 7, v_response_3929_);
lean_closure_set(v___f_3943_, 8, v_socket_3930_);
lean_closure_set(v___f_3943_, 9, v___x_3939_);
lean_closure_set(v___f_3943_, 10, v___x_3940_);
lean_closure_set(v___f_3943_, 11, v_reader_3933_);
lean_closure_set(v___f_3943_, 12, v___x_3941_);
lean_closure_set(v___f_3943_, 13, v___x_3942_);
lean_closure_set(v___f_3943_, 14, v_requestStream_3935_);
v___f_3944_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3944_, 0, v___f_3943_);
if (v_sentMessage_3932_ == 0)
{
lean_object* v_state_3952_; 
v_state_3952_ = lean_ctor_get(v_reader_3933_, 0);
lean_inc(v_state_3952_);
lean_dec_ref(v_reader_3933_);
if (lean_obj_tag(v_state_3952_) == 2)
{
lean_dec_ref_known(v_state_3952_, 1);
if (v_requestBodyOpen_3936_ == 0)
{
lean_dec_ref(v_requestStream_3935_);
v___y_3946_ = v_requestBodyOpen_3936_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = lean_unsigned_to_nat(0u);
v___x_3954_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3935_);
v___x_3955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3953_, v_sentMessage_3932_, v___x_3954_, v___f_3944_);
return v___x_3955_;
}
}
else
{
lean_dec(v_state_3952_);
lean_dec_ref(v_requestStream_3935_);
v___y_3946_ = v_sentMessage_3932_;
goto v___jp_3945_;
}
}
else
{
uint8_t v___x_3956_; 
lean_dec_ref(v_requestStream_3935_);
lean_dec_ref(v_reader_3933_);
v___x_3956_ = 0;
v___y_3946_ = v___x_3956_;
goto v___jp_3945_;
}
v___jp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3947_ = lean_unsigned_to_nat(0u);
v___x_3948_ = lean_box(v___y_3946_);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
v___x_3951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3947_, v___y_3946_, v___x_3950_, v___f_3944_);
return v___x_3951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3957_, lean_object* v_handlerDispatched_3958_, lean_object* v_currentTimeout_3959_, lean_object* v_respStream_3960_, lean_object* v_expectData_3961_, lean_object* v_headerTimeout_3962_, lean_object* v_keepAliveTimeout_3963_, lean_object* v_response_3964_, lean_object* v_socket_3965_, lean_object* v_requiresData_3966_, lean_object* v_sentMessage_3967_, lean_object* v_reader_3968_, lean_object* v_pullBodyStalled_3969_, lean_object* v_requestStream_3970_, lean_object* v_requestBodyOpen_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v_handlerDispatched_boxed_3973_; uint8_t v_requiresData_boxed_3974_; uint8_t v_sentMessage_boxed_3975_; uint8_t v_pullBodyStalled_boxed_3976_; uint8_t v_requestBodyOpen_boxed_3977_; lean_object* v_res_3978_; 
v_handlerDispatched_boxed_3973_ = lean_unbox(v_handlerDispatched_3958_);
v_requiresData_boxed_3974_ = lean_unbox(v_requiresData_3966_);
v_sentMessage_boxed_3975_ = lean_unbox(v_sentMessage_3967_);
v_pullBodyStalled_boxed_3976_ = lean_unbox(v_pullBodyStalled_3969_);
v_requestBodyOpen_boxed_3977_ = lean_unbox(v_requestBodyOpen_3971_);
v_res_3978_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3957_, v_handlerDispatched_boxed_3973_, v_currentTimeout_3959_, v_respStream_3960_, v_expectData_3961_, v_headerTimeout_3962_, v_keepAliveTimeout_3963_, v_response_3964_, v_socket_3965_, v_requiresData_boxed_3974_, v_sentMessage_boxed_3975_, v_reader_3968_, v_pullBodyStalled_boxed_3976_, v_requestStream_3970_, v_requestBodyOpen_boxed_3977_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3979_, lean_object* v___f_3980_, uint8_t v___x_3981_, lean_object* v_x_3982_){
_start:
{
uint8_t v___y_3985_; 
if (lean_obj_tag(v_x_3982_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3999_; 
lean_dec_ref(v___f_3980_);
v_a_3991_ = lean_ctor_get(v_x_3982_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_x_3982_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3993_ = v_x_3982_;
v_isShared_3994_ = v_isSharedCheck_3999_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v_x_3982_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3999_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
return v___x_3997_;
}
}
}
else
{
lean_object* v_a_4000_; uint8_t v___x_4001_; 
v_a_4000_ = lean_ctor_get(v_x_3982_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v_x_3982_, 1);
v___x_4001_ = lean_unbox(v_a_4000_);
lean_dec(v_a_4000_);
if (v___x_4001_ == 0)
{
v___y_3985_ = v___x_3981_;
goto v___jp_3984_;
}
else
{
v___y_3985_ = v_sentMessage_3979_;
goto v___jp_3984_;
}
}
v___jp_3984_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = lean_box(v___y_3985_);
v___x_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
v___x_3990_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3986_, v_sentMessage_3979_, v___x_3989_, v___f_3980_);
return v___x_3990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_4002_, lean_object* v___f_4003_, lean_object* v___x_4004_, lean_object* v_x_4005_, lean_object* v___y_4006_){
_start:
{
uint8_t v_sentMessage_boxed_4007_; uint8_t v___x_2892__boxed_4008_; lean_object* v_res_4009_; 
v_sentMessage_boxed_4007_ = lean_unbox(v_sentMessage_4002_);
v___x_2892__boxed_4008_ = lean_unbox(v___x_4004_);
v_res_4009_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_4007_, v___f_4003_, v___x_2892__boxed_4008_, v_x_4005_);
return v_res_4009_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___f_4010_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_4011_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4012_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_4013_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4013_, 0, lean_box(0));
lean_closure_set(v___x_4013_, 1, lean_box(0));
lean_closure_set(v___x_4013_, 2, v___x_4012_);
lean_closure_set(v___x_4013_, 3, lean_box(0));
lean_closure_set(v___x_4013_, 4, lean_box(0));
lean_closure_set(v___x_4013_, 5, v___x_4011_);
lean_closure_set(v___x_4013_, 6, v___f_4010_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4014_, lean_object* v_connectionContext_4015_, lean_object* v_state_4016_){
_start:
{
lean_object* v_machine_4018_; lean_object* v_writer_4019_; lean_object* v_requestStream_4020_; lean_object* v_keepAliveTimeout_4021_; lean_object* v_currentTimeout_4022_; lean_object* v_headerTimeout_4023_; lean_object* v_response_4024_; lean_object* v_respStream_4025_; uint8_t v_requiresData_4026_; lean_object* v_expectData_4027_; uint8_t v_handlerDispatched_4028_; lean_object* v_reader_4029_; uint8_t v_pullBodyStalled_4030_; uint8_t v_sentMessage_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___f_4036_; lean_object* v___f_4037_; uint8_t v___y_4039_; 
v_machine_4018_ = lean_ctor_get(v_state_4016_, 0);
lean_inc_ref(v_machine_4018_);
v_writer_4019_ = lean_ctor_get(v_machine_4018_, 1);
lean_inc_ref(v_writer_4019_);
v_requestStream_4020_ = lean_ctor_get(v_state_4016_, 1);
lean_inc_ref_n(v_requestStream_4020_, 2);
v_keepAliveTimeout_4021_ = lean_ctor_get(v_state_4016_, 2);
lean_inc(v_keepAliveTimeout_4021_);
v_currentTimeout_4022_ = lean_ctor_get(v_state_4016_, 3);
lean_inc(v_currentTimeout_4022_);
v_headerTimeout_4023_ = lean_ctor_get(v_state_4016_, 4);
lean_inc(v_headerTimeout_4023_);
v_response_4024_ = lean_ctor_get(v_state_4016_, 5);
lean_inc_ref(v_response_4024_);
v_respStream_4025_ = lean_ctor_get(v_state_4016_, 6);
lean_inc(v_respStream_4025_);
v_requiresData_4026_ = lean_ctor_get_uint8(v_state_4016_, sizeof(void*)*9);
v_expectData_4027_ = lean_ctor_get(v_state_4016_, 7);
lean_inc(v_expectData_4027_);
v_handlerDispatched_4028_ = lean_ctor_get_uint8(v_state_4016_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4016_);
v_reader_4029_ = lean_ctor_get(v_machine_4018_, 0);
lean_inc_ref_n(v_reader_4029_, 2);
v_pullBodyStalled_4030_ = lean_ctor_get_uint8(v_machine_4018_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_4018_);
v_sentMessage_4031_ = lean_ctor_get_uint8(v_writer_4019_, sizeof(void*)*6);
lean_dec_ref(v_writer_4019_);
v___x_4032_ = lean_box(v_handlerDispatched_4028_);
v___x_4033_ = lean_box(v_requiresData_4026_);
v___x_4034_ = lean_box(v_sentMessage_4031_);
v___x_4035_ = lean_box(v_pullBodyStalled_4030_);
v___f_4036_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_4036_, 0, v_connectionContext_4015_);
lean_closure_set(v___f_4036_, 1, v___x_4032_);
lean_closure_set(v___f_4036_, 2, v_currentTimeout_4022_);
lean_closure_set(v___f_4036_, 3, v_respStream_4025_);
lean_closure_set(v___f_4036_, 4, v_expectData_4027_);
lean_closure_set(v___f_4036_, 5, v_headerTimeout_4023_);
lean_closure_set(v___f_4036_, 6, v_keepAliveTimeout_4021_);
lean_closure_set(v___f_4036_, 7, v_response_4024_);
lean_closure_set(v___f_4036_, 8, v_socket_4014_);
lean_closure_set(v___f_4036_, 9, v___x_4033_);
lean_closure_set(v___f_4036_, 10, v___x_4034_);
lean_closure_set(v___f_4036_, 11, v_reader_4029_);
lean_closure_set(v___f_4036_, 12, v___x_4035_);
lean_closure_set(v___f_4036_, 13, v_requestStream_4020_);
v___f_4037_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4037_, 0, v___f_4036_);
if (v_sentMessage_4031_ == 0)
{
lean_object* v_state_4045_; 
v_state_4045_ = lean_ctor_get(v_reader_4029_, 0);
lean_inc(v_state_4045_);
lean_dec_ref(v_reader_4029_);
if (lean_obj_tag(v_state_4045_) == 2)
{
uint8_t v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___f_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___f_4052_; lean_object* v___f_4053_; lean_object* v___x_4054_; lean_object* v___x_2542__overap_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_dec_ref_known(v_state_4045_, 1);
v___x_4046_ = 1;
v___x_4047_ = lean_box(v_sentMessage_4031_);
v___x_4048_ = lean_box(v___x_4046_);
v___f_4049_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4049_, 0, v___x_4047_);
lean_closure_set(v___f_4049_, 1, v___f_4037_);
lean_closure_set(v___f_4049_, 2, v___x_4048_);
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4052_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4053_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4054_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2542__overap_4055_ = l_Std_Mutex_atomically___redArg(v___x_4051_, v___f_4052_, v___f_4053_, v_requestStream_4020_, v___x_4054_);
v___x_4056_ = lean_apply_1(v___x_2542__overap_4055_, lean_box(0));
v___x_4057_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4050_, v_sentMessage_4031_, v___x_4056_, v___f_4049_);
return v___x_4057_;
}
else
{
lean_dec(v_state_4045_);
lean_dec_ref(v_requestStream_4020_);
v___y_4039_ = v_sentMessage_4031_;
goto v___jp_4038_;
}
}
else
{
uint8_t v___x_4058_; 
lean_dec_ref(v_reader_4029_);
lean_dec_ref(v_requestStream_4020_);
v___x_4058_ = 0;
v___y_4039_ = v___x_4058_;
goto v___jp_4038_;
}
v___jp_4038_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = lean_box(v___y_4039_);
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
v___x_4044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4040_, v___y_4039_, v___x_4043_, v___f_4037_);
return v___x_4044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4059_, lean_object* v_connectionContext_4060_, lean_object* v_state_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4059_, v_connectionContext_4060_, v_state_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4064_, lean_object* v_00_u03b2_4065_, lean_object* v_inst_4066_, lean_object* v_socket_4067_, lean_object* v_connectionContext_4068_, lean_object* v_state_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4067_, v_connectionContext_4068_, v_state_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4072_, lean_object* v_00_u03b2_4073_, lean_object* v_inst_4074_, lean_object* v_socket_4075_, lean_object* v_connectionContext_4076_, lean_object* v_state_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4072_, v_00_u03b2_4073_, v_inst_4074_, v_socket_4075_, v_connectionContext_4076_, v_state_4077_);
lean_dec_ref(v_inst_4074_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_4080_){
_start:
{
if (lean_obj_tag(v_x_4080_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4090_; 
v_a_4082_ = lean_ctor_get(v_x_4080_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_x_4080_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4084_ = v_x_4080_;
v_isShared_4085_ = v_isSharedCheck_4090_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v_x_4080_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4090_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4100_; 
v_a_4091_ = lean_ctor_get(v_x_4080_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_x_4080_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4093_ = v_x_4080_;
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v_x_4080_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; lean_object* v___x_4097_; 
v___x_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_a_4091_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 0, v___x_4095_);
v___x_4097_ = v___x_4093_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4095_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_4108_){
_start:
{
if (lean_obj_tag(v_x_4108_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4118_; 
v_a_4110_ = lean_ctor_get(v_x_4108_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_x_4108_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4112_ = v_x_4108_;
v_isShared_4113_ = v_isSharedCheck_4118_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v_x_4108_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4118_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
return v___x_4116_;
}
}
}
else
{
lean_object* v___x_4119_; 
lean_dec_ref_known(v_x_4108_, 1);
v___x_4119_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_4120_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_4123_, lean_object* v_handler_4124_, lean_object* v___f_4125_, lean_object* v_x_4126_){
_start:
{
if (lean_obj_tag(v_x_4126_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_a_4128_ = lean_ctor_get(v_x_4126_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v_x_4126_, 1);
v___x_4129_ = lean_unsigned_to_nat(0u);
v___x_4130_ = 0;
v___x_4131_ = lean_apply_3(v_onFailure_4123_, v_handler_4124_, v_a_4128_, lean_box(0));
v___x_4132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4129_, v___x_4130_, v___x_4131_, v___f_4125_);
return v___x_4132_;
}
else
{
lean_object* v___x_4133_; 
lean_dec_ref(v___f_4125_);
lean_dec(v_handler_4124_);
lean_dec_ref(v_onFailure_4123_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_x_4126_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_4134_, lean_object* v_handler_4135_, lean_object* v___f_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_4134_, v_handler_4135_, v___f_4136_, v_x_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4140_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4150_; 
v_a_4142_ = lean_ctor_get(v_x_4140_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_x_4140_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4144_ = v_x_4140_;
v_isShared_4145_ = v_isSharedCheck_4150_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v_x_4140_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4150_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4142_);
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
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4169_; 
v_a_4151_ = lean_ctor_get(v_x_4140_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_x_4140_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4153_ = v_x_4140_;
v_isShared_4154_ = v_isSharedCheck_4169_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v_x_4140_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4169_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v_snd_4155_; uint8_t v___x_4156_; 
v_snd_4155_ = lean_ctor_get(v_a_4151_, 1);
v___x_4156_ = lean_unbox(v_snd_4155_);
if (v___x_4156_ == 0)
{
lean_object* v_fst_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v_fst_4157_ = lean_ctor_get(v_a_4151_, 0);
lean_inc(v_fst_4157_);
lean_dec(v_a_4151_);
v___x_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4158_, 0, v_fst_4157_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4158_);
v___x_4160_ = v___x_4153_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
lean_object* v___x_4161_; 
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
else
{
lean_object* v_fst_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v_fst_4163_ = lean_ctor_get(v_a_4151_, 0);
lean_inc(v_fst_4163_);
lean_dec(v_a_4151_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_fst_4163_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4164_);
v___x_4166_ = v___x_4153_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4170_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4173_, lean_object* v_socket_4174_, lean_object* v_____r_4175_){
_start:
{
lean_object* v_val_4178_; lean_object* v_close_4180_; lean_object* v___x_4181_; 
v_close_4180_ = lean_ctor_get(v_inst_4173_, 3);
lean_inc_ref(v_close_4180_);
lean_dec_ref(v_inst_4173_);
v___x_4181_ = lean_apply_2(v_close_4180_, v_socket_4174_, lean_box(0));
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4181_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4181_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
lean_ctor_set_tag(v___x_4184_, 1);
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
v_val_4178_ = v___x_4187_;
goto v___jp_4177_;
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
v_a_4190_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4181_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4181_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 0);
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
v_val_4178_ = v___x_4195_;
goto v___jp_4177_;
}
}
}
v___jp_4177_:
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_val_4178_);
return v___x_4179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4198_, lean_object* v_socket_4199_, lean_object* v_____r_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4198_, v_socket_4199_, v_____r_4200_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4203_, lean_object* v_x_4204_){
_start:
{
if (lean_obj_tag(v_x_4204_) == 0)
{
lean_object* v___x_4206_; 
lean_dec_ref(v___f_4203_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_x_4204_);
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4208_; 
v_a_4207_ = lean_ctor_get(v_x_4204_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v_x_4204_, 1);
v___x_4208_ = lean_apply_2(v___f_4203_, v_a_4207_, lean_box(0));
return v___x_4208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4209_, lean_object* v_x_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4209_, v_x_4210_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4213_, lean_object* v_val_4214_, lean_object* v___f_4215_, lean_object* v___f_4216_, lean_object* v_x_4217_){
_start:
{
if (lean_obj_tag(v_x_4217_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4227_; 
lean_dec_ref(v___f_4216_);
lean_dec_ref(v___f_4215_);
lean_dec(v_val_4214_);
lean_dec_ref(v_close_4213_);
v_a_4219_ = lean_ctor_get(v_x_4217_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_x_4217_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4221_ = v_x_4217_;
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v_x_4217_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
}
else
{
lean_object* v_a_4228_; uint8_t v___x_4229_; 
v_a_4228_ = lean_ctor_get(v_x_4217_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v_x_4217_, 1);
v___x_4229_ = lean_unbox(v_a_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref(v___f_4216_);
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = lean_apply_2(v_close_4213_, v_val_4214_, lean_box(0));
v___x_4232_ = lean_unbox(v_a_4228_);
lean_dec(v_a_4228_);
v___x_4233_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4230_, v___x_4232_, v___x_4231_, v___f_4215_);
return v___x_4233_;
}
else
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_dec(v_a_4228_);
lean_dec_ref(v___f_4215_);
lean_dec(v_val_4214_);
lean_dec_ref(v_close_4213_);
v___x_4234_ = lean_box(0);
v___x_4235_ = lean_apply_2(v___f_4216_, v___x_4234_, lean_box(0));
return v___x_4235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4236_, lean_object* v_val_4237_, lean_object* v___f_4238_, lean_object* v___f_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4236_, v_val_4237_, v___f_4238_, v___f_4239_, v_x_4240_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4243_, lean_object* v_responseBodyInstance_4244_, lean_object* v___f_4245_, lean_object* v___f_4246_, lean_object* v_____r_4247_){
_start:
{
if (lean_obj_tag(v_respStream_4243_) == 1)
{
lean_object* v_val_4249_; lean_object* v_close_4250_; lean_object* v_isClosed_4251_; lean_object* v___f_4252_; lean_object* v___x_4253_; uint8_t v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_val_4249_ = lean_ctor_get(v_respStream_4243_, 0);
lean_inc_n(v_val_4249_, 2);
lean_dec_ref_known(v_respStream_4243_, 1);
v_close_4250_ = lean_ctor_get(v_responseBodyInstance_4244_, 1);
lean_inc_ref(v_close_4250_);
v_isClosed_4251_ = lean_ctor_get(v_responseBodyInstance_4244_, 2);
lean_inc_ref(v_isClosed_4251_);
lean_dec_ref(v_responseBodyInstance_4244_);
v___f_4252_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4252_, 0, v_close_4250_);
lean_closure_set(v___f_4252_, 1, v_val_4249_);
lean_closure_set(v___f_4252_, 2, v___f_4245_);
lean_closure_set(v___f_4252_, 3, v___f_4246_);
v___x_4253_ = lean_unsigned_to_nat(0u);
v___x_4254_ = 0;
v___x_4255_ = lean_apply_2(v_isClosed_4251_, v_val_4249_, lean_box(0));
v___x_4256_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4253_, v___x_4254_, v___x_4255_, v___f_4252_);
return v___x_4256_;
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec_ref(v___f_4245_);
lean_dec_ref(v_responseBodyInstance_4244_);
lean_dec(v_respStream_4243_);
v___x_4257_ = lean_box(0);
v___x_4258_ = lean_apply_2(v___f_4246_, v___x_4257_, lean_box(0));
return v___x_4258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4259_, lean_object* v_responseBodyInstance_4260_, lean_object* v___f_4261_, lean_object* v___f_4262_, lean_object* v_____r_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4259_, v_responseBodyInstance_4260_, v___f_4261_, v___f_4262_, v_____r_4263_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4266_, lean_object* v___f_4267_, lean_object* v___f_4268_, lean_object* v_x_4269_){
_start:
{
if (lean_obj_tag(v_x_4269_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4279_; 
lean_dec_ref(v___f_4268_);
lean_dec_ref(v___f_4267_);
lean_dec_ref(v_requestStream_4266_);
v_a_4271_ = lean_ctor_get(v_x_4269_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_x_4269_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4273_ = v_x_4269_;
v_isShared_4274_ = v_isSharedCheck_4279_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v_x_4269_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4279_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
return v___x_4277_;
}
}
}
else
{
lean_object* v_a_4280_; uint8_t v___x_4281_; 
v_a_4280_ = lean_ctor_get(v_x_4269_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v_x_4269_, 1);
v___x_4281_ = lean_unbox(v_a_4280_);
if (v___x_4281_ == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4283_; uint8_t v___x_4284_; lean_object* v___x_4285_; 
lean_dec_ref(v___f_4268_);
v___x_4282_ = lean_unsigned_to_nat(0u);
v___x_4283_ = l_Std_Http_Body_Stream_close(v_requestStream_4266_);
v___x_4284_ = lean_unbox(v_a_4280_);
lean_dec(v_a_4280_);
v___x_4285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4282_, v___x_4284_, v___x_4283_, v___f_4267_);
return v___x_4285_;
}
else
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_dec(v_a_4280_);
lean_dec_ref(v___f_4267_);
lean_dec_ref(v_requestStream_4266_);
v___x_4286_ = lean_box(0);
v___x_4287_ = lean_apply_2(v___f_4268_, v___x_4286_, lean_box(0));
return v___x_4287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4288_, lean_object* v___f_4289_, lean_object* v___f_4290_, lean_object* v_x_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4288_, v___f_4289_, v___f_4290_, v_x_4291_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4294_, lean_object* v___f_4295_, lean_object* v___f_4296_, lean_object* v___f_4297_, lean_object* v_x_4298_){
_start:
{
if (lean_obj_tag(v_x_4298_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4308_; 
lean_dec_ref(v___f_4297_);
lean_dec_ref(v___f_4296_);
lean_dec_ref(v___f_4295_);
lean_dec_ref(v_responseBodyInstance_4294_);
v_a_4300_ = lean_ctor_get(v_x_4298_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_x_4298_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4302_ = v_x_4298_;
v_isShared_4303_ = v_isSharedCheck_4308_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v_x_4298_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4308_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
return v___x_4306_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v_requestStream_4310_; lean_object* v_respStream_4311_; lean_object* v___f_4312_; lean_object* v___f_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; lean_object* v___x_4317_; lean_object* v___f_4318_; lean_object* v___f_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4542__overap_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_a_4309_ = lean_ctor_get(v_x_4298_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v_x_4298_, 1);
v_requestStream_4310_ = lean_ctor_get(v_a_4309_, 1);
lean_inc_ref_n(v_requestStream_4310_, 2);
v_respStream_4311_ = lean_ctor_get(v_a_4309_, 6);
lean_inc(v_respStream_4311_);
lean_dec(v_a_4309_);
v___f_4312_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4312_, 0, v_respStream_4311_);
lean_closure_set(v___f_4312_, 1, v_responseBodyInstance_4294_);
lean_closure_set(v___f_4312_, 2, v___f_4295_);
lean_closure_set(v___f_4312_, 3, v___f_4296_);
lean_inc_ref(v___f_4312_);
v___f_4313_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4313_, 0, v___f_4312_);
v___f_4314_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4314_, 0, v_requestStream_4310_);
lean_closure_set(v___f_4314_, 1, v___f_4313_);
lean_closure_set(v___f_4314_, 2, v___f_4312_);
v___x_4315_ = lean_unsigned_to_nat(0u);
v___x_4316_ = 0;
v___x_4317_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4318_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4319_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4320_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4321_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4321_, 0, lean_box(0));
lean_closure_set(v___x_4321_, 1, lean_box(0));
lean_closure_set(v___x_4321_, 2, v___x_4317_);
lean_closure_set(v___x_4321_, 3, lean_box(0));
lean_closure_set(v___x_4321_, 4, lean_box(0));
lean_closure_set(v___x_4321_, 5, v___x_4320_);
lean_closure_set(v___x_4321_, 6, v___f_4297_);
v___x_4542__overap_4322_ = l_Std_Mutex_atomically___redArg(v___x_4317_, v___f_4318_, v___f_4319_, v_requestStream_4310_, v___x_4321_);
v___x_4323_ = lean_apply_1(v___x_4542__overap_4322_, lean_box(0));
v___x_4324_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4315_, v___x_4316_, v___x_4323_, v___f_4314_);
return v___x_4324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4325_, lean_object* v___f_4326_, lean_object* v___f_4327_, lean_object* v___f_4328_, lean_object* v_x_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4325_, v___f_4326_, v___f_4327_, v___f_4328_, v_x_4329_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4332_, lean_object* v_responseBodyInstance_4333_, lean_object* v_handler_4334_, lean_object* v_config_4335_, lean_object* v___x_4336_, uint8_t v___x_4337_, lean_object* v___f_4338_, lean_object* v_x_4339_){
_start:
{
if (lean_obj_tag(v_x_4339_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4349_; 
lean_dec_ref(v___f_4338_);
lean_dec_ref(v___x_4336_);
lean_dec_ref(v_config_4335_);
lean_dec(v_handler_4334_);
lean_dec_ref(v_responseBodyInstance_4333_);
lean_dec_ref(v_h_4332_);
v_a_4341_ = lean_ctor_get(v_x_4339_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_x_4339_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4343_ = v_x_4339_;
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v_x_4339_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
return v___x_4347_;
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v_a_4350_ = lean_ctor_get(v_x_4339_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v_x_4339_, 1);
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4332_, v_responseBodyInstance_4333_, v_handler_4334_, v_config_4335_, v_a_4350_, v___x_4336_);
v___x_4353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4351_, v___x_4337_, v___x_4352_, v___f_4338_);
return v___x_4353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4354_, lean_object* v_responseBodyInstance_4355_, lean_object* v_handler_4356_, lean_object* v_config_4357_, lean_object* v___x_4358_, lean_object* v___x_4359_, lean_object* v___f_4360_, lean_object* v_x_4361_, lean_object* v___y_4362_){
_start:
{
uint8_t v___x_5208__boxed_4363_; lean_object* v_res_4364_; 
v___x_5208__boxed_4363_ = lean_unbox(v___x_4359_);
v_res_4364_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4354_, v_responseBodyInstance_4355_, v_handler_4356_, v_config_4357_, v___x_4358_, v___x_5208__boxed_4363_, v___f_4360_, v_x_4361_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4365_, lean_object* v_h_4366_, lean_object* v_responseBodyInstance_4367_, lean_object* v_config_4368_, lean_object* v_handler_4369_, uint8_t v___x_4370_, lean_object* v___f_4371_, lean_object* v_x_4372_){
_start:
{
if (lean_obj_tag(v_x_4372_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4382_; 
lean_dec_ref(v___f_4371_);
lean_dec(v_handler_4369_);
lean_dec_ref(v_config_4368_);
lean_dec_ref(v_responseBodyInstance_4367_);
lean_dec_ref(v_h_4366_);
lean_dec_ref(v_inst_4365_);
v_a_4374_ = lean_ctor_get(v_x_4372_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v_x_4372_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4376_ = v_x_4372_;
v_isShared_4377_ = v_isSharedCheck_4382_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v_x_4372_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4382_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4380_; 
v___x_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
return v___x_4380_;
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_a_4383_ = lean_ctor_get(v_x_4372_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v_x_4372_, 1);
v___x_4384_ = lean_unsigned_to_nat(0u);
v___x_4385_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4365_, v_h_4366_, v_responseBodyInstance_4367_, v_config_4368_, v_handler_4369_, v_a_4383_);
v___x_4386_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4384_, v___x_4370_, v___x_4385_, v___f_4371_);
return v___x_4386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4387_, lean_object* v_h_4388_, lean_object* v_responseBodyInstance_4389_, lean_object* v_config_4390_, lean_object* v_handler_4391_, lean_object* v___x_4392_, lean_object* v___f_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_){
_start:
{
uint8_t v___x_5249__boxed_4396_; lean_object* v_res_4397_; 
v___x_5249__boxed_4396_ = lean_unbox(v___x_4392_);
v_res_4397_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4387_, v_h_4388_, v_responseBodyInstance_4389_, v_config_4390_, v_handler_4391_, v___x_5249__boxed_4396_, v___f_4393_, v_x_4394_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4398_, lean_object* v_h_4399_, lean_object* v_responseBodyInstance_4400_, lean_object* v_handler_4401_, lean_object* v_config_4402_, lean_object* v___f_4403_, lean_object* v_inst_4404_, lean_object* v_socket_4405_, lean_object* v_connectionContext_4406_, lean_object* v_x_4407_){
_start:
{
if (lean_obj_tag(v_x_4407_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4417_; 
lean_dec_ref(v_connectionContext_4406_);
lean_dec(v_socket_4405_);
lean_dec_ref(v_inst_4404_);
lean_dec_ref(v___f_4403_);
lean_dec_ref(v_config_4402_);
lean_dec(v_handler_4401_);
lean_dec_ref(v_responseBodyInstance_4400_);
lean_dec_ref(v_h_4399_);
v_a_4409_ = lean_ctor_get(v_x_4407_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4411_ = v_x_4407_;
v_isShared_4412_ = v_isSharedCheck_4417_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v_x_4407_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4417_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
return v___x_4415_;
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4452_; 
v_a_4418_ = lean_ctor_get(v_x_4407_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4420_ = v_x_4407_;
v_isShared_4421_ = v_isSharedCheck_4452_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v_x_4407_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4452_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v_machine_4428_; lean_object* v_requestStream_4429_; lean_object* v_keepAliveTimeout_4430_; lean_object* v_currentTimeout_4431_; lean_object* v_headerTimeout_4432_; lean_object* v_response_4433_; lean_object* v_respStream_4434_; uint8_t v_requiresData_4435_; lean_object* v_expectData_4436_; uint8_t v_handlerDispatched_4437_; lean_object* v_pendingHead_4438_; 
v_machine_4428_ = lean_ctor_get(v_a_4418_, 0);
v_requestStream_4429_ = lean_ctor_get(v_a_4418_, 1);
v_keepAliveTimeout_4430_ = lean_ctor_get(v_a_4418_, 2);
v_currentTimeout_4431_ = lean_ctor_get(v_a_4418_, 3);
v_headerTimeout_4432_ = lean_ctor_get(v_a_4418_, 4);
v_response_4433_ = lean_ctor_get(v_a_4418_, 5);
v_respStream_4434_ = lean_ctor_get(v_a_4418_, 6);
v_requiresData_4435_ = lean_ctor_get_uint8(v_a_4418_, sizeof(void*)*9);
v_expectData_4436_ = lean_ctor_get(v_a_4418_, 7);
v_handlerDispatched_4437_ = lean_ctor_get_uint8(v_a_4418_, sizeof(void*)*9 + 1);
v_pendingHead_4438_ = lean_ctor_get(v_a_4418_, 8);
if (v_requiresData_4435_ == 0)
{
if (v_handlerDispatched_4437_ == 0)
{
if (lean_obj_tag(v_respStream_4434_) == 0)
{
lean_object* v_writer_4448_; uint8_t v_sentMessage_4449_; 
v_writer_4448_ = lean_ctor_get(v_machine_4428_, 1);
v_sentMessage_4449_ = lean_ctor_get_uint8(v_writer_4448_, sizeof(void*)*6);
if (v_sentMessage_4449_ == 0)
{
lean_object* v_reader_4450_; lean_object* v_state_4451_; 
v_reader_4450_ = lean_ctor_get(v_machine_4428_, 0);
v_state_4451_ = lean_ctor_get(v_reader_4450_, 0);
if (lean_obj_tag(v_state_4451_) == 2)
{
lean_inc(v_respStream_4434_);
lean_inc(v_pendingHead_4438_);
lean_inc(v_expectData_4436_);
lean_inc_ref(v_response_4433_);
lean_inc(v_headerTimeout_4432_);
lean_inc(v_currentTimeout_4431_);
lean_inc(v_keepAliveTimeout_4430_);
lean_inc_ref(v_requestStream_4429_);
lean_inc_ref(v_machine_4428_);
lean_del_object(v___x_4420_);
lean_dec(v_a_4418_);
goto v___jp_4439_;
}
else
{
lean_dec_ref(v_connectionContext_4406_);
lean_dec(v_socket_4405_);
lean_dec_ref(v_inst_4404_);
lean_dec_ref(v___f_4403_);
lean_dec_ref(v_config_4402_);
lean_dec(v_handler_4401_);
lean_dec_ref(v_responseBodyInstance_4400_);
lean_dec_ref(v_h_4399_);
goto v___jp_4422_;
}
}
else
{
lean_dec_ref(v_connectionContext_4406_);
lean_dec(v_socket_4405_);
lean_dec_ref(v_inst_4404_);
lean_dec_ref(v___f_4403_);
lean_dec_ref(v_config_4402_);
lean_dec(v_handler_4401_);
lean_dec_ref(v_responseBodyInstance_4400_);
lean_dec_ref(v_h_4399_);
goto v___jp_4422_;
}
}
else
{
lean_inc_ref(v_respStream_4434_);
lean_inc(v_pendingHead_4438_);
lean_inc(v_expectData_4436_);
lean_inc_ref(v_response_4433_);
lean_inc(v_headerTimeout_4432_);
lean_inc(v_currentTimeout_4431_);
lean_inc(v_keepAliveTimeout_4430_);
lean_inc_ref(v_requestStream_4429_);
lean_inc_ref(v_machine_4428_);
lean_del_object(v___x_4420_);
lean_dec(v_a_4418_);
goto v___jp_4439_;
}
}
else
{
lean_inc(v_pendingHead_4438_);
lean_inc(v_expectData_4436_);
lean_inc(v_respStream_4434_);
lean_inc_ref(v_response_4433_);
lean_inc(v_headerTimeout_4432_);
lean_inc(v_currentTimeout_4431_);
lean_inc(v_keepAliveTimeout_4430_);
lean_inc_ref(v_requestStream_4429_);
lean_inc_ref(v_machine_4428_);
lean_del_object(v___x_4420_);
lean_dec(v_a_4418_);
goto v___jp_4439_;
}
}
else
{
lean_inc(v_pendingHead_4438_);
lean_inc(v_expectData_4436_);
lean_inc(v_respStream_4434_);
lean_inc_ref(v_response_4433_);
lean_inc(v_headerTimeout_4432_);
lean_inc(v_currentTimeout_4431_);
lean_inc(v_keepAliveTimeout_4430_);
lean_inc_ref(v_requestStream_4429_);
lean_inc_ref(v_machine_4428_);
lean_del_object(v___x_4420_);
lean_dec(v_a_4418_);
goto v___jp_4439_;
}
v___jp_4422_:
{
lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4423_, 0, v_a_4418_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4423_);
v___x_4425_ = v___x_4420_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
v___jp_4439_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; lean_object* v___f_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4440_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4440_, 0, v_machine_4428_);
lean_ctor_set(v___x_4440_, 1, v_requestStream_4429_);
lean_ctor_set(v___x_4440_, 2, v_keepAliveTimeout_4430_);
lean_ctor_set(v___x_4440_, 3, v_currentTimeout_4431_);
lean_ctor_set(v___x_4440_, 4, v_headerTimeout_4432_);
lean_ctor_set(v___x_4440_, 5, v_response_4433_);
lean_ctor_set(v___x_4440_, 6, v_respStream_4434_);
lean_ctor_set(v___x_4440_, 7, v_expectData_4436_);
lean_ctor_set(v___x_4440_, 8, v_pendingHead_4438_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*9, v___x_4398_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*9 + 1, v_handlerDispatched_4437_);
v___x_4441_ = lean_box(v___x_4398_);
lean_inc_ref(v___x_4440_);
lean_inc_ref(v_config_4402_);
lean_inc(v_handler_4401_);
lean_inc_ref(v_responseBodyInstance_4400_);
lean_inc_ref(v_h_4399_);
v___f_4442_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4442_, 0, v_h_4399_);
lean_closure_set(v___f_4442_, 1, v_responseBodyInstance_4400_);
lean_closure_set(v___f_4442_, 2, v_handler_4401_);
lean_closure_set(v___f_4442_, 3, v_config_4402_);
lean_closure_set(v___f_4442_, 4, v___x_4440_);
lean_closure_set(v___f_4442_, 5, v___x_4441_);
lean_closure_set(v___f_4442_, 6, v___f_4403_);
v___x_4443_ = lean_box(v___x_4398_);
v___f_4444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4444_, 0, v_inst_4404_);
lean_closure_set(v___f_4444_, 1, v_h_4399_);
lean_closure_set(v___f_4444_, 2, v_responseBodyInstance_4400_);
lean_closure_set(v___f_4444_, 3, v_config_4402_);
lean_closure_set(v___f_4444_, 4, v_handler_4401_);
lean_closure_set(v___f_4444_, 5, v___x_4443_);
lean_closure_set(v___f_4444_, 6, v___f_4442_);
v___x_4445_ = lean_unsigned_to_nat(0u);
v___x_4446_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4405_, v_connectionContext_4406_, v___x_4440_);
v___x_4447_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4445_, v___x_4398_, v___x_4446_, v___f_4444_);
return v___x_4447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4453_, lean_object* v_h_4454_, lean_object* v_responseBodyInstance_4455_, lean_object* v_handler_4456_, lean_object* v_config_4457_, lean_object* v___f_4458_, lean_object* v_inst_4459_, lean_object* v_socket_4460_, lean_object* v_connectionContext_4461_, lean_object* v_x_4462_, lean_object* v___y_4463_){
_start:
{
uint8_t v___x_5289__boxed_4464_; lean_object* v_res_4465_; 
v___x_5289__boxed_4464_ = lean_unbox(v___x_4453_);
v_res_4465_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5289__boxed_4464_, v_h_4454_, v_responseBodyInstance_4455_, v_handler_4456_, v_config_4457_, v___f_4458_, v_inst_4459_, v_socket_4460_, v_connectionContext_4461_, v_x_4462_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4466_, lean_object* v_handler_4467_, lean_object* v_extensions_4468_, lean_object* v_connectionContext_4469_, uint8_t v___x_4470_, lean_object* v___f_4471_, lean_object* v_x_4472_){
_start:
{
if (lean_obj_tag(v_x_4472_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4482_; 
lean_dec_ref(v___f_4471_);
lean_dec_ref(v_connectionContext_4469_);
lean_dec(v_extensions_4468_);
lean_dec(v_handler_4467_);
lean_dec_ref(v_h_4466_);
v_a_4474_ = lean_ctor_get(v_x_4472_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_x_4472_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4476_ = v_x_4472_;
v_isShared_4477_ = v_isSharedCheck_4482_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v_x_4472_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4482_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_a_4483_ = lean_ctor_get(v_x_4472_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v_x_4472_, 1);
v___x_4484_ = lean_unsigned_to_nat(0u);
v___x_4485_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4466_, v_handler_4467_, v_extensions_4468_, v_connectionContext_4469_, v_a_4483_);
v___x_4486_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4484_, v___x_4470_, v___x_4485_, v___f_4471_);
return v___x_4486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4487_, lean_object* v_handler_4488_, lean_object* v_extensions_4489_, lean_object* v_connectionContext_4490_, lean_object* v___x_4491_, lean_object* v___f_4492_, lean_object* v_x_4493_, lean_object* v___y_4494_){
_start:
{
uint8_t v___x_5364__boxed_4495_; lean_object* v_res_4496_; 
v___x_5364__boxed_4495_ = lean_unbox(v___x_4491_);
v_res_4496_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4487_, v_handler_4488_, v_extensions_4489_, v_connectionContext_4490_, v___x_5364__boxed_4495_, v___f_4492_, v_x_4493_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4497_, lean_object* v_responseBodyInstance_4498_, lean_object* v_handler_4499_, lean_object* v_config_4500_, lean_object* v_connectionContext_4501_, lean_object* v_events_4502_, lean_object* v___x_4503_, uint8_t v___x_4504_, lean_object* v___f_4505_, lean_object* v_____r_4506_){
_start:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = lean_unsigned_to_nat(0u);
v___x_4509_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4497_, v_responseBodyInstance_4498_, v_handler_4499_, v_config_4500_, v_connectionContext_4501_, v_events_4502_, v___x_4503_);
v___x_4510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4508_, v___x_4504_, v___x_4509_, v___f_4505_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4511_, lean_object* v_responseBodyInstance_4512_, lean_object* v_handler_4513_, lean_object* v_config_4514_, lean_object* v_connectionContext_4515_, lean_object* v_events_4516_, lean_object* v___x_4517_, lean_object* v___x_4518_, lean_object* v___f_4519_, lean_object* v_____r_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v___x_5403__boxed_4522_; lean_object* v_res_4523_; 
v___x_5403__boxed_4522_ = lean_unbox(v___x_4518_);
v_res_4523_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4511_, v_responseBodyInstance_4512_, v_handler_4513_, v_config_4514_, v_connectionContext_4515_, v_events_4516_, v___x_4517_, v___x_5403__boxed_4522_, v___f_4519_, v_____r_4520_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4524_, lean_object* v___f_4525_, lean_object* v_x_4526_){
_start:
{
if (lean_obj_tag(v_x_4526_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4536_; 
lean_dec_ref(v___f_4525_);
lean_dec_ref(v___x_4524_);
v_a_4528_ = lean_ctor_get(v_x_4526_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_x_4526_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4530_ = v_x_4526_;
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v_x_4526_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
return v___x_4534_;
}
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4548_; 
v_a_4537_ = lean_ctor_get(v_x_4526_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v_x_4526_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4539_ = v_x_4526_;
v_isShared_4540_ = v_isSharedCheck_4548_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v_x_4526_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4548_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
if (lean_obj_tag(v_a_4537_) == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4543_; 
lean_dec_ref(v___f_4525_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4524_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4541_);
v___x_4543_ = v___x_4539_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4541_);
v___x_4543_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4544_; 
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
return v___x_4544_;
}
}
else
{
lean_object* v_val_4546_; lean_object* v___x_4547_; 
lean_del_object(v___x_4539_);
lean_dec_ref(v___x_4524_);
v_val_4546_ = lean_ctor_get(v_a_4537_, 0);
lean_inc(v_val_4546_);
lean_dec_ref_known(v_a_4537_, 1);
v___x_4547_ = lean_apply_2(v___f_4525_, v_val_4546_, lean_box(0));
return v___x_4547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4549_, lean_object* v___f_4550_, lean_object* v_x_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4549_, v___f_4550_, v_x_4551_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4554_, lean_object* v_responseBodyInstance_4555_, lean_object* v_handler_4556_, lean_object* v_config_4557_, lean_object* v_connectionContext_4558_, uint8_t v___x_4559_, lean_object* v___f_4560_, lean_object* v_inst_4561_, lean_object* v_socket_4562_, lean_object* v___f_4563_, lean_object* v___f_4564_, lean_object* v_x_4565_, lean_object* v_____s_4566_){
_start:
{
lean_object* v_machine_4568_; lean_object* v_reader_4569_; lean_object* v_requestStream_4570_; lean_object* v_keepAliveTimeout_4571_; lean_object* v_currentTimeout_4572_; lean_object* v_headerTimeout_4573_; lean_object* v_response_4574_; lean_object* v_respStream_4575_; uint8_t v_requiresData_4576_; lean_object* v_expectData_4577_; uint8_t v_handlerDispatched_4578_; lean_object* v_pendingHead_4579_; lean_object* v_writer_4580_; lean_object* v_state_4581_; uint8_t v___x_4582_; 
v_machine_4568_ = lean_ctor_get(v_____s_4566_, 0);
v_reader_4569_ = lean_ctor_get(v_machine_4568_, 0);
v_requestStream_4570_ = lean_ctor_get(v_____s_4566_, 1);
v_keepAliveTimeout_4571_ = lean_ctor_get(v_____s_4566_, 2);
v_currentTimeout_4572_ = lean_ctor_get(v_____s_4566_, 3);
v_headerTimeout_4573_ = lean_ctor_get(v_____s_4566_, 4);
v_response_4574_ = lean_ctor_get(v_____s_4566_, 5);
v_respStream_4575_ = lean_ctor_get(v_____s_4566_, 6);
v_requiresData_4576_ = lean_ctor_get_uint8(v_____s_4566_, sizeof(void*)*9);
v_expectData_4577_ = lean_ctor_get(v_____s_4566_, 7);
v_handlerDispatched_4578_ = lean_ctor_get_uint8(v_____s_4566_, sizeof(void*)*9 + 1);
v_pendingHead_4579_ = lean_ctor_get(v_____s_4566_, 8);
v_writer_4580_ = lean_ctor_get(v_machine_4568_, 1);
v_state_4581_ = lean_ctor_get(v_reader_4569_, 0);
v___x_4582_ = 0;
if (lean_obj_tag(v_state_4581_) == 6)
{
lean_object* v_state_4604_; 
v_state_4604_ = lean_ctor_get(v_writer_4580_, 2);
if (lean_obj_tag(v_state_4604_) == 7)
{
lean_object* v_outputData_4605_; lean_object* v_size_4606_; lean_object* v___x_4607_; uint8_t v___x_4608_; 
v_outputData_4605_ = lean_ctor_get(v_writer_4580_, 1);
v_size_4606_ = lean_ctor_get(v_outputData_4605_, 1);
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = lean_nat_dec_eq(v_size_4606_, v___x_4607_);
if (v___x_4608_ == 0)
{
lean_inc(v_pendingHead_4579_);
lean_inc(v_expectData_4577_);
lean_inc(v_respStream_4575_);
lean_inc_ref(v_response_4574_);
lean_inc(v_headerTimeout_4573_);
lean_inc(v_currentTimeout_4572_);
lean_inc(v_keepAliveTimeout_4571_);
lean_inc_ref(v_requestStream_4570_);
lean_inc_ref(v_machine_4568_);
lean_dec_ref(v_____s_4566_);
goto v___jp_4583_;
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
lean_dec_ref(v___f_4564_);
lean_dec_ref(v___f_4563_);
lean_dec(v_socket_4562_);
lean_dec_ref(v_inst_4561_);
lean_dec_ref(v___f_4560_);
lean_dec_ref(v_connectionContext_4558_);
lean_dec_ref(v_config_4557_);
lean_dec(v_handler_4556_);
lean_dec_ref(v_responseBodyInstance_4555_);
lean_dec_ref(v_h_4554_);
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v_____s_4566_);
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
return v___x_4611_;
}
}
else
{
lean_inc(v_pendingHead_4579_);
lean_inc(v_expectData_4577_);
lean_inc(v_respStream_4575_);
lean_inc_ref(v_response_4574_);
lean_inc(v_headerTimeout_4573_);
lean_inc(v_currentTimeout_4572_);
lean_inc(v_keepAliveTimeout_4571_);
lean_inc_ref(v_requestStream_4570_);
lean_inc_ref(v_machine_4568_);
lean_dec_ref(v_____s_4566_);
goto v___jp_4583_;
}
}
else
{
lean_inc(v_pendingHead_4579_);
lean_inc(v_expectData_4577_);
lean_inc(v_respStream_4575_);
lean_inc_ref(v_response_4574_);
lean_inc(v_headerTimeout_4573_);
lean_inc(v_currentTimeout_4572_);
lean_inc(v_keepAliveTimeout_4571_);
lean_inc_ref(v_requestStream_4570_);
lean_inc_ref(v_machine_4568_);
lean_dec_ref(v_____s_4566_);
goto v___jp_4583_;
}
v___jp_4583_:
{
lean_object* v___x_4584_; lean_object* v_snd_4585_; lean_object* v_output_4586_; lean_object* v_fst_4587_; lean_object* v_events_4588_; lean_object* v_data_4589_; lean_object* v_size_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___f_4593_; lean_object* v___x_4594_; uint8_t v___x_4595_; 
v___x_4584_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4582_, v_machine_4568_);
v_snd_4585_ = lean_ctor_get(v___x_4584_, 1);
lean_inc(v_snd_4585_);
v_output_4586_ = lean_ctor_get(v_snd_4585_, 1);
lean_inc_ref(v_output_4586_);
v_fst_4587_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_fst_4587_);
lean_dec_ref(v___x_4584_);
v_events_4588_ = lean_ctor_get(v_snd_4585_, 0);
lean_inc_ref_n(v_events_4588_, 2);
lean_dec(v_snd_4585_);
v_data_4589_ = lean_ctor_get(v_output_4586_, 0);
lean_inc_ref(v_data_4589_);
v_size_4590_ = lean_ctor_get(v_output_4586_, 1);
lean_inc(v_size_4590_);
lean_dec_ref(v_output_4586_);
v___x_4591_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4591_, 0, v_fst_4587_);
lean_ctor_set(v___x_4591_, 1, v_requestStream_4570_);
lean_ctor_set(v___x_4591_, 2, v_keepAliveTimeout_4571_);
lean_ctor_set(v___x_4591_, 3, v_currentTimeout_4572_);
lean_ctor_set(v___x_4591_, 4, v_headerTimeout_4573_);
lean_ctor_set(v___x_4591_, 5, v_response_4574_);
lean_ctor_set(v___x_4591_, 6, v_respStream_4575_);
lean_ctor_set(v___x_4591_, 7, v_expectData_4577_);
lean_ctor_set(v___x_4591_, 8, v_pendingHead_4579_);
lean_ctor_set_uint8(v___x_4591_, sizeof(void*)*9, v_requiresData_4576_);
lean_ctor_set_uint8(v___x_4591_, sizeof(void*)*9 + 1, v_handlerDispatched_4578_);
v___x_4592_ = lean_box(v___x_4559_);
lean_inc_ref(v___f_4560_);
lean_inc_ref(v___x_4591_);
lean_inc_ref(v_connectionContext_4558_);
lean_inc_ref(v_config_4557_);
lean_inc(v_handler_4556_);
lean_inc_ref(v_responseBodyInstance_4555_);
lean_inc_ref(v_h_4554_);
v___f_4593_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4593_, 0, v_h_4554_);
lean_closure_set(v___f_4593_, 1, v_responseBodyInstance_4555_);
lean_closure_set(v___f_4593_, 2, v_handler_4556_);
lean_closure_set(v___f_4593_, 3, v_config_4557_);
lean_closure_set(v___f_4593_, 4, v_connectionContext_4558_);
lean_closure_set(v___f_4593_, 5, v_events_4588_);
lean_closure_set(v___f_4593_, 6, v___x_4591_);
lean_closure_set(v___f_4593_, 7, v___x_4592_);
lean_closure_set(v___f_4593_, 8, v___f_4560_);
v___x_4594_ = lean_unsigned_to_nat(0u);
v___x_4595_ = lean_nat_dec_lt(v___x_4594_, v_size_4590_);
lean_dec(v_size_4590_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
lean_dec_ref(v___f_4593_);
lean_dec_ref(v_data_4589_);
lean_dec_ref(v___f_4564_);
lean_dec_ref(v___f_4563_);
lean_dec(v_socket_4562_);
lean_dec_ref(v_inst_4561_);
v___x_4596_ = lean_box(0);
v___x_4597_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4554_, v_responseBodyInstance_4555_, v_handler_4556_, v_config_4557_, v_connectionContext_4558_, v_events_4588_, v___x_4591_, v___x_4559_, v___f_4560_, v___x_4596_);
return v___x_4597_;
}
else
{
lean_object* v_sendAll_4598_; lean_object* v___f_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
lean_dec_ref(v_events_4588_);
lean_dec_ref(v___f_4560_);
lean_dec_ref(v_connectionContext_4558_);
lean_dec_ref(v_config_4557_);
lean_dec(v_handler_4556_);
lean_dec_ref(v_responseBodyInstance_4555_);
lean_dec_ref(v_h_4554_);
v_sendAll_4598_ = lean_ctor_get(v_inst_4561_, 1);
lean_inc_ref(v_sendAll_4598_);
lean_dec_ref(v_inst_4561_);
v___f_4599_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4599_, 0, v___x_4591_);
lean_closure_set(v___f_4599_, 1, v___f_4593_);
v___x_4600_ = lean_apply_3(v_sendAll_4598_, v_socket_4562_, v_data_4589_, lean_box(0));
v___x_4601_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4594_, v___x_4559_, v___x_4600_, v___f_4563_);
v___x_4602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4594_, v___x_4559_, v___x_4601_, v___f_4564_);
v___x_4603_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4594_, v___x_4559_, v___x_4602_, v___f_4599_);
return v___x_4603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4612_, lean_object* v_responseBodyInstance_4613_, lean_object* v_handler_4614_, lean_object* v_config_4615_, lean_object* v_connectionContext_4616_, lean_object* v___x_4617_, lean_object* v___f_4618_, lean_object* v_inst_4619_, lean_object* v_socket_4620_, lean_object* v___f_4621_, lean_object* v___f_4622_, lean_object* v_x_4623_, lean_object* v_____s_4624_, lean_object* v___y_4625_){
_start:
{
uint8_t v___x_5477__boxed_4626_; lean_object* v_res_4627_; 
v___x_5477__boxed_4626_ = lean_unbox(v___x_4617_);
v_res_4627_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4612_, v_responseBodyInstance_4613_, v_handler_4614_, v_config_4615_, v_connectionContext_4616_, v___x_5477__boxed_4626_, v___f_4618_, v_inst_4619_, v_socket_4620_, v___f_4621_, v___f_4622_, v_x_4623_, v_____s_4624_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4628_, lean_object* v_x_4629_){
_start:
{
if (lean_obj_tag(v_x_4629_) == 0)
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4639_; 
v_a_4631_ = lean_ctor_get(v_x_4629_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_x_4629_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4633_ = v_x_4629_;
v_isShared_4634_ = v_isSharedCheck_4639_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v_x_4629_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4639_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
return v___x_4637_;
}
}
}
else
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
lean_dec_ref_known(v_x_4629_, 1);
v___x_4640_ = l_IO_Promise_result_x21___redArg(v_a_4628_);
v___x_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4640_);
return v___x_4641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4642_, lean_object* v_x_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4642_, v_x_4643_);
lean_dec(v_a_4642_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4646_, lean_object* v___x_4647_, lean_object* v___x_4648_, uint8_t v___x_4649_, lean_object* v_x_4650_){
_start:
{
if (lean_obj_tag(v_x_4650_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4660_; 
lean_dec_ref(v___x_4648_);
lean_dec(v___x_4647_);
lean_dec_ref(v___f_4646_);
v_a_4652_ = lean_ctor_get(v_x_4650_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_x_4650_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4654_ = v_x_4650_;
v_isShared_4655_ = v_isSharedCheck_4660_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v_x_4650_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4660_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4658_; 
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
}
}
else
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4672_; 
v_a_4661_ = lean_ctor_get(v_x_4650_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_x_4650_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4663_ = v_x_4650_;
v_isShared_4664_ = v_isSharedCheck_4672_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v_x_4650_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4672_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___f_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
lean_inc(v_a_4661_);
v___f_4665_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4665_, 0, v_a_4661_);
lean_inc(v___x_4647_);
v___x_4666_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4646_, v___x_4647_, v_a_4661_, v___x_4648_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 0, v___x_4666_);
v___x_4668_ = v___x_4663_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4666_);
v___x_4668_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
v___x_4670_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4647_, v___x_4649_, v___x_4669_, v___f_4665_);
return v___x_4670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4673_, lean_object* v___x_4674_, lean_object* v___x_4675_, lean_object* v___x_4676_, lean_object* v_x_4677_, lean_object* v___y_4678_){
_start:
{
uint8_t v___x_5580__boxed_4679_; lean_object* v_res_4680_; 
v___x_5580__boxed_4679_ = lean_unbox(v___x_4676_);
v_res_4680_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4673_, v___x_4674_, v___x_4675_, v___x_5580__boxed_4679_, v_x_4677_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4681_, lean_object* v_h_4682_, lean_object* v_responseBodyInstance_4683_, lean_object* v_handler_4684_, lean_object* v___f_4685_, lean_object* v_inst_4686_, lean_object* v_socket_4687_, lean_object* v_connectionContext_4688_, lean_object* v_extensions_4689_, lean_object* v___f_4690_, lean_object* v___f_4691_, lean_object* v_machine_4692_, lean_object* v_a_4693_, lean_object* v___x_4694_, lean_object* v___f_4695_, lean_object* v_x_4696_){
_start:
{
if (lean_obj_tag(v_x_4696_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4706_; 
lean_dec_ref(v___f_4695_);
lean_dec(v___x_4694_);
lean_dec_ref(v_a_4693_);
lean_dec_ref(v_machine_4692_);
lean_dec_ref(v___f_4691_);
lean_dec_ref(v___f_4690_);
lean_dec(v_extensions_4689_);
lean_dec_ref(v_connectionContext_4688_);
lean_dec(v_socket_4687_);
lean_dec_ref(v_inst_4686_);
lean_dec_ref(v___f_4685_);
lean_dec(v_handler_4684_);
lean_dec_ref(v_responseBodyInstance_4683_);
lean_dec_ref(v_h_4682_);
lean_dec_ref(v_config_4681_);
v_a_4698_ = lean_ctor_get(v_x_4696_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v_x_4696_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4700_ = v_x_4696_;
v_isShared_4701_ = v_isSharedCheck_4706_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v_x_4696_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4706_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; 
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
}
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4732_; 
v_a_4707_ = lean_ctor_get(v_x_4696_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_x_4696_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4709_ = v_x_4696_;
v_isShared_4710_ = v_isSharedCheck_4732_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v_x_4696_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4732_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v_keepAliveTimeout_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; lean_object* v___x_4715_; lean_object* v___f_4716_; lean_object* v___x_4717_; lean_object* v___f_4718_; lean_object* v___x_4719_; lean_object* v___f_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___x_4725_; lean_object* v___x_4727_; 
v_keepAliveTimeout_4711_ = lean_ctor_get(v_config_4681_, 5);
lean_inc_n(v_keepAliveTimeout_4711_, 2);
v___x_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4712_, 0, v_keepAliveTimeout_4711_);
v___x_4713_ = lean_box(0);
v___x_4714_ = 0;
v___x_4715_ = lean_box(v___x_4714_);
lean_inc_ref_n(v_connectionContext_4688_, 2);
lean_inc(v_socket_4687_);
lean_inc_ref(v_inst_4686_);
lean_inc_ref(v_config_4681_);
lean_inc_n(v_handler_4684_, 2);
lean_inc_ref(v_responseBodyInstance_4683_);
lean_inc_ref_n(v_h_4682_, 2);
v___f_4716_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4716_, 0, v___x_4715_);
lean_closure_set(v___f_4716_, 1, v_h_4682_);
lean_closure_set(v___f_4716_, 2, v_responseBodyInstance_4683_);
lean_closure_set(v___f_4716_, 3, v_handler_4684_);
lean_closure_set(v___f_4716_, 4, v_config_4681_);
lean_closure_set(v___f_4716_, 5, v___f_4685_);
lean_closure_set(v___f_4716_, 6, v_inst_4686_);
lean_closure_set(v___f_4716_, 7, v_socket_4687_);
lean_closure_set(v___f_4716_, 8, v_connectionContext_4688_);
v___x_4717_ = lean_box(v___x_4714_);
v___f_4718_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4718_, 0, v_h_4682_);
lean_closure_set(v___f_4718_, 1, v_handler_4684_);
lean_closure_set(v___f_4718_, 2, v_extensions_4689_);
lean_closure_set(v___f_4718_, 3, v_connectionContext_4688_);
lean_closure_set(v___f_4718_, 4, v___x_4717_);
lean_closure_set(v___f_4718_, 5, v___f_4716_);
v___x_4719_ = lean_box(v___x_4714_);
v___f_4720_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4720_, 0, v_h_4682_);
lean_closure_set(v___f_4720_, 1, v_responseBodyInstance_4683_);
lean_closure_set(v___f_4720_, 2, v_handler_4684_);
lean_closure_set(v___f_4720_, 3, v_config_4681_);
lean_closure_set(v___f_4720_, 4, v_connectionContext_4688_);
lean_closure_set(v___f_4720_, 5, v___x_4719_);
lean_closure_set(v___f_4720_, 6, v___f_4718_);
lean_closure_set(v___f_4720_, 7, v_inst_4686_);
lean_closure_set(v___f_4720_, 8, v_socket_4687_);
lean_closure_set(v___f_4720_, 9, v___f_4690_);
lean_closure_set(v___f_4720_, 10, v___f_4691_);
v___x_4721_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4721_, 0, v_machine_4692_);
lean_ctor_set(v___x_4721_, 1, v_a_4693_);
lean_ctor_set(v___x_4721_, 2, v___x_4712_);
lean_ctor_set(v___x_4721_, 3, v_keepAliveTimeout_4711_);
lean_ctor_set(v___x_4721_, 4, v___x_4713_);
lean_ctor_set(v___x_4721_, 5, v_a_4707_);
lean_ctor_set(v___x_4721_, 6, v___x_4713_);
lean_ctor_set(v___x_4721_, 7, v___x_4694_);
lean_ctor_set(v___x_4721_, 8, v___x_4713_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*9, v___x_4714_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*9 + 1, v___x_4714_);
v___x_4722_ = lean_unsigned_to_nat(0u);
v___x_4723_ = lean_box(v___x_4714_);
v___f_4724_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4724_, 0, v___f_4720_);
lean_closure_set(v___f_4724_, 1, v___x_4722_);
lean_closure_set(v___f_4724_, 2, v___x_4721_);
lean_closure_set(v___f_4724_, 3, v___x_4723_);
v___x_4725_ = lean_io_promise_new();
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4725_);
v___x_4727_ = v___x_4709_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4725_);
v___x_4727_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
v___x_4729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4722_, v___x_4714_, v___x_4728_, v___f_4724_);
v___x_4730_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4722_, v___x_4714_, v___x_4729_, v___f_4695_);
return v___x_4730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4733_ = _args[0];
lean_object* v_h_4734_ = _args[1];
lean_object* v_responseBodyInstance_4735_ = _args[2];
lean_object* v_handler_4736_ = _args[3];
lean_object* v___f_4737_ = _args[4];
lean_object* v_inst_4738_ = _args[5];
lean_object* v_socket_4739_ = _args[6];
lean_object* v_connectionContext_4740_ = _args[7];
lean_object* v_extensions_4741_ = _args[8];
lean_object* v___f_4742_ = _args[9];
lean_object* v___f_4743_ = _args[10];
lean_object* v_machine_4744_ = _args[11];
lean_object* v_a_4745_ = _args[12];
lean_object* v___x_4746_ = _args[13];
lean_object* v___f_4747_ = _args[14];
lean_object* v_x_4748_ = _args[15];
lean_object* v___y_4749_ = _args[16];
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4733_, v_h_4734_, v_responseBodyInstance_4735_, v_handler_4736_, v___f_4737_, v_inst_4738_, v_socket_4739_, v_connectionContext_4740_, v_extensions_4741_, v___f_4742_, v___f_4743_, v_machine_4744_, v_a_4745_, v___x_4746_, v___f_4747_, v_x_4748_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4751_, lean_object* v_h_4752_, lean_object* v_responseBodyInstance_4753_, lean_object* v_handler_4754_, lean_object* v___f_4755_, lean_object* v_inst_4756_, lean_object* v_socket_4757_, lean_object* v_connectionContext_4758_, lean_object* v_extensions_4759_, lean_object* v___f_4760_, lean_object* v___f_4761_, lean_object* v_machine_4762_, lean_object* v___f_4763_, lean_object* v_x_4764_){
_start:
{
if (lean_obj_tag(v_x_4764_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4774_; 
lean_dec_ref(v___f_4763_);
lean_dec_ref(v_machine_4762_);
lean_dec_ref(v___f_4761_);
lean_dec_ref(v___f_4760_);
lean_dec(v_extensions_4759_);
lean_dec_ref(v_connectionContext_4758_);
lean_dec(v_socket_4757_);
lean_dec_ref(v_inst_4756_);
lean_dec_ref(v___f_4755_);
lean_dec(v_handler_4754_);
lean_dec_ref(v_responseBodyInstance_4753_);
lean_dec_ref(v_h_4752_);
lean_dec_ref(v_config_4751_);
v_a_4766_ = lean_ctor_get(v_x_4764_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_x_4764_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4768_ = v_x_4764_;
v_isShared_4769_ = v_isSharedCheck_4774_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v_x_4764_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4774_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; 
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4789_; 
v_a_4775_ = lean_ctor_get(v_x_4764_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_x_4764_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4777_ = v_x_4764_;
v_isShared_4778_ = v_isSharedCheck_4789_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v_x_4764_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4789_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4779_; lean_object* v___f_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4779_ = lean_box(0);
v___f_4780_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4780_, 0, v_config_4751_);
lean_closure_set(v___f_4780_, 1, v_h_4752_);
lean_closure_set(v___f_4780_, 2, v_responseBodyInstance_4753_);
lean_closure_set(v___f_4780_, 3, v_handler_4754_);
lean_closure_set(v___f_4780_, 4, v___f_4755_);
lean_closure_set(v___f_4780_, 5, v_inst_4756_);
lean_closure_set(v___f_4780_, 6, v_socket_4757_);
lean_closure_set(v___f_4780_, 7, v_connectionContext_4758_);
lean_closure_set(v___f_4780_, 8, v_extensions_4759_);
lean_closure_set(v___f_4780_, 9, v___f_4760_);
lean_closure_set(v___f_4780_, 10, v___f_4761_);
lean_closure_set(v___f_4780_, 11, v_machine_4762_);
lean_closure_set(v___f_4780_, 12, v_a_4775_);
lean_closure_set(v___f_4780_, 13, v___x_4779_);
lean_closure_set(v___f_4780_, 14, v___f_4763_);
v___x_4781_ = lean_unsigned_to_nat(0u);
v___x_4782_ = 0;
v___x_4783_ = l_Std_CloseableChannel_new___redArg(v___x_4779_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4783_);
v___x_4785_ = v___x_4777_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
v___x_4787_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4781_, v___x_4782_, v___x_4786_, v___f_4780_);
return v___x_4787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4790_, lean_object* v_h_4791_, lean_object* v_responseBodyInstance_4792_, lean_object* v_handler_4793_, lean_object* v___f_4794_, lean_object* v_inst_4795_, lean_object* v_socket_4796_, lean_object* v_connectionContext_4797_, lean_object* v_extensions_4798_, lean_object* v___f_4799_, lean_object* v___f_4800_, lean_object* v_machine_4801_, lean_object* v___f_4802_, lean_object* v_x_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4790_, v_h_4791_, v_responseBodyInstance_4792_, v_handler_4793_, v___f_4794_, v_inst_4795_, v_socket_4796_, v_connectionContext_4797_, v_extensions_4798_, v___f_4799_, v___f_4800_, v_machine_4801_, v___f_4802_, v_x_4803_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4809_, lean_object* v_h_4810_, lean_object* v_connection_4811_, lean_object* v_config_4812_, lean_object* v_connectionContext_4813_, lean_object* v_handler_4814_){
_start:
{
lean_object* v_responseBodyInstance_4816_; lean_object* v_onFailure_4817_; lean_object* v_socket_4818_; lean_object* v_machine_4819_; lean_object* v_extensions_4820_; lean_object* v___f_4821_; lean_object* v___f_4822_; lean_object* v___f_4823_; lean_object* v___f_4824_; lean_object* v___f_4825_; lean_object* v___f_4826_; lean_object* v___f_4827_; lean_object* v___f_4828_; lean_object* v___f_4829_; lean_object* v___x_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v_responseBodyInstance_4816_ = lean_ctor_get(v_h_4810_, 0);
lean_inc_ref_n(v_responseBodyInstance_4816_, 2);
v_onFailure_4817_ = lean_ctor_get(v_h_4810_, 2);
v_socket_4818_ = lean_ctor_get(v_connection_4811_, 0);
lean_inc_n(v_socket_4818_, 2);
v_machine_4819_ = lean_ctor_get(v_connection_4811_, 1);
lean_inc_ref(v_machine_4819_);
v_extensions_4820_ = lean_ctor_get(v_connection_4811_, 2);
lean_inc(v_extensions_4820_);
lean_dec_ref(v_connection_4811_);
v___f_4821_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4822_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4823_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4814_);
lean_inc_ref(v_onFailure_4817_);
v___f_4824_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4824_, 0, v_onFailure_4817_);
lean_closure_set(v___f_4824_, 1, v_handler_4814_);
lean_closure_set(v___f_4824_, 2, v___f_4823_);
v___f_4825_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4809_);
v___f_4826_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4826_, 0, v_inst_4809_);
lean_closure_set(v___f_4826_, 1, v_socket_4818_);
lean_inc_ref(v___f_4826_);
v___f_4827_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4827_, 0, v___f_4826_);
v___f_4828_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4828_, 0, v_responseBodyInstance_4816_);
lean_closure_set(v___f_4828_, 1, v___f_4827_);
lean_closure_set(v___f_4828_, 2, v___f_4826_);
lean_closure_set(v___f_4828_, 3, v___f_4821_);
v___f_4829_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4829_, 0, v_config_4812_);
lean_closure_set(v___f_4829_, 1, v_h_4810_);
lean_closure_set(v___f_4829_, 2, v_responseBodyInstance_4816_);
lean_closure_set(v___f_4829_, 3, v_handler_4814_);
lean_closure_set(v___f_4829_, 4, v___f_4825_);
lean_closure_set(v___f_4829_, 5, v_inst_4809_);
lean_closure_set(v___f_4829_, 6, v_socket_4818_);
lean_closure_set(v___f_4829_, 7, v_connectionContext_4813_);
lean_closure_set(v___f_4829_, 8, v_extensions_4820_);
lean_closure_set(v___f_4829_, 9, v___f_4822_);
lean_closure_set(v___f_4829_, 10, v___f_4824_);
lean_closure_set(v___f_4829_, 11, v_machine_4819_);
lean_closure_set(v___f_4829_, 12, v___f_4828_);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = 0;
v___x_4832_ = l_Std_Http_Body_mkStream();
v___x_4833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4830_, v___x_4831_, v___x_4832_, v___f_4829_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4834_, lean_object* v_h_4835_, lean_object* v_connection_4836_, lean_object* v_config_4837_, lean_object* v_connectionContext_4838_, lean_object* v_handler_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4834_, v_h_4835_, v_connection_4836_, v_config_4837_, v_connectionContext_4838_, v_handler_4839_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4842_, lean_object* v_00_u03c3_4843_, lean_object* v_inst_4844_, lean_object* v_h_4845_, lean_object* v_connection_4846_, lean_object* v_config_4847_, lean_object* v_connectionContext_4848_, lean_object* v_handler_4849_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4844_, v_h_4845_, v_connection_4846_, v_config_4847_, v_connectionContext_4848_, v_handler_4849_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4852_, lean_object* v_00_u03c3_4853_, lean_object* v_inst_4854_, lean_object* v_h_4855_, lean_object* v_connection_4856_, lean_object* v_config_4857_, lean_object* v_connectionContext_4858_, lean_object* v_handler_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4852_, v_00_u03c3_4853_, v_inst_4854_, v_h_4855_, v_connection_4856_, v_config_4857_, v_connectionContext_4858_, v_handler_4859_);
return v_res_4861_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = 0;
v___x_4863_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4862_);
return v___x_4863_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = lean_unsigned_to_nat(4096u);
v___x_4865_ = lean_mk_empty_byte_array(v___x_4864_);
return v___x_4865_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4867_ = l_ByteArray_mkIterator(v___x_4866_);
return v___x_4867_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4868_ = 0;
v___x_4869_ = lean_unsigned_to_nat(0u);
v___x_4870_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4871_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4872_ = lean_box(0);
v___x_4873_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
lean_ctor_set(v___x_4873_, 1, v___x_4871_);
lean_ctor_set(v___x_4873_, 2, v___x_4870_);
lean_ctor_set(v___x_4873_, 3, v___x_4869_);
lean_ctor_set(v___x_4873_, 4, v___x_4869_);
lean_ctor_set(v___x_4873_, 5, v___x_4869_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*6, v___x_4868_);
return v___x_4873_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = 1;
v___x_4882_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4881_);
return v___x_4882_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4883_; uint8_t v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = 0;
v___x_4885_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4886_ = lean_box(0);
v___x_4887_ = lean_box(0);
v___x_4888_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4889_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4890_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
lean_ctor_set(v___x_4890_, 1, v___x_4888_);
lean_ctor_set(v___x_4890_, 2, v___x_4887_);
lean_ctor_set(v___x_4890_, 3, v___x_4886_);
lean_ctor_set(v___x_4890_, 4, v___x_4885_);
lean_ctor_set(v___x_4890_, 5, v___x_4883_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*6, v___x_4884_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*6 + 1, v___x_4884_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*6 + 2, v___x_4884_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4891_, lean_object* v_client_4892_, lean_object* v_extensions_4893_, lean_object* v_inst_4894_, lean_object* v_inst_4895_, lean_object* v_handler_4896_, lean_object* v_x_4897_){
_start:
{
if (lean_obj_tag(v_x_4897_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4907_; 
lean_dec(v_handler_4896_);
lean_dec_ref(v_inst_4895_);
lean_dec_ref(v_inst_4894_);
lean_dec(v_extensions_4893_);
lean_dec(v_client_4892_);
lean_dec_ref(v_config_4891_);
v_a_4899_ = lean_ctor_get(v_x_4897_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_x_4897_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4901_ = v_x_4897_;
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v_x_4897_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
}
}
else
{
lean_object* v_a_4908_; uint8_t v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v_enableKeepAlive_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v_a_4908_ = lean_ctor_get(v_x_4897_, 0);
lean_inc(v_a_4908_);
lean_dec_ref_known(v_x_4897_, 1);
v___x_4909_ = 0;
v___x_4910_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4911_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4912_ = lean_box(0);
v___x_4913_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4914_ = l_Std_Http_Config_toH1Config(v_config_4891_);
v_enableKeepAlive_4915_ = lean_ctor_get_uint8(v___x_4914_, sizeof(void*)*18);
v___x_4916_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4916_, 0, v___x_4910_);
lean_ctor_set(v___x_4916_, 1, v___x_4913_);
lean_ctor_set(v___x_4916_, 2, v___x_4914_);
lean_ctor_set(v___x_4916_, 3, v___x_4911_);
lean_ctor_set(v___x_4916_, 4, v___x_4912_);
lean_ctor_set(v___x_4916_, 5, v___x_4912_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*6, v_enableKeepAlive_4915_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*6 + 1, v___x_4909_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*6 + 2, v___x_4909_);
v___x_4917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4917_, 0, v_client_4892_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
lean_ctor_set(v___x_4917_, 2, v_extensions_4893_);
v___x_4918_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4894_, v_inst_4895_, v___x_4917_, v_config_4891_, v_a_4908_, v_handler_4896_);
return v___x_4918_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4919_, lean_object* v_client_4920_, lean_object* v_extensions_4921_, lean_object* v_inst_4922_, lean_object* v_inst_4923_, lean_object* v_handler_4924_, lean_object* v_x_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4919_, v_client_4920_, v_extensions_4921_, v_inst_4922_, v_inst_4923_, v_handler_4924_, v_x_4925_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4928_, lean_object* v_inst_4929_, lean_object* v_client_4930_, lean_object* v_handler_4931_, lean_object* v_config_4932_, lean_object* v_extensions_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___f_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___f_4936_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4936_, 0, v_config_4932_);
lean_closure_set(v___f_4936_, 1, v_client_4930_);
lean_closure_set(v___f_4936_, 2, v_extensions_4933_);
lean_closure_set(v___f_4936_, 3, v_inst_4928_);
lean_closure_set(v___f_4936_, 4, v_inst_4929_);
lean_closure_set(v___f_4936_, 5, v_handler_4931_);
v___x_4937_ = lean_unsigned_to_nat(0u);
v___x_4938_ = 0;
lean_inc_ref(v_a_4934_);
v___x_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4939_, 0, v_a_4934_);
v___x_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
v___x_4941_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4937_, v___x_4938_, v___x_4940_, v___f_4936_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4942_, lean_object* v_inst_4943_, lean_object* v_client_4944_, lean_object* v_handler_4945_, lean_object* v_config_4946_, lean_object* v_extensions_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4942_, v_inst_4943_, v_client_4944_, v_handler_4945_, v_config_4946_, v_extensions_4947_, v_a_4948_);
lean_dec_ref(v_a_4948_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4951_, lean_object* v_00_u03c3_4952_, lean_object* v_inst_4953_, lean_object* v_inst_4954_, lean_object* v_client_4955_, lean_object* v_handler_4956_, lean_object* v_config_4957_, lean_object* v_extensions_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4953_, v_inst_4954_, v_client_4955_, v_handler_4956_, v_config_4957_, v_extensions_4958_, v_a_4959_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4962_, lean_object* v_00_u03c3_4963_, lean_object* v_inst_4964_, lean_object* v_inst_4965_, lean_object* v_client_4966_, lean_object* v_handler_4967_, lean_object* v_config_4968_, lean_object* v_extensions_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Std_Http_Server_serveConnection(v_t_4962_, v_00_u03c3_4963_, v_inst_4964_, v_inst_4965_, v_client_4966_, v_handler_4967_, v_config_4968_, v_extensions_4969_, v_a_4970_);
lean_dec_ref(v_a_4970_);
return v_res_4972_;
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
