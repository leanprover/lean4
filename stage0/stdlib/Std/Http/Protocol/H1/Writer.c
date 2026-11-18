// Lean compiler output
// Module: Std.Http.Protocol.H1.Writer
// Imports: public import Std.Time public import Std.Http.Data public import Std.Http.Internal public import Std.Http.Protocol.H1.Parser public import Std.Http.Protocol.H1.Config public import Std.Http.Protocol.H1.Message public import Std.Http.Protocol.H1.Error
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Http_Internal_ChunkedBuffer_pushChunk(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instInhabitedState;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Std.Http.Protocol.H1.Writer.State.waitingForFlush"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Std.Http.Protocol.H1.Writer.State.waitingHeaders"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Std.Http.Protocol.H1.Writer.State.pending"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Std.Http.Protocol.H1.Writer.State.writingBodyChunked"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Std.Http.Protocol.H1.Writer.State.writingBodyClosingFrame"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Writer.State.complete"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Writer.State.closed"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Std.Http.Protocol.H1.Writer.State.writingBodyFixed"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__16_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_instReprState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instBEqState___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_sentMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_sentMessage___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_sentMessage(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_sentMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__1_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__8_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__3_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__4_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__5_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__9_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__7_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value;
static const lean_array_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "0\r\n\r\n"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Http_Protocol_H1_Writer_State_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 3)
{
lean_object* v_n_7_; lean_object* v___x_8_; 
v_n_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_n_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_n_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim___redArg(lean_object* v_t_21_, lean_object* v_pending_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_21_, v_pending_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_pending_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_25_, v_pending_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim___redArg(lean_object* v_t_29_, lean_object* v_waitingHeaders_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_29_, v_waitingHeaders_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_waitingHeaders_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_33_, v_waitingHeaders_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim___redArg(lean_object* v_t_37_, lean_object* v_waitingForFlush_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_37_, v_waitingForFlush_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_waitingForFlush_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_41_, v_waitingForFlush_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim___redArg(lean_object* v_t_45_, lean_object* v_writingBodyFixed_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_45_, v_writingBodyFixed_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_writingBodyFixed_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_49_, v_writingBodyFixed_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim___redArg(lean_object* v_t_53_, lean_object* v_writingBodyChunked_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_53_, v_writingBodyChunked_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_writingBodyChunked_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_57_, v_writingBodyChunked_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim___redArg(lean_object* v_t_61_, lean_object* v_writingBodyClosingFrame_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_61_, v_writingBodyClosingFrame_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_writingBodyClosingFrame_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_65_, v_writingBodyClosingFrame_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim___redArg(lean_object* v_t_69_, lean_object* v_complete_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_69_, v_complete_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_complete_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_73_, v_complete_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim___redArg(lean_object* v_t_77_, lean_object* v_closed_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_77_, v_closed_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_closed_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_81_, v_closed_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(2u);
v___x_109_ = lean_nat_to_int(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr(lean_object* v_x_118_, lean_object* v_prec_119_){
_start:
{
lean_object* v___y_121_; lean_object* v___y_128_; lean_object* v___y_135_; lean_object* v___y_142_; lean_object* v___y_149_; lean_object* v___y_156_; lean_object* v___y_163_; 
switch(lean_obj_tag(v_x_118_))
{
case 0:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1024u);
v___x_170_ = lean_nat_dec_le(v___x_169_, v_prec_119_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_135_ = v___x_171_;
goto v___jp_134_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_135_ = v___x_172_;
goto v___jp_134_;
}
}
case 1:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1024u);
v___x_174_ = lean_nat_dec_le(v___x_173_, v_prec_119_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_128_ = v___x_175_;
goto v___jp_127_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_128_ = v___x_176_;
goto v___jp_127_;
}
}
case 2:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1024u);
v___x_178_ = lean_nat_dec_le(v___x_177_, v_prec_119_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_121_ = v___x_179_;
goto v___jp_120_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_121_ = v___x_180_;
goto v___jp_120_;
}
}
case 3:
{
lean_object* v_n_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_201_; 
v_n_181_ = lean_ctor_get(v_x_118_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_118_);
if (v_isSharedCheck_201_ == 0)
{
v___x_183_ = v_x_118_;
v_isShared_184_ = v_isSharedCheck_201_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_n_181_);
lean_dec(v_x_118_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_201_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___y_186_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_198_ = lean_nat_dec_le(v___x_197_, v_prec_119_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_186_ = v___x_199_;
goto v___jp_185_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_186_ = v___x_200_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18));
v___x_188_ = l_Nat_reprFast(v_n_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_188_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_196_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_187_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
lean_inc(v___y_186_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___y_186_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = 0;
v___x_194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_193_);
v___x_195_ = l_Repr_addAppParen(v___x_194_, v_prec_119_);
return v___x_195_;
}
}
}
}
case 4:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(1024u);
v___x_203_ = lean_nat_dec_le(v___x_202_, v_prec_119_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_142_ = v___x_204_;
goto v___jp_141_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_142_ = v___x_205_;
goto v___jp_141_;
}
}
case 5:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1024u);
v___x_207_ = lean_nat_dec_le(v___x_206_, v_prec_119_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_149_ = v___x_208_;
goto v___jp_148_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_149_ = v___x_209_;
goto v___jp_148_;
}
}
case 6:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1024u);
v___x_211_ = lean_nat_dec_le(v___x_210_, v_prec_119_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_156_ = v___x_212_;
goto v___jp_155_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_156_ = v___x_213_;
goto v___jp_155_;
}
}
default: 
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1024u);
v___x_215_ = lean_nat_dec_le(v___x_214_, v_prec_119_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_163_ = v___x_216_;
goto v___jp_162_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_163_ = v___x_217_;
goto v___jp_162_;
}
}
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_119_);
return v___x_126_;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3));
lean_inc(v___y_128_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___y_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = l_Repr_addAppParen(v___x_132_, v_prec_119_);
return v___x_133_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5));
lean_inc(v___y_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_119_);
return v___x_140_;
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7));
lean_inc(v___y_142_);
v___x_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_119_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9));
lean_inc(v___y_149_);
v___x_151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_151_, 0, v___y_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_152_);
v___x_154_ = l_Repr_addAppParen(v___x_153_, v_prec_119_);
return v___x_154_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11));
lean_inc(v___y_156_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___y_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = 0;
v___x_160_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_159_);
v___x_161_ = l_Repr_addAppParen(v___x_160_, v_prec_119_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13));
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = l_Repr_addAppParen(v___x_167_, v_prec_119_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed(lean_object* v_x_218_, lean_object* v_prec_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr(v_x_218_, v_prec_219_);
lean_dec(v_prec_219_);
return v_res_220_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
switch(lean_obj_tag(v_x_223_))
{
case 0:
{
if (lean_obj_tag(v_x_224_) == 0)
{
uint8_t v___x_225_; 
v___x_225_ = 1;
return v___x_225_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
}
case 1:
{
if (lean_obj_tag(v_x_224_) == 1)
{
uint8_t v___x_227_; 
v___x_227_ = 1;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
case 2:
{
if (lean_obj_tag(v_x_224_) == 2)
{
uint8_t v___x_229_; 
v___x_229_ = 1;
return v___x_229_;
}
else
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
}
case 3:
{
if (lean_obj_tag(v_x_224_) == 3)
{
lean_object* v_n_231_; lean_object* v_n_232_; uint8_t v___x_233_; 
v_n_231_ = lean_ctor_get(v_x_223_, 0);
v_n_232_ = lean_ctor_get(v_x_224_, 0);
v___x_233_ = lean_nat_dec_eq(v_n_231_, v_n_232_);
return v___x_233_;
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
}
case 4:
{
if (lean_obj_tag(v_x_224_) == 4)
{
uint8_t v___x_235_; 
v___x_235_ = 1;
return v___x_235_;
}
else
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
}
case 5:
{
if (lean_obj_tag(v_x_224_) == 5)
{
uint8_t v___x_237_; 
v___x_237_ = 1;
return v___x_237_;
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
}
case 6:
{
if (lean_obj_tag(v_x_224_) == 6)
{
uint8_t v___x_239_; 
v___x_239_ = 1;
return v___x_239_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 0;
return v___x_240_;
}
}
default: 
{
if (lean_obj_tag(v_x_224_) == 7)
{
uint8_t v___x_241_; 
v___x_241_ = 1;
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 0;
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed(lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_x_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec(v_x_243_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_sentMessage___redArg(lean_object* v_writer_249_){
_start:
{
lean_object* v_state_250_; 
v_state_250_ = lean_ctor_get(v_writer_249_, 2);
switch(lean_obj_tag(v_state_250_))
{
case 0:
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
case 1:
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
default: 
{
uint8_t v___x_253_; 
v___x_253_ = 1;
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_sentMessage___redArg___boxed(lean_object* v_writer_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_Http_Protocol_H1_Writer_sentMessage___redArg(v_writer_254_);
lean_dec_ref(v_writer_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_sentMessage(uint8_t v_dir_257_, lean_object* v_writer_258_){
_start:
{
lean_object* v_state_259_; 
v_state_259_ = lean_ctor_get(v_writer_258_, 2);
switch(lean_obj_tag(v_state_259_))
{
case 0:
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
case 1:
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
default: 
{
uint8_t v___x_262_; 
v___x_262_ = 1;
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_sentMessage___boxed(lean_object* v_dir_263_, lean_object* v_writer_264_){
_start:
{
uint8_t v_dir_boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_dir_boxed_265_ = lean_unbox(v_dir_263_);
v_res_266_ = l_Std_Http_Protocol_H1_Writer_sentMessage(v_dir_boxed_265_, v_writer_264_);
lean_dec_ref(v_writer_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(lean_object* v_writer_268_){
_start:
{
lean_object* v_state_269_; 
v_state_269_ = lean_ctor_get(v_writer_268_, 2);
switch(lean_obj_tag(v_state_269_))
{
case 7:
{
uint8_t v___x_270_; 
v___x_270_ = 1;
return v___x_270_;
}
case 6:
{
uint8_t v___x_271_; 
v___x_271_ = 1;
return v___x_271_;
}
default: 
{
uint8_t v_userClosedBody_272_; 
v_userClosedBody_272_ = lean_ctor_get_uint8(v_writer_268_, sizeof(void*)*6);
return v_userClosedBody_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(lean_object* v_writer_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_273_);
lean_dec_ref(v_writer_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData(uint8_t v_dir_276_, lean_object* v_writer_277_){
_start:
{
lean_object* v_state_278_; 
v_state_278_ = lean_ctor_get(v_writer_277_, 2);
switch(lean_obj_tag(v_state_278_))
{
case 7:
{
uint8_t v___x_279_; 
v___x_279_ = 1;
return v___x_279_;
}
case 6:
{
uint8_t v___x_280_; 
v___x_280_ = 1;
return v___x_280_;
}
default: 
{
uint8_t v_userClosedBody_281_; 
v_userClosedBody_281_ = lean_ctor_get_uint8(v_writer_277_, sizeof(void*)*6);
return v_userClosedBody_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(lean_object* v_dir_282_, lean_object* v_writer_283_){
_start:
{
uint8_t v_dir_boxed_284_; uint8_t v_res_285_; lean_object* v_r_286_; 
v_dir_boxed_284_ = lean_unbox(v_dir_282_);
v_res_285_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_boxed_284_, v_writer_283_);
lean_dec_ref(v_writer_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed___redArg(lean_object* v_writer_287_){
_start:
{
lean_object* v_state_288_; 
v_state_288_ = lean_ctor_get(v_writer_287_, 2);
if (lean_obj_tag(v_state_288_) == 7)
{
uint8_t v___x_289_; 
v___x_289_ = 1;
return v___x_289_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = 0;
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(lean_object* v_writer_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_291_);
lean_dec_ref(v_writer_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed(uint8_t v_dir_294_, lean_object* v_writer_295_){
_start:
{
lean_object* v_state_296_; 
v_state_296_ = lean_ctor_get(v_writer_295_, 2);
if (lean_obj_tag(v_state_296_) == 7)
{
uint8_t v___x_297_; 
v___x_297_ = 1;
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___boxed(lean_object* v_dir_299_, lean_object* v_writer_300_){
_start:
{
uint8_t v_dir_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_dir_boxed_301_ = lean_unbox(v_dir_299_);
v_res_302_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_boxed_301_, v_writer_300_);
lean_dec_ref(v_writer_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete___redArg(lean_object* v_writer_304_){
_start:
{
lean_object* v_state_305_; 
v_state_305_ = lean_ctor_get(v_writer_304_, 2);
if (lean_obj_tag(v_state_305_) == 6)
{
uint8_t v___x_306_; 
v___x_306_ = 1;
return v___x_306_;
}
else
{
uint8_t v___x_307_; 
v___x_307_ = 0;
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(lean_object* v_writer_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_308_);
lean_dec_ref(v_writer_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete(uint8_t v_dir_311_, lean_object* v_writer_312_){
_start:
{
lean_object* v_state_313_; 
v_state_313_ = lean_ctor_get(v_writer_312_, 2);
if (lean_obj_tag(v_state_313_) == 6)
{
uint8_t v___x_314_; 
v___x_314_ = 1;
return v___x_314_;
}
else
{
uint8_t v___x_315_; 
v___x_315_ = 0;
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___boxed(lean_object* v_dir_316_, lean_object* v_writer_317_){
_start:
{
uint8_t v_dir_boxed_318_; uint8_t v_res_319_; lean_object* v_r_320_; 
v_dir_boxed_318_ = lean_unbox(v_dir_316_);
v_res_319_ = l_Std_Http_Protocol_H1_Writer_isComplete(v_dir_boxed_318_, v_writer_317_);
lean_dec_ref(v_writer_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(lean_object* v_writer_321_){
_start:
{
lean_object* v_state_322_; uint8_t v_userClosedBody_323_; 
v_state_322_ = lean_ctor_get(v_writer_321_, 2);
v_userClosedBody_323_ = lean_ctor_get_uint8(v_writer_321_, sizeof(void*)*6);
switch(lean_obj_tag(v_state_322_))
{
case 1:
{
uint8_t v___x_327_; 
v___x_327_ = 1;
return v___x_327_;
}
case 2:
{
uint8_t v___x_328_; 
v___x_328_ = 1;
return v___x_328_;
}
case 3:
{
if (v_userClosedBody_323_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = 1;
return v___x_329_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
}
case 4:
{
goto v___jp_324_;
}
case 5:
{
goto v___jp_324_;
}
default: 
{
uint8_t v___x_331_; 
v___x_331_ = 0;
return v___x_331_;
}
}
v___jp_324_:
{
if (v_userClosedBody_323_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = 1;
return v___x_325_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(lean_object* v_writer_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_332_);
lean_dec_ref(v_writer_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData(uint8_t v_dir_335_, lean_object* v_writer_336_){
_start:
{
lean_object* v_state_337_; uint8_t v_userClosedBody_338_; 
v_state_337_ = lean_ctor_get(v_writer_336_, 2);
v_userClosedBody_338_ = lean_ctor_get_uint8(v_writer_336_, sizeof(void*)*6);
switch(lean_obj_tag(v_state_337_))
{
case 1:
{
uint8_t v___x_342_; 
v___x_342_ = 1;
return v___x_342_;
}
case 2:
{
uint8_t v___x_343_; 
v___x_343_ = 1;
return v___x_343_;
}
case 3:
{
if (v_userClosedBody_338_ == 0)
{
uint8_t v___x_344_; 
v___x_344_ = 1;
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
case 4:
{
goto v___jp_339_;
}
case 5:
{
goto v___jp_339_;
}
default: 
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
v___jp_339_:
{
if (v_userClosedBody_338_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 1;
return v___x_340_;
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(lean_object* v_dir_347_, lean_object* v_writer_348_){
_start:
{
uint8_t v_dir_boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_dir_boxed_349_ = lean_unbox(v_dir_347_);
v_res_350_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_boxed_349_, v_writer_348_);
lean_dec_ref(v_writer_348_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___redArg(lean_object* v_writer_352_){
_start:
{
lean_object* v_userData_353_; lean_object* v_outputData_354_; lean_object* v_state_355_; lean_object* v_knownSize_356_; lean_object* v_messageHead_357_; uint8_t v_omitBody_358_; lean_object* v_userDataBytes_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_userData_353_ = lean_ctor_get(v_writer_352_, 0);
v_outputData_354_ = lean_ctor_get(v_writer_352_, 1);
v_state_355_ = lean_ctor_get(v_writer_352_, 2);
v_knownSize_356_ = lean_ctor_get(v_writer_352_, 3);
v_messageHead_357_ = lean_ctor_get(v_writer_352_, 4);
v_omitBody_358_ = lean_ctor_get_uint8(v_writer_352_, sizeof(void*)*6 + 1);
v_userDataBytes_359_ = lean_ctor_get(v_writer_352_, 5);
v_isSharedCheck_367_ = !lean_is_exclusive(v_writer_352_);
if (v_isSharedCheck_367_ == 0)
{
v___x_361_ = v_writer_352_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_userDataBytes_359_);
lean_inc(v_messageHead_357_);
lean_inc(v_knownSize_356_);
lean_inc(v_state_355_);
lean_inc(v_outputData_354_);
lean_inc(v_userData_353_);
lean_dec(v_writer_352_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
uint8_t v___x_363_; lean_object* v___x_365_; 
v___x_363_ = 1;
if (v_isShared_362_ == 0)
{
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_userData_353_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_outputData_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_state_355_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_knownSize_356_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_messageHead_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_userDataBytes_359_);
lean_ctor_set_uint8(v_reuseFailAlloc_366_, sizeof(void*)*6 + 1, v_omitBody_358_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*6, v___x_363_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody(uint8_t v_dir_368_, lean_object* v_writer_369_){
_start:
{
lean_object* v_userData_370_; lean_object* v_outputData_371_; lean_object* v_state_372_; lean_object* v_knownSize_373_; lean_object* v_messageHead_374_; uint8_t v_omitBody_375_; lean_object* v_userDataBytes_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_userData_370_ = lean_ctor_get(v_writer_369_, 0);
v_outputData_371_ = lean_ctor_get(v_writer_369_, 1);
v_state_372_ = lean_ctor_get(v_writer_369_, 2);
v_knownSize_373_ = lean_ctor_get(v_writer_369_, 3);
v_messageHead_374_ = lean_ctor_get(v_writer_369_, 4);
v_omitBody_375_ = lean_ctor_get_uint8(v_writer_369_, sizeof(void*)*6 + 1);
v_userDataBytes_376_ = lean_ctor_get(v_writer_369_, 5);
v_isSharedCheck_384_ = !lean_is_exclusive(v_writer_369_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v_writer_369_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_userDataBytes_376_);
lean_inc(v_messageHead_374_);
lean_inc(v_knownSize_373_);
lean_inc(v_state_372_);
lean_inc(v_outputData_371_);
lean_inc(v_userData_370_);
lean_dec(v_writer_369_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint8_t v___x_380_; lean_object* v___x_382_; 
v___x_380_ = 1;
if (v_isShared_379_ == 0)
{
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_userData_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_outputData_371_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_state_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_knownSize_373_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_messageHead_374_);
lean_ctor_set(v_reuseFailAlloc_383_, 5, v_userDataBytes_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*6 + 1, v_omitBody_375_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*6, v___x_380_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___boxed(lean_object* v_dir_385_, lean_object* v_writer_386_){
_start:
{
uint8_t v_dir_boxed_387_; lean_object* v_res_388_; 
v_dir_boxed_387_ = lean_unbox(v_dir_385_);
v_res_388_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_boxed_387_, v_writer_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(lean_object* v_writer_389_){
_start:
{
lean_object* v_knownSize_390_; 
v_knownSize_390_ = lean_ctor_get(v_writer_389_, 3);
if (lean_obj_tag(v_knownSize_390_) == 1)
{
lean_object* v_val_391_; 
v_val_391_ = lean_ctor_get(v_knownSize_390_, 0);
lean_inc(v_val_391_);
return v_val_391_;
}
else
{
uint8_t v_userClosedBody_392_; 
v_userClosedBody_392_ = lean_ctor_get_uint8(v_writer_389_, sizeof(void*)*6);
if (v_userClosedBody_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v_userDataBytes_394_; lean_object* v___x_395_; 
v_userDataBytes_394_ = lean_ctor_get(v_writer_389_, 5);
lean_inc(v_userDataBytes_394_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_userDataBytes_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(lean_object* v_writer_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_396_);
lean_dec_ref(v_writer_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode(uint8_t v_dir_398_, lean_object* v_writer_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(lean_object* v_dir_401_, lean_object* v_writer_402_){
_start:
{
uint8_t v_dir_boxed_403_; lean_object* v_res_404_; 
v_dir_boxed_403_ = lean_unbox(v_dir_401_);
v_res_404_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_boxed_403_, v_writer_402_);
lean_dec_ref(v_writer_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(lean_object* v_x1_405_, lean_object* v_x2_406_){
_start:
{
lean_object* v_data_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_data_407_ = lean_ctor_get(v_x2_406_, 0);
v___x_408_ = lean_byte_array_size(v_data_407_);
v___x_409_ = lean_nat_add(v_x1_405_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(lean_object* v_x1_410_, lean_object* v_x2_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(v_x1_410_, v_x2_411_);
lean_dec_ref(v_x2_411_);
lean_dec(v_x1_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg(lean_object* v_data_433_, lean_object* v_writer_434_){
_start:
{
lean_object* v_userData_435_; lean_object* v_outputData_436_; lean_object* v_state_437_; lean_object* v_knownSize_438_; lean_object* v_messageHead_439_; uint8_t v_userClosedBody_440_; uint8_t v_omitBody_441_; lean_object* v_userDataBytes_442_; lean_object* v___y_444_; lean_object* v___f_448_; 
v_userData_435_ = lean_ctor_get(v_writer_434_, 0);
v_outputData_436_ = lean_ctor_get(v_writer_434_, 1);
v_state_437_ = lean_ctor_get(v_writer_434_, 2);
v_knownSize_438_ = lean_ctor_get(v_writer_434_, 3);
v_messageHead_439_ = lean_ctor_get(v_writer_434_, 4);
v_userClosedBody_440_ = lean_ctor_get_uint8(v_writer_434_, sizeof(void*)*6);
v_omitBody_441_ = lean_ctor_get_uint8(v_writer_434_, sizeof(void*)*6 + 1);
v_userDataBytes_442_ = lean_ctor_get(v_writer_434_, 5);
v___f_448_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_437_))
{
case 1:
{
lean_inc(v_state_437_);
lean_inc(v_userDataBytes_442_);
lean_inc(v_messageHead_439_);
lean_inc(v_knownSize_438_);
lean_inc_ref(v_outputData_436_);
lean_inc_ref(v_userData_435_);
lean_dec_ref(v_writer_434_);
goto v___jp_449_;
}
case 2:
{
lean_inc(v_state_437_);
lean_inc(v_userDataBytes_442_);
lean_inc(v_messageHead_439_);
lean_inc(v_knownSize_438_);
lean_inc_ref(v_outputData_436_);
lean_inc_ref(v_userData_435_);
lean_dec_ref(v_writer_434_);
goto v___jp_449_;
}
case 3:
{
if (v_userClosedBody_440_ == 0)
{
lean_inc_ref(v_state_437_);
lean_inc(v_userDataBytes_442_);
lean_inc(v_messageHead_439_);
lean_inc(v_knownSize_438_);
lean_inc_ref(v_outputData_436_);
lean_inc_ref(v_userData_435_);
lean_dec_ref(v_writer_434_);
goto v___jp_449_;
}
else
{
lean_dec_ref(v_data_433_);
return v_writer_434_;
}
}
case 4:
{
goto v___jp_457_;
}
case 5:
{
goto v___jp_457_;
}
default: 
{
lean_dec_ref(v_data_433_);
return v_writer_434_;
}
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = l_Array_append___redArg(v_userData_435_, v_data_433_);
lean_dec_ref(v_data_433_);
v___x_446_ = lean_nat_add(v_userDataBytes_442_, v___y_444_);
lean_dec(v___y_444_);
lean_dec(v_userDataBytes_442_);
v___x_447_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v_outputData_436_);
lean_ctor_set(v___x_447_, 2, v_state_437_);
lean_ctor_set(v___x_447_, 3, v_knownSize_438_);
lean_ctor_set(v___x_447_, 4, v_messageHead_439_);
lean_ctor_set(v___x_447_, 5, v___x_446_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*6, v_userClosedBody_440_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*6 + 1, v_omitBody_441_);
return v___x_447_;
}
v___jp_449_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_array_get_size(v_data_433_);
v___x_452_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_453_ = lean_nat_dec_lt(v___x_450_, v___x_451_);
if (v___x_453_ == 0)
{
v___y_444_ = v___x_450_;
goto v___jp_443_;
}
else
{
size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
v___x_454_ = ((size_t)0ULL);
v___x_455_ = lean_usize_of_nat(v___x_451_);
lean_inc_ref(v_data_433_);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_452_, v___f_448_, v_data_433_, v___x_454_, v___x_455_, v___x_450_);
v___y_444_ = v___x_456_;
goto v___jp_443_;
}
}
v___jp_457_:
{
if (v_userClosedBody_440_ == 0)
{
lean_inc(v_userDataBytes_442_);
lean_inc(v_messageHead_439_);
lean_inc(v_knownSize_438_);
lean_inc(v_state_437_);
lean_inc_ref(v_outputData_436_);
lean_inc_ref(v_userData_435_);
lean_dec_ref(v_writer_434_);
goto v___jp_449_;
}
else
{
lean_dec_ref(v_data_433_);
return v_writer_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_458_, lean_object* v_data_459_, lean_object* v_writer_460_){
_start:
{
lean_object* v_userData_461_; lean_object* v_outputData_462_; lean_object* v_state_463_; lean_object* v_knownSize_464_; lean_object* v_messageHead_465_; uint8_t v_userClosedBody_466_; uint8_t v_omitBody_467_; lean_object* v_userDataBytes_468_; lean_object* v___y_470_; lean_object* v___f_474_; 
v_userData_461_ = lean_ctor_get(v_writer_460_, 0);
v_outputData_462_ = lean_ctor_get(v_writer_460_, 1);
v_state_463_ = lean_ctor_get(v_writer_460_, 2);
v_knownSize_464_ = lean_ctor_get(v_writer_460_, 3);
v_messageHead_465_ = lean_ctor_get(v_writer_460_, 4);
v_userClosedBody_466_ = lean_ctor_get_uint8(v_writer_460_, sizeof(void*)*6);
v_omitBody_467_ = lean_ctor_get_uint8(v_writer_460_, sizeof(void*)*6 + 1);
v_userDataBytes_468_ = lean_ctor_get(v_writer_460_, 5);
v___f_474_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_463_))
{
case 1:
{
lean_inc(v_state_463_);
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_465_);
lean_inc(v_knownSize_464_);
lean_inc_ref(v_outputData_462_);
lean_inc_ref(v_userData_461_);
lean_dec_ref(v_writer_460_);
goto v___jp_475_;
}
case 2:
{
lean_inc(v_state_463_);
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_465_);
lean_inc(v_knownSize_464_);
lean_inc_ref(v_outputData_462_);
lean_inc_ref(v_userData_461_);
lean_dec_ref(v_writer_460_);
goto v___jp_475_;
}
case 3:
{
if (v_userClosedBody_466_ == 0)
{
lean_inc_ref(v_state_463_);
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_465_);
lean_inc(v_knownSize_464_);
lean_inc_ref(v_outputData_462_);
lean_inc_ref(v_userData_461_);
lean_dec_ref(v_writer_460_);
goto v___jp_475_;
}
else
{
lean_dec_ref(v_data_459_);
return v_writer_460_;
}
}
case 4:
{
goto v___jp_483_;
}
case 5:
{
goto v___jp_483_;
}
default: 
{
lean_dec_ref(v_data_459_);
return v_writer_460_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = l_Array_append___redArg(v_userData_461_, v_data_459_);
lean_dec_ref(v_data_459_);
v___x_472_ = lean_nat_add(v_userDataBytes_468_, v___y_470_);
lean_dec(v___y_470_);
lean_dec(v_userDataBytes_468_);
v___x_473_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v_outputData_462_);
lean_ctor_set(v___x_473_, 2, v_state_463_);
lean_ctor_set(v___x_473_, 3, v_knownSize_464_);
lean_ctor_set(v___x_473_, 4, v_messageHead_465_);
lean_ctor_set(v___x_473_, 5, v___x_472_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*6, v_userClosedBody_466_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*6 + 1, v_omitBody_467_);
return v___x_473_;
}
v___jp_475_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_array_get_size(v_data_459_);
v___x_478_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_479_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_479_ == 0)
{
v___y_470_ = v___x_476_;
goto v___jp_469_;
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_477_);
lean_inc_ref(v_data_459_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_478_, v___f_474_, v_data_459_, v___x_480_, v___x_481_, v___x_476_);
v___y_470_ = v___x_482_;
goto v___jp_469_;
}
}
v___jp_483_:
{
if (v_userClosedBody_466_ == 0)
{
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_465_);
lean_inc(v_knownSize_464_);
lean_inc(v_state_463_);
lean_inc_ref(v_outputData_462_);
lean_inc_ref(v_userData_461_);
lean_dec_ref(v_writer_460_);
goto v___jp_475_;
}
else
{
lean_dec_ref(v_data_459_);
return v_writer_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object* v_dir_484_, lean_object* v_data_485_, lean_object* v_writer_486_){
_start:
{
uint8_t v_dir_boxed_487_; lean_object* v_res_488_; 
v_dir_boxed_487_ = lean_unbox(v_dir_484_);
v_res_488_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_487_, v_data_485_, v_writer_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object* v_limitSize_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_, lean_object* v_b_493_){
_start:
{
lean_object* v___y_495_; uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_499_ == 0)
{
lean_object* v_snd_500_; lean_object* v_fst_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_557_; 
v_snd_500_ = lean_ctor_get(v_b_493_, 1);
v_fst_501_ = lean_ctor_get(v_b_493_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_b_493_);
if (v_isSharedCheck_557_ == 0)
{
v___x_503_ = v_b_493_;
v_isShared_504_ = v_isSharedCheck_557_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snd_500_);
lean_inc(v_fst_501_);
lean_dec(v_b_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_557_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_556_; 
v_fst_505_ = lean_ctor_get(v_snd_500_, 0);
v_snd_506_ = lean_ctor_get(v_snd_500_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_snd_500_);
if (v_isSharedCheck_556_ == 0)
{
v___x_508_ = v_snd_500_;
v_isShared_509_ = v_isSharedCheck_556_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_inc(v_fst_505_);
lean_dec(v_snd_500_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_556_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_array_uget(v_as_490_, v_i_491_);
v___x_511_ = lean_nat_dec_le(v_limitSize_489_, v_snd_506_);
if (v___x_511_ == 0)
{
lean_object* v_data_512_; lean_object* v_extensions_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_548_; 
v_data_512_ = lean_ctor_get(v___x_510_, 0);
v_extensions_513_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_548_ == 0)
{
v___x_515_ = v___x_510_;
v_isShared_516_ = v_isSharedCheck_548_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_extensions_513_);
lean_inc(v_data_512_);
lean_dec(v___x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_548_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v_remaining_518_; lean_object* v___x_519_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_543_; uint8_t v___x_547_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v_remaining_518_ = lean_nat_sub(v_limitSize_489_, v_snd_506_);
v___x_519_ = lean_byte_array_size(v_data_512_);
v___x_547_ = lean_nat_dec_le(v___x_519_, v_remaining_518_);
if (v___x_547_ == 0)
{
v___y_543_ = v_remaining_518_;
goto v___jp_542_;
}
else
{
lean_dec(v_remaining_518_);
v___y_543_ = v___x_519_;
goto v___jp_542_;
}
v___jp_520_:
{
lean_object* v_size_523_; uint8_t v___x_524_; 
v_size_523_ = lean_nat_add(v_snd_506_, v___y_521_);
lean_dec(v_snd_506_);
v___x_524_ = lean_nat_dec_lt(v___y_521_, v___x_519_);
if (v___x_524_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v___y_521_);
lean_del_object(v___x_515_);
lean_dec_ref(v_extensions_513_);
lean_dec_ref(v_data_512_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_size_523_);
v___x_526_ = v___x_508_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_505_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_size_523_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_526_);
lean_ctor_set(v___x_503_, 0, v___y_522_);
v___x_528_ = v___x_503_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v___y_495_ = v___x_528_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v___x_531_; lean_object* v_pendingChunk_533_; 
v___x_531_ = l_ByteArray_extract(v_data_512_, v___y_521_, v___x_519_);
lean_dec_ref(v_data_512_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_531_);
v_pendingChunk_533_ = v___x_515_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_extensions_513_);
v_pendingChunk_533_ = v_reuseFailAlloc_541_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_array_push(v_fst_505_, v_pendingChunk_533_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_size_523_);
lean_ctor_set(v___x_508_, 0, v___x_534_);
v___x_536_ = v___x_508_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_size_523_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_536_);
lean_ctor_set(v___x_503_, 0, v___y_522_);
v___x_538_ = v___x_503_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v___y_495_ = v___x_538_;
goto v___jp_494_;
}
}
}
}
}
v___jp_542_:
{
uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_eq(v___y_543_, v___x_517_);
if (v___x_544_ == 0)
{
lean_object* v_dataPart_545_; lean_object* v___x_546_; 
v_dataPart_545_ = l_ByteArray_extract(v_data_512_, v___x_517_, v___y_543_);
v___x_546_ = lean_array_push(v_fst_501_, v_dataPart_545_);
v___y_521_ = v___y_543_;
v___y_522_ = v___x_546_;
goto v___jp_520_;
}
else
{
v___y_521_ = v___y_543_;
v___y_522_ = v_fst_501_;
goto v___jp_520_;
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_array_push(v_fst_505_, v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_549_);
v___x_551_ = v___x_508_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_snd_506_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_551_);
v___x_553_ = v___x_503_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_fst_501_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v___y_495_ = v___x_553_;
goto v___jp_494_;
}
}
}
}
}
}
else
{
return v_b_493_;
}
v___jp_494_:
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_491_, v___x_496_);
v_i_491_ = v___x_497_;
v_b_493_ = v___y_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_558_, lean_object* v_as_559_, lean_object* v_i_560_, lean_object* v_stop_561_, lean_object* v_b_562_){
_start:
{
size_t v_i_boxed_563_; size_t v_stop_boxed_564_; lean_object* v_res_565_; 
v_i_boxed_563_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_stop_boxed_564_ = lean_unbox_usize(v_stop_561_);
lean_dec(v_stop_561_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_558_, v_as_559_, v_i_boxed_563_, v_stop_boxed_564_, v_b_562_);
lean_dec_ref(v_as_559_);
lean_dec(v_limitSize_558_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_, lean_object* v_b_569_){
_start:
{
lean_object* v___y_571_; uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v___x_577_ = l_ByteArray_isEmpty(v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v_data_578_; lean_object* v_size_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
v_data_578_ = lean_ctor_get(v_b_569_, 0);
v_size_579_ = lean_ctor_get(v_b_569_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_b_569_);
if (v_isSharedCheck_589_ == 0)
{
v___x_581_ = v_b_569_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_size_579_);
lean_inc(v_data_578_);
lean_dec(v_b_569_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
lean_inc(v___x_576_);
v___x_583_ = lean_array_push(v_data_578_, v___x_576_);
v___x_584_ = lean_byte_array_size(v___x_576_);
v___x_585_ = lean_nat_add(v_size_579_, v___x_584_);
lean_dec(v_size_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_585_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v___y_571_ = v___x_587_;
goto v___jp_570_;
}
}
}
else
{
v___y_571_ = v_b_569_;
goto v___jp_570_;
}
}
else
{
return v_b_569_;
}
v___jp_570_:
{
size_t v___x_572_; size_t v___x_573_; 
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_567_, v___x_572_);
v_i_567_ = v___x_573_;
v_b_569_ = v___y_571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_590_, lean_object* v_i_591_, lean_object* v_stop_592_, lean_object* v_b_593_){
_start:
{
size_t v_i_boxed_594_; size_t v_stop_boxed_595_; lean_object* v_res_596_; 
v_i_boxed_594_ = lean_unbox_usize(v_i_591_);
lean_dec(v_i_591_);
v_stop_boxed_595_ = lean_unbox_usize(v_stop_592_);
lean_dec(v_stop_592_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_590_, v_i_boxed_594_, v_stop_boxed_595_, v_b_593_);
lean_dec_ref(v_as_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(lean_object* v_as_597_, size_t v_i_598_, size_t v_stop_599_, lean_object* v_b_600_){
_start:
{
lean_object* v___y_602_; uint8_t v___x_606_; 
v___x_606_ = lean_usize_dec_eq(v_i_598_, v_stop_599_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v_data_608_; uint8_t v___x_609_; 
v___x_607_ = lean_array_uget_borrowed(v_as_597_, v_i_598_);
v_data_608_ = lean_ctor_get(v___x_607_, 0);
v___x_609_ = l_ByteArray_isEmpty(v_data_608_);
if (v___x_609_ == 0)
{
lean_object* v_data_610_; lean_object* v_size_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_621_; 
v_data_610_ = lean_ctor_get(v_b_600_, 0);
v_size_611_ = lean_ctor_get(v_b_600_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_b_600_);
if (v_isSharedCheck_621_ == 0)
{
v___x_613_ = v_b_600_;
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_size_611_);
lean_inc(v_data_610_);
lean_dec(v_b_600_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
lean_inc_ref(v_data_608_);
v___x_615_ = lean_array_push(v_data_610_, v_data_608_);
v___x_616_ = lean_byte_array_size(v_data_608_);
v___x_617_ = lean_nat_add(v_size_611_, v___x_616_);
lean_dec(v_size_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_617_);
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
v___y_602_ = v___x_619_;
goto v___jp_601_;
}
}
}
else
{
v___y_602_ = v_b_600_;
goto v___jp_601_;
}
}
else
{
return v_b_600_;
}
v___jp_601_:
{
size_t v___x_603_; size_t v___x_604_; 
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_598_, v___x_603_);
v_i_598_ = v___x_604_;
v_b_600_ = v___y_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2___boxed(lean_object* v_as_622_, lean_object* v_i_623_, lean_object* v_stop_624_, lean_object* v_b_625_){
_start:
{
size_t v_i_boxed_626_; size_t v_stop_boxed_627_; lean_object* v_res_628_; 
v_i_boxed_626_ = lean_unbox_usize(v_i_623_);
lean_dec(v_i_623_);
v_stop_boxed_627_ = lean_unbox_usize(v_stop_624_);
lean_dec(v_stop_624_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(v_as_622_, v_i_boxed_626_, v_stop_boxed_627_, v_b_625_);
lean_dec_ref(v_as_622_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_639_, lean_object* v_limitSize_640_){
_start:
{
lean_object* v_userData_641_; lean_object* v_outputData_642_; lean_object* v_state_643_; lean_object* v_knownSize_644_; lean_object* v_messageHead_645_; uint8_t v_userClosedBody_646_; uint8_t v_omitBody_647_; lean_object* v_userDataBytes_648_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___y_660_; lean_object* v_fst_666_; lean_object* v_fst_667_; lean_object* v_snd_668_; uint8_t v___x_674_; 
v_userData_641_ = lean_ctor_get(v_writer_639_, 0);
v_outputData_642_ = lean_ctor_get(v_writer_639_, 1);
v_state_643_ = lean_ctor_get(v_writer_639_, 2);
v_knownSize_644_ = lean_ctor_get(v_writer_639_, 3);
v_messageHead_645_ = lean_ctor_get(v_writer_639_, 4);
v_userClosedBody_646_ = lean_ctor_get_uint8(v_writer_639_, sizeof(void*)*6);
v_omitBody_647_ = lean_ctor_get_uint8(v_writer_639_, sizeof(void*)*6 + 1);
v_userDataBytes_648_ = lean_ctor_get(v_writer_639_, 5);
v___x_657_ = lean_array_get_size(v_userData_641_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
lean_inc(v_userDataBytes_648_);
lean_inc(v_messageHead_645_);
lean_inc(v_knownSize_644_);
lean_inc(v_state_643_);
lean_inc_ref(v_outputData_642_);
lean_inc_ref(v_userData_641_);
lean_dec_ref(v_writer_639_);
v___x_675_ = lean_nat_dec_le(v_userDataBytes_648_, v_limitSize_640_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1));
v___x_677_ = lean_nat_dec_lt(v___x_658_, v___x_657_);
if (v___x_677_ == 0)
{
lean_dec_ref(v_userData_641_);
v_fst_666_ = v___x_676_;
v_fst_667_ = v___x_676_;
v_snd_668_ = v___x_658_;
goto v___jp_665_;
}
else
{
lean_object* v___x_678_; size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; lean_object* v_snd_682_; lean_object* v_fst_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; 
v___x_678_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__3));
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_657_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_640_, v_userData_641_, v___x_679_, v___x_680_, v___x_678_);
lean_dec_ref(v_userData_641_);
v_snd_682_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_snd_682_);
v_fst_683_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_fst_683_);
lean_dec_ref(v___x_681_);
v_fst_684_ = lean_ctor_get(v_snd_682_, 0);
lean_inc(v_fst_684_);
v_snd_685_ = lean_ctor_get(v_snd_682_, 1);
lean_inc(v_snd_685_);
lean_dec(v_snd_682_);
v_fst_666_ = v_fst_683_;
v_fst_667_ = v_fst_684_;
v_snd_668_ = v_snd_685_;
goto v___jp_665_;
}
}
else
{
uint8_t v___x_686_; 
v___x_686_ = lean_nat_dec_lt(v___x_658_, v___x_657_);
if (v___x_686_ == 0)
{
lean_dec_ref(v_userData_641_);
v___y_660_ = v_outputData_642_;
goto v___jp_659_;
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_657_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(v_userData_641_, v___x_687_, v___x_688_, v_outputData_642_);
lean_dec_ref(v_userData_641_);
v___y_660_ = v___x_689_;
goto v___jp_659_;
}
}
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_writer_639_);
lean_ctor_set(v___x_690_, 1, v_limitSize_640_);
return v___x_690_;
}
v___jp_649_:
{
lean_object* v_remaining_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_remaining_653_ = lean_nat_sub(v_limitSize_640_, v___y_651_);
lean_dec(v_limitSize_640_);
v___x_654_ = lean_nat_sub(v_userDataBytes_648_, v___y_651_);
lean_dec(v___y_651_);
lean_dec(v_userDataBytes_648_);
v___x_655_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_655_, 0, v___y_650_);
lean_ctor_set(v___x_655_, 1, v___y_652_);
lean_ctor_set(v___x_655_, 2, v_state_643_);
lean_ctor_set(v___x_655_, 3, v_knownSize_644_);
lean_ctor_set(v___x_655_, 4, v_messageHead_645_);
lean_ctor_set(v___x_655_, 5, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*6, v_userClosedBody_646_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*6 + 1, v_omitBody_647_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_remaining_653_);
return v___x_656_;
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_662_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___y_660_);
lean_ctor_set(v___x_662_, 2, v_state_643_);
lean_ctor_set(v___x_662_, 3, v_knownSize_644_);
lean_ctor_set(v___x_662_, 4, v_messageHead_645_);
lean_ctor_set(v___x_662_, 5, v___x_658_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*6, v_userClosedBody_646_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*6 + 1, v_omitBody_647_);
v___x_663_ = lean_nat_sub(v_limitSize_640_, v_userDataBytes_648_);
lean_dec(v_userDataBytes_648_);
lean_dec(v_limitSize_640_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
return v___x_664_;
}
v___jp_665_:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_array_get_size(v_fst_666_);
v___x_670_ = lean_nat_dec_lt(v___x_658_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec_ref(v_fst_666_);
v___y_650_ = v_fst_667_;
v___y_651_ = v_snd_668_;
v___y_652_ = v_outputData_642_;
goto v___jp_649_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_669_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_666_, v___x_671_, v___x_672_, v_outputData_642_);
lean_dec_ref(v_fst_666_);
v___y_650_ = v_fst_667_;
v___y_651_ = v_snd_668_;
v___y_652_ = v___x_673_;
goto v___jp_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_691_, lean_object* v_writer_692_, lean_object* v_limitSize_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_692_, v_limitSize_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_695_, lean_object* v_writer_696_, lean_object* v_limitSize_697_){
_start:
{
uint8_t v_dir_boxed_698_; lean_object* v_res_699_; 
v_dir_boxed_698_ = lean_unbox(v_dir_695_);
v_res_699_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_698_, v_writer_696_, v_limitSize_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(lean_object* v_as_700_, size_t v_i_701_, size_t v_stop_702_, lean_object* v_b_703_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = lean_usize_dec_eq(v_i_701_, v_stop_702_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; 
v___x_705_ = lean_array_uget_borrowed(v_as_700_, v_i_701_);
lean_inc(v___x_705_);
v___x_706_ = l_Std_Http_Internal_ChunkedBuffer_pushChunk(v_b_703_, v___x_705_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_701_, v___x_707_);
v_i_701_ = v___x_708_;
v_b_703_ = v___x_706_;
goto _start;
}
else
{
return v_b_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_, lean_object* v_b_713_){
_start:
{
size_t v_i_boxed_714_; size_t v_stop_boxed_715_; lean_object* v_res_716_; 
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_715_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_as_710_, v_i_boxed_714_, v_stop_boxed_715_, v_b_713_);
lean_dec_ref(v_as_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_717_, size_t v_i_718_, size_t v_stop_719_, lean_object* v_b_720_){
_start:
{
lean_object* v___y_722_; uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_eq(v_i_718_, v_stop_719_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v_data_728_; uint8_t v___x_729_; 
v___x_727_ = lean_array_uget_borrowed(v_as_717_, v_i_718_);
v_data_728_ = lean_ctor_get(v___x_727_, 0);
v___x_729_ = l_ByteArray_isEmpty(v_data_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_inc(v___x_727_);
v___x_730_ = lean_array_push(v_b_720_, v___x_727_);
v___y_722_ = v___x_730_;
goto v___jp_721_;
}
else
{
v___y_722_ = v_b_720_;
goto v___jp_721_;
}
}
else
{
return v_b_720_;
}
v___jp_721_:
{
size_t v___x_723_; size_t v___x_724_; 
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_718_, v___x_723_);
v_i_718_ = v___x_724_;
v_b_720_ = v___y_722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_stop_733_, lean_object* v_b_734_){
_start:
{
size_t v_i_boxed_735_; size_t v_stop_boxed_736_; lean_object* v_res_737_; 
v_i_boxed_735_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_stop_boxed_736_ = lean_unbox_usize(v_stop_733_);
lean_dec(v_stop_733_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_731_, v_i_boxed_735_, v_stop_boxed_736_, v_b_734_);
lean_dec_ref(v_as_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_738_){
_start:
{
lean_object* v_userData_739_; lean_object* v_outputData_740_; lean_object* v_state_741_; lean_object* v_knownSize_742_; lean_object* v_messageHead_743_; uint8_t v_userClosedBody_744_; uint8_t v_omitBody_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___y_749_; uint8_t v___x_758_; 
v_userData_739_ = lean_ctor_get(v_writer_738_, 0);
v_outputData_740_ = lean_ctor_get(v_writer_738_, 1);
v_state_741_ = lean_ctor_get(v_writer_738_, 2);
v_knownSize_742_ = lean_ctor_get(v_writer_738_, 3);
v_messageHead_743_ = lean_ctor_get(v_writer_738_, 4);
v_userClosedBody_744_ = lean_ctor_get_uint8(v_writer_738_, sizeof(void*)*6);
v_omitBody_745_ = lean_ctor_get_uint8(v_writer_738_, sizeof(void*)*6 + 1);
v___x_746_ = lean_array_get_size(v_userData_739_);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; uint8_t v___x_760_; 
lean_inc(v_messageHead_743_);
lean_inc(v_knownSize_742_);
lean_inc(v_state_741_);
lean_inc_ref(v_outputData_740_);
lean_inc_ref(v_userData_739_);
lean_dec_ref(v_writer_738_);
v___x_759_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_760_ = lean_nat_dec_lt(v___x_747_, v___x_746_);
if (v___x_760_ == 0)
{
lean_dec_ref(v_userData_739_);
v___y_749_ = v___x_759_;
goto v___jp_748_;
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_746_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_userData_739_, v___x_761_, v___x_762_, v___x_759_);
lean_dec_ref(v_userData_739_);
v___y_749_ = v___x_763_;
goto v___jp_748_;
}
}
else
{
return v_writer_738_;
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_751_ = lean_array_get_size(v___y_749_);
v___x_752_ = lean_nat_dec_lt(v___x_747_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec_ref(v___y_749_);
v___x_753_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v_outputData_740_);
lean_ctor_set(v___x_753_, 2, v_state_741_);
lean_ctor_set(v___x_753_, 3, v_knownSize_742_);
lean_ctor_set(v___x_753_, 4, v_messageHead_743_);
lean_ctor_set(v___x_753_, 5, v___x_747_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*6, v_userClosedBody_744_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*6 + 1, v_omitBody_745_);
return v___x_753_;
}
else
{
size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_751_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v___y_749_, v___x_754_, v___x_755_, v_outputData_740_);
lean_dec_ref(v___y_749_);
v___x_757_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_757_, 0, v___x_750_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
lean_ctor_set(v___x_757_, 2, v_state_741_);
lean_ctor_set(v___x_757_, 3, v_knownSize_742_);
lean_ctor_set(v___x_757_, 4, v_messageHead_743_);
lean_ctor_set(v___x_757_, 5, v___x_747_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*6, v_userClosedBody_744_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*6 + 1, v_omitBody_745_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_764_, lean_object* v_writer_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_767_, lean_object* v_writer_768_){
_start:
{
uint8_t v_dir_boxed_769_; lean_object* v_res_770_; 
v_dir_boxed_769_ = lean_unbox(v_dir_767_);
v_res_770_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_769_, v_writer_768_);
return v_res_770_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_773_ = lean_string_to_utf8(v___x_772_);
return v___x_773_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_775_ = l_ByteArray_isEmpty(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_777_ = lean_byte_array_size(v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_778_){
_start:
{
lean_object* v_writer_779_; lean_object* v_userData_780_; lean_object* v_outputData_781_; lean_object* v_knownSize_782_; lean_object* v_messageHead_783_; uint8_t v_userClosedBody_784_; uint8_t v_omitBody_785_; lean_object* v_userDataBytes_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_810_; 
v_writer_779_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_778_);
v_userData_780_ = lean_ctor_get(v_writer_779_, 0);
v_outputData_781_ = lean_ctor_get(v_writer_779_, 1);
v_knownSize_782_ = lean_ctor_get(v_writer_779_, 3);
v_messageHead_783_ = lean_ctor_get(v_writer_779_, 4);
v_userClosedBody_784_ = lean_ctor_get_uint8(v_writer_779_, sizeof(void*)*6);
v_omitBody_785_ = lean_ctor_get_uint8(v_writer_779_, sizeof(void*)*6 + 1);
v_userDataBytes_786_ = lean_ctor_get(v_writer_779_, 5);
v_isSharedCheck_810_ = !lean_is_exclusive(v_writer_779_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_writer_779_, 2);
lean_dec(v_unused_811_);
v___x_788_ = v_writer_779_;
v_isShared_789_ = v_isSharedCheck_810_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_userDataBytes_786_);
lean_inc(v_messageHead_783_);
lean_inc(v_knownSize_782_);
lean_inc(v_outputData_781_);
lean_inc(v_userData_780_);
lean_dec(v_writer_779_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_810_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___y_791_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_797_ = lean_uint8_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
if (v___x_797_ == 0)
{
lean_object* v_data_798_; lean_object* v_size_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_809_; 
v_data_798_ = lean_ctor_get(v_outputData_781_, 0);
v_size_799_ = lean_ctor_get(v_outputData_781_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_outputData_781_);
if (v_isSharedCheck_809_ == 0)
{
v___x_801_ = v_outputData_781_;
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_size_799_);
lean_inc(v_data_798_);
lean_dec(v_outputData_781_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_803_ = lean_array_push(v_data_798_, v___x_796_);
v___x_804_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3);
v___x_805_ = lean_nat_add(v_size_799_, v___x_804_);
lean_dec(v_size_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_805_);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
v___y_791_ = v___x_807_;
goto v___jp_790_;
}
}
}
else
{
v___y_791_ = v_outputData_781_;
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_box(6);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v___x_792_);
lean_ctor_set(v___x_788_, 1, v___y_791_);
v___x_794_ = v___x_788_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_userData_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___y_791_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_knownSize_782_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_messageHead_783_);
lean_ctor_set(v_reuseFailAlloc_795_, 5, v_userDataBytes_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_795_, sizeof(void*)*6, v_userClosedBody_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_795_, sizeof(void*)*6 + 1, v_omitBody_785_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_812_, lean_object* v_writer_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_815_, lean_object* v_writer_816_){
_start:
{
uint8_t v_dir_boxed_817_; lean_object* v_res_818_; 
v_dir_boxed_817_ = lean_unbox(v_dir_815_);
v_res_818_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_817_, v_writer_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_819_){
_start:
{
lean_object* v_userData_820_; lean_object* v_outputData_821_; lean_object* v_state_822_; lean_object* v_knownSize_823_; lean_object* v_messageHead_824_; uint8_t v_userClosedBody_825_; uint8_t v_omitBody_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_843_; 
v_userData_820_ = lean_ctor_get(v_writer_819_, 0);
v_outputData_821_ = lean_ctor_get(v_writer_819_, 1);
v_state_822_ = lean_ctor_get(v_writer_819_, 2);
v_knownSize_823_ = lean_ctor_get(v_writer_819_, 3);
v_messageHead_824_ = lean_ctor_get(v_writer_819_, 4);
v_userClosedBody_825_ = lean_ctor_get_uint8(v_writer_819_, sizeof(void*)*6);
v_omitBody_826_ = lean_ctor_get_uint8(v_writer_819_, sizeof(void*)*6 + 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_writer_819_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_writer_819_, 5);
lean_dec(v_unused_844_);
v___x_828_ = v_writer_819_;
v_isShared_829_ = v_isSharedCheck_843_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_messageHead_824_);
lean_inc(v_knownSize_823_);
lean_inc(v_state_822_);
lean_inc(v_outputData_821_);
lean_inc(v_userData_820_);
lean_dec(v_writer_819_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_843_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_832_ = lean_array_get_size(v_userData_820_);
v___x_833_ = lean_nat_dec_lt(v___x_830_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_userData_820_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 5, v___x_830_);
lean_ctor_set(v___x_828_, 0, v___x_831_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_outputData_821_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_state_822_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_knownSize_823_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_messageHead_824_);
lean_ctor_set(v_reuseFailAlloc_836_, 5, v___x_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_836_, sizeof(void*)*6, v_userClosedBody_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_836_, sizeof(void*)*6 + 1, v_omitBody_826_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_of_nat(v___x_832_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(v_userData_820_, v___x_837_, v___x_838_, v_outputData_821_);
lean_dec_ref(v_userData_820_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 5, v___x_830_);
lean_ctor_set(v___x_828_, 1, v___x_839_);
lean_ctor_set(v___x_828_, 0, v___x_831_);
v___x_841_ = v___x_828_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_state_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_knownSize_823_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_messageHead_824_);
lean_ctor_set(v_reuseFailAlloc_842_, 5, v___x_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*6, v_userClosedBody_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*6 + 1, v_omitBody_826_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_845_, lean_object* v_writer_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_848_, lean_object* v_writer_849_){
_start:
{
uint8_t v_dir_boxed_850_; lean_object* v_res_851_; 
v_dir_boxed_850_ = lean_unbox(v_dir_848_);
v_res_851_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_850_, v_writer_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_852_, lean_object* v_writer_853_){
_start:
{
lean_object* v_userData_854_; lean_object* v_outputData_855_; lean_object* v_knownSize_856_; lean_object* v_messageHead_857_; uint8_t v_userClosedBody_858_; uint8_t v_omitBody_859_; lean_object* v_userDataBytes_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_userData_854_ = lean_ctor_get(v_writer_853_, 0);
v_outputData_855_ = lean_ctor_get(v_writer_853_, 1);
v_knownSize_856_ = lean_ctor_get(v_writer_853_, 3);
v_messageHead_857_ = lean_ctor_get(v_writer_853_, 4);
v_userClosedBody_858_ = lean_ctor_get_uint8(v_writer_853_, sizeof(void*)*6);
v_omitBody_859_ = lean_ctor_get_uint8(v_writer_853_, sizeof(void*)*6 + 1);
v_userDataBytes_860_ = lean_ctor_get(v_writer_853_, 5);
v_isSharedCheck_867_ = !lean_is_exclusive(v_writer_853_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_writer_853_, 2);
lean_dec(v_unused_868_);
v___x_862_ = v_writer_853_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_userDataBytes_860_);
lean_inc(v_messageHead_857_);
lean_inc(v_knownSize_856_);
lean_inc(v_outputData_855_);
lean_inc(v_userData_854_);
lean_dec(v_writer_853_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 2, v_state_852_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_userData_854_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_outputData_855_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_state_852_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_knownSize_856_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_messageHead_857_);
lean_ctor_set(v_reuseFailAlloc_866_, 5, v_userDataBytes_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_866_, sizeof(void*)*6, v_userClosedBody_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_866_, sizeof(void*)*6 + 1, v_omitBody_859_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_869_, lean_object* v_state_870_, lean_object* v_writer_871_){
_start:
{
lean_object* v_userData_872_; lean_object* v_outputData_873_; lean_object* v_knownSize_874_; lean_object* v_messageHead_875_; uint8_t v_userClosedBody_876_; uint8_t v_omitBody_877_; lean_object* v_userDataBytes_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_userData_872_ = lean_ctor_get(v_writer_871_, 0);
v_outputData_873_ = lean_ctor_get(v_writer_871_, 1);
v_knownSize_874_ = lean_ctor_get(v_writer_871_, 3);
v_messageHead_875_ = lean_ctor_get(v_writer_871_, 4);
v_userClosedBody_876_ = lean_ctor_get_uint8(v_writer_871_, sizeof(void*)*6);
v_omitBody_877_ = lean_ctor_get_uint8(v_writer_871_, sizeof(void*)*6 + 1);
v_userDataBytes_878_ = lean_ctor_get(v_writer_871_, 5);
v_isSharedCheck_885_ = !lean_is_exclusive(v_writer_871_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v_writer_871_, 2);
lean_dec(v_unused_886_);
v___x_880_ = v_writer_871_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_userDataBytes_878_);
lean_inc(v_messageHead_875_);
lean_inc(v_knownSize_874_);
lean_inc(v_outputData_873_);
lean_inc(v_userData_872_);
lean_dec(v_writer_871_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v_state_870_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_userData_872_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_outputData_873_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_state_870_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_knownSize_874_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v_messageHead_875_);
lean_ctor_set(v_reuseFailAlloc_884_, 5, v_userDataBytes_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_884_, sizeof(void*)*6, v_userClosedBody_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_884_, sizeof(void*)*6 + 1, v_omitBody_877_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_887_, lean_object* v_state_888_, lean_object* v_writer_889_){
_start:
{
uint8_t v_dir_boxed_890_; lean_object* v_res_891_; 
v_dir_boxed_890_ = lean_unbox(v_dir_887_);
v_res_891_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_890_, v_state_888_, v_writer_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_map_892_, lean_object* v_key_893_, lean_object* v_i_894_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_array_get_size(v_map_892_);
v___x_896_ = lean_nat_dec_lt(v_i_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v_i_894_);
return v___x_895_;
}
else
{
lean_object* v___x_897_; lean_object* v_fst_898_; uint8_t v___x_899_; 
v___x_897_ = lean_array_fget_borrowed(v_map_892_, v_i_894_);
v_fst_898_ = lean_ctor_get(v___x_897_, 0);
v___x_899_ = lean_string_dec_eq(v_fst_898_, v_key_893_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_i_894_, v___x_900_);
lean_dec(v_i_894_);
v_i_894_ = v___x_901_;
goto _start;
}
else
{
return v_i_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_map_903_, lean_object* v_key_904_, lean_object* v_i_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_map_903_, v_key_904_, v_i_905_);
lean_dec_ref(v_key_904_);
lean_dec_ref(v_map_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_s_907_, lean_object* v_p_908_){
_start:
{
lean_object* v___y_910_; lean_object* v___y_911_; uint32_t v___y_915_; lean_object* v___x_927_; uint8_t v_decide_928_; 
v___x_927_ = lean_string_utf8_byte_size(v_s_907_);
v_decide_928_ = lean_nat_dec_eq(v_p_908_, v___x_927_);
if (v_decide_928_ == 0)
{
uint32_t v___x_929_; uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_929_ = lean_string_utf8_get_fast(v_s_907_, v_p_908_);
v___x_930_ = 65;
v___x_931_ = lean_uint32_dec_le(v___x_930_, v___x_929_);
if (v___x_931_ == 0)
{
v___y_915_ = v___x_929_;
goto v___jp_914_;
}
else
{
uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = 90;
v___x_933_ = lean_uint32_dec_le(v___x_929_, v___x_932_);
if (v___x_933_ == 0)
{
v___y_915_ = v___x_929_;
goto v___jp_914_;
}
else
{
uint32_t v___x_934_; uint32_t v___x_935_; 
v___x_934_ = 32;
v___x_935_ = lean_uint32_add(v___x_929_, v___x_934_);
v___y_915_ = v___x_935_;
goto v___jp_914_;
}
}
}
else
{
lean_dec(v_p_908_);
return v_s_907_;
}
v___jp_909_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_nat_add(v_p_908_, v___y_911_);
lean_dec(v_p_908_);
v_s_907_ = v___y_910_;
v_p_908_ = v___x_912_;
goto _start;
}
v___jp_914_:
{
lean_object* v___x_916_; uint32_t v___x_917_; uint8_t v___x_918_; 
lean_inc(v_p_908_);
v___x_916_ = lean_string_utf8_set(v_s_907_, v_p_908_, v___y_915_);
v___x_917_ = 127;
v___x_918_ = lean_uint32_dec_le(v___y_915_, v___x_917_);
if (v___x_918_ == 0)
{
uint32_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 2047;
v___x_920_ = lean_uint32_dec_le(v___y_915_, v___x_919_);
if (v___x_920_ == 0)
{
uint32_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = 65535;
v___x_922_ = lean_uint32_dec_le(v___y_915_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = lean_unsigned_to_nat(4u);
v___y_910_ = v___x_916_;
v___y_911_ = v___x_923_;
goto v___jp_909_;
}
else
{
lean_object* v___x_924_; 
v___x_924_ = lean_unsigned_to_nat(3u);
v___y_910_ = v___x_916_;
v___y_911_ = v___x_924_;
goto v___jp_909_;
}
}
else
{
lean_object* v___x_925_; 
v___x_925_ = lean_unsigned_to_nat(2u);
v___y_910_ = v___x_916_;
v___y_911_ = v___x_925_;
goto v___jp_909_;
}
}
else
{
lean_object* v___x_926_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___y_910_ = v___x_916_;
v___y_911_ = v___x_926_;
goto v___jp_909_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_937_, lean_object* v_writer_938_){
_start:
{
uint8_t v___y_940_; 
if (v_dir_937_ == 0)
{
uint8_t v___x_955_; 
v___x_955_ = 1;
v___y_940_ = v___x_955_;
goto v___jp_939_;
}
else
{
uint8_t v___x_956_; 
v___x_956_ = 0;
v___y_940_ = v___x_956_;
goto v___jp_939_;
}
v___jp_939_:
{
lean_object* v_messageHead_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_i_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_messageHead_941_ = lean_ctor_get(v_writer_938_, 4);
v___x_942_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_940_, v_messageHead_941_);
v___x_943_ = l_Std_Http_Header_Name_connection;
v___x_944_ = lean_unsigned_to_nat(0u);
v_i_945_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v___x_942_, v___x_943_, v___x_944_);
v___x_946_ = lean_array_get_size(v___x_942_);
v___x_947_ = lean_nat_dec_lt(v_i_945_, v___x_946_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; 
lean_dec(v_i_945_);
lean_dec_ref(v___x_942_);
v___x_948_ = 1;
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v_snd_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_949_ = lean_array_fget(v___x_942_, v_i_945_);
lean_dec(v_i_945_);
lean_dec_ref(v___x_942_);
v_snd_950_ = lean_ctor_get(v___x_949_, 1);
lean_inc(v_snd_950_);
lean_dec(v___x_949_);
v___x_951_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_snd_950_, v___x_944_);
v___x_952_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_953_ = lean_string_dec_eq(v___x_951_, v___x_952_);
lean_dec_ref(v___x_951_);
if (v___x_953_ == 0)
{
return v___x_947_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = 0;
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_957_, lean_object* v_writer_958_){
_start:
{
uint8_t v_dir_boxed_959_; uint8_t v_res_960_; lean_object* v_r_961_; 
v_dir_boxed_959_ = lean_unbox(v_dir_957_);
v_res_960_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_959_, v_writer_958_);
lean_dec_ref(v_writer_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_962_, lean_object* v_map_963_, lean_object* v_key_964_, lean_object* v_i_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_map_963_, v_key_964_, v_i_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_967_, lean_object* v_map_968_, lean_object* v_key_969_, lean_object* v_i_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_967_, v_map_968_, v_key_969_, v_i_970_);
lean_dec_ref(v_key_969_);
lean_dec_ref(v_map_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_972_){
_start:
{
lean_object* v_userData_973_; lean_object* v_outputData_974_; lean_object* v_knownSize_975_; lean_object* v_messageHead_976_; uint8_t v_userClosedBody_977_; uint8_t v_omitBody_978_; lean_object* v_userDataBytes_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_userData_973_ = lean_ctor_get(v_writer_972_, 0);
v_outputData_974_ = lean_ctor_get(v_writer_972_, 1);
v_knownSize_975_ = lean_ctor_get(v_writer_972_, 3);
v_messageHead_976_ = lean_ctor_get(v_writer_972_, 4);
v_userClosedBody_977_ = lean_ctor_get_uint8(v_writer_972_, sizeof(void*)*6);
v_omitBody_978_ = lean_ctor_get_uint8(v_writer_972_, sizeof(void*)*6 + 1);
v_userDataBytes_979_ = lean_ctor_get(v_writer_972_, 5);
v_isSharedCheck_987_ = !lean_is_exclusive(v_writer_972_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; 
v_unused_988_ = lean_ctor_get(v_writer_972_, 2);
lean_dec(v_unused_988_);
v___x_981_ = v_writer_972_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_userDataBytes_979_);
lean_inc(v_messageHead_976_);
lean_inc(v_knownSize_975_);
lean_inc(v_outputData_974_);
lean_inc(v_userData_973_);
lean_dec(v_writer_972_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_box(7);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 2, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_userData_973_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_outputData_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_knownSize_975_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_messageHead_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 5, v_userDataBytes_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_986_, sizeof(void*)*6, v_userClosedBody_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_986_, sizeof(void*)*6 + 1, v_omitBody_978_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_989_, lean_object* v_writer_990_){
_start:
{
lean_object* v_userData_991_; lean_object* v_outputData_992_; lean_object* v_knownSize_993_; lean_object* v_messageHead_994_; uint8_t v_userClosedBody_995_; uint8_t v_omitBody_996_; lean_object* v_userDataBytes_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
v_userData_991_ = lean_ctor_get(v_writer_990_, 0);
v_outputData_992_ = lean_ctor_get(v_writer_990_, 1);
v_knownSize_993_ = lean_ctor_get(v_writer_990_, 3);
v_messageHead_994_ = lean_ctor_get(v_writer_990_, 4);
v_userClosedBody_995_ = lean_ctor_get_uint8(v_writer_990_, sizeof(void*)*6);
v_omitBody_996_ = lean_ctor_get_uint8(v_writer_990_, sizeof(void*)*6 + 1);
v_userDataBytes_997_ = lean_ctor_get(v_writer_990_, 5);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_writer_990_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v_writer_990_, 2);
lean_dec(v_unused_1006_);
v___x_999_ = v_writer_990_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_userDataBytes_997_);
lean_inc(v_messageHead_994_);
lean_inc(v_knownSize_993_);
lean_inc(v_outputData_992_);
lean_inc(v_userData_991_);
lean_dec(v_writer_990_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(7);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 2, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_userData_991_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_outputData_992_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_knownSize_993_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_messageHead_994_);
lean_ctor_set(v_reuseFailAlloc_1004_, 5, v_userDataBytes_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*6, v_userClosedBody_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*6 + 1, v_omitBody_996_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1007_, lean_object* v_writer_1008_){
_start:
{
uint8_t v_dir_boxed_1009_; lean_object* v_res_1010_; 
v_dir_boxed_1009_ = lean_unbox(v_dir_1007_);
v_res_1010_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1009_, v_writer_1008_);
return v_res_1010_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_Writer_instInhabitedState_default = _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default();
lean_mark_persistent(l_Std_Http_Protocol_H1_Writer_instInhabitedState_default);
l_Std_Http_Protocol_H1_Writer_instInhabitedState = _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState();
lean_mark_persistent(l_Std_Http_Protocol_H1_Writer_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Writer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Writer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Writer(builtin);
}
#ifdef __cplusplus
}
#endif
