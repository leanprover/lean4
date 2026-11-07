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
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(lean_object* v_writer_249_){
_start:
{
lean_object* v_state_250_; 
v_state_250_ = lean_ctor_get(v_writer_249_, 2);
switch(lean_obj_tag(v_state_250_))
{
case 7:
{
uint8_t v___x_251_; 
v___x_251_ = 1;
return v___x_251_;
}
case 6:
{
uint8_t v___x_252_; 
v___x_252_ = 1;
return v___x_252_;
}
default: 
{
uint8_t v_userClosedBody_253_; 
v_userClosedBody_253_ = lean_ctor_get_uint8(v_writer_249_, sizeof(void*)*6 + 1);
return v_userClosedBody_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(lean_object* v_writer_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_254_);
lean_dec_ref(v_writer_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData(uint8_t v_dir_257_, lean_object* v_writer_258_){
_start:
{
lean_object* v_state_259_; 
v_state_259_ = lean_ctor_get(v_writer_258_, 2);
switch(lean_obj_tag(v_state_259_))
{
case 7:
{
uint8_t v___x_260_; 
v___x_260_ = 1;
return v___x_260_;
}
case 6:
{
uint8_t v___x_261_; 
v___x_261_ = 1;
return v___x_261_;
}
default: 
{
uint8_t v_userClosedBody_262_; 
v_userClosedBody_262_ = lean_ctor_get_uint8(v_writer_258_, sizeof(void*)*6 + 1);
return v_userClosedBody_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(lean_object* v_dir_263_, lean_object* v_writer_264_){
_start:
{
uint8_t v_dir_boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_dir_boxed_265_ = lean_unbox(v_dir_263_);
v_res_266_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_boxed_265_, v_writer_264_);
lean_dec_ref(v_writer_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed___redArg(lean_object* v_writer_268_){
_start:
{
lean_object* v_state_269_; 
v_state_269_ = lean_ctor_get(v_writer_268_, 2);
if (lean_obj_tag(v_state_269_) == 7)
{
uint8_t v___x_270_; 
v___x_270_ = 1;
return v___x_270_;
}
else
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(lean_object* v_writer_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_272_);
lean_dec_ref(v_writer_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed(uint8_t v_dir_275_, lean_object* v_writer_276_){
_start:
{
lean_object* v_state_277_; 
v_state_277_ = lean_ctor_get(v_writer_276_, 2);
if (lean_obj_tag(v_state_277_) == 7)
{
uint8_t v___x_278_; 
v___x_278_ = 1;
return v___x_278_;
}
else
{
uint8_t v___x_279_; 
v___x_279_ = 0;
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___boxed(lean_object* v_dir_280_, lean_object* v_writer_281_){
_start:
{
uint8_t v_dir_boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_dir_boxed_282_ = lean_unbox(v_dir_280_);
v_res_283_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_boxed_282_, v_writer_281_);
lean_dec_ref(v_writer_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete___redArg(lean_object* v_writer_285_){
_start:
{
lean_object* v_state_286_; 
v_state_286_ = lean_ctor_get(v_writer_285_, 2);
if (lean_obj_tag(v_state_286_) == 6)
{
uint8_t v___x_287_; 
v___x_287_ = 1;
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(lean_object* v_writer_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_289_);
lean_dec_ref(v_writer_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete(uint8_t v_dir_292_, lean_object* v_writer_293_){
_start:
{
lean_object* v_state_294_; 
v_state_294_ = lean_ctor_get(v_writer_293_, 2);
if (lean_obj_tag(v_state_294_) == 6)
{
uint8_t v___x_295_; 
v___x_295_ = 1;
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___boxed(lean_object* v_dir_297_, lean_object* v_writer_298_){
_start:
{
uint8_t v_dir_boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_dir_boxed_299_ = lean_unbox(v_dir_297_);
v_res_300_ = l_Std_Http_Protocol_H1_Writer_isComplete(v_dir_boxed_299_, v_writer_298_);
lean_dec_ref(v_writer_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(lean_object* v_writer_302_){
_start:
{
lean_object* v_state_303_; uint8_t v_userClosedBody_304_; 
v_state_303_ = lean_ctor_get(v_writer_302_, 2);
v_userClosedBody_304_ = lean_ctor_get_uint8(v_writer_302_, sizeof(void*)*6 + 1);
switch(lean_obj_tag(v_state_303_))
{
case 1:
{
uint8_t v___x_308_; 
v___x_308_ = 1;
return v___x_308_;
}
case 2:
{
uint8_t v___x_309_; 
v___x_309_ = 1;
return v___x_309_;
}
case 3:
{
if (v_userClosedBody_304_ == 0)
{
uint8_t v___x_310_; 
v___x_310_ = 1;
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
case 4:
{
goto v___jp_305_;
}
case 5:
{
goto v___jp_305_;
}
default: 
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
}
v___jp_305_:
{
if (v_userClosedBody_304_ == 0)
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
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(lean_object* v_writer_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_313_);
lean_dec_ref(v_writer_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData(uint8_t v_dir_316_, lean_object* v_writer_317_){
_start:
{
lean_object* v_state_318_; uint8_t v_userClosedBody_319_; 
v_state_318_ = lean_ctor_get(v_writer_317_, 2);
v_userClosedBody_319_ = lean_ctor_get_uint8(v_writer_317_, sizeof(void*)*6 + 1);
switch(lean_obj_tag(v_state_318_))
{
case 1:
{
uint8_t v___x_323_; 
v___x_323_ = 1;
return v___x_323_;
}
case 2:
{
uint8_t v___x_324_; 
v___x_324_ = 1;
return v___x_324_;
}
case 3:
{
if (v_userClosedBody_319_ == 0)
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
case 4:
{
goto v___jp_320_;
}
case 5:
{
goto v___jp_320_;
}
default: 
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
}
v___jp_320_:
{
if (v_userClosedBody_319_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = 1;
return v___x_321_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = 0;
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(lean_object* v_dir_328_, lean_object* v_writer_329_){
_start:
{
uint8_t v_dir_boxed_330_; uint8_t v_res_331_; lean_object* v_r_332_; 
v_dir_boxed_330_ = lean_unbox(v_dir_328_);
v_res_331_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_boxed_330_, v_writer_329_);
lean_dec_ref(v_writer_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___redArg(lean_object* v_writer_333_){
_start:
{
lean_object* v_userData_334_; lean_object* v_outputData_335_; lean_object* v_state_336_; lean_object* v_knownSize_337_; lean_object* v_messageHead_338_; uint8_t v_sentMessage_339_; uint8_t v_omitBody_340_; lean_object* v_userDataBytes_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v_userData_334_ = lean_ctor_get(v_writer_333_, 0);
v_outputData_335_ = lean_ctor_get(v_writer_333_, 1);
v_state_336_ = lean_ctor_get(v_writer_333_, 2);
v_knownSize_337_ = lean_ctor_get(v_writer_333_, 3);
v_messageHead_338_ = lean_ctor_get(v_writer_333_, 4);
v_sentMessage_339_ = lean_ctor_get_uint8(v_writer_333_, sizeof(void*)*6);
v_omitBody_340_ = lean_ctor_get_uint8(v_writer_333_, sizeof(void*)*6 + 2);
v_userDataBytes_341_ = lean_ctor_get(v_writer_333_, 5);
v_isSharedCheck_349_ = !lean_is_exclusive(v_writer_333_);
if (v_isSharedCheck_349_ == 0)
{
v___x_343_ = v_writer_333_;
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_userDataBytes_341_);
lean_inc(v_messageHead_338_);
lean_inc(v_knownSize_337_);
lean_inc(v_state_336_);
lean_inc(v_outputData_335_);
lean_inc(v_userData_334_);
lean_dec(v_writer_333_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___x_345_; lean_object* v___x_347_; 
v___x_345_ = 1;
if (v_isShared_344_ == 0)
{
v___x_347_ = v___x_343_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_userData_334_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_outputData_335_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_state_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_knownSize_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_messageHead_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 5, v_userDataBytes_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*6, v_sentMessage_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*6 + 2, v_omitBody_340_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*6 + 1, v___x_345_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody(uint8_t v_dir_350_, lean_object* v_writer_351_){
_start:
{
lean_object* v_userData_352_; lean_object* v_outputData_353_; lean_object* v_state_354_; lean_object* v_knownSize_355_; lean_object* v_messageHead_356_; uint8_t v_sentMessage_357_; uint8_t v_omitBody_358_; lean_object* v_userDataBytes_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_userData_352_ = lean_ctor_get(v_writer_351_, 0);
v_outputData_353_ = lean_ctor_get(v_writer_351_, 1);
v_state_354_ = lean_ctor_get(v_writer_351_, 2);
v_knownSize_355_ = lean_ctor_get(v_writer_351_, 3);
v_messageHead_356_ = lean_ctor_get(v_writer_351_, 4);
v_sentMessage_357_ = lean_ctor_get_uint8(v_writer_351_, sizeof(void*)*6);
v_omitBody_358_ = lean_ctor_get_uint8(v_writer_351_, sizeof(void*)*6 + 2);
v_userDataBytes_359_ = lean_ctor_get(v_writer_351_, 5);
v_isSharedCheck_367_ = !lean_is_exclusive(v_writer_351_);
if (v_isSharedCheck_367_ == 0)
{
v___x_361_ = v_writer_351_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_userDataBytes_359_);
lean_inc(v_messageHead_356_);
lean_inc(v_knownSize_355_);
lean_inc(v_state_354_);
lean_inc(v_outputData_353_);
lean_inc(v_userData_352_);
lean_dec(v_writer_351_);
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
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_userData_352_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_outputData_353_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_state_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_knownSize_355_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_messageHead_356_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_userDataBytes_359_);
lean_ctor_set_uint8(v_reuseFailAlloc_366_, sizeof(void*)*6, v_sentMessage_357_);
lean_ctor_set_uint8(v_reuseFailAlloc_366_, sizeof(void*)*6 + 2, v_omitBody_358_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*6 + 1, v___x_363_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___boxed(lean_object* v_dir_368_, lean_object* v_writer_369_){
_start:
{
uint8_t v_dir_boxed_370_; lean_object* v_res_371_; 
v_dir_boxed_370_ = lean_unbox(v_dir_368_);
v_res_371_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_boxed_370_, v_writer_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(lean_object* v_writer_372_){
_start:
{
lean_object* v_knownSize_373_; 
v_knownSize_373_ = lean_ctor_get(v_writer_372_, 3);
if (lean_obj_tag(v_knownSize_373_) == 1)
{
lean_object* v_val_374_; 
v_val_374_ = lean_ctor_get(v_knownSize_373_, 0);
lean_inc(v_val_374_);
return v_val_374_;
}
else
{
uint8_t v_userClosedBody_375_; 
v_userClosedBody_375_ = lean_ctor_get_uint8(v_writer_372_, sizeof(void*)*6 + 1);
if (v_userClosedBody_375_ == 0)
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
else
{
lean_object* v_userDataBytes_377_; lean_object* v___x_378_; 
v_userDataBytes_377_ = lean_ctor_get(v_writer_372_, 5);
lean_inc(v_userDataBytes_377_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_userDataBytes_377_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(lean_object* v_writer_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_379_);
lean_dec_ref(v_writer_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode(uint8_t v_dir_381_, lean_object* v_writer_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(lean_object* v_dir_384_, lean_object* v_writer_385_){
_start:
{
uint8_t v_dir_boxed_386_; lean_object* v_res_387_; 
v_dir_boxed_386_ = lean_unbox(v_dir_384_);
v_res_387_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_boxed_386_, v_writer_385_);
lean_dec_ref(v_writer_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(lean_object* v_x1_388_, lean_object* v_x2_389_){
_start:
{
lean_object* v_data_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_data_390_ = lean_ctor_get(v_x2_389_, 0);
v___x_391_ = lean_byte_array_size(v_data_390_);
v___x_392_ = lean_nat_add(v_x1_388_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(lean_object* v_x1_393_, lean_object* v_x2_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(v_x1_393_, v_x2_394_);
lean_dec_ref(v_x2_394_);
lean_dec(v_x1_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg(lean_object* v_data_416_, lean_object* v_writer_417_){
_start:
{
lean_object* v_userData_418_; lean_object* v_outputData_419_; lean_object* v_state_420_; lean_object* v_knownSize_421_; lean_object* v_messageHead_422_; uint8_t v_sentMessage_423_; uint8_t v_userClosedBody_424_; uint8_t v_omitBody_425_; lean_object* v_userDataBytes_426_; lean_object* v___y_428_; lean_object* v___f_432_; 
v_userData_418_ = lean_ctor_get(v_writer_417_, 0);
v_outputData_419_ = lean_ctor_get(v_writer_417_, 1);
v_state_420_ = lean_ctor_get(v_writer_417_, 2);
v_knownSize_421_ = lean_ctor_get(v_writer_417_, 3);
v_messageHead_422_ = lean_ctor_get(v_writer_417_, 4);
v_sentMessage_423_ = lean_ctor_get_uint8(v_writer_417_, sizeof(void*)*6);
v_userClosedBody_424_ = lean_ctor_get_uint8(v_writer_417_, sizeof(void*)*6 + 1);
v_omitBody_425_ = lean_ctor_get_uint8(v_writer_417_, sizeof(void*)*6 + 2);
v_userDataBytes_426_ = lean_ctor_get(v_writer_417_, 5);
v___f_432_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_420_))
{
case 1:
{
lean_inc(v_state_420_);
lean_inc(v_userDataBytes_426_);
lean_inc(v_messageHead_422_);
lean_inc(v_knownSize_421_);
lean_inc_ref(v_outputData_419_);
lean_inc_ref(v_userData_418_);
lean_dec_ref(v_writer_417_);
goto v___jp_433_;
}
case 2:
{
lean_inc(v_state_420_);
lean_inc(v_userDataBytes_426_);
lean_inc(v_messageHead_422_);
lean_inc(v_knownSize_421_);
lean_inc_ref(v_outputData_419_);
lean_inc_ref(v_userData_418_);
lean_dec_ref(v_writer_417_);
goto v___jp_433_;
}
case 3:
{
if (v_userClosedBody_424_ == 0)
{
lean_inc_ref(v_state_420_);
lean_inc(v_userDataBytes_426_);
lean_inc(v_messageHead_422_);
lean_inc(v_knownSize_421_);
lean_inc_ref(v_outputData_419_);
lean_inc_ref(v_userData_418_);
lean_dec_ref(v_writer_417_);
goto v___jp_433_;
}
else
{
lean_dec_ref(v_data_416_);
return v_writer_417_;
}
}
case 4:
{
goto v___jp_441_;
}
case 5:
{
goto v___jp_441_;
}
default: 
{
lean_dec_ref(v_data_416_);
return v_writer_417_;
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = l_Array_append___redArg(v_userData_418_, v_data_416_);
lean_dec_ref(v_data_416_);
v___x_430_ = lean_nat_add(v_userDataBytes_426_, v___y_428_);
lean_dec(v___y_428_);
lean_dec(v_userDataBytes_426_);
v___x_431_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v_outputData_419_);
lean_ctor_set(v___x_431_, 2, v_state_420_);
lean_ctor_set(v___x_431_, 3, v_knownSize_421_);
lean_ctor_set(v___x_431_, 4, v_messageHead_422_);
lean_ctor_set(v___x_431_, 5, v___x_430_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*6, v_sentMessage_423_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*6 + 1, v_userClosedBody_424_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*6 + 2, v_omitBody_425_);
return v___x_431_;
}
v___jp_433_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_array_get_size(v_data_416_);
v___x_436_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_437_ = lean_nat_dec_lt(v___x_434_, v___x_435_);
if (v___x_437_ == 0)
{
v___y_428_ = v___x_434_;
goto v___jp_427_;
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_435_);
lean_inc_ref(v_data_416_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_436_, v___f_432_, v_data_416_, v___x_438_, v___x_439_, v___x_434_);
v___y_428_ = v___x_440_;
goto v___jp_427_;
}
}
v___jp_441_:
{
if (v_userClosedBody_424_ == 0)
{
lean_inc(v_userDataBytes_426_);
lean_inc(v_messageHead_422_);
lean_inc(v_knownSize_421_);
lean_inc(v_state_420_);
lean_inc_ref(v_outputData_419_);
lean_inc_ref(v_userData_418_);
lean_dec_ref(v_writer_417_);
goto v___jp_433_;
}
else
{
lean_dec_ref(v_data_416_);
return v_writer_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_442_, lean_object* v_data_443_, lean_object* v_writer_444_){
_start:
{
lean_object* v_userData_445_; lean_object* v_outputData_446_; lean_object* v_state_447_; lean_object* v_knownSize_448_; lean_object* v_messageHead_449_; uint8_t v_sentMessage_450_; uint8_t v_userClosedBody_451_; uint8_t v_omitBody_452_; lean_object* v_userDataBytes_453_; lean_object* v___y_455_; lean_object* v___f_459_; 
v_userData_445_ = lean_ctor_get(v_writer_444_, 0);
v_outputData_446_ = lean_ctor_get(v_writer_444_, 1);
v_state_447_ = lean_ctor_get(v_writer_444_, 2);
v_knownSize_448_ = lean_ctor_get(v_writer_444_, 3);
v_messageHead_449_ = lean_ctor_get(v_writer_444_, 4);
v_sentMessage_450_ = lean_ctor_get_uint8(v_writer_444_, sizeof(void*)*6);
v_userClosedBody_451_ = lean_ctor_get_uint8(v_writer_444_, sizeof(void*)*6 + 1);
v_omitBody_452_ = lean_ctor_get_uint8(v_writer_444_, sizeof(void*)*6 + 2);
v_userDataBytes_453_ = lean_ctor_get(v_writer_444_, 5);
v___f_459_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_447_))
{
case 1:
{
lean_inc(v_state_447_);
lean_inc(v_userDataBytes_453_);
lean_inc(v_messageHead_449_);
lean_inc(v_knownSize_448_);
lean_inc_ref(v_outputData_446_);
lean_inc_ref(v_userData_445_);
lean_dec_ref(v_writer_444_);
goto v___jp_460_;
}
case 2:
{
lean_inc(v_state_447_);
lean_inc(v_userDataBytes_453_);
lean_inc(v_messageHead_449_);
lean_inc(v_knownSize_448_);
lean_inc_ref(v_outputData_446_);
lean_inc_ref(v_userData_445_);
lean_dec_ref(v_writer_444_);
goto v___jp_460_;
}
case 3:
{
if (v_userClosedBody_451_ == 0)
{
lean_inc_ref(v_state_447_);
lean_inc(v_userDataBytes_453_);
lean_inc(v_messageHead_449_);
lean_inc(v_knownSize_448_);
lean_inc_ref(v_outputData_446_);
lean_inc_ref(v_userData_445_);
lean_dec_ref(v_writer_444_);
goto v___jp_460_;
}
else
{
lean_dec_ref(v_data_443_);
return v_writer_444_;
}
}
case 4:
{
goto v___jp_468_;
}
case 5:
{
goto v___jp_468_;
}
default: 
{
lean_dec_ref(v_data_443_);
return v_writer_444_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = l_Array_append___redArg(v_userData_445_, v_data_443_);
lean_dec_ref(v_data_443_);
v___x_457_ = lean_nat_add(v_userDataBytes_453_, v___y_455_);
lean_dec(v___y_455_);
lean_dec(v_userDataBytes_453_);
v___x_458_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v_outputData_446_);
lean_ctor_set(v___x_458_, 2, v_state_447_);
lean_ctor_set(v___x_458_, 3, v_knownSize_448_);
lean_ctor_set(v___x_458_, 4, v_messageHead_449_);
lean_ctor_set(v___x_458_, 5, v___x_457_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*6, v_sentMessage_450_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*6 + 1, v_userClosedBody_451_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*6 + 2, v_omitBody_452_);
return v___x_458_;
}
v___jp_460_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_array_get_size(v_data_443_);
v___x_463_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_464_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
if (v___x_464_ == 0)
{
v___y_455_ = v___x_461_;
goto v___jp_454_;
}
else
{
size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((size_t)0ULL);
v___x_466_ = lean_usize_of_nat(v___x_462_);
lean_inc_ref(v_data_443_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_463_, v___f_459_, v_data_443_, v___x_465_, v___x_466_, v___x_461_);
v___y_455_ = v___x_467_;
goto v___jp_454_;
}
}
v___jp_468_:
{
if (v_userClosedBody_451_ == 0)
{
lean_inc(v_userDataBytes_453_);
lean_inc(v_messageHead_449_);
lean_inc(v_knownSize_448_);
lean_inc(v_state_447_);
lean_inc_ref(v_outputData_446_);
lean_inc_ref(v_userData_445_);
lean_dec_ref(v_writer_444_);
goto v___jp_460_;
}
else
{
lean_dec_ref(v_data_443_);
return v_writer_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object* v_dir_469_, lean_object* v_data_470_, lean_object* v_writer_471_){
_start:
{
uint8_t v_dir_boxed_472_; lean_object* v_res_473_; 
v_dir_boxed_472_ = lean_unbox(v_dir_469_);
v_res_473_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_472_, v_data_470_, v_writer_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object* v_limitSize_474_, lean_object* v_as_475_, size_t v_i_476_, size_t v_stop_477_, lean_object* v_b_478_){
_start:
{
lean_object* v___y_480_; uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_eq(v_i_476_, v_stop_477_);
if (v___x_484_ == 0)
{
lean_object* v_snd_485_; lean_object* v_fst_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_542_; 
v_snd_485_ = lean_ctor_get(v_b_478_, 1);
v_fst_486_ = lean_ctor_get(v_b_478_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_b_478_);
if (v_isSharedCheck_542_ == 0)
{
v___x_488_ = v_b_478_;
v_isShared_489_ = v_isSharedCheck_542_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_485_);
lean_inc(v_fst_486_);
lean_dec(v_b_478_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_542_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_fst_490_; lean_object* v_snd_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_541_; 
v_fst_490_ = lean_ctor_get(v_snd_485_, 0);
v_snd_491_ = lean_ctor_get(v_snd_485_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_snd_485_);
if (v_isSharedCheck_541_ == 0)
{
v___x_493_ = v_snd_485_;
v_isShared_494_ = v_isSharedCheck_541_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_snd_491_);
lean_inc(v_fst_490_);
lean_dec(v_snd_485_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_541_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_array_uget(v_as_475_, v_i_476_);
v___x_496_ = lean_nat_dec_le(v_limitSize_474_, v_snd_491_);
if (v___x_496_ == 0)
{
lean_object* v_data_497_; lean_object* v_extensions_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_533_; 
v_data_497_ = lean_ctor_get(v___x_495_, 0);
v_extensions_498_ = lean_ctor_get(v___x_495_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_533_ == 0)
{
v___x_500_ = v___x_495_;
v_isShared_501_ = v_isSharedCheck_533_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_extensions_498_);
lean_inc(v_data_497_);
lean_dec(v___x_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_533_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v_remaining_503_; lean_object* v___x_504_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_528_; uint8_t v___x_532_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v_remaining_503_ = lean_nat_sub(v_limitSize_474_, v_snd_491_);
v___x_504_ = lean_byte_array_size(v_data_497_);
v___x_532_ = lean_nat_dec_le(v___x_504_, v_remaining_503_);
if (v___x_532_ == 0)
{
v___y_528_ = v_remaining_503_;
goto v___jp_527_;
}
else
{
lean_dec(v_remaining_503_);
v___y_528_ = v___x_504_;
goto v___jp_527_;
}
v___jp_505_:
{
lean_object* v_size_508_; uint8_t v___x_509_; 
v_size_508_ = lean_nat_add(v_snd_491_, v___y_506_);
lean_dec(v_snd_491_);
v___x_509_ = lean_nat_dec_lt(v___y_506_, v___x_504_);
if (v___x_509_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v___y_506_);
lean_del_object(v___x_500_);
lean_dec_ref(v_extensions_498_);
lean_dec_ref(v_data_497_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v_size_508_);
v___x_511_ = v___x_493_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_490_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_size_508_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_511_);
lean_ctor_set(v___x_488_, 0, v___y_507_);
v___x_513_ = v___x_488_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___y_507_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v___y_480_ = v___x_513_;
goto v___jp_479_;
}
}
}
else
{
lean_object* v___x_516_; lean_object* v_pendingChunk_518_; 
v___x_516_ = l_ByteArray_extract(v_data_497_, v___y_506_, v___x_504_);
lean_dec_ref(v_data_497_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_516_);
v_pendingChunk_518_ = v___x_500_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_extensions_498_);
v_pendingChunk_518_ = v_reuseFailAlloc_526_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_array_push(v_fst_490_, v_pendingChunk_518_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v_size_508_);
lean_ctor_set(v___x_493_, 0, v___x_519_);
v___x_521_ = v___x_493_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_size_508_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_521_);
lean_ctor_set(v___x_488_, 0, v___y_507_);
v___x_523_ = v___x_488_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___y_507_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
v___y_480_ = v___x_523_;
goto v___jp_479_;
}
}
}
}
}
v___jp_527_:
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_eq(v___y_528_, v___x_502_);
if (v___x_529_ == 0)
{
lean_object* v_dataPart_530_; lean_object* v___x_531_; 
v_dataPart_530_ = l_ByteArray_extract(v_data_497_, v___x_502_, v___y_528_);
v___x_531_ = lean_array_push(v_fst_486_, v_dataPart_530_);
v___y_506_ = v___y_528_;
v___y_507_ = v___x_531_;
goto v___jp_505_;
}
else
{
v___y_506_ = v___y_528_;
v___y_507_ = v_fst_486_;
goto v___jp_505_;
}
}
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_array_push(v_fst_490_, v___x_495_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_534_);
v___x_536_ = v___x_493_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_snd_491_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_536_);
v___x_538_ = v___x_488_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fst_486_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v___y_480_ = v___x_538_;
goto v___jp_479_;
}
}
}
}
}
}
else
{
return v_b_478_;
}
v___jp_479_:
{
size_t v___x_481_; size_t v___x_482_; 
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_i_476_, v___x_481_);
v_i_476_ = v___x_482_;
v_b_478_ = v___y_480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_543_, lean_object* v_as_544_, lean_object* v_i_545_, lean_object* v_stop_546_, lean_object* v_b_547_){
_start:
{
size_t v_i_boxed_548_; size_t v_stop_boxed_549_; lean_object* v_res_550_; 
v_i_boxed_548_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_stop_boxed_549_ = lean_unbox_usize(v_stop_546_);
lean_dec(v_stop_546_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_543_, v_as_544_, v_i_boxed_548_, v_stop_boxed_549_, v_b_547_);
lean_dec_ref(v_as_544_);
lean_dec(v_limitSize_543_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_551_, size_t v_i_552_, size_t v_stop_553_, lean_object* v_b_554_){
_start:
{
lean_object* v___y_556_; uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_eq(v_i_552_, v_stop_553_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_uget_borrowed(v_as_551_, v_i_552_);
v___x_562_ = l_ByteArray_isEmpty(v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v_data_563_; lean_object* v_size_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_574_; 
v_data_563_ = lean_ctor_get(v_b_554_, 0);
v_size_564_ = lean_ctor_get(v_b_554_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_b_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_566_ = v_b_554_;
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_size_564_);
lean_inc(v_data_563_);
lean_dec(v_b_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_inc(v___x_561_);
v___x_568_ = lean_array_push(v_data_563_, v___x_561_);
v___x_569_ = lean_byte_array_size(v___x_561_);
v___x_570_ = lean_nat_add(v_size_564_, v___x_569_);
lean_dec(v_size_564_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_570_);
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_572_ = v___x_566_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_556_ = v___x_572_;
goto v___jp_555_;
}
}
}
else
{
v___y_556_ = v_b_554_;
goto v___jp_555_;
}
}
else
{
return v_b_554_;
}
v___jp_555_:
{
size_t v___x_557_; size_t v___x_558_; 
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_552_, v___x_557_);
v_i_552_ = v___x_558_;
v_b_554_ = v___y_556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_575_, lean_object* v_i_576_, lean_object* v_stop_577_, lean_object* v_b_578_){
_start:
{
size_t v_i_boxed_579_; size_t v_stop_boxed_580_; lean_object* v_res_581_; 
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_stop_boxed_580_ = lean_unbox_usize(v_stop_577_);
lean_dec(v_stop_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_575_, v_i_boxed_579_, v_stop_boxed_580_, v_b_578_);
lean_dec_ref(v_as_575_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(lean_object* v_as_582_, size_t v_i_583_, size_t v_stop_584_, lean_object* v_b_585_){
_start:
{
lean_object* v___y_587_; uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_eq(v_i_583_, v_stop_584_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v_data_593_; uint8_t v___x_594_; 
v___x_592_ = lean_array_uget_borrowed(v_as_582_, v_i_583_);
v_data_593_ = lean_ctor_get(v___x_592_, 0);
v___x_594_ = l_ByteArray_isEmpty(v_data_593_);
if (v___x_594_ == 0)
{
lean_object* v_data_595_; lean_object* v_size_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v_data_595_ = lean_ctor_get(v_b_585_, 0);
v_size_596_ = lean_ctor_get(v_b_585_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_b_585_);
if (v_isSharedCheck_606_ == 0)
{
v___x_598_ = v_b_585_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_size_596_);
lean_inc(v_data_595_);
lean_dec(v_b_585_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_inc_ref(v_data_593_);
v___x_600_ = lean_array_push(v_data_595_, v_data_593_);
v___x_601_ = lean_byte_array_size(v_data_593_);
v___x_602_ = lean_nat_add(v_size_596_, v___x_601_);
lean_dec(v_size_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_602_);
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_604_ = v___x_598_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
v___y_587_ = v___x_604_;
goto v___jp_586_;
}
}
}
else
{
v___y_587_ = v_b_585_;
goto v___jp_586_;
}
}
else
{
return v_b_585_;
}
v___jp_586_:
{
size_t v___x_588_; size_t v___x_589_; 
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_583_, v___x_588_);
v_i_583_ = v___x_589_;
v_b_585_ = v___y_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2___boxed(lean_object* v_as_607_, lean_object* v_i_608_, lean_object* v_stop_609_, lean_object* v_b_610_){
_start:
{
size_t v_i_boxed_611_; size_t v_stop_boxed_612_; lean_object* v_res_613_; 
v_i_boxed_611_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_stop_boxed_612_ = lean_unbox_usize(v_stop_609_);
lean_dec(v_stop_609_);
v_res_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(v_as_607_, v_i_boxed_611_, v_stop_boxed_612_, v_b_610_);
lean_dec_ref(v_as_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_624_, lean_object* v_limitSize_625_){
_start:
{
lean_object* v_userData_626_; lean_object* v_outputData_627_; lean_object* v_state_628_; lean_object* v_knownSize_629_; lean_object* v_messageHead_630_; uint8_t v_sentMessage_631_; uint8_t v_userClosedBody_632_; uint8_t v_omitBody_633_; lean_object* v_userDataBytes_634_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___y_646_; lean_object* v_fst_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; uint8_t v___x_660_; 
v_userData_626_ = lean_ctor_get(v_writer_624_, 0);
v_outputData_627_ = lean_ctor_get(v_writer_624_, 1);
v_state_628_ = lean_ctor_get(v_writer_624_, 2);
v_knownSize_629_ = lean_ctor_get(v_writer_624_, 3);
v_messageHead_630_ = lean_ctor_get(v_writer_624_, 4);
v_sentMessage_631_ = lean_ctor_get_uint8(v_writer_624_, sizeof(void*)*6);
v_userClosedBody_632_ = lean_ctor_get_uint8(v_writer_624_, sizeof(void*)*6 + 1);
v_omitBody_633_ = lean_ctor_get_uint8(v_writer_624_, sizeof(void*)*6 + 2);
v_userDataBytes_634_ = lean_ctor_get(v_writer_624_, 5);
v___x_643_ = lean_array_get_size(v_userData_626_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_nat_dec_eq(v___x_643_, v___x_644_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; 
lean_inc(v_userDataBytes_634_);
lean_inc(v_messageHead_630_);
lean_inc(v_knownSize_629_);
lean_inc(v_state_628_);
lean_inc_ref(v_outputData_627_);
lean_inc_ref(v_userData_626_);
lean_dec_ref(v_writer_624_);
v___x_661_ = lean_nat_dec_le(v_userDataBytes_634_, v_limitSize_625_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1));
v___x_663_ = lean_nat_dec_lt(v___x_644_, v___x_643_);
if (v___x_663_ == 0)
{
lean_dec_ref(v_userData_626_);
v_fst_652_ = v___x_662_;
v_fst_653_ = v___x_662_;
v_snd_654_ = v___x_644_;
goto v___jp_651_;
}
else
{
lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; lean_object* v_snd_668_; lean_object* v_fst_669_; lean_object* v_fst_670_; lean_object* v_snd_671_; 
v___x_664_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__3));
v___x_665_ = ((size_t)0ULL);
v___x_666_ = lean_usize_of_nat(v___x_643_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_625_, v_userData_626_, v___x_665_, v___x_666_, v___x_664_);
lean_dec_ref(v_userData_626_);
v_snd_668_ = lean_ctor_get(v___x_667_, 1);
lean_inc(v_snd_668_);
v_fst_669_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_fst_669_);
lean_dec_ref(v___x_667_);
v_fst_670_ = lean_ctor_get(v_snd_668_, 0);
lean_inc(v_fst_670_);
v_snd_671_ = lean_ctor_get(v_snd_668_, 1);
lean_inc(v_snd_671_);
lean_dec(v_snd_668_);
v_fst_652_ = v_fst_669_;
v_fst_653_ = v_fst_670_;
v_snd_654_ = v_snd_671_;
goto v___jp_651_;
}
}
else
{
uint8_t v___x_672_; 
v___x_672_ = lean_nat_dec_lt(v___x_644_, v___x_643_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_userData_626_);
v___y_646_ = v_outputData_627_;
goto v___jp_645_;
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_643_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(v_userData_626_, v___x_673_, v___x_674_, v_outputData_627_);
lean_dec_ref(v_userData_626_);
v___y_646_ = v___x_675_;
goto v___jp_645_;
}
}
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_writer_624_);
lean_ctor_set(v___x_676_, 1, v_limitSize_625_);
return v___x_676_;
}
v___jp_635_:
{
lean_object* v_remaining_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_remaining_639_ = lean_nat_sub(v_limitSize_625_, v___y_636_);
lean_dec(v_limitSize_625_);
v___x_640_ = lean_nat_sub(v_userDataBytes_634_, v___y_636_);
lean_dec(v___y_636_);
lean_dec(v_userDataBytes_634_);
v___x_641_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_641_, 0, v___y_637_);
lean_ctor_set(v___x_641_, 1, v___y_638_);
lean_ctor_set(v___x_641_, 2, v_state_628_);
lean_ctor_set(v___x_641_, 3, v_knownSize_629_);
lean_ctor_set(v___x_641_, 4, v_messageHead_630_);
lean_ctor_set(v___x_641_, 5, v___x_640_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*6, v_sentMessage_631_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*6 + 1, v_userClosedBody_632_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*6 + 2, v_omitBody_633_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v_remaining_639_);
return v___x_642_;
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_648_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___y_646_);
lean_ctor_set(v___x_648_, 2, v_state_628_);
lean_ctor_set(v___x_648_, 3, v_knownSize_629_);
lean_ctor_set(v___x_648_, 4, v_messageHead_630_);
lean_ctor_set(v___x_648_, 5, v___x_644_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*6, v_sentMessage_631_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*6 + 1, v_userClosedBody_632_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*6 + 2, v_omitBody_633_);
v___x_649_ = lean_nat_sub(v_limitSize_625_, v_userDataBytes_634_);
lean_dec(v_userDataBytes_634_);
lean_dec(v_limitSize_625_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
return v___x_650_;
}
v___jp_651_:
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_array_get_size(v_fst_652_);
v___x_656_ = lean_nat_dec_lt(v___x_644_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec_ref(v_fst_652_);
v___y_636_ = v_snd_654_;
v___y_637_ = v_fst_653_;
v___y_638_ = v_outputData_627_;
goto v___jp_635_;
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_655_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_652_, v___x_657_, v___x_658_, v_outputData_627_);
lean_dec_ref(v_fst_652_);
v___y_636_ = v_snd_654_;
v___y_637_ = v_fst_653_;
v___y_638_ = v___x_659_;
goto v___jp_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_677_, lean_object* v_writer_678_, lean_object* v_limitSize_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_678_, v_limitSize_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_681_, lean_object* v_writer_682_, lean_object* v_limitSize_683_){
_start:
{
uint8_t v_dir_boxed_684_; lean_object* v_res_685_; 
v_dir_boxed_684_ = lean_unbox(v_dir_681_);
v_res_685_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_684_, v_writer_682_, v_limitSize_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(lean_object* v_as_686_, size_t v_i_687_, size_t v_stop_688_, lean_object* v_b_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = lean_usize_dec_eq(v_i_687_, v_stop_688_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; size_t v___x_693_; size_t v___x_694_; 
v___x_691_ = lean_array_uget_borrowed(v_as_686_, v_i_687_);
lean_inc(v___x_691_);
v___x_692_ = l_Std_Http_Internal_ChunkedBuffer_pushChunk(v_b_689_, v___x_691_);
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_add(v_i_687_, v___x_693_);
v_i_687_ = v___x_694_;
v_b_689_ = v___x_692_;
goto _start;
}
else
{
return v_b_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_as_696_, lean_object* v_i_697_, lean_object* v_stop_698_, lean_object* v_b_699_){
_start:
{
size_t v_i_boxed_700_; size_t v_stop_boxed_701_; lean_object* v_res_702_; 
v_i_boxed_700_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_stop_boxed_701_ = lean_unbox_usize(v_stop_698_);
lean_dec(v_stop_698_);
v_res_702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_as_696_, v_i_boxed_700_, v_stop_boxed_701_, v_b_699_);
lean_dec_ref(v_as_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_703_, size_t v_i_704_, size_t v_stop_705_, lean_object* v_b_706_){
_start:
{
lean_object* v___y_708_; uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_eq(v_i_704_, v_stop_705_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v_data_714_; uint8_t v___x_715_; 
v___x_713_ = lean_array_uget_borrowed(v_as_703_, v_i_704_);
v_data_714_ = lean_ctor_get(v___x_713_, 0);
v___x_715_ = l_ByteArray_isEmpty(v_data_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_inc(v___x_713_);
v___x_716_ = lean_array_push(v_b_706_, v___x_713_);
v___y_708_ = v___x_716_;
goto v___jp_707_;
}
else
{
v___y_708_ = v_b_706_;
goto v___jp_707_;
}
}
else
{
return v_b_706_;
}
v___jp_707_:
{
size_t v___x_709_; size_t v___x_710_; 
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_add(v_i_704_, v___x_709_);
v_i_704_ = v___x_710_;
v_b_706_ = v___y_708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_717_, lean_object* v_i_718_, lean_object* v_stop_719_, lean_object* v_b_720_){
_start:
{
size_t v_i_boxed_721_; size_t v_stop_boxed_722_; lean_object* v_res_723_; 
v_i_boxed_721_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_stop_boxed_722_ = lean_unbox_usize(v_stop_719_);
lean_dec(v_stop_719_);
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_717_, v_i_boxed_721_, v_stop_boxed_722_, v_b_720_);
lean_dec_ref(v_as_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_724_){
_start:
{
lean_object* v_userData_725_; lean_object* v_outputData_726_; lean_object* v_state_727_; lean_object* v_knownSize_728_; lean_object* v_messageHead_729_; uint8_t v_sentMessage_730_; uint8_t v_userClosedBody_731_; uint8_t v_omitBody_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___y_736_; uint8_t v___x_745_; 
v_userData_725_ = lean_ctor_get(v_writer_724_, 0);
v_outputData_726_ = lean_ctor_get(v_writer_724_, 1);
v_state_727_ = lean_ctor_get(v_writer_724_, 2);
v_knownSize_728_ = lean_ctor_get(v_writer_724_, 3);
v_messageHead_729_ = lean_ctor_get(v_writer_724_, 4);
v_sentMessage_730_ = lean_ctor_get_uint8(v_writer_724_, sizeof(void*)*6);
v_userClosedBody_731_ = lean_ctor_get_uint8(v_writer_724_, sizeof(void*)*6 + 1);
v_omitBody_732_ = lean_ctor_get_uint8(v_writer_724_, sizeof(void*)*6 + 2);
v___x_733_ = lean_array_get_size(v_userData_725_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; 
lean_inc(v_messageHead_729_);
lean_inc(v_knownSize_728_);
lean_inc(v_state_727_);
lean_inc_ref(v_outputData_726_);
lean_inc_ref(v_userData_725_);
lean_dec_ref(v_writer_724_);
v___x_746_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_747_ = lean_nat_dec_lt(v___x_734_, v___x_733_);
if (v___x_747_ == 0)
{
lean_dec_ref(v_userData_725_);
v___y_736_ = v___x_746_;
goto v___jp_735_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_733_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_userData_725_, v___x_748_, v___x_749_, v___x_746_);
lean_dec_ref(v_userData_725_);
v___y_736_ = v___x_750_;
goto v___jp_735_;
}
}
else
{
return v_writer_724_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_738_ = lean_array_get_size(v___y_736_);
v___x_739_ = lean_nat_dec_lt(v___x_734_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___y_736_);
v___x_740_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v_outputData_726_);
lean_ctor_set(v___x_740_, 2, v_state_727_);
lean_ctor_set(v___x_740_, 3, v_knownSize_728_);
lean_ctor_set(v___x_740_, 4, v_messageHead_729_);
lean_ctor_set(v___x_740_, 5, v___x_734_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*6, v_sentMessage_730_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*6 + 1, v_userClosedBody_731_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*6 + 2, v_omitBody_732_);
return v___x_740_;
}
else
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_738_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v___y_736_, v___x_741_, v___x_742_, v_outputData_726_);
lean_dec_ref(v___y_736_);
v___x_744_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_744_, 0, v___x_737_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
lean_ctor_set(v___x_744_, 2, v_state_727_);
lean_ctor_set(v___x_744_, 3, v_knownSize_728_);
lean_ctor_set(v___x_744_, 4, v_messageHead_729_);
lean_ctor_set(v___x_744_, 5, v___x_734_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*6, v_sentMessage_730_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*6 + 1, v_userClosedBody_731_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*6 + 2, v_omitBody_732_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_751_, lean_object* v_writer_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_754_, lean_object* v_writer_755_){
_start:
{
uint8_t v_dir_boxed_756_; lean_object* v_res_757_; 
v_dir_boxed_756_ = lean_unbox(v_dir_754_);
v_res_757_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_756_, v_writer_755_);
return v_res_757_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_760_ = lean_string_to_utf8(v___x_759_);
return v___x_760_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_762_ = l_ByteArray_isEmpty(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_764_ = lean_byte_array_size(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_765_){
_start:
{
lean_object* v_writer_766_; lean_object* v_userData_767_; lean_object* v_outputData_768_; lean_object* v_knownSize_769_; lean_object* v_messageHead_770_; uint8_t v_sentMessage_771_; uint8_t v_userClosedBody_772_; uint8_t v_omitBody_773_; lean_object* v_userDataBytes_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_798_; 
v_writer_766_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_765_);
v_userData_767_ = lean_ctor_get(v_writer_766_, 0);
v_outputData_768_ = lean_ctor_get(v_writer_766_, 1);
v_knownSize_769_ = lean_ctor_get(v_writer_766_, 3);
v_messageHead_770_ = lean_ctor_get(v_writer_766_, 4);
v_sentMessage_771_ = lean_ctor_get_uint8(v_writer_766_, sizeof(void*)*6);
v_userClosedBody_772_ = lean_ctor_get_uint8(v_writer_766_, sizeof(void*)*6 + 1);
v_omitBody_773_ = lean_ctor_get_uint8(v_writer_766_, sizeof(void*)*6 + 2);
v_userDataBytes_774_ = lean_ctor_get(v_writer_766_, 5);
v_isSharedCheck_798_ = !lean_is_exclusive(v_writer_766_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_writer_766_, 2);
lean_dec(v_unused_799_);
v___x_776_ = v_writer_766_;
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_userDataBytes_774_);
lean_inc(v_messageHead_770_);
lean_inc(v_knownSize_769_);
lean_inc(v_outputData_768_);
lean_inc(v_userData_767_);
lean_dec(v_writer_766_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___y_779_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_785_ = lean_uint8_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
if (v___x_785_ == 0)
{
lean_object* v_data_786_; lean_object* v_size_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_797_; 
v_data_786_ = lean_ctor_get(v_outputData_768_, 0);
v_size_787_ = lean_ctor_get(v_outputData_768_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_outputData_768_);
if (v_isSharedCheck_797_ == 0)
{
v___x_789_ = v_outputData_768_;
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_size_787_);
lean_inc(v_data_786_);
lean_dec(v_outputData_768_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_791_ = lean_array_push(v_data_786_, v___x_784_);
v___x_792_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__3);
v___x_793_ = lean_nat_add(v_size_787_, v___x_792_);
lean_dec(v_size_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_793_);
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_795_ = v___x_789_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_779_ = v___x_795_;
goto v___jp_778_;
}
}
}
else
{
v___y_779_ = v_outputData_768_;
goto v___jp_778_;
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_box(6);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v___x_780_);
lean_ctor_set(v___x_776_, 1, v___y_779_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_userData_767_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___y_779_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_knownSize_769_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_messageHead_770_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v_userDataBytes_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*6, v_sentMessage_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*6 + 1, v_userClosedBody_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*6 + 2, v_omitBody_773_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_800_, lean_object* v_writer_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_803_, lean_object* v_writer_804_){
_start:
{
uint8_t v_dir_boxed_805_; lean_object* v_res_806_; 
v_dir_boxed_805_ = lean_unbox(v_dir_803_);
v_res_806_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_805_, v_writer_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_807_){
_start:
{
lean_object* v_userData_808_; lean_object* v_outputData_809_; lean_object* v_state_810_; lean_object* v_knownSize_811_; lean_object* v_messageHead_812_; uint8_t v_sentMessage_813_; uint8_t v_userClosedBody_814_; uint8_t v_omitBody_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_832_; 
v_userData_808_ = lean_ctor_get(v_writer_807_, 0);
v_outputData_809_ = lean_ctor_get(v_writer_807_, 1);
v_state_810_ = lean_ctor_get(v_writer_807_, 2);
v_knownSize_811_ = lean_ctor_get(v_writer_807_, 3);
v_messageHead_812_ = lean_ctor_get(v_writer_807_, 4);
v_sentMessage_813_ = lean_ctor_get_uint8(v_writer_807_, sizeof(void*)*6);
v_userClosedBody_814_ = lean_ctor_get_uint8(v_writer_807_, sizeof(void*)*6 + 1);
v_omitBody_815_ = lean_ctor_get_uint8(v_writer_807_, sizeof(void*)*6 + 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_writer_807_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_writer_807_, 5);
lean_dec(v_unused_833_);
v___x_817_ = v_writer_807_;
v_isShared_818_ = v_isSharedCheck_832_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_messageHead_812_);
lean_inc(v_knownSize_811_);
lean_inc(v_state_810_);
lean_inc(v_outputData_809_);
lean_inc(v_userData_808_);
lean_dec(v_writer_807_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_832_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_821_ = lean_array_get_size(v_userData_808_);
v___x_822_ = lean_nat_dec_lt(v___x_819_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v_userData_808_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 5, v___x_819_);
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_824_ = v___x_817_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_outputData_809_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_state_810_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_knownSize_811_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_messageHead_812_);
lean_ctor_set(v_reuseFailAlloc_825_, 5, v___x_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_825_, sizeof(void*)*6, v_sentMessage_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_825_, sizeof(void*)*6 + 1, v_userClosedBody_814_);
lean_ctor_set_uint8(v_reuseFailAlloc_825_, sizeof(void*)*6 + 2, v_omitBody_815_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_826_ = ((size_t)0ULL);
v___x_827_ = lean_usize_of_nat(v___x_821_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__2(v_userData_808_, v___x_826_, v___x_827_, v_outputData_809_);
lean_dec_ref(v_userData_808_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 5, v___x_819_);
lean_ctor_set(v___x_817_, 1, v___x_828_);
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_830_ = v___x_817_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_state_810_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_knownSize_811_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_messageHead_812_);
lean_ctor_set(v_reuseFailAlloc_831_, 5, v___x_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*6, v_sentMessage_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*6 + 1, v_userClosedBody_814_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*6 + 2, v_omitBody_815_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_834_, lean_object* v_writer_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_837_, lean_object* v_writer_838_){
_start:
{
uint8_t v_dir_boxed_839_; lean_object* v_res_840_; 
v_dir_boxed_839_ = lean_unbox(v_dir_837_);
v_res_840_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_839_, v_writer_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_841_, lean_object* v_writer_842_){
_start:
{
lean_object* v_userData_843_; lean_object* v_outputData_844_; lean_object* v_knownSize_845_; lean_object* v_messageHead_846_; uint8_t v_sentMessage_847_; uint8_t v_userClosedBody_848_; uint8_t v_omitBody_849_; lean_object* v_userDataBytes_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_userData_843_ = lean_ctor_get(v_writer_842_, 0);
v_outputData_844_ = lean_ctor_get(v_writer_842_, 1);
v_knownSize_845_ = lean_ctor_get(v_writer_842_, 3);
v_messageHead_846_ = lean_ctor_get(v_writer_842_, 4);
v_sentMessage_847_ = lean_ctor_get_uint8(v_writer_842_, sizeof(void*)*6);
v_userClosedBody_848_ = lean_ctor_get_uint8(v_writer_842_, sizeof(void*)*6 + 1);
v_omitBody_849_ = lean_ctor_get_uint8(v_writer_842_, sizeof(void*)*6 + 2);
v_userDataBytes_850_ = lean_ctor_get(v_writer_842_, 5);
v_isSharedCheck_857_ = !lean_is_exclusive(v_writer_842_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v_writer_842_, 2);
lean_dec(v_unused_858_);
v___x_852_ = v_writer_842_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_userDataBytes_850_);
lean_inc(v_messageHead_846_);
lean_inc(v_knownSize_845_);
lean_inc(v_outputData_844_);
lean_inc(v_userData_843_);
lean_dec(v_writer_842_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 2, v_state_841_);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_userData_843_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_outputData_844_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_state_841_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_knownSize_845_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v_messageHead_846_);
lean_ctor_set(v_reuseFailAlloc_856_, 5, v_userDataBytes_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_856_, sizeof(void*)*6, v_sentMessage_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_856_, sizeof(void*)*6 + 1, v_userClosedBody_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_856_, sizeof(void*)*6 + 2, v_omitBody_849_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_859_, lean_object* v_state_860_, lean_object* v_writer_861_){
_start:
{
lean_object* v_userData_862_; lean_object* v_outputData_863_; lean_object* v_knownSize_864_; lean_object* v_messageHead_865_; uint8_t v_sentMessage_866_; uint8_t v_userClosedBody_867_; uint8_t v_omitBody_868_; lean_object* v_userDataBytes_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_userData_862_ = lean_ctor_get(v_writer_861_, 0);
v_outputData_863_ = lean_ctor_get(v_writer_861_, 1);
v_knownSize_864_ = lean_ctor_get(v_writer_861_, 3);
v_messageHead_865_ = lean_ctor_get(v_writer_861_, 4);
v_sentMessage_866_ = lean_ctor_get_uint8(v_writer_861_, sizeof(void*)*6);
v_userClosedBody_867_ = lean_ctor_get_uint8(v_writer_861_, sizeof(void*)*6 + 1);
v_omitBody_868_ = lean_ctor_get_uint8(v_writer_861_, sizeof(void*)*6 + 2);
v_userDataBytes_869_ = lean_ctor_get(v_writer_861_, 5);
v_isSharedCheck_876_ = !lean_is_exclusive(v_writer_861_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; 
v_unused_877_ = lean_ctor_get(v_writer_861_, 2);
lean_dec(v_unused_877_);
v___x_871_ = v_writer_861_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_userDataBytes_869_);
lean_inc(v_messageHead_865_);
lean_inc(v_knownSize_864_);
lean_inc(v_outputData_863_);
lean_inc(v_userData_862_);
lean_dec(v_writer_861_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 2, v_state_860_);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_userData_862_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_outputData_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_state_860_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_knownSize_864_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_messageHead_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_userDataBytes_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6, v_sentMessage_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6 + 1, v_userClosedBody_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6 + 2, v_omitBody_868_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_878_, lean_object* v_state_879_, lean_object* v_writer_880_){
_start:
{
uint8_t v_dir_boxed_881_; lean_object* v_res_882_; 
v_dir_boxed_881_ = lean_unbox(v_dir_878_);
v_res_882_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_881_, v_state_879_, v_writer_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_map_883_, lean_object* v_key_884_, lean_object* v_i_885_){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = lean_array_get_size(v_map_883_);
v___x_887_ = lean_nat_dec_lt(v_i_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_dec(v_i_885_);
return v___x_886_;
}
else
{
lean_object* v___x_888_; lean_object* v_fst_889_; uint8_t v___x_890_; 
v___x_888_ = lean_array_fget_borrowed(v_map_883_, v_i_885_);
v_fst_889_ = lean_ctor_get(v___x_888_, 0);
v___x_890_ = lean_string_dec_eq(v_fst_889_, v_key_884_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_add(v_i_885_, v___x_891_);
lean_dec(v_i_885_);
v_i_885_ = v___x_892_;
goto _start;
}
else
{
return v_i_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_map_894_, lean_object* v_key_895_, lean_object* v_i_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_map_894_, v_key_895_, v_i_896_);
lean_dec_ref(v_key_895_);
lean_dec_ref(v_map_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_s_898_, lean_object* v_p_899_){
_start:
{
lean_object* v___y_901_; lean_object* v___y_902_; uint32_t v___y_906_; lean_object* v___x_918_; uint8_t v_decide_919_; 
v___x_918_ = lean_string_utf8_byte_size(v_s_898_);
v_decide_919_ = lean_nat_dec_eq(v_p_899_, v___x_918_);
if (v_decide_919_ == 0)
{
uint32_t v___x_920_; uint32_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_string_utf8_get_fast(v_s_898_, v_p_899_);
v___x_921_ = 65;
v___x_922_ = lean_uint32_dec_le(v___x_921_, v___x_920_);
if (v___x_922_ == 0)
{
v___y_906_ = v___x_920_;
goto v___jp_905_;
}
else
{
uint32_t v___x_923_; uint8_t v___x_924_; 
v___x_923_ = 90;
v___x_924_ = lean_uint32_dec_le(v___x_920_, v___x_923_);
if (v___x_924_ == 0)
{
v___y_906_ = v___x_920_;
goto v___jp_905_;
}
else
{
uint32_t v___x_925_; uint32_t v___x_926_; 
v___x_925_ = 32;
v___x_926_ = lean_uint32_add(v___x_920_, v___x_925_);
v___y_906_ = v___x_926_;
goto v___jp_905_;
}
}
}
else
{
lean_dec(v_p_899_);
return v_s_898_;
}
v___jp_900_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_nat_add(v_p_899_, v___y_902_);
lean_dec(v_p_899_);
v_s_898_ = v___y_901_;
v_p_899_ = v___x_903_;
goto _start;
}
v___jp_905_:
{
lean_object* v___x_907_; uint32_t v___x_908_; uint8_t v___x_909_; 
lean_inc(v_p_899_);
v___x_907_ = lean_string_utf8_set(v_s_898_, v_p_899_, v___y_906_);
v___x_908_ = 127;
v___x_909_ = lean_uint32_dec_le(v___y_906_, v___x_908_);
if (v___x_909_ == 0)
{
uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 2047;
v___x_911_ = lean_uint32_dec_le(v___y_906_, v___x_910_);
if (v___x_911_ == 0)
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 65535;
v___x_913_ = lean_uint32_dec_le(v___y_906_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(4u);
v___y_901_ = v___x_907_;
v___y_902_ = v___x_914_;
goto v___jp_900_;
}
else
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(3u);
v___y_901_ = v___x_907_;
v___y_902_ = v___x_915_;
goto v___jp_900_;
}
}
else
{
lean_object* v___x_916_; 
v___x_916_ = lean_unsigned_to_nat(2u);
v___y_901_ = v___x_907_;
v___y_902_ = v___x_916_;
goto v___jp_900_;
}
}
else
{
lean_object* v___x_917_; 
v___x_917_ = lean_unsigned_to_nat(1u);
v___y_901_ = v___x_907_;
v___y_902_ = v___x_917_;
goto v___jp_900_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_928_, lean_object* v_writer_929_){
_start:
{
uint8_t v___y_931_; 
if (v_dir_928_ == 0)
{
uint8_t v___x_946_; 
v___x_946_ = 1;
v___y_931_ = v___x_946_;
goto v___jp_930_;
}
else
{
uint8_t v___x_947_; 
v___x_947_ = 0;
v___y_931_ = v___x_947_;
goto v___jp_930_;
}
v___jp_930_:
{
lean_object* v_messageHead_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_i_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_messageHead_932_ = lean_ctor_get(v_writer_929_, 4);
v___x_933_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_931_, v_messageHead_932_);
v___x_934_ = l_Std_Http_Header_Name_connection;
v___x_935_ = lean_unsigned_to_nat(0u);
v_i_936_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v___x_933_, v___x_934_, v___x_935_);
v___x_937_ = lean_array_get_size(v___x_933_);
v___x_938_ = lean_nat_dec_lt(v_i_936_, v___x_937_);
if (v___x_938_ == 0)
{
uint8_t v___x_939_; 
lean_dec(v_i_936_);
lean_dec_ref(v___x_933_);
v___x_939_ = 1;
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v_snd_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_940_ = lean_array_fget(v___x_933_, v_i_936_);
lean_dec(v_i_936_);
lean_dec_ref(v___x_933_);
v_snd_941_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_snd_941_);
lean_dec(v___x_940_);
v___x_942_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_snd_941_, v___x_935_);
v___x_943_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_944_ = lean_string_dec_eq(v___x_942_, v___x_943_);
lean_dec_ref(v___x_942_);
if (v___x_944_ == 0)
{
return v___x_938_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = 0;
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_948_, lean_object* v_writer_949_){
_start:
{
uint8_t v_dir_boxed_950_; uint8_t v_res_951_; lean_object* v_r_952_; 
v_dir_boxed_950_ = lean_unbox(v_dir_948_);
v_res_951_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_950_, v_writer_949_);
lean_dec_ref(v_writer_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_953_, lean_object* v_map_954_, lean_object* v_key_955_, lean_object* v_i_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_map_954_, v_key_955_, v_i_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_958_, lean_object* v_map_959_, lean_object* v_key_960_, lean_object* v_i_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_958_, v_map_959_, v_key_960_, v_i_961_);
lean_dec_ref(v_key_960_);
lean_dec_ref(v_map_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_963_){
_start:
{
lean_object* v_userData_964_; lean_object* v_outputData_965_; lean_object* v_knownSize_966_; lean_object* v_messageHead_967_; uint8_t v_sentMessage_968_; uint8_t v_userClosedBody_969_; uint8_t v_omitBody_970_; lean_object* v_userDataBytes_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_userData_964_ = lean_ctor_get(v_writer_963_, 0);
v_outputData_965_ = lean_ctor_get(v_writer_963_, 1);
v_knownSize_966_ = lean_ctor_get(v_writer_963_, 3);
v_messageHead_967_ = lean_ctor_get(v_writer_963_, 4);
v_sentMessage_968_ = lean_ctor_get_uint8(v_writer_963_, sizeof(void*)*6);
v_userClosedBody_969_ = lean_ctor_get_uint8(v_writer_963_, sizeof(void*)*6 + 1);
v_omitBody_970_ = lean_ctor_get_uint8(v_writer_963_, sizeof(void*)*6 + 2);
v_userDataBytes_971_ = lean_ctor_get(v_writer_963_, 5);
v_isSharedCheck_979_ = !lean_is_exclusive(v_writer_963_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_writer_963_, 2);
lean_dec(v_unused_980_);
v___x_973_ = v_writer_963_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_userDataBytes_971_);
lean_inc(v_messageHead_967_);
lean_inc(v_knownSize_966_);
lean_inc(v_outputData_965_);
lean_inc(v_userData_964_);
lean_dec(v_writer_963_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_box(7);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_userData_964_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_outputData_965_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_knownSize_966_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_messageHead_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 5, v_userDataBytes_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*6, v_sentMessage_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*6 + 1, v_userClosedBody_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*6 + 2, v_omitBody_970_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_981_, lean_object* v_writer_982_){
_start:
{
lean_object* v_userData_983_; lean_object* v_outputData_984_; lean_object* v_knownSize_985_; lean_object* v_messageHead_986_; uint8_t v_sentMessage_987_; uint8_t v_userClosedBody_988_; uint8_t v_omitBody_989_; lean_object* v_userDataBytes_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_userData_983_ = lean_ctor_get(v_writer_982_, 0);
v_outputData_984_ = lean_ctor_get(v_writer_982_, 1);
v_knownSize_985_ = lean_ctor_get(v_writer_982_, 3);
v_messageHead_986_ = lean_ctor_get(v_writer_982_, 4);
v_sentMessage_987_ = lean_ctor_get_uint8(v_writer_982_, sizeof(void*)*6);
v_userClosedBody_988_ = lean_ctor_get_uint8(v_writer_982_, sizeof(void*)*6 + 1);
v_omitBody_989_ = lean_ctor_get_uint8(v_writer_982_, sizeof(void*)*6 + 2);
v_userDataBytes_990_ = lean_ctor_get(v_writer_982_, 5);
v_isSharedCheck_998_ = !lean_is_exclusive(v_writer_982_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v_writer_982_, 2);
lean_dec(v_unused_999_);
v___x_992_ = v_writer_982_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_userDataBytes_990_);
lean_inc(v_messageHead_986_);
lean_inc(v_knownSize_985_);
lean_inc(v_outputData_984_);
lean_inc(v_userData_983_);
lean_dec(v_writer_982_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_box(7);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_userData_983_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_outputData_984_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_knownSize_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_messageHead_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v_userDataBytes_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6, v_sentMessage_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6 + 1, v_userClosedBody_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6 + 2, v_omitBody_989_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1000_, lean_object* v_writer_1001_){
_start:
{
uint8_t v_dir_boxed_1002_; lean_object* v_res_1003_; 
v_dir_boxed_1002_ = lean_unbox(v_dir_1000_);
v_res_1003_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1002_, v_writer_1001_);
return v_res_1003_;
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
