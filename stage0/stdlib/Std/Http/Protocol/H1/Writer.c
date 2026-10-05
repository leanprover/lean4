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
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionValue_quote(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
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
static const lean_array_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value),((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "0\r\n\r\n"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
goto v___jp_445_;
}
case 5:
{
goto v___jp_445_;
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
uint8_t v___x_438_; 
v___x_438_ = lean_nat_dec_le(v___x_435_, v___x_435_);
if (v___x_438_ == 0)
{
if (v___x_437_ == 0)
{
v___y_428_ = v___x_434_;
goto v___jp_427_;
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_435_);
lean_inc_ref(v_data_416_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_436_, v___f_432_, v_data_416_, v___x_439_, v___x_440_, v___x_434_);
v___y_428_ = v___x_441_;
goto v___jp_427_;
}
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_435_);
lean_inc_ref(v_data_416_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_436_, v___f_432_, v_data_416_, v___x_442_, v___x_443_, v___x_434_);
v___y_428_ = v___x_444_;
goto v___jp_427_;
}
}
}
v___jp_445_:
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_446_, lean_object* v_data_447_, lean_object* v_writer_448_){
_start:
{
lean_object* v_userData_449_; lean_object* v_outputData_450_; lean_object* v_state_451_; lean_object* v_knownSize_452_; lean_object* v_messageHead_453_; uint8_t v_sentMessage_454_; uint8_t v_userClosedBody_455_; uint8_t v_omitBody_456_; lean_object* v_userDataBytes_457_; lean_object* v___y_459_; lean_object* v___f_463_; 
v_userData_449_ = lean_ctor_get(v_writer_448_, 0);
v_outputData_450_ = lean_ctor_get(v_writer_448_, 1);
v_state_451_ = lean_ctor_get(v_writer_448_, 2);
v_knownSize_452_ = lean_ctor_get(v_writer_448_, 3);
v_messageHead_453_ = lean_ctor_get(v_writer_448_, 4);
v_sentMessage_454_ = lean_ctor_get_uint8(v_writer_448_, sizeof(void*)*6);
v_userClosedBody_455_ = lean_ctor_get_uint8(v_writer_448_, sizeof(void*)*6 + 1);
v_omitBody_456_ = lean_ctor_get_uint8(v_writer_448_, sizeof(void*)*6 + 2);
v_userDataBytes_457_ = lean_ctor_get(v_writer_448_, 5);
v___f_463_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_451_))
{
case 1:
{
lean_inc(v_state_451_);
lean_inc(v_userDataBytes_457_);
lean_inc(v_messageHead_453_);
lean_inc(v_knownSize_452_);
lean_inc_ref(v_outputData_450_);
lean_inc_ref(v_userData_449_);
lean_dec_ref(v_writer_448_);
goto v___jp_464_;
}
case 2:
{
lean_inc(v_state_451_);
lean_inc(v_userDataBytes_457_);
lean_inc(v_messageHead_453_);
lean_inc(v_knownSize_452_);
lean_inc_ref(v_outputData_450_);
lean_inc_ref(v_userData_449_);
lean_dec_ref(v_writer_448_);
goto v___jp_464_;
}
case 3:
{
if (v_userClosedBody_455_ == 0)
{
lean_inc_ref(v_state_451_);
lean_inc(v_userDataBytes_457_);
lean_inc(v_messageHead_453_);
lean_inc(v_knownSize_452_);
lean_inc_ref(v_outputData_450_);
lean_inc_ref(v_userData_449_);
lean_dec_ref(v_writer_448_);
goto v___jp_464_;
}
else
{
lean_dec_ref(v_data_447_);
return v_writer_448_;
}
}
case 4:
{
goto v___jp_476_;
}
case 5:
{
goto v___jp_476_;
}
default: 
{
lean_dec_ref(v_data_447_);
return v_writer_448_;
}
}
v___jp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = l_Array_append___redArg(v_userData_449_, v_data_447_);
lean_dec_ref(v_data_447_);
v___x_461_ = lean_nat_add(v_userDataBytes_457_, v___y_459_);
lean_dec(v___y_459_);
lean_dec(v_userDataBytes_457_);
v___x_462_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v_outputData_450_);
lean_ctor_set(v___x_462_, 2, v_state_451_);
lean_ctor_set(v___x_462_, 3, v_knownSize_452_);
lean_ctor_set(v___x_462_, 4, v_messageHead_453_);
lean_ctor_set(v___x_462_, 5, v___x_461_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*6, v_sentMessage_454_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*6 + 1, v_userClosedBody_455_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*6 + 2, v_omitBody_456_);
return v___x_462_;
}
v___jp_464_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_array_get_size(v_data_447_);
v___x_467_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_468_ = lean_nat_dec_lt(v___x_465_, v___x_466_);
if (v___x_468_ == 0)
{
v___y_459_ = v___x_465_;
goto v___jp_458_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = lean_nat_dec_le(v___x_466_, v___x_466_);
if (v___x_469_ == 0)
{
if (v___x_468_ == 0)
{
v___y_459_ = v___x_465_;
goto v___jp_458_;
}
else
{
size_t v___x_470_; size_t v___x_471_; lean_object* v___x_472_; 
v___x_470_ = ((size_t)0ULL);
v___x_471_ = lean_usize_of_nat(v___x_466_);
lean_inc_ref(v_data_447_);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_467_, v___f_463_, v_data_447_, v___x_470_, v___x_471_, v___x_465_);
v___y_459_ = v___x_472_;
goto v___jp_458_;
}
}
else
{
size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((size_t)0ULL);
v___x_474_ = lean_usize_of_nat(v___x_466_);
lean_inc_ref(v_data_447_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_467_, v___f_463_, v_data_447_, v___x_473_, v___x_474_, v___x_465_);
v___y_459_ = v___x_475_;
goto v___jp_458_;
}
}
}
v___jp_476_:
{
if (v_userClosedBody_455_ == 0)
{
lean_inc(v_userDataBytes_457_);
lean_inc(v_messageHead_453_);
lean_inc(v_knownSize_452_);
lean_inc(v_state_451_);
lean_inc_ref(v_outputData_450_);
lean_inc_ref(v_userData_449_);
lean_dec_ref(v_writer_448_);
goto v___jp_464_;
}
else
{
lean_dec_ref(v_data_447_);
return v_writer_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object* v_dir_477_, lean_object* v_data_478_, lean_object* v_writer_479_){
_start:
{
uint8_t v_dir_boxed_480_; lean_object* v_res_481_; 
v_dir_boxed_480_ = lean_unbox(v_dir_477_);
v_res_481_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_480_, v_data_478_, v_writer_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object* v_limitSize_482_, lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___y_488_; uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_492_ == 0)
{
lean_object* v_snd_493_; lean_object* v_fst_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_550_; 
v_snd_493_ = lean_ctor_get(v_b_486_, 1);
v_fst_494_ = lean_ctor_get(v_b_486_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_550_ == 0)
{
v___x_496_ = v_b_486_;
v_isShared_497_ = v_isSharedCheck_550_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_snd_493_);
lean_inc(v_fst_494_);
lean_dec(v_b_486_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_550_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_549_; 
v_fst_498_ = lean_ctor_get(v_snd_493_, 0);
v_snd_499_ = lean_ctor_get(v_snd_493_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_snd_493_);
if (v_isSharedCheck_549_ == 0)
{
v___x_501_ = v_snd_493_;
v_isShared_502_ = v_isSharedCheck_549_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snd_499_);
lean_inc(v_fst_498_);
lean_dec(v_snd_493_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_549_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_uget(v_as_483_, v_i_484_);
v___x_504_ = lean_nat_dec_le(v_limitSize_482_, v_snd_499_);
if (v___x_504_ == 0)
{
lean_object* v_data_505_; lean_object* v_extensions_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_541_; 
v_data_505_ = lean_ctor_get(v___x_503_, 0);
v_extensions_506_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_541_ == 0)
{
v___x_508_ = v___x_503_;
v_isShared_509_ = v_isSharedCheck_541_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_extensions_506_);
lean_inc(v_data_505_);
lean_dec(v___x_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_541_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_remaining_511_; lean_object* v___x_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_536_; uint8_t v___x_540_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v_remaining_511_ = lean_nat_sub(v_limitSize_482_, v_snd_499_);
v___x_512_ = lean_byte_array_size(v_data_505_);
v___x_540_ = lean_nat_dec_le(v___x_512_, v_remaining_511_);
if (v___x_540_ == 0)
{
v___y_536_ = v_remaining_511_;
goto v___jp_535_;
}
else
{
lean_dec(v_remaining_511_);
v___y_536_ = v___x_512_;
goto v___jp_535_;
}
v___jp_513_:
{
lean_object* v_size_516_; uint8_t v___x_517_; 
v_size_516_ = lean_nat_add(v_snd_499_, v___y_514_);
lean_dec(v_snd_499_);
v___x_517_ = lean_nat_dec_lt(v___y_514_, v___x_512_);
if (v___x_517_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v___y_514_);
lean_del_object(v___x_508_);
lean_dec_ref(v_extensions_506_);
lean_dec_ref(v_data_505_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v_size_516_);
v___x_519_ = v___x_501_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_fst_498_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_size_516_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_519_);
lean_ctor_set(v___x_496_, 0, v___y_515_);
v___x_521_ = v___x_496_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___y_515_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
v___y_488_ = v___x_521_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v___x_524_; lean_object* v_pendingChunk_526_; 
v___x_524_ = l_ByteArray_extract(v_data_505_, v___y_514_, v___x_512_);
lean_dec_ref(v_data_505_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_524_);
v_pendingChunk_526_ = v___x_508_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_extensions_506_);
v_pendingChunk_526_ = v_reuseFailAlloc_534_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_array_push(v_fst_498_, v_pendingChunk_526_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v_size_516_);
lean_ctor_set(v___x_501_, 0, v___x_527_);
v___x_529_ = v___x_501_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_size_516_);
v___x_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_529_);
lean_ctor_set(v___x_496_, 0, v___y_515_);
v___x_531_ = v___x_496_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___y_515_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
v___y_488_ = v___x_531_;
goto v___jp_487_;
}
}
}
}
}
v___jp_535_:
{
uint8_t v___x_537_; 
v___x_537_ = lean_nat_dec_eq(v___y_536_, v___x_510_);
if (v___x_537_ == 0)
{
lean_object* v_dataPart_538_; lean_object* v___x_539_; 
v_dataPart_538_ = l_ByteArray_extract(v_data_505_, v___x_510_, v___y_536_);
v___x_539_ = lean_array_push(v_fst_494_, v_dataPart_538_);
v___y_514_ = v___y_536_;
v___y_515_ = v___x_539_;
goto v___jp_513_;
}
else
{
v___y_514_ = v___y_536_;
v___y_515_ = v_fst_494_;
goto v___jp_513_;
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_array_push(v_fst_498_, v___x_503_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_542_);
v___x_544_ = v___x_501_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_snd_499_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_544_);
v___x_546_ = v___x_496_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_fst_494_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v___y_488_ = v___x_546_;
goto v___jp_487_;
}
}
}
}
}
}
else
{
return v_b_486_;
}
v___jp_487_:
{
size_t v___x_489_; size_t v___x_490_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_484_, v___x_489_);
v_i_484_ = v___x_490_;
v_b_486_ = v___y_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_551_, lean_object* v_as_552_, lean_object* v_i_553_, lean_object* v_stop_554_, lean_object* v_b_555_){
_start:
{
size_t v_i_boxed_556_; size_t v_stop_boxed_557_; lean_object* v_res_558_; 
v_i_boxed_556_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_stop_boxed_557_ = lean_unbox_usize(v_stop_554_);
lean_dec(v_stop_554_);
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_551_, v_as_552_, v_i_boxed_556_, v_stop_boxed_557_, v_b_555_);
lean_dec_ref(v_as_552_);
lean_dec(v_limitSize_551_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_559_, size_t v_i_560_, size_t v_stop_561_, lean_object* v_b_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_eq(v_i_560_, v_stop_561_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; 
v___x_564_ = lean_array_uget_borrowed(v_as_559_, v_i_560_);
v___x_565_ = lean_byte_array_size(v___x_564_);
v___x_566_ = lean_nat_add(v_b_562_, v___x_565_);
lean_dec(v_b_562_);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_560_, v___x_567_);
v_i_560_ = v___x_568_;
v_b_562_ = v___x_566_;
goto _start;
}
else
{
return v_b_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_570_, lean_object* v_i_571_, lean_object* v_stop_572_, lean_object* v_b_573_){
_start:
{
size_t v_i_boxed_574_; size_t v_stop_boxed_575_; lean_object* v_res_576_; 
v_i_boxed_574_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_stop_boxed_575_ = lean_unbox_usize(v_stop_572_);
lean_dec(v_stop_572_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_570_, v_i_boxed_574_, v_stop_boxed_575_, v_b_573_);
lean_dec_ref(v_as_570_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_585_, lean_object* v_limitSize_586_){
_start:
{
lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; uint8_t v___y_592_; uint8_t v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v_userData_622_; lean_object* v_outputData_623_; lean_object* v_state_624_; lean_object* v_knownSize_625_; lean_object* v_messageHead_626_; uint8_t v_sentMessage_627_; uint8_t v_userClosedBody_628_; uint8_t v_omitBody_629_; lean_object* v_userDataBytes_630_; lean_object* v_fst_632_; lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___y_644_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_userData_622_ = lean_ctor_get(v_writer_585_, 0);
v_outputData_623_ = lean_ctor_get(v_writer_585_, 1);
v_state_624_ = lean_ctor_get(v_writer_585_, 2);
v_knownSize_625_ = lean_ctor_get(v_writer_585_, 3);
v_messageHead_626_ = lean_ctor_get(v_writer_585_, 4);
v_sentMessage_627_ = lean_ctor_get_uint8(v_writer_585_, sizeof(void*)*6);
v_userClosedBody_628_ = lean_ctor_get_uint8(v_writer_585_, sizeof(void*)*6 + 1);
v_omitBody_629_ = lean_ctor_get_uint8(v_writer_585_, sizeof(void*)*6 + 2);
v_userDataBytes_630_ = lean_ctor_get(v_writer_585_, 5);
v___x_649_ = lean_array_get_size(v_userData_622_);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_nat_dec_eq(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; uint8_t v___x_653_; 
lean_inc(v_userDataBytes_630_);
lean_inc(v_messageHead_626_);
lean_inc(v_knownSize_625_);
lean_inc(v_state_624_);
lean_inc_ref(v_outputData_623_);
lean_inc_ref(v_userData_622_);
lean_dec_ref(v_writer_585_);
v___x_652_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_653_ = lean_nat_dec_lt(v___x_650_, v___x_649_);
if (v___x_653_ == 0)
{
lean_dec_ref(v_userData_622_);
v_fst_632_ = v___x_652_;
v_fst_633_ = v___x_652_;
v_snd_634_ = v___x_650_;
goto v___jp_631_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_655_ = lean_nat_dec_le(v___x_649_, v___x_649_);
if (v___x_655_ == 0)
{
if (v___x_653_ == 0)
{
lean_dec_ref(v_userData_622_);
v_fst_632_ = v___x_652_;
v_fst_633_ = v___x_652_;
v_snd_634_ = v___x_650_;
goto v___jp_631_;
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_649_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_586_, v_userData_622_, v___x_656_, v___x_657_, v___x_654_);
lean_dec_ref(v_userData_622_);
v___y_644_ = v___x_658_;
goto v___jp_643_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_649_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_586_, v_userData_622_, v___x_659_, v___x_660_, v___x_654_);
lean_dec_ref(v_userData_622_);
v___y_644_ = v___x_661_;
goto v___jp_643_;
}
}
}
else
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_writer_585_);
lean_ctor_set(v___x_662_, 1, v_limitSize_586_);
return v___x_662_;
}
v___jp_587_:
{
lean_object* v_data_599_; lean_object* v_size_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_621_; 
v_data_599_ = lean_ctor_get(v___y_590_, 0);
v_size_600_ = lean_ctor_get(v___y_590_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v___y_590_);
if (v_isSharedCheck_621_ == 0)
{
v___x_602_ = v___y_590_;
v_isShared_603_ = v_isSharedCheck_621_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_size_600_);
lean_inc(v_data_599_);
lean_dec(v___y_590_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_621_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_data_604_; lean_object* v_size_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_620_; 
v_data_604_ = lean_ctor_get(v___y_598_, 0);
v_size_605_ = lean_ctor_get(v___y_598_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v___y_598_);
if (v_isSharedCheck_620_ == 0)
{
v___x_607_ = v___y_598_;
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_size_605_);
lean_inc(v_data_604_);
lean_dec(v___y_598_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_outputData_612_; 
v___x_609_ = l_Array_append___redArg(v_data_599_, v_data_604_);
lean_dec_ref(v_data_604_);
v___x_610_ = lean_nat_add(v_size_600_, v_size_605_);
lean_dec(v_size_605_);
lean_dec(v_size_600_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_610_);
lean_ctor_set(v___x_607_, 0, v___x_609_);
v_outputData_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_610_);
v_outputData_612_ = v_reuseFailAlloc_619_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v_remaining_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v_remaining_613_ = lean_nat_sub(v_limitSize_586_, v___y_589_);
lean_dec(v_limitSize_586_);
v___x_614_ = lean_nat_sub(v___y_594_, v___y_589_);
lean_dec(v___y_589_);
lean_dec(v___y_594_);
v___x_615_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_615_, 0, v___y_597_);
lean_ctor_set(v___x_615_, 1, v_outputData_612_);
lean_ctor_set(v___x_615_, 2, v___y_591_);
lean_ctor_set(v___x_615_, 3, v___y_595_);
lean_ctor_set(v___x_615_, 4, v___y_588_);
lean_ctor_set(v___x_615_, 5, v___x_614_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*6, v___y_596_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*6 + 1, v___y_593_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*6 + 2, v___y_592_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_remaining_613_);
lean_ctor_set(v___x_602_, 0, v___x_615_);
v___x_617_ = v___x_602_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_remaining_613_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
v___jp_631_:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_array_get_size(v_fst_632_);
v___x_637_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_fst_632_);
lean_ctor_set(v___x_638_, 1, v___x_635_);
v___y_588_ = v_messageHead_626_;
v___y_589_ = v_snd_634_;
v___y_590_ = v_outputData_623_;
v___y_591_ = v_state_624_;
v___y_592_ = v_omitBody_629_;
v___y_593_ = v_userClosedBody_628_;
v___y_594_ = v_userDataBytes_630_;
v___y_595_ = v_knownSize_625_;
v___y_596_ = v_sentMessage_627_;
v___y_597_ = v_fst_633_;
v___y_598_ = v___x_638_;
goto v___jp_587_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_636_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_632_, v___x_639_, v___x_640_, v___x_635_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_fst_632_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___y_588_ = v_messageHead_626_;
v___y_589_ = v_snd_634_;
v___y_590_ = v_outputData_623_;
v___y_591_ = v_state_624_;
v___y_592_ = v_omitBody_629_;
v___y_593_ = v_userClosedBody_628_;
v___y_594_ = v_userDataBytes_630_;
v___y_595_ = v_knownSize_625_;
v___y_596_ = v_sentMessage_627_;
v___y_597_ = v_fst_633_;
v___y_598_ = v___x_642_;
goto v___jp_587_;
}
}
v___jp_643_:
{
lean_object* v_snd_645_; lean_object* v_fst_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; 
v_snd_645_ = lean_ctor_get(v___y_644_, 1);
lean_inc(v_snd_645_);
v_fst_646_ = lean_ctor_get(v___y_644_, 0);
lean_inc(v_fst_646_);
lean_dec_ref(v___y_644_);
v_fst_647_ = lean_ctor_get(v_snd_645_, 0);
lean_inc(v_fst_647_);
v_snd_648_ = lean_ctor_get(v_snd_645_, 1);
lean_inc(v_snd_648_);
lean_dec(v_snd_645_);
v_fst_632_ = v_fst_646_;
v_fst_633_ = v_fst_647_;
v_snd_634_ = v_snd_648_;
goto v___jp_631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_663_, lean_object* v_writer_664_, lean_object* v_limitSize_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_664_, v_limitSize_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_667_, lean_object* v_writer_668_, lean_object* v_limitSize_669_){
_start:
{
uint8_t v_dir_boxed_670_; lean_object* v_res_671_; 
v_dir_boxed_670_ = lean_unbox(v_dir_667_);
v_res_671_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_670_, v_writer_668_, v_limitSize_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_672_, size_t v_i_673_, size_t v_stop_674_, lean_object* v_b_675_){
_start:
{
lean_object* v___y_677_; uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_eq(v_i_673_, v_stop_674_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v_data_683_; uint8_t v___x_684_; 
v___x_682_ = lean_array_uget_borrowed(v_as_672_, v_i_673_);
v_data_683_ = lean_ctor_get(v___x_682_, 0);
v___x_684_ = l_ByteArray_isEmpty(v_data_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_inc(v___x_682_);
v___x_685_ = lean_array_push(v_b_675_, v___x_682_);
v___y_677_ = v___x_685_;
goto v___jp_676_;
}
else
{
v___y_677_ = v_b_675_;
goto v___jp_676_;
}
}
else
{
return v_b_675_;
}
v___jp_676_:
{
size_t v___x_678_; size_t v___x_679_; 
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_673_, v___x_678_);
v_i_673_ = v___x_679_;
v_b_675_ = v___y_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_686_, lean_object* v_i_687_, lean_object* v_stop_688_, lean_object* v_b_689_){
_start:
{
size_t v_i_boxed_690_; size_t v_stop_boxed_691_; lean_object* v_res_692_; 
v_i_boxed_690_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_stop_boxed_691_ = lean_unbox_usize(v_stop_688_);
lean_dec(v_stop_688_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_686_, v_i_boxed_690_, v_stop_boxed_691_, v_b_689_);
lean_dec_ref(v_as_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_693_, size_t v_i_694_, lean_object* v_bs_695_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_696_ == 0)
{
return v_bs_695_;
}
else
{
lean_object* v_v_697_; lean_object* v___x_698_; lean_object* v_bs_x27_699_; uint32_t v___x_700_; uint8_t v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_v_697_ = lean_array_uget(v_bs_695_, v_i_694_);
v___x_698_ = lean_unsigned_to_nat(0u);
v_bs_x27_699_ = lean_array_uset(v_bs_695_, v_i_694_, v___x_698_);
v___x_700_ = lean_unbox_uint32(v_v_697_);
lean_dec(v_v_697_);
v___x_701_ = lean_uint32_to_uint8(v___x_700_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_add(v_i_694_, v___x_702_);
v___x_704_ = lean_box(v___x_701_);
v___x_705_ = lean_array_uset(v_bs_x27_699_, v_i_694_, v___x_704_);
v_i_694_ = v___x_703_;
v_bs_695_ = v___x_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_707_, lean_object* v_i_708_, lean_object* v_bs_709_){
_start:
{
size_t v_sz_boxed_710_; size_t v_i_boxed_711_; lean_object* v_res_712_; 
v_sz_boxed_710_ = lean_unbox_usize(v_sz_707_);
lean_dec(v_sz_707_);
v_i_boxed_711_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_710_, v_i_boxed_711_, v_bs_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_715_, size_t v_i_716_, size_t v_stop_717_, lean_object* v_b_718_){
_start:
{
lean_object* v___y_720_; uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_eq(v_i_716_, v_stop_717_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = lean_array_uget_borrowed(v_as_715_, v_i_716_);
v_fst_726_ = lean_ctor_get(v___x_725_, 0);
v_snd_727_ = lean_ctor_get(v___x_725_, 1);
v___x_728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_729_ = lean_string_append(v_b_718_, v___x_728_);
v___x_730_ = lean_string_append(v___x_729_, v_fst_726_);
if (lean_obj_tag(v_snd_727_) == 0)
{
v___y_720_ = v___x_730_;
goto v___jp_719_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_val_731_ = lean_ctor_get(v_snd_727_, 0);
v___x_732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_731_);
v___x_733_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_731_);
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
lean_dec_ref(v___x_733_);
v___x_735_ = lean_string_append(v___x_730_, v___x_734_);
lean_dec_ref(v___x_734_);
v___y_720_ = v___x_735_;
goto v___jp_719_;
}
}
else
{
return v_b_718_;
}
v___jp_719_:
{
size_t v___x_721_; size_t v___x_722_; 
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_716_, v___x_721_);
v_i_716_ = v___x_722_;
v_b_718_ = v___y_720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_736_, lean_object* v_i_737_, lean_object* v_stop_738_, lean_object* v_b_739_){
_start:
{
size_t v_i_boxed_740_; size_t v_stop_boxed_741_; lean_object* v_res_742_; 
v_i_boxed_740_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_stop_boxed_741_ = lean_unbox_usize(v_stop_738_);
lean_dec(v_stop_738_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_736_, v_i_boxed_740_, v_stop_boxed_741_, v_b_739_);
lean_dec_ref(v_as_736_);
return v_res_742_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_745_ = lean_string_to_utf8(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_747_, size_t v_i_748_, size_t v_stop_749_, lean_object* v_b_750_){
_start:
{
lean_object* v___y_752_; uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_eq(v_i_748_, v_stop_749_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v_data_771_; lean_object* v_extensions_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_813_; 
v___x_770_ = lean_array_uget(v_as_747_, v_i_748_);
v_data_771_ = lean_ctor_get(v___x_770_, 0);
v_extensions_772_ = lean_ctor_get(v___x_770_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_813_ == 0)
{
v___x_774_ = v___x_770_;
v_isShared_775_ = v_isSharedCheck_813_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_extensions_772_);
lean_inc(v_data_771_);
lean_dec(v___x_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_813_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_chunkLen_776_; lean_object* v___y_778_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_chunkLen_776_ = lean_byte_array_size(v_data_771_);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_array_get_size(v_extensions_772_);
v___x_809_ = lean_nat_dec_lt(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_extensions_772_);
v___y_778_ = v___x_806_;
goto v___jp_777_;
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_808_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_772_, v___x_810_, v___x_811_, v___x_806_);
lean_dec_ref(v_extensions_772_);
v___y_778_ = v___x_812_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; size_t v_sz_782_; size_t v___x_783_; lean_object* v___x_784_; lean_object* v_size_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_779_ = lean_unsigned_to_nat(16u);
v___x_780_ = l_Nat_toDigits(v___x_779_, v_chunkLen_776_);
v___x_781_ = lean_array_mk(v___x_780_);
v_sz_782_ = lean_array_size(v___x_781_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_782_, v___x_783_, v___x_781_);
v_size_785_ = lean_byte_array_mk(v___x_784_);
v___x_786_ = lean_string_to_utf8(v___y_778_);
lean_dec_ref(v___y_778_);
v___x_787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_788_ = lean_unsigned_to_nat(5u);
v___x_789_ = lean_mk_empty_array_with_capacity(v___x_788_);
v___x_790_ = lean_array_push(v___x_789_, v_size_785_);
v___x_791_ = lean_array_push(v___x_790_, v___x_786_);
v___x_792_ = lean_array_push(v___x_791_, v___x_787_);
v___x_793_ = lean_array_push(v___x_792_, v_data_771_);
v___x_794_ = lean_array_push(v___x_793_, v___x_787_);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v___x_794_);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_795_);
lean_ctor_set(v___x_774_, 0, v___x_794_);
v___x_799_ = v___x_774_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_795_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v___y_752_ = v___x_799_;
goto v___jp_751_;
}
}
else
{
size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_801_ = lean_usize_of_nat(v___x_796_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_794_, v___x_783_, v___x_801_, v___x_795_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_802_);
lean_ctor_set(v___x_774_, 0, v___x_794_);
v___x_804_ = v___x_774_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_752_ = v___x_804_;
goto v___jp_751_;
}
}
}
}
}
else
{
return v_b_750_;
}
v___jp_751_:
{
lean_object* v_data_753_; lean_object* v_size_754_; lean_object* v_data_755_; lean_object* v_size_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_768_; 
v_data_753_ = lean_ctor_get(v_b_750_, 0);
lean_inc_ref(v_data_753_);
v_size_754_ = lean_ctor_get(v_b_750_, 1);
lean_inc(v_size_754_);
lean_dec_ref(v_b_750_);
v_data_755_ = lean_ctor_get(v___y_752_, 0);
v_size_756_ = lean_ctor_get(v___y_752_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v___y_752_);
if (v_isSharedCheck_768_ == 0)
{
v___x_758_ = v___y_752_;
v_isShared_759_ = v_isSharedCheck_768_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_size_756_);
lean_inc(v_data_755_);
lean_dec(v___y_752_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_768_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = l_Array_append___redArg(v_data_753_, v_data_755_);
lean_dec_ref(v_data_755_);
v___x_761_ = lean_nat_add(v_size_754_, v_size_756_);
lean_dec(v_size_756_);
lean_dec(v_size_754_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_761_);
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
size_t v___x_764_; size_t v___x_765_; 
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_748_, v___x_764_);
v_i_748_ = v___x_765_;
v_b_750_ = v___x_763_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_814_, lean_object* v_i_815_, lean_object* v_stop_816_, lean_object* v_b_817_){
_start:
{
size_t v_i_boxed_818_; size_t v_stop_boxed_819_; lean_object* v_res_820_; 
v_i_boxed_818_ = lean_unbox_usize(v_i_815_);
lean_dec(v_i_815_);
v_stop_boxed_819_ = lean_unbox_usize(v_stop_816_);
lean_dec(v_stop_816_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_814_, v_i_boxed_818_, v_stop_boxed_819_, v_b_817_);
lean_dec_ref(v_as_814_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_823_){
_start:
{
lean_object* v_userData_824_; lean_object* v_outputData_825_; lean_object* v_state_826_; lean_object* v_knownSize_827_; lean_object* v_messageHead_828_; uint8_t v_sentMessage_829_; uint8_t v_userClosedBody_830_; uint8_t v_omitBody_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___y_835_; uint8_t v___x_850_; 
v_userData_824_ = lean_ctor_get(v_writer_823_, 0);
v_outputData_825_ = lean_ctor_get(v_writer_823_, 1);
v_state_826_ = lean_ctor_get(v_writer_823_, 2);
v_knownSize_827_ = lean_ctor_get(v_writer_823_, 3);
v_messageHead_828_ = lean_ctor_get(v_writer_823_, 4);
v_sentMessage_829_ = lean_ctor_get_uint8(v_writer_823_, sizeof(void*)*6);
v_userClosedBody_830_ = lean_ctor_get_uint8(v_writer_823_, sizeof(void*)*6 + 1);
v_omitBody_831_ = lean_ctor_get_uint8(v_writer_823_, sizeof(void*)*6 + 2);
v___x_832_ = lean_array_get_size(v_userData_824_);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_nat_dec_eq(v___x_832_, v___x_833_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
lean_inc(v_messageHead_828_);
lean_inc(v_knownSize_827_);
lean_inc(v_state_826_);
lean_inc_ref(v_outputData_825_);
lean_inc_ref(v_userData_824_);
lean_dec_ref(v_writer_823_);
v___x_851_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_852_ = lean_nat_dec_lt(v___x_833_, v___x_832_);
if (v___x_852_ == 0)
{
lean_dec_ref(v_userData_824_);
v___y_835_ = v___x_851_;
goto v___jp_834_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = lean_nat_dec_le(v___x_832_, v___x_832_);
if (v___x_853_ == 0)
{
if (v___x_852_ == 0)
{
lean_dec_ref(v_userData_824_);
v___y_835_ = v___x_851_;
goto v___jp_834_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_832_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_824_, v___x_854_, v___x_855_, v___x_851_);
lean_dec_ref(v_userData_824_);
v___y_835_ = v___x_856_;
goto v___jp_834_;
}
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_832_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_824_, v___x_857_, v___x_858_, v___x_851_);
lean_dec_ref(v_userData_824_);
v___y_835_ = v___x_859_;
goto v___jp_834_;
}
}
}
else
{
return v_writer_823_;
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_837_ = lean_array_get_size(v___y_835_);
v___x_838_ = lean_nat_dec_lt(v___x_833_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v___y_835_);
v___x_839_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_839_, 0, v___x_836_);
lean_ctor_set(v___x_839_, 1, v_outputData_825_);
lean_ctor_set(v___x_839_, 2, v_state_826_);
lean_ctor_set(v___x_839_, 3, v_knownSize_827_);
lean_ctor_set(v___x_839_, 4, v_messageHead_828_);
lean_ctor_set(v___x_839_, 5, v___x_833_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*6, v_sentMessage_829_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*6 + 1, v_userClosedBody_830_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*6 + 2, v_omitBody_831_);
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
v___x_840_ = lean_nat_dec_le(v___x_837_, v___x_837_);
if (v___x_840_ == 0)
{
if (v___x_838_ == 0)
{
lean_object* v___x_841_; 
lean_dec_ref(v___y_835_);
v___x_841_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_841_, 0, v___x_836_);
lean_ctor_set(v___x_841_, 1, v_outputData_825_);
lean_ctor_set(v___x_841_, 2, v_state_826_);
lean_ctor_set(v___x_841_, 3, v_knownSize_827_);
lean_ctor_set(v___x_841_, 4, v_messageHead_828_);
lean_ctor_set(v___x_841_, 5, v___x_833_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*6, v_sentMessage_829_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*6 + 1, v_userClosedBody_830_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*6 + 2, v_omitBody_831_);
return v___x_841_;
}
else
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_842_ = ((size_t)0ULL);
v___x_843_ = lean_usize_of_nat(v___x_837_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_835_, v___x_842_, v___x_843_, v_outputData_825_);
lean_dec_ref(v___y_835_);
v___x_845_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_845_, 0, v___x_836_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
lean_ctor_set(v___x_845_, 2, v_state_826_);
lean_ctor_set(v___x_845_, 3, v_knownSize_827_);
lean_ctor_set(v___x_845_, 4, v_messageHead_828_);
lean_ctor_set(v___x_845_, 5, v___x_833_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*6, v_sentMessage_829_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*6 + 1, v_userClosedBody_830_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*6 + 2, v_omitBody_831_);
return v___x_845_;
}
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = ((size_t)0ULL);
v___x_847_ = lean_usize_of_nat(v___x_837_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_835_, v___x_846_, v___x_847_, v_outputData_825_);
lean_dec_ref(v___y_835_);
v___x_849_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_849_, 0, v___x_836_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
lean_ctor_set(v___x_849_, 2, v_state_826_);
lean_ctor_set(v___x_849_, 3, v_knownSize_827_);
lean_ctor_set(v___x_849_, 4, v_messageHead_828_);
lean_ctor_set(v___x_849_, 5, v___x_833_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6, v_sentMessage_829_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6 + 1, v_userClosedBody_830_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6 + 2, v_omitBody_831_);
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_860_, lean_object* v_writer_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_863_, lean_object* v_writer_864_){
_start:
{
uint8_t v_dir_boxed_865_; lean_object* v_res_866_; 
v_dir_boxed_865_ = lean_unbox(v_dir_863_);
v_res_866_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_865_, v_writer_864_);
return v_res_866_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_869_ = lean_string_to_utf8(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_871_ = lean_byte_array_size(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_872_){
_start:
{
lean_object* v_writer_873_; lean_object* v_outputData_874_; lean_object* v_userData_875_; lean_object* v_knownSize_876_; lean_object* v_messageHead_877_; uint8_t v_sentMessage_878_; uint8_t v_userClosedBody_879_; uint8_t v_omitBody_880_; lean_object* v_userDataBytes_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_902_; 
v_writer_873_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_872_);
v_outputData_874_ = lean_ctor_get(v_writer_873_, 1);
v_userData_875_ = lean_ctor_get(v_writer_873_, 0);
v_knownSize_876_ = lean_ctor_get(v_writer_873_, 3);
v_messageHead_877_ = lean_ctor_get(v_writer_873_, 4);
v_sentMessage_878_ = lean_ctor_get_uint8(v_writer_873_, sizeof(void*)*6);
v_userClosedBody_879_ = lean_ctor_get_uint8(v_writer_873_, sizeof(void*)*6 + 1);
v_omitBody_880_ = lean_ctor_get_uint8(v_writer_873_, sizeof(void*)*6 + 2);
v_userDataBytes_881_ = lean_ctor_get(v_writer_873_, 5);
v_isSharedCheck_902_ = !lean_is_exclusive(v_writer_873_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_writer_873_, 2);
lean_dec(v_unused_903_);
v___x_883_ = v_writer_873_;
v_isShared_884_ = v_isSharedCheck_902_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_userDataBytes_881_);
lean_inc(v_messageHead_877_);
lean_inc(v_knownSize_876_);
lean_inc(v_outputData_874_);
lean_inc(v_userData_875_);
lean_dec(v_writer_873_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_902_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_data_885_; lean_object* v_size_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_901_; 
v_data_885_ = lean_ctor_get(v_outputData_874_, 0);
v_size_886_ = lean_ctor_get(v_outputData_874_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_outputData_874_);
if (v_isSharedCheck_901_ == 0)
{
v___x_888_ = v_outputData_874_;
v_isShared_889_ = v_isSharedCheck_901_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_size_886_);
lean_inc(v_data_885_);
lean_dec(v_outputData_874_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_901_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_890_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_891_ = lean_array_push(v_data_885_, v___x_890_);
v___x_892_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_893_ = lean_nat_add(v_size_886_, v___x_892_);
lean_dec(v_size_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_893_);
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_895_ = v___x_888_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_900_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_box(6);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 2, v___x_896_);
lean_ctor_set(v___x_883_, 1, v___x_895_);
v___x_898_ = v___x_883_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_userData_875_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_knownSize_876_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_messageHead_877_);
lean_ctor_set(v_reuseFailAlloc_899_, 5, v_userDataBytes_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_899_, sizeof(void*)*6, v_sentMessage_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_899_, sizeof(void*)*6 + 1, v_userClosedBody_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_899_, sizeof(void*)*6 + 2, v_omitBody_880_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_904_, lean_object* v_writer_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_907_, lean_object* v_writer_908_){
_start:
{
uint8_t v_dir_boxed_909_; lean_object* v_res_910_; 
v_dir_boxed_909_ = lean_unbox(v_dir_907_);
v_res_910_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_909_, v_writer_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_911_, size_t v_i_912_, size_t v_stop_913_, lean_object* v_b_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = lean_usize_dec_eq(v_i_912_, v_stop_913_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v_data_917_; lean_object* v_data_918_; lean_object* v_size_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_932_; 
v___x_916_ = lean_array_uget_borrowed(v_as_911_, v_i_912_);
v_data_917_ = lean_ctor_get(v___x_916_, 0);
v_data_918_ = lean_ctor_get(v_b_914_, 0);
v_size_919_ = lean_ctor_get(v_b_914_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_b_914_);
if (v_isSharedCheck_932_ == 0)
{
v___x_921_ = v_b_914_;
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_size_919_);
lean_inc(v_data_918_);
lean_dec(v_b_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_inc_ref(v_data_917_);
v___x_923_ = lean_array_push(v_data_918_, v_data_917_);
v___x_924_ = lean_byte_array_size(v_data_917_);
v___x_925_ = lean_nat_add(v_size_919_, v___x_924_);
lean_dec(v_size_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_925_);
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_927_ = v___x_921_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_925_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
size_t v___x_928_; size_t v___x_929_; 
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_912_, v___x_928_);
v_i_912_ = v___x_929_;
v_b_914_ = v___x_927_;
goto _start;
}
}
}
else
{
return v_b_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_933_, lean_object* v_i_934_, lean_object* v_stop_935_, lean_object* v_b_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; lean_object* v_res_939_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_935_);
lean_dec(v_stop_935_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_933_, v_i_boxed_937_, v_stop_boxed_938_, v_b_936_);
lean_dec_ref(v_as_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_940_){
_start:
{
lean_object* v_userData_941_; lean_object* v_outputData_942_; lean_object* v_state_943_; lean_object* v_knownSize_944_; lean_object* v_messageHead_945_; uint8_t v_sentMessage_946_; uint8_t v_userClosedBody_947_; uint8_t v_omitBody_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_975_; 
v_userData_941_ = lean_ctor_get(v_writer_940_, 0);
v_outputData_942_ = lean_ctor_get(v_writer_940_, 1);
v_state_943_ = lean_ctor_get(v_writer_940_, 2);
v_knownSize_944_ = lean_ctor_get(v_writer_940_, 3);
v_messageHead_945_ = lean_ctor_get(v_writer_940_, 4);
v_sentMessage_946_ = lean_ctor_get_uint8(v_writer_940_, sizeof(void*)*6);
v_userClosedBody_947_ = lean_ctor_get_uint8(v_writer_940_, sizeof(void*)*6 + 1);
v_omitBody_948_ = lean_ctor_get_uint8(v_writer_940_, sizeof(void*)*6 + 2);
v_isSharedCheck_975_ = !lean_is_exclusive(v_writer_940_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_writer_940_, 5);
lean_dec(v_unused_976_);
v___x_950_ = v_writer_940_;
v_isShared_951_ = v_isSharedCheck_975_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_messageHead_945_);
lean_inc(v_knownSize_944_);
lean_inc(v_state_943_);
lean_inc(v_outputData_942_);
lean_inc(v_userData_941_);
lean_dec(v_writer_940_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_975_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_954_ = lean_array_get_size(v_userData_941_);
v___x_955_ = lean_nat_dec_lt(v___x_952_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_957_; 
lean_dec_ref(v_userData_941_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 5, v___x_952_);
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_957_ = v___x_950_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_outputData_942_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_state_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_knownSize_944_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_messageHead_945_);
lean_ctor_set(v_reuseFailAlloc_958_, 5, v___x_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*6, v_sentMessage_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*6 + 1, v_userClosedBody_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*6 + 2, v_omitBody_948_);
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
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_le(v___x_954_, v___x_954_);
if (v___x_959_ == 0)
{
if (v___x_955_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_userData_941_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 5, v___x_952_);
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_961_ = v___x_950_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_outputData_942_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_state_943_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_knownSize_944_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_messageHead_945_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v___x_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, sizeof(void*)*6, v_sentMessage_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, sizeof(void*)*6 + 1, v_userClosedBody_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, sizeof(void*)*6 + 2, v_omitBody_948_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_usize_of_nat(v___x_954_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_941_, v___x_963_, v___x_964_, v_outputData_942_);
lean_dec_ref(v_userData_941_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 5, v___x_952_);
lean_ctor_set(v___x_950_, 1, v___x_965_);
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_967_ = v___x_950_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_state_943_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_knownSize_944_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_messageHead_945_);
lean_ctor_set(v_reuseFailAlloc_968_, 5, v___x_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*6, v_sentMessage_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*6 + 1, v_userClosedBody_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*6 + 2, v_omitBody_948_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
else
{
size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_969_ = ((size_t)0ULL);
v___x_970_ = lean_usize_of_nat(v___x_954_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_941_, v___x_969_, v___x_970_, v_outputData_942_);
lean_dec_ref(v_userData_941_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 5, v___x_952_);
lean_ctor_set(v___x_950_, 1, v___x_971_);
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_973_ = v___x_950_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_state_943_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_knownSize_944_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_messageHead_945_);
lean_ctor_set(v_reuseFailAlloc_974_, 5, v___x_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*6, v_sentMessage_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*6 + 1, v_userClosedBody_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*6 + 2, v_omitBody_948_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_977_, lean_object* v_writer_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_980_, lean_object* v_writer_981_){
_start:
{
uint8_t v_dir_boxed_982_; lean_object* v_res_983_; 
v_dir_boxed_982_ = lean_unbox(v_dir_980_);
v_res_983_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_982_, v_writer_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_984_, lean_object* v_x1_985_, lean_object* v_x2_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_byte_array_size(v_x1_985_);
v___x_989_ = lean_byte_array_size(v_x2_986_);
v___x_990_ = lean_byte_array_copy_slice(v_x2_986_, v___x_987_, v_x1_985_, v___x_988_, v___x_989_, v___x_984_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_991_, lean_object* v_x1_992_, lean_object* v_x2_993_){
_start:
{
uint8_t v___x_115__boxed_994_; lean_object* v_res_995_; 
v___x_115__boxed_994_ = lean_unbox(v___x_991_);
v_res_995_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_115__boxed_994_, v_x1_992_, v_x2_993_);
lean_dec_ref(v_x2_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_999_){
_start:
{
lean_object* v_userData_1000_; lean_object* v_outputData_1001_; lean_object* v_state_1002_; lean_object* v_knownSize_1003_; lean_object* v_messageHead_1004_; uint8_t v_sentMessage_1005_; uint8_t v_userClosedBody_1006_; uint8_t v_omitBody_1007_; lean_object* v_userDataBytes_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1036_; 
v_userData_1000_ = lean_ctor_get(v_writer_999_, 0);
v_outputData_1001_ = lean_ctor_get(v_writer_999_, 1);
v_state_1002_ = lean_ctor_get(v_writer_999_, 2);
v_knownSize_1003_ = lean_ctor_get(v_writer_999_, 3);
v_messageHead_1004_ = lean_ctor_get(v_writer_999_, 4);
v_sentMessage_1005_ = lean_ctor_get_uint8(v_writer_999_, sizeof(void*)*6);
v_userClosedBody_1006_ = lean_ctor_get_uint8(v_writer_999_, sizeof(void*)*6 + 1);
v_omitBody_1007_ = lean_ctor_get_uint8(v_writer_999_, sizeof(void*)*6 + 2);
v_userDataBytes_1008_ = lean_ctor_get(v_writer_999_, 5);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_writer_999_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1010_ = v_writer_999_;
v_isShared_1011_ = v_isSharedCheck_1036_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_userDataBytes_1008_);
lean_inc(v_messageHead_1004_);
lean_inc(v_knownSize_1003_);
lean_inc(v_state_1002_);
lean_inc(v_outputData_1001_);
lean_inc(v_userData_1000_);
lean_dec(v_writer_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1036_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___y_1013_; lean_object* v_data_1020_; lean_object* v_size_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_data_1020_ = lean_ctor_get(v_outputData_1001_, 0);
lean_inc_ref(v_data_1020_);
v_size_1021_ = lean_ctor_get(v_outputData_1001_, 1);
lean_inc(v_size_1021_);
lean_dec_ref(v_outputData_1001_);
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_array_get_size(v_data_1020_);
v___x_1024_ = lean_nat_dec_eq(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1025_ = lean_mk_empty_byte_array(v_size_1021_);
lean_dec(v_size_1021_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1028_ = lean_nat_dec_lt(v___x_1026_, v___x_1023_);
if (v___x_1028_ == 0)
{
lean_dec_ref(v_data_1020_);
v___y_1013_ = v___x_1025_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1029_; lean_object* v___f_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1029_ = lean_box(v___x_1024_);
v___f_1030_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1030_, 0, v___x_1029_);
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = lean_usize_of_nat(v___x_1023_);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1027_, v___f_1030_, v_data_1020_, v___x_1031_, v___x_1032_, v___x_1025_);
v___y_1013_ = v___x_1033_;
goto v___jp_1012_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_size_1021_);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_array_fget(v_data_1020_, v___x_1034_);
lean_dec_ref(v_data_1020_);
v___y_1013_ = v___x_1035_;
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___x_1014_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_userData_1000_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_state_1002_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_knownSize_1003_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_messageHead_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 5, v_userDataBytes_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*6, v_sentMessage_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*6 + 1, v_userClosedBody_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*6 + 2, v_omitBody_1007_);
v___x_1016_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___y_1013_);
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1037_, lean_object* v_writer_1038_){
_start:
{
lean_object* v_userData_1039_; lean_object* v_outputData_1040_; lean_object* v_state_1041_; lean_object* v_knownSize_1042_; lean_object* v_messageHead_1043_; uint8_t v_sentMessage_1044_; uint8_t v_userClosedBody_1045_; uint8_t v_omitBody_1046_; lean_object* v_userDataBytes_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1075_; 
v_userData_1039_ = lean_ctor_get(v_writer_1038_, 0);
v_outputData_1040_ = lean_ctor_get(v_writer_1038_, 1);
v_state_1041_ = lean_ctor_get(v_writer_1038_, 2);
v_knownSize_1042_ = lean_ctor_get(v_writer_1038_, 3);
v_messageHead_1043_ = lean_ctor_get(v_writer_1038_, 4);
v_sentMessage_1044_ = lean_ctor_get_uint8(v_writer_1038_, sizeof(void*)*6);
v_userClosedBody_1045_ = lean_ctor_get_uint8(v_writer_1038_, sizeof(void*)*6 + 1);
v_omitBody_1046_ = lean_ctor_get_uint8(v_writer_1038_, sizeof(void*)*6 + 2);
v_userDataBytes_1047_ = lean_ctor_get(v_writer_1038_, 5);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_writer_1038_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1049_ = v_writer_1038_;
v_isShared_1050_ = v_isSharedCheck_1075_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_userDataBytes_1047_);
lean_inc(v_messageHead_1043_);
lean_inc(v_knownSize_1042_);
lean_inc(v_state_1041_);
lean_inc(v_outputData_1040_);
lean_inc(v_userData_1039_);
lean_dec(v_writer_1038_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1075_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___y_1052_; lean_object* v_data_1059_; lean_object* v_size_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_data_1059_ = lean_ctor_get(v_outputData_1040_, 0);
lean_inc_ref(v_data_1059_);
v_size_1060_ = lean_ctor_get(v_outputData_1040_, 1);
lean_inc(v_size_1060_);
lean_dec_ref(v_outputData_1040_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_array_get_size(v_data_1059_);
v___x_1063_ = lean_nat_dec_eq(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1064_ = lean_mk_empty_byte_array(v_size_1060_);
lean_dec(v_size_1060_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1067_ = lean_nat_dec_lt(v___x_1065_, v___x_1062_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v_data_1059_);
v___y_1052_ = v___x_1064_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1068_; lean_object* v___f_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1068_ = lean_box(v___x_1063_);
v___f_1069_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = lean_usize_of_nat(v___x_1062_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1066_, v___f_1069_, v_data_1059_, v___x_1070_, v___x_1071_, v___x_1064_);
v___y_1052_ = v___x_1072_;
goto v___jp_1051_;
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_size_1060_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_array_fget(v_data_1059_, v___x_1073_);
lean_dec_ref(v_data_1059_);
v___y_1052_ = v___x_1074_;
goto v___jp_1051_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1053_);
v___x_1055_ = v___x_1049_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_userData_1039_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_state_1041_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_knownSize_1042_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_messageHead_1043_);
lean_ctor_set(v_reuseFailAlloc_1058_, 5, v_userDataBytes_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1058_, sizeof(void*)*6, v_sentMessage_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1058_, sizeof(void*)*6 + 1, v_userClosedBody_1045_);
lean_ctor_set_uint8(v_reuseFailAlloc_1058_, sizeof(void*)*6 + 2, v_omitBody_1046_);
v___x_1055_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___y_1052_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1076_, lean_object* v_writer_1077_){
_start:
{
uint8_t v_dir_boxed_1078_; lean_object* v_res_1079_; 
v_dir_boxed_1078_ = lean_unbox(v_dir_1076_);
v_res_1079_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1078_, v_writer_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1080_, lean_object* v_writer_1081_){
_start:
{
lean_object* v_userData_1082_; lean_object* v_outputData_1083_; lean_object* v_knownSize_1084_; lean_object* v_messageHead_1085_; uint8_t v_sentMessage_1086_; uint8_t v_userClosedBody_1087_; uint8_t v_omitBody_1088_; lean_object* v_userDataBytes_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_userData_1082_ = lean_ctor_get(v_writer_1081_, 0);
v_outputData_1083_ = lean_ctor_get(v_writer_1081_, 1);
v_knownSize_1084_ = lean_ctor_get(v_writer_1081_, 3);
v_messageHead_1085_ = lean_ctor_get(v_writer_1081_, 4);
v_sentMessage_1086_ = lean_ctor_get_uint8(v_writer_1081_, sizeof(void*)*6);
v_userClosedBody_1087_ = lean_ctor_get_uint8(v_writer_1081_, sizeof(void*)*6 + 1);
v_omitBody_1088_ = lean_ctor_get_uint8(v_writer_1081_, sizeof(void*)*6 + 2);
v_userDataBytes_1089_ = lean_ctor_get(v_writer_1081_, 5);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_writer_1081_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_writer_1081_, 2);
lean_dec(v_unused_1097_);
v___x_1091_ = v_writer_1081_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_userDataBytes_1089_);
lean_inc(v_messageHead_1085_);
lean_inc(v_knownSize_1084_);
lean_inc(v_outputData_1083_);
lean_inc(v_userData_1082_);
lean_dec(v_writer_1081_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 2, v_state_1080_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_userData_1082_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_outputData_1083_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_state_1080_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_knownSize_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_messageHead_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 5, v_userDataBytes_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*6, v_sentMessage_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*6 + 1, v_userClosedBody_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*6 + 2, v_omitBody_1088_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1098_, lean_object* v_state_1099_, lean_object* v_writer_1100_){
_start:
{
lean_object* v_userData_1101_; lean_object* v_outputData_1102_; lean_object* v_knownSize_1103_; lean_object* v_messageHead_1104_; uint8_t v_sentMessage_1105_; uint8_t v_userClosedBody_1106_; uint8_t v_omitBody_1107_; lean_object* v_userDataBytes_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_userData_1101_ = lean_ctor_get(v_writer_1100_, 0);
v_outputData_1102_ = lean_ctor_get(v_writer_1100_, 1);
v_knownSize_1103_ = lean_ctor_get(v_writer_1100_, 3);
v_messageHead_1104_ = lean_ctor_get(v_writer_1100_, 4);
v_sentMessage_1105_ = lean_ctor_get_uint8(v_writer_1100_, sizeof(void*)*6);
v_userClosedBody_1106_ = lean_ctor_get_uint8(v_writer_1100_, sizeof(void*)*6 + 1);
v_omitBody_1107_ = lean_ctor_get_uint8(v_writer_1100_, sizeof(void*)*6 + 2);
v_userDataBytes_1108_ = lean_ctor_get(v_writer_1100_, 5);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_writer_1100_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v_writer_1100_, 2);
lean_dec(v_unused_1116_);
v___x_1110_ = v_writer_1100_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_userDataBytes_1108_);
lean_inc(v_messageHead_1104_);
lean_inc(v_knownSize_1103_);
lean_inc(v_outputData_1102_);
lean_inc(v_userData_1101_);
lean_dec(v_writer_1100_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 2, v_state_1099_);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_userData_1101_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_outputData_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_state_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_knownSize_1103_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_messageHead_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 5, v_userDataBytes_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*6, v_sentMessage_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*6 + 1, v_userClosedBody_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*6 + 2, v_omitBody_1107_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1117_, lean_object* v_state_1118_, lean_object* v_writer_1119_){
_start:
{
uint8_t v_dir_boxed_1120_; lean_object* v_res_1121_; 
v_dir_boxed_1120_ = lean_unbox(v_dir_1117_);
v_res_1121_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1120_, v_state_1118_, v_writer_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1122_, lean_object* v_messageHead_1123_, lean_object* v_writer_1124_){
_start:
{
lean_object* v_userData_1125_; lean_object* v_outputData_1126_; lean_object* v_state_1127_; lean_object* v_knownSize_1128_; lean_object* v_messageHead_1129_; uint8_t v_sentMessage_1130_; uint8_t v_userClosedBody_1131_; uint8_t v_omitBody_1132_; lean_object* v_userDataBytes_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1146_; 
v_userData_1125_ = lean_ctor_get(v_writer_1124_, 0);
v_outputData_1126_ = lean_ctor_get(v_writer_1124_, 1);
v_state_1127_ = lean_ctor_get(v_writer_1124_, 2);
v_knownSize_1128_ = lean_ctor_get(v_writer_1124_, 3);
v_messageHead_1129_ = lean_ctor_get(v_writer_1124_, 4);
v_sentMessage_1130_ = lean_ctor_get_uint8(v_writer_1124_, sizeof(void*)*6);
v_userClosedBody_1131_ = lean_ctor_get_uint8(v_writer_1124_, sizeof(void*)*6 + 1);
v_omitBody_1132_ = lean_ctor_get_uint8(v_writer_1124_, sizeof(void*)*6 + 2);
v_userDataBytes_1133_ = lean_ctor_get(v_writer_1124_, 5);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_writer_1124_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1135_ = v_writer_1124_;
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_userDataBytes_1133_);
lean_inc(v_messageHead_1129_);
lean_inc(v_knownSize_1128_);
lean_inc(v_state_1127_);
lean_inc(v_outputData_1126_);
lean_inc(v_userData_1125_);
lean_dec(v_writer_1124_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
uint8_t v___y_1138_; 
if (v_dir_1122_ == 0)
{
uint8_t v___x_1144_; 
v___x_1144_ = 1;
v___y_1138_ = v___x_1144_;
goto v___jp_1137_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = 0;
v___y_1138_ = v___x_1145_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_6__overap_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_6__overap_1139_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1138_);
v___x_1140_ = lean_apply_2(v___x_6__overap_1139_, v_outputData_1126_, v_messageHead_1123_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 1, v___x_1140_);
v___x_1142_ = v___x_1135_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_userData_1125_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_state_1127_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_knownSize_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_messageHead_1129_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_userDataBytes_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*6, v_sentMessage_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*6 + 1, v_userClosedBody_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*6 + 2, v_omitBody_1132_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1147_, lean_object* v_messageHead_1148_, lean_object* v_writer_1149_){
_start:
{
uint8_t v_dir_boxed_1150_; lean_object* v_res_1151_; 
v_dir_boxed_1150_ = lean_unbox(v_dir_1147_);
v_res_1151_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1150_, v_messageHead_1148_, v_writer_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(lean_object* v_a_1152_, lean_object* v_x_1153_){
_start:
{
lean_object* v_key_1154_; lean_object* v_value_1155_; lean_object* v_tail_1156_; uint8_t v___x_1157_; 
v_key_1154_ = lean_ctor_get(v_x_1153_, 0);
v_value_1155_ = lean_ctor_get(v_x_1153_, 1);
v_tail_1156_ = lean_ctor_get(v_x_1153_, 2);
v___x_1157_ = lean_string_dec_eq(v_key_1154_, v_a_1152_);
if (v___x_1157_ == 0)
{
v_x_1153_ = v_tail_1156_;
goto _start;
}
else
{
lean_inc(v_value_1155_);
return v_value_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg___boxed(lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1159_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(lean_object* v_m_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_buckets_1164_; lean_object* v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v_fold_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_buckets_1164_ = lean_ctor_get(v_m_1162_, 1);
v___x_1165_ = lean_array_get_size(v_buckets_1164_);
v___x_1166_ = lean_string_hash(v_a_1163_);
v___x_1167_ = 32ULL;
v___x_1168_ = lean_uint64_shift_right(v___x_1166_, v___x_1167_);
v_fold_1169_ = lean_uint64_xor(v___x_1166_, v___x_1168_);
v___x_1170_ = 16ULL;
v___x_1171_ = lean_uint64_shift_right(v_fold_1169_, v___x_1170_);
v___x_1172_ = lean_uint64_xor(v_fold_1169_, v___x_1171_);
v___x_1173_ = lean_uint64_to_usize(v___x_1172_);
v___x_1174_ = lean_usize_of_nat(v___x_1165_);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_sub(v___x_1174_, v___x_1175_);
v___x_1177_ = lean_usize_land(v___x_1173_, v___x_1176_);
v___x_1178_ = lean_array_uget_borrowed(v_buckets_1164_, v___x_1177_);
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1163_, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg___boxed(lean_object* v_m_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1180_, v_a_1181_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_m_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1183_, lean_object* v_x_1184_){
_start:
{
if (lean_obj_tag(v_x_1184_) == 0)
{
uint8_t v___x_1185_; 
v___x_1185_ = 0;
return v___x_1185_;
}
else
{
lean_object* v_key_1186_; lean_object* v_tail_1187_; uint8_t v___x_1188_; 
v_key_1186_ = lean_ctor_get(v_x_1184_, 0);
v_tail_1187_ = lean_ctor_get(v_x_1184_, 2);
v___x_1188_ = lean_string_dec_eq(v_key_1186_, v_a_1183_);
if (v___x_1188_ == 0)
{
v_x_1184_ = v_tail_1187_;
goto _start;
}
else
{
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1190_, lean_object* v_x_1191_){
_start:
{
uint8_t v_res_1192_; lean_object* v_r_1193_; 
v_res_1192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1190_, v_x_1191_);
lean_dec(v_x_1191_);
lean_dec_ref(v_a_1190_);
v_r_1193_ = lean_box(v_res_1192_);
return v_r_1193_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_buckets_1196_; lean_object* v___x_1197_; uint64_t v___x_1198_; uint64_t v___x_1199_; uint64_t v___x_1200_; uint64_t v_fold_1201_; uint64_t v___x_1202_; uint64_t v___x_1203_; uint64_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_buckets_1196_ = lean_ctor_get(v_m_1194_, 1);
v___x_1197_ = lean_array_get_size(v_buckets_1196_);
v___x_1198_ = lean_string_hash(v_a_1195_);
v___x_1199_ = 32ULL;
v___x_1200_ = lean_uint64_shift_right(v___x_1198_, v___x_1199_);
v_fold_1201_ = lean_uint64_xor(v___x_1198_, v___x_1200_);
v___x_1202_ = 16ULL;
v___x_1203_ = lean_uint64_shift_right(v_fold_1201_, v___x_1202_);
v___x_1204_ = lean_uint64_xor(v_fold_1201_, v___x_1203_);
v___x_1205_ = lean_uint64_to_usize(v___x_1204_);
v___x_1206_ = lean_usize_of_nat(v___x_1197_);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = lean_usize_sub(v___x_1206_, v___x_1207_);
v___x_1209_ = lean_usize_land(v___x_1205_, v___x_1208_);
v___x_1210_ = lean_array_uget_borrowed(v_buckets_1196_, v___x_1209_);
v___x_1211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1195_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1212_, lean_object* v_a_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1212_, v_a_1213_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v_m_1212_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(lean_object* v_s_1216_, lean_object* v_p_1217_){
_start:
{
uint32_t v___y_1219_; lean_object* v___x_1224_; uint8_t v_decide_1225_; 
v___x_1224_ = lean_string_utf8_byte_size(v_s_1216_);
v_decide_1225_ = lean_nat_dec_eq(v_p_1217_, v___x_1224_);
if (v_decide_1225_ == 0)
{
uint32_t v___x_1226_; uint32_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1226_ = lean_string_utf8_get_fast(v_s_1216_, v_p_1217_);
v___x_1227_ = 65;
v___x_1228_ = lean_uint32_dec_le(v___x_1227_, v___x_1226_);
if (v___x_1228_ == 0)
{
v___y_1219_ = v___x_1226_;
goto v___jp_1218_;
}
else
{
uint32_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 90;
v___x_1230_ = lean_uint32_dec_le(v___x_1226_, v___x_1229_);
if (v___x_1230_ == 0)
{
v___y_1219_ = v___x_1226_;
goto v___jp_1218_;
}
else
{
uint32_t v___x_1231_; uint32_t v___x_1232_; 
v___x_1231_ = 32;
v___x_1232_ = lean_uint32_add(v___x_1226_, v___x_1231_);
v___y_1219_ = v___x_1232_;
goto v___jp_1218_;
}
}
}
else
{
lean_dec(v_p_1217_);
return v_s_1216_;
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_inc(v_p_1217_);
v___x_1220_ = lean_string_utf8_set(v_s_1216_, v_p_1217_, v___y_1219_);
v___x_1221_ = l_Char_utf8Size(v___y_1219_);
v___x_1222_ = lean_nat_add(v_p_1217_, v___x_1221_);
lean_dec(v___x_1221_);
lean_dec(v_p_1217_);
v_s_1216_ = v___x_1220_;
v_p_1217_ = v___x_1222_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1234_, lean_object* v_writer_1235_){
_start:
{
uint8_t v___y_1237_; 
if (v_dir_1234_ == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = 1;
v___y_1237_ = v___x_1254_;
goto v___jp_1236_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
v___y_1237_ = v___x_1255_;
goto v___jp_1236_;
}
v___jp_1236_:
{
lean_object* v_messageHead_1238_; lean_object* v___x_1239_; lean_object* v_entries_1240_; lean_object* v_indexes_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_messageHead_1238_ = lean_ctor_get(v_writer_1235_, 4);
v___x_1239_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1237_, v_messageHead_1238_);
v_entries_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref(v_entries_1240_);
v_indexes_1241_ = lean_ctor_get(v___x_1239_, 1);
lean_inc_ref(v_indexes_1241_);
lean_dec_ref(v___x_1239_);
v___x_1242_ = l_Std_Http_Header_Name_connection;
v___x_1243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; 
lean_dec_ref(v_indexes_1241_);
lean_dec_ref(v_entries_1240_);
v___x_1244_ = 1;
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_entry_1247_; lean_object* v___x_1248_; lean_object* v_snd_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_indexes_1241_, v___x_1242_);
lean_dec_ref(v_indexes_1241_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v_entry_1247_ = lean_array_fget(v___x_1245_, v___x_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_array_fget(v_entries_1240_, v_entry_1247_);
lean_dec(v_entry_1247_);
lean_dec_ref(v_entries_1240_);
v_snd_1249_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_snd_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(v_snd_1249_, v___x_1246_);
v___x_1251_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_1252_ = lean_string_dec_eq(v___x_1250_, v___x_1251_);
lean_dec_ref(v___x_1250_);
if (v___x_1252_ == 0)
{
return v___x_1243_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1256_, lean_object* v_writer_1257_){
_start:
{
uint8_t v_dir_boxed_1258_; uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_dir_boxed_1258_ = lean_unbox(v_dir_1256_);
v_res_1259_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1258_, v_writer_1257_);
lean_dec_ref(v_writer_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1261_, lean_object* v_m_1262_, lean_object* v_a_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1262_, v_a_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_m_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1265_, v_m_1266_, v_a_1267_);
lean_dec_ref(v_a_1267_);
lean_dec_ref(v_m_1266_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_00_u03b2_1270_, lean_object* v_m_1271_, lean_object* v_a_1272_, lean_object* v_hma_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1271_, v_a_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_, lean_object* v_hma_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_00_u03b2_1275_, v_m_1276_, v_a_1277_, v_hma_1278_);
lean_dec_ref(v_a_1277_);
lean_dec_ref(v_m_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1280_, lean_object* v_a_1281_, lean_object* v_x_1282_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1281_, v_x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1284_, lean_object* v_a_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1284_, v_a_1285_, v_x_1286_);
lean_dec(v_x_1286_);
lean_dec_ref(v_a_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(lean_object* v_00_u03b2_1289_, lean_object* v_a_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1290_, v_x_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_a_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(v_00_u03b2_1294_, v_a_1295_, v_x_1296_, v_x_1297_);
lean_dec(v_x_1296_);
lean_dec_ref(v_a_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1299_){
_start:
{
lean_object* v_userData_1300_; lean_object* v_outputData_1301_; lean_object* v_knownSize_1302_; lean_object* v_messageHead_1303_; uint8_t v_sentMessage_1304_; uint8_t v_userClosedBody_1305_; uint8_t v_omitBody_1306_; lean_object* v_userDataBytes_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
v_userData_1300_ = lean_ctor_get(v_writer_1299_, 0);
v_outputData_1301_ = lean_ctor_get(v_writer_1299_, 1);
v_knownSize_1302_ = lean_ctor_get(v_writer_1299_, 3);
v_messageHead_1303_ = lean_ctor_get(v_writer_1299_, 4);
v_sentMessage_1304_ = lean_ctor_get_uint8(v_writer_1299_, sizeof(void*)*6);
v_userClosedBody_1305_ = lean_ctor_get_uint8(v_writer_1299_, sizeof(void*)*6 + 1);
v_omitBody_1306_ = lean_ctor_get_uint8(v_writer_1299_, sizeof(void*)*6 + 2);
v_userDataBytes_1307_ = lean_ctor_get(v_writer_1299_, 5);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_writer_1299_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v_writer_1299_, 2);
lean_dec(v_unused_1316_);
v___x_1309_ = v_writer_1299_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_userDataBytes_1307_);
lean_inc(v_messageHead_1303_);
lean_inc(v_knownSize_1302_);
lean_inc(v_outputData_1301_);
lean_inc(v_userData_1300_);
lean_dec(v_writer_1299_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(7);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 2, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_userData_1300_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_outputData_1301_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_knownSize_1302_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_messageHead_1303_);
lean_ctor_set(v_reuseFailAlloc_1314_, 5, v_userDataBytes_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*6, v_sentMessage_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*6 + 1, v_userClosedBody_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*6 + 2, v_omitBody_1306_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1317_, lean_object* v_writer_1318_){
_start:
{
lean_object* v_userData_1319_; lean_object* v_outputData_1320_; lean_object* v_knownSize_1321_; lean_object* v_messageHead_1322_; uint8_t v_sentMessage_1323_; uint8_t v_userClosedBody_1324_; uint8_t v_omitBody_1325_; lean_object* v_userDataBytes_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_userData_1319_ = lean_ctor_get(v_writer_1318_, 0);
v_outputData_1320_ = lean_ctor_get(v_writer_1318_, 1);
v_knownSize_1321_ = lean_ctor_get(v_writer_1318_, 3);
v_messageHead_1322_ = lean_ctor_get(v_writer_1318_, 4);
v_sentMessage_1323_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6);
v_userClosedBody_1324_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6 + 1);
v_omitBody_1325_ = lean_ctor_get_uint8(v_writer_1318_, sizeof(void*)*6 + 2);
v_userDataBytes_1326_ = lean_ctor_get(v_writer_1318_, 5);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_writer_1318_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v_writer_1318_, 2);
lean_dec(v_unused_1335_);
v___x_1328_ = v_writer_1318_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_userDataBytes_1326_);
lean_inc(v_messageHead_1322_);
lean_inc(v_knownSize_1321_);
lean_inc(v_outputData_1320_);
lean_inc(v_userData_1319_);
lean_dec(v_writer_1318_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = lean_box(7);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 2, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_userData_1319_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_outputData_1320_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_knownSize_1321_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_messageHead_1322_);
lean_ctor_set(v_reuseFailAlloc_1333_, 5, v_userDataBytes_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, sizeof(void*)*6, v_sentMessage_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, sizeof(void*)*6 + 1, v_userClosedBody_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, sizeof(void*)*6 + 2, v_omitBody_1325_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1336_, lean_object* v_writer_1337_){
_start:
{
uint8_t v_dir_boxed_1338_; lean_object* v_res_1339_; 
v_dir_boxed_1338_ = lean_unbox(v_dir_1336_);
v_res_1339_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1338_, v_writer_1337_);
return v_res_1339_;
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
