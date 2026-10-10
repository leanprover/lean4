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
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object* v_x_223_, lean_object* v_x_224_){
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
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_instBEqState_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_223_ = stack[0].m_obj;
lean_object* v_x_224_ = stack[1].m_obj;
uint8_t v_res_243_;
v_res_243_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_x_223_, v_x_224_);
stack->m_num = v_res_243_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_x_244_, v_x_245_);
lean_dec(v_x_245_);
lean_dec(v_x_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(lean_object* v_writer_250_){
_start:
{
lean_object* v_state_251_; 
v_state_251_ = lean_ctor_get(v_writer_250_, 2);
switch(lean_obj_tag(v_state_251_))
{
case 7:
{
uint8_t v___x_252_; 
v___x_252_ = 1;
return v___x_252_;
}
case 6:
{
uint8_t v___x_253_; 
v___x_253_ = 1;
return v___x_253_;
}
default: 
{
uint8_t v_userClosedBody_254_; 
v_userClosedBody_254_ = lean_ctor_get_uint8(v_writer_250_, sizeof(void*)*6 + 1);
return v_userClosedBody_254_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_writer_250_ = stack[0].m_obj;
uint8_t v_res_255_;
v_res_255_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_250_);
stack->m_num = v_res_255_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(lean_object* v_writer_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_256_);
lean_dec_ref(v_writer_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData(uint8_t v_dir_259_, lean_object* v_writer_260_){
_start:
{
lean_object* v_state_261_; 
v_state_261_ = lean_ctor_get(v_writer_260_, 2);
switch(lean_obj_tag(v_state_261_))
{
case 7:
{
uint8_t v___x_262_; 
v___x_262_ = 1;
return v___x_262_;
}
case 6:
{
uint8_t v___x_263_; 
v___x_263_ = 1;
return v___x_263_;
}
default: 
{
uint8_t v_userClosedBody_264_; 
v_userClosedBody_264_ = lean_ctor_get_uint8(v_writer_260_, sizeof(void*)*6 + 1);
return v_userClosedBody_264_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_noMoreUserData_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_259_ = stack[0].m_num;
lean_object* v_writer_260_ = stack[1].m_obj;
uint8_t v_res_265_;
v_res_265_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_259_, v_writer_260_);
stack->m_num = v_res_265_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(lean_object* v_dir_266_, lean_object* v_writer_267_){
_start:
{
uint8_t v_dir_boxed_268_; uint8_t v_res_269_; lean_object* v_r_270_; 
v_dir_boxed_268_ = lean_unbox(v_dir_266_);
v_res_269_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_boxed_268_, v_writer_267_);
lean_dec_ref(v_writer_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_isClosed___redArg(lean_object* v_writer_271_){
_start:
{
lean_object* v_state_272_; 
v_state_272_ = lean_ctor_get(v_writer_271_, 2);
if (lean_obj_tag(v_state_272_) == 7)
{
uint8_t v___x_273_; 
v___x_273_ = 1;
return v___x_273_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_writer_271_ = stack[0].m_obj;
uint8_t v_res_275_;
v_res_275_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_271_);
stack->m_num = v_res_275_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(lean_object* v_writer_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_276_);
lean_dec_ref(v_writer_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_isClosed(uint8_t v_dir_279_, lean_object* v_writer_280_){
_start:
{
lean_object* v_state_281_; 
v_state_281_ = lean_ctor_get(v_writer_280_, 2);
if (lean_obj_tag(v_state_281_) == 7)
{
uint8_t v___x_282_; 
v___x_282_ = 1;
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_isClosed_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_279_ = stack[0].m_num;
lean_object* v_writer_280_ = stack[1].m_obj;
uint8_t v_res_284_;
v_res_284_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_279_, v_writer_280_);
stack->m_num = v_res_284_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___boxed(lean_object* v_dir_285_, lean_object* v_writer_286_){
_start:
{
uint8_t v_dir_boxed_287_; uint8_t v_res_288_; lean_object* v_r_289_; 
v_dir_boxed_287_ = lean_unbox(v_dir_285_);
v_res_288_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_boxed_287_, v_writer_286_);
lean_dec_ref(v_writer_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_isComplete___redArg(lean_object* v_writer_290_){
_start:
{
lean_object* v_state_291_; 
v_state_291_ = lean_ctor_get(v_writer_290_, 2);
if (lean_obj_tag(v_state_291_) == 6)
{
uint8_t v___x_292_; 
v___x_292_ = 1;
return v___x_292_;
}
else
{
uint8_t v___x_293_; 
v___x_293_ = 0;
return v___x_293_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_isComplete___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_writer_290_ = stack[0].m_obj;
uint8_t v_res_294_;
v_res_294_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_290_);
stack->m_num = v_res_294_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(lean_object* v_writer_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_295_);
lean_dec_ref(v_writer_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_isComplete(uint8_t v_dir_298_, lean_object* v_writer_299_){
_start:
{
lean_object* v_state_300_; 
v_state_300_ = lean_ctor_get(v_writer_299_, 2);
if (lean_obj_tag(v_state_300_) == 6)
{
uint8_t v___x_301_; 
v___x_301_ = 1;
return v___x_301_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_isComplete_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_298_ = stack[0].m_num;
lean_object* v_writer_299_ = stack[1].m_obj;
uint8_t v_res_303_;
v_res_303_ = l_Std_Http_Protocol_H1_Writer_isComplete(v_dir_298_, v_writer_299_);
stack->m_num = v_res_303_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___boxed(lean_object* v_dir_304_, lean_object* v_writer_305_){
_start:
{
uint8_t v_dir_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_dir_boxed_306_ = lean_unbox(v_dir_304_);
v_res_307_ = l_Std_Http_Protocol_H1_Writer_isComplete(v_dir_boxed_306_, v_writer_305_);
lean_dec_ref(v_writer_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(lean_object* v_writer_309_){
_start:
{
lean_object* v_state_310_; uint8_t v_userClosedBody_311_; 
v_state_310_ = lean_ctor_get(v_writer_309_, 2);
v_userClosedBody_311_ = lean_ctor_get_uint8(v_writer_309_, sizeof(void*)*6 + 1);
switch(lean_obj_tag(v_state_310_))
{
case 1:
{
uint8_t v___x_315_; 
v___x_315_ = 1;
return v___x_315_;
}
case 2:
{
uint8_t v___x_316_; 
v___x_316_ = 1;
return v___x_316_;
}
case 3:
{
if (v_userClosedBody_311_ == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 1;
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
case 4:
{
goto v___jp_312_;
}
case 5:
{
goto v___jp_312_;
}
default: 
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
}
v___jp_312_:
{
if (v_userClosedBody_311_ == 0)
{
uint8_t v___x_313_; 
v___x_313_ = 1;
return v___x_313_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_writer_309_ = stack[0].m_obj;
uint8_t v_res_320_;
v_res_320_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_309_);
stack->m_num = v_res_320_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(lean_object* v_writer_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_321_);
lean_dec_ref(v_writer_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData(uint8_t v_dir_324_, lean_object* v_writer_325_){
_start:
{
lean_object* v_state_326_; uint8_t v_userClosedBody_327_; 
v_state_326_ = lean_ctor_get(v_writer_325_, 2);
v_userClosedBody_327_ = lean_ctor_get_uint8(v_writer_325_, sizeof(void*)*6 + 1);
switch(lean_obj_tag(v_state_326_))
{
case 1:
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
case 2:
{
uint8_t v___x_332_; 
v___x_332_ = 1;
return v___x_332_;
}
case 3:
{
if (v_userClosedBody_327_ == 0)
{
uint8_t v___x_333_; 
v___x_333_ = 1;
return v___x_333_;
}
else
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
}
}
case 4:
{
goto v___jp_328_;
}
case 5:
{
goto v___jp_328_;
}
default: 
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
}
v___jp_328_:
{
if (v_userClosedBody_327_ == 0)
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
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_canAcceptData_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_324_ = stack[0].m_num;
lean_object* v_writer_325_ = stack[1].m_obj;
uint8_t v_res_336_;
v_res_336_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_324_, v_writer_325_);
stack->m_num = v_res_336_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(lean_object* v_dir_337_, lean_object* v_writer_338_){
_start:
{
uint8_t v_dir_boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_dir_boxed_339_ = lean_unbox(v_dir_337_);
v_res_340_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_boxed_339_, v_writer_338_);
lean_dec_ref(v_writer_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___redArg(lean_object* v_writer_342_){
_start:
{
lean_object* v_userData_343_; lean_object* v_outputData_344_; lean_object* v_state_345_; lean_object* v_knownSize_346_; lean_object* v_messageHead_347_; uint8_t v_sentMessage_348_; uint8_t v_omitBody_349_; lean_object* v_userDataBytes_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_userData_343_ = lean_ctor_get(v_writer_342_, 0);
v_outputData_344_ = lean_ctor_get(v_writer_342_, 1);
v_state_345_ = lean_ctor_get(v_writer_342_, 2);
v_knownSize_346_ = lean_ctor_get(v_writer_342_, 3);
v_messageHead_347_ = lean_ctor_get(v_writer_342_, 4);
v_sentMessage_348_ = lean_ctor_get_uint8(v_writer_342_, sizeof(void*)*6);
v_omitBody_349_ = lean_ctor_get_uint8(v_writer_342_, sizeof(void*)*6 + 2);
v_userDataBytes_350_ = lean_ctor_get(v_writer_342_, 5);
v_isSharedCheck_358_ = !lean_is_exclusive(v_writer_342_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v_writer_342_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_userDataBytes_350_);
lean_inc(v_messageHead_347_);
lean_inc(v_knownSize_346_);
lean_inc(v_state_345_);
lean_inc(v_outputData_344_);
lean_inc(v_userData_343_);
lean_dec(v_writer_342_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; lean_object* v___x_356_; 
v___x_354_ = 1;
if (v_isShared_353_ == 0)
{
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_userData_343_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_outputData_344_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_state_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_knownSize_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_messageHead_347_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v_userDataBytes_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*6, v_sentMessage_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*6 + 2, v_omitBody_349_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*6 + 1, v___x_354_);
return v___x_356_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_closeBody(uint8_t v_dir_359_, lean_object* v_writer_360_){
_start:
{
lean_object* v_userData_361_; lean_object* v_outputData_362_; lean_object* v_state_363_; lean_object* v_knownSize_364_; lean_object* v_messageHead_365_; uint8_t v_sentMessage_366_; uint8_t v_omitBody_367_; lean_object* v_userDataBytes_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v_userData_361_ = lean_ctor_get(v_writer_360_, 0);
v_outputData_362_ = lean_ctor_get(v_writer_360_, 1);
v_state_363_ = lean_ctor_get(v_writer_360_, 2);
v_knownSize_364_ = lean_ctor_get(v_writer_360_, 3);
v_messageHead_365_ = lean_ctor_get(v_writer_360_, 4);
v_sentMessage_366_ = lean_ctor_get_uint8(v_writer_360_, sizeof(void*)*6);
v_omitBody_367_ = lean_ctor_get_uint8(v_writer_360_, sizeof(void*)*6 + 2);
v_userDataBytes_368_ = lean_ctor_get(v_writer_360_, 5);
v_isSharedCheck_376_ = !lean_is_exclusive(v_writer_360_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v_writer_360_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_userDataBytes_368_);
lean_inc(v_messageHead_365_);
lean_inc(v_knownSize_364_);
lean_inc(v_state_363_);
lean_inc(v_outputData_362_);
lean_inc(v_userData_361_);
lean_dec(v_writer_360_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; lean_object* v___x_374_; 
v___x_372_ = 1;
if (v_isShared_371_ == 0)
{
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_userData_361_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_outputData_362_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_state_363_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_knownSize_364_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_messageHead_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 5, v_userDataBytes_368_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, sizeof(void*)*6, v_sentMessage_366_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, sizeof(void*)*6 + 2, v_omitBody_367_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*6 + 1, v___x_372_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_closeBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_359_ = stack[0].m_num;
lean_object* v_writer_360_ = stack[1].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_359_, v_writer_360_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___boxed(lean_object* v_dir_378_, lean_object* v_writer_379_){
_start:
{
uint8_t v_dir_boxed_380_; lean_object* v_res_381_; 
v_dir_boxed_380_ = lean_unbox(v_dir_378_);
v_res_381_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_boxed_380_, v_writer_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(lean_object* v_writer_382_){
_start:
{
lean_object* v_knownSize_383_; 
v_knownSize_383_ = lean_ctor_get(v_writer_382_, 3);
if (lean_obj_tag(v_knownSize_383_) == 1)
{
lean_object* v_val_384_; 
v_val_384_ = lean_ctor_get(v_knownSize_383_, 0);
lean_inc(v_val_384_);
return v_val_384_;
}
else
{
uint8_t v_userClosedBody_385_; 
v_userClosedBody_385_ = lean_ctor_get_uint8(v_writer_382_, sizeof(void*)*6 + 1);
if (v_userClosedBody_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v_userDataBytes_387_; lean_object* v___x_388_; 
v_userDataBytes_387_ = lean_ctor_get(v_writer_382_, 5);
lean_inc(v_userDataBytes_387_);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v_userDataBytes_387_);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(lean_object* v_writer_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_389_);
lean_dec_ref(v_writer_389_);
return v_res_390_;
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode(uint8_t v_dir_391_, lean_object* v_writer_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_392_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_determineTransferMode_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_391_ = stack[0].m_num;
lean_object* v_writer_392_ = stack[1].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_391_, v_writer_392_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(lean_object* v_dir_395_, lean_object* v_writer_396_){
_start:
{
uint8_t v_dir_boxed_397_; lean_object* v_res_398_; 
v_dir_boxed_397_ = lean_unbox(v_dir_395_);
v_res_398_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_boxed_397_, v_writer_396_);
lean_dec_ref(v_writer_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(lean_object* v_x1_399_, lean_object* v_x2_400_){
_start:
{
lean_object* v_data_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_data_401_ = lean_ctor_get(v_x2_400_, 0);
v___x_402_ = lean_byte_array_size(v_data_401_);
v___x_403_ = lean_nat_add(v_x1_399_, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(lean_object* v_x1_404_, lean_object* v_x2_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(v_x1_404_, v_x2_405_);
lean_dec_ref(v_x2_405_);
lean_dec(v_x1_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg(lean_object* v_data_427_, lean_object* v_writer_428_){
_start:
{
lean_object* v_userData_429_; lean_object* v_outputData_430_; lean_object* v_state_431_; lean_object* v_knownSize_432_; lean_object* v_messageHead_433_; uint8_t v_sentMessage_434_; uint8_t v_userClosedBody_435_; uint8_t v_omitBody_436_; lean_object* v_userDataBytes_437_; lean_object* v___y_439_; lean_object* v___f_443_; 
v_userData_429_ = lean_ctor_get(v_writer_428_, 0);
v_outputData_430_ = lean_ctor_get(v_writer_428_, 1);
v_state_431_ = lean_ctor_get(v_writer_428_, 2);
v_knownSize_432_ = lean_ctor_get(v_writer_428_, 3);
v_messageHead_433_ = lean_ctor_get(v_writer_428_, 4);
v_sentMessage_434_ = lean_ctor_get_uint8(v_writer_428_, sizeof(void*)*6);
v_userClosedBody_435_ = lean_ctor_get_uint8(v_writer_428_, sizeof(void*)*6 + 1);
v_omitBody_436_ = lean_ctor_get_uint8(v_writer_428_, sizeof(void*)*6 + 2);
v_userDataBytes_437_ = lean_ctor_get(v_writer_428_, 5);
v___f_443_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_431_))
{
case 1:
{
lean_inc(v_state_431_);
lean_inc(v_userDataBytes_437_);
lean_inc(v_messageHead_433_);
lean_inc(v_knownSize_432_);
lean_inc_ref(v_outputData_430_);
lean_inc_ref(v_userData_429_);
lean_dec_ref(v_writer_428_);
goto v___jp_444_;
}
case 2:
{
lean_inc(v_state_431_);
lean_inc(v_userDataBytes_437_);
lean_inc(v_messageHead_433_);
lean_inc(v_knownSize_432_);
lean_inc_ref(v_outputData_430_);
lean_inc_ref(v_userData_429_);
lean_dec_ref(v_writer_428_);
goto v___jp_444_;
}
case 3:
{
if (v_userClosedBody_435_ == 0)
{
lean_inc_ref(v_state_431_);
lean_inc(v_userDataBytes_437_);
lean_inc(v_messageHead_433_);
lean_inc(v_knownSize_432_);
lean_inc_ref(v_outputData_430_);
lean_inc_ref(v_userData_429_);
lean_dec_ref(v_writer_428_);
goto v___jp_444_;
}
else
{
lean_dec_ref(v_data_427_);
return v_writer_428_;
}
}
case 4:
{
goto v___jp_456_;
}
case 5:
{
goto v___jp_456_;
}
default: 
{
lean_dec_ref(v_data_427_);
return v_writer_428_;
}
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = l_Array_append___redArg(v_userData_429_, v_data_427_);
lean_dec_ref(v_data_427_);
v___x_441_ = lean_nat_add(v_userDataBytes_437_, v___y_439_);
lean_dec(v___y_439_);
lean_dec(v_userDataBytes_437_);
v___x_442_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v_outputData_430_);
lean_ctor_set(v___x_442_, 2, v_state_431_);
lean_ctor_set(v___x_442_, 3, v_knownSize_432_);
lean_ctor_set(v___x_442_, 4, v_messageHead_433_);
lean_ctor_set(v___x_442_, 5, v___x_441_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*6, v_sentMessage_434_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*6 + 1, v_userClosedBody_435_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*6 + 2, v_omitBody_436_);
return v___x_442_;
}
v___jp_444_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_array_get_size(v_data_427_);
v___x_447_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_448_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_448_ == 0)
{
v___y_439_ = v___x_445_;
goto v___jp_438_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_le(v___x_446_, v___x_446_);
if (v___x_449_ == 0)
{
if (v___x_448_ == 0)
{
v___y_439_ = v___x_445_;
goto v___jp_438_;
}
else
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((size_t)0ULL);
v___x_451_ = lean_usize_of_nat(v___x_446_);
lean_inc_ref(v_data_427_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_447_, v___f_443_, v_data_427_, v___x_450_, v___x_451_, v___x_445_);
v___y_439_ = v___x_452_;
goto v___jp_438_;
}
}
else
{
size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((size_t)0ULL);
v___x_454_ = lean_usize_of_nat(v___x_446_);
lean_inc_ref(v_data_427_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_447_, v___f_443_, v_data_427_, v___x_453_, v___x_454_, v___x_445_);
v___y_439_ = v___x_455_;
goto v___jp_438_;
}
}
}
v___jp_456_:
{
if (v_userClosedBody_435_ == 0)
{
lean_inc(v_userDataBytes_437_);
lean_inc(v_messageHead_433_);
lean_inc(v_knownSize_432_);
lean_inc(v_state_431_);
lean_inc_ref(v_outputData_430_);
lean_inc_ref(v_userData_429_);
lean_dec_ref(v_writer_428_);
goto v___jp_444_;
}
else
{
lean_dec_ref(v_data_427_);
return v_writer_428_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_457_, lean_object* v_data_458_, lean_object* v_writer_459_){
_start:
{
lean_object* v_userData_460_; lean_object* v_outputData_461_; lean_object* v_state_462_; lean_object* v_knownSize_463_; lean_object* v_messageHead_464_; uint8_t v_sentMessage_465_; uint8_t v_userClosedBody_466_; uint8_t v_omitBody_467_; lean_object* v_userDataBytes_468_; lean_object* v___y_470_; lean_object* v___f_474_; 
v_userData_460_ = lean_ctor_get(v_writer_459_, 0);
v_outputData_461_ = lean_ctor_get(v_writer_459_, 1);
v_state_462_ = lean_ctor_get(v_writer_459_, 2);
v_knownSize_463_ = lean_ctor_get(v_writer_459_, 3);
v_messageHead_464_ = lean_ctor_get(v_writer_459_, 4);
v_sentMessage_465_ = lean_ctor_get_uint8(v_writer_459_, sizeof(void*)*6);
v_userClosedBody_466_ = lean_ctor_get_uint8(v_writer_459_, sizeof(void*)*6 + 1);
v_omitBody_467_ = lean_ctor_get_uint8(v_writer_459_, sizeof(void*)*6 + 2);
v_userDataBytes_468_ = lean_ctor_get(v_writer_459_, 5);
v___f_474_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_462_))
{
case 1:
{
lean_inc(v_state_462_);
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_464_);
lean_inc(v_knownSize_463_);
lean_inc_ref(v_outputData_461_);
lean_inc_ref(v_userData_460_);
lean_dec_ref(v_writer_459_);
goto v___jp_475_;
}
case 2:
{
lean_inc(v_state_462_);
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_464_);
lean_inc(v_knownSize_463_);
lean_inc_ref(v_outputData_461_);
lean_inc_ref(v_userData_460_);
lean_dec_ref(v_writer_459_);
goto v___jp_475_;
}
case 3:
{
if (v_userClosedBody_466_ == 0)
{
lean_inc_ref(v_state_462_);
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_464_);
lean_inc(v_knownSize_463_);
lean_inc_ref(v_outputData_461_);
lean_inc_ref(v_userData_460_);
lean_dec_ref(v_writer_459_);
goto v___jp_475_;
}
else
{
lean_dec_ref(v_data_458_);
return v_writer_459_;
}
}
case 4:
{
goto v___jp_487_;
}
case 5:
{
goto v___jp_487_;
}
default: 
{
lean_dec_ref(v_data_458_);
return v_writer_459_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = l_Array_append___redArg(v_userData_460_, v_data_458_);
lean_dec_ref(v_data_458_);
v___x_472_ = lean_nat_add(v_userDataBytes_468_, v___y_470_);
lean_dec(v___y_470_);
lean_dec(v_userDataBytes_468_);
v___x_473_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v_outputData_461_);
lean_ctor_set(v___x_473_, 2, v_state_462_);
lean_ctor_set(v___x_473_, 3, v_knownSize_463_);
lean_ctor_set(v___x_473_, 4, v_messageHead_464_);
lean_ctor_set(v___x_473_, 5, v___x_472_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*6, v_sentMessage_465_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*6 + 1, v_userClosedBody_466_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*6 + 2, v_omitBody_467_);
return v___x_473_;
}
v___jp_475_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_array_get_size(v_data_458_);
v___x_478_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_479_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_479_ == 0)
{
v___y_470_ = v___x_476_;
goto v___jp_469_;
}
else
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_le(v___x_477_, v___x_477_);
if (v___x_480_ == 0)
{
if (v___x_479_ == 0)
{
v___y_470_ = v___x_476_;
goto v___jp_469_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_477_);
lean_inc_ref(v_data_458_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_478_, v___f_474_, v_data_458_, v___x_481_, v___x_482_, v___x_476_);
v___y_470_ = v___x_483_;
goto v___jp_469_;
}
}
else
{
size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((size_t)0ULL);
v___x_485_ = lean_usize_of_nat(v___x_477_);
lean_inc_ref(v_data_458_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_478_, v___f_474_, v_data_458_, v___x_484_, v___x_485_, v___x_476_);
v___y_470_ = v___x_486_;
goto v___jp_469_;
}
}
}
v___jp_487_:
{
if (v_userClosedBody_466_ == 0)
{
lean_inc(v_userDataBytes_468_);
lean_inc(v_messageHead_464_);
lean_inc(v_knownSize_463_);
lean_inc(v_state_462_);
lean_inc_ref(v_outputData_461_);
lean_inc_ref(v_userData_460_);
lean_dec_ref(v_writer_459_);
goto v___jp_475_;
}
else
{
lean_dec_ref(v_data_458_);
return v_writer_459_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_addUserData_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_457_ = stack[0].m_num;
lean_object* v_data_458_ = stack[1].m_obj;
lean_object* v_writer_459_ = stack[2].m_obj;
lean_object* v_res_488_;
v_res_488_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_457_, v_data_458_, v_writer_459_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object* v_dir_489_, lean_object* v_data_490_, lean_object* v_writer_491_){
_start:
{
uint8_t v_dir_boxed_492_; lean_object* v_res_493_; 
v_dir_boxed_492_ = lean_unbox(v_dir_489_);
v_res_493_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_492_, v_data_490_, v_writer_491_);
return v_res_493_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object* v_limitSize_494_, lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_){
_start:
{
lean_object* v___y_500_; uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_504_ == 0)
{
lean_object* v_snd_505_; lean_object* v_fst_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_562_; 
v_snd_505_ = lean_ctor_get(v_b_498_, 1);
v_fst_506_ = lean_ctor_get(v_b_498_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_b_498_);
if (v_isSharedCheck_562_ == 0)
{
v___x_508_ = v_b_498_;
v_isShared_509_ = v_isSharedCheck_562_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_506_);
lean_dec(v_b_498_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_562_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_561_; 
v_fst_510_ = lean_ctor_get(v_snd_505_, 0);
v_snd_511_ = lean_ctor_get(v_snd_505_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_snd_505_);
if (v_isSharedCheck_561_ == 0)
{
v___x_513_ = v_snd_505_;
v_isShared_514_ = v_isSharedCheck_561_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_snd_511_);
lean_inc(v_fst_510_);
lean_dec(v_snd_505_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_561_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_uget(v_as_495_, v_i_496_);
v___x_516_ = lean_nat_dec_le(v_limitSize_494_, v_snd_511_);
if (v___x_516_ == 0)
{
lean_object* v_data_517_; lean_object* v_extensions_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_553_; 
v_data_517_ = lean_ctor_get(v___x_515_, 0);
v_extensions_518_ = lean_ctor_get(v___x_515_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_553_ == 0)
{
v___x_520_ = v___x_515_;
v_isShared_521_ = v_isSharedCheck_553_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_extensions_518_);
lean_inc(v_data_517_);
lean_dec(v___x_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_553_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v_remaining_523_; lean_object* v___x_524_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_548_; uint8_t v___x_552_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v_remaining_523_ = lean_nat_sub(v_limitSize_494_, v_snd_511_);
v___x_524_ = lean_byte_array_size(v_data_517_);
v___x_552_ = lean_nat_dec_le(v___x_524_, v_remaining_523_);
if (v___x_552_ == 0)
{
v___y_548_ = v_remaining_523_;
goto v___jp_547_;
}
else
{
lean_dec(v_remaining_523_);
v___y_548_ = v___x_524_;
goto v___jp_547_;
}
v___jp_525_:
{
lean_object* v_size_528_; uint8_t v___x_529_; 
v_size_528_ = lean_nat_add(v_snd_511_, v___y_526_);
lean_dec(v_snd_511_);
v___x_529_ = lean_nat_dec_lt(v___y_526_, v___x_524_);
if (v___x_529_ == 0)
{
lean_object* v___x_531_; 
lean_dec(v___y_526_);
lean_del_object(v___x_520_);
lean_dec_ref(v_extensions_518_);
lean_dec_ref(v_data_517_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_size_528_);
v___x_531_ = v___x_513_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_fst_510_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_size_528_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_531_);
lean_ctor_set(v___x_508_, 0, v___y_527_);
v___x_533_ = v___x_508_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___y_527_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v___y_500_ = v___x_533_;
goto v___jp_499_;
}
}
}
else
{
lean_object* v___x_536_; lean_object* v_pendingChunk_538_; 
v___x_536_ = l_ByteArray_extract(v_data_517_, v___y_526_, v___x_524_);
lean_dec_ref(v_data_517_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_536_);
v_pendingChunk_538_ = v___x_520_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_extensions_518_);
v_pendingChunk_538_ = v_reuseFailAlloc_546_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = lean_array_push(v_fst_510_, v_pendingChunk_538_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_size_528_);
lean_ctor_set(v___x_513_, 0, v___x_539_);
v___x_541_ = v___x_513_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_size_528_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_541_);
lean_ctor_set(v___x_508_, 0, v___y_527_);
v___x_543_ = v___x_508_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___y_527_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
v___y_500_ = v___x_543_;
goto v___jp_499_;
}
}
}
}
}
v___jp_547_:
{
uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_eq(v___y_548_, v___x_522_);
if (v___x_549_ == 0)
{
lean_object* v_dataPart_550_; lean_object* v___x_551_; 
v_dataPart_550_ = l_ByteArray_extract(v_data_517_, v___x_522_, v___y_548_);
v___x_551_ = lean_array_push(v_fst_506_, v_dataPart_550_);
v___y_526_ = v___y_548_;
v___y_527_ = v___x_551_;
goto v___jp_525_;
}
else
{
v___y_526_ = v___y_548_;
v___y_527_ = v_fst_506_;
goto v___jp_525_;
}
}
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_array_push(v_fst_510_, v___x_515_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_554_);
v___x_556_ = v___x_513_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_snd_511_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_556_);
v___x_558_ = v___x_508_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_fst_506_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v___y_500_ = v___x_558_;
goto v___jp_499_;
}
}
}
}
}
}
else
{
return v_b_498_;
}
v___jp_499_:
{
size_t v___x_501_; size_t v___x_502_; 
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_496_, v___x_501_);
v_i_496_ = v___x_502_;
v_b_498_ = v___y_500_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_limitSize_494_ = stack[0].m_obj;
lean_object* v_as_495_ = stack[1].m_obj;
size_t v_i_496_ = stack[2].m_num;
size_t v_stop_497_ = stack[3].m_num;
lean_object* v_b_498_ = stack[4].m_obj;
lean_object* v_res_563_;
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_494_, v_as_495_, v_i_496_, v_stop_497_, v_b_498_);
stack->m_obj
 = v_res_563_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_564_, lean_object* v_as_565_, lean_object* v_i_566_, lean_object* v_stop_567_, lean_object* v_b_568_){
_start:
{
size_t v_i_boxed_569_; size_t v_stop_boxed_570_; lean_object* v_res_571_; 
v_i_boxed_569_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_stop_boxed_570_ = lean_unbox_usize(v_stop_567_);
lean_dec(v_stop_567_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_564_, v_as_565_, v_i_boxed_569_, v_stop_boxed_570_, v_b_568_);
lean_dec_ref(v_as_565_);
lean_dec(v_limitSize_564_);
return v_res_571_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_572_, size_t v_i_573_, size_t v_stop_574_, lean_object* v_b_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_eq(v_i_573_, v_stop_574_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; size_t v___x_580_; size_t v___x_581_; 
v___x_577_ = lean_array_uget_borrowed(v_as_572_, v_i_573_);
v___x_578_ = lean_byte_array_size(v___x_577_);
v___x_579_ = lean_nat_add(v_b_575_, v___x_578_);
lean_dec(v_b_575_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_573_, v___x_580_);
v_i_573_ = v___x_581_;
v_b_575_ = v___x_579_;
goto _start;
}
else
{
return v_b_575_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_572_ = stack[0].m_obj;
size_t v_i_573_ = stack[1].m_num;
size_t v_stop_574_ = stack[2].m_num;
lean_object* v_b_575_ = stack[3].m_obj;
lean_object* v_res_583_;
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_572_, v_i_573_, v_stop_574_, v_b_575_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_584_, lean_object* v_i_585_, lean_object* v_stop_586_, lean_object* v_b_587_){
_start:
{
size_t v_i_boxed_588_; size_t v_stop_boxed_589_; lean_object* v_res_590_; 
v_i_boxed_588_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_stop_boxed_589_ = lean_unbox_usize(v_stop_586_);
lean_dec(v_stop_586_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_584_, v_i_boxed_588_, v_stop_boxed_589_, v_b_587_);
lean_dec_ref(v_as_584_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_599_, lean_object* v_limitSize_600_){
_start:
{
lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; uint8_t v___y_606_; uint8_t v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v_userData_636_; lean_object* v_outputData_637_; lean_object* v_state_638_; lean_object* v_knownSize_639_; lean_object* v_messageHead_640_; uint8_t v_sentMessage_641_; uint8_t v_userClosedBody_642_; uint8_t v_omitBody_643_; lean_object* v_userDataBytes_644_; lean_object* v_fst_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___y_658_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_userData_636_ = lean_ctor_get(v_writer_599_, 0);
v_outputData_637_ = lean_ctor_get(v_writer_599_, 1);
v_state_638_ = lean_ctor_get(v_writer_599_, 2);
v_knownSize_639_ = lean_ctor_get(v_writer_599_, 3);
v_messageHead_640_ = lean_ctor_get(v_writer_599_, 4);
v_sentMessage_641_ = lean_ctor_get_uint8(v_writer_599_, sizeof(void*)*6);
v_userClosedBody_642_ = lean_ctor_get_uint8(v_writer_599_, sizeof(void*)*6 + 1);
v_omitBody_643_ = lean_ctor_get_uint8(v_writer_599_, sizeof(void*)*6 + 2);
v_userDataBytes_644_ = lean_ctor_get(v_writer_599_, 5);
v___x_663_ = lean_array_get_size(v_userData_636_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_nat_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
lean_inc(v_userDataBytes_644_);
lean_inc(v_messageHead_640_);
lean_inc(v_knownSize_639_);
lean_inc(v_state_638_);
lean_inc_ref(v_outputData_637_);
lean_inc_ref(v_userData_636_);
lean_dec_ref(v_writer_599_);
v___x_666_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_667_ = lean_nat_dec_lt(v___x_664_, v___x_663_);
if (v___x_667_ == 0)
{
lean_dec_ref(v_userData_636_);
v_fst_646_ = v___x_666_;
v_fst_647_ = v___x_666_;
v_snd_648_ = v___x_664_;
goto v___jp_645_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_669_ = lean_nat_dec_le(v___x_663_, v___x_663_);
if (v___x_669_ == 0)
{
if (v___x_667_ == 0)
{
lean_dec_ref(v_userData_636_);
v_fst_646_ = v___x_666_;
v_fst_647_ = v___x_666_;
v_snd_648_ = v___x_664_;
goto v___jp_645_;
}
else
{
size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((size_t)0ULL);
v___x_671_ = lean_usize_of_nat(v___x_663_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_600_, v_userData_636_, v___x_670_, v___x_671_, v___x_668_);
lean_dec_ref(v_userData_636_);
v___y_658_ = v___x_672_;
goto v___jp_657_;
}
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_663_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_600_, v_userData_636_, v___x_673_, v___x_674_, v___x_668_);
lean_dec_ref(v_userData_636_);
v___y_658_ = v___x_675_;
goto v___jp_657_;
}
}
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_writer_599_);
lean_ctor_set(v___x_676_, 1, v_limitSize_600_);
return v___x_676_;
}
v___jp_601_:
{
lean_object* v_data_613_; lean_object* v_size_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_635_; 
v_data_613_ = lean_ctor_get(v___y_604_, 0);
v_size_614_ = lean_ctor_get(v___y_604_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_604_);
if (v_isSharedCheck_635_ == 0)
{
v___x_616_ = v___y_604_;
v_isShared_617_ = v_isSharedCheck_635_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_size_614_);
lean_inc(v_data_613_);
lean_dec(v___y_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_635_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_data_618_; lean_object* v_size_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_634_; 
v_data_618_ = lean_ctor_get(v___y_612_, 0);
v_size_619_ = lean_ctor_get(v___y_612_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___y_612_);
if (v_isSharedCheck_634_ == 0)
{
v___x_621_ = v___y_612_;
v_isShared_622_ = v_isSharedCheck_634_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_size_619_);
lean_inc(v_data_618_);
lean_dec(v___y_612_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_634_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_outputData_626_; 
v___x_623_ = l_Array_append___redArg(v_data_613_, v_data_618_);
lean_dec_ref(v_data_618_);
v___x_624_ = lean_nat_add(v_size_614_, v_size_619_);
lean_dec(v_size_619_);
lean_dec(v_size_614_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_624_);
lean_ctor_set(v___x_621_, 0, v___x_623_);
v_outputData_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_624_);
v_outputData_626_ = v_reuseFailAlloc_633_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v_remaining_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v_remaining_627_ = lean_nat_sub(v_limitSize_600_, v___y_603_);
lean_dec(v_limitSize_600_);
v___x_628_ = lean_nat_sub(v___y_608_, v___y_603_);
lean_dec(v___y_603_);
lean_dec(v___y_608_);
v___x_629_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_629_, 0, v___y_611_);
lean_ctor_set(v___x_629_, 1, v_outputData_626_);
lean_ctor_set(v___x_629_, 2, v___y_605_);
lean_ctor_set(v___x_629_, 3, v___y_609_);
lean_ctor_set(v___x_629_, 4, v___y_602_);
lean_ctor_set(v___x_629_, 5, v___x_628_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*6, v___y_610_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*6 + 1, v___y_607_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*6 + 2, v___y_606_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_remaining_627_);
lean_ctor_set(v___x_616_, 0, v___x_629_);
v___x_631_ = v___x_616_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_remaining_627_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
v___jp_645_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_fst_646_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_fst_646_);
lean_ctor_set(v___x_652_, 1, v___x_649_);
v___y_602_ = v_messageHead_640_;
v___y_603_ = v_snd_648_;
v___y_604_ = v_outputData_637_;
v___y_605_ = v_state_638_;
v___y_606_ = v_omitBody_643_;
v___y_607_ = v_userClosedBody_642_;
v___y_608_ = v_userDataBytes_644_;
v___y_609_ = v_knownSize_639_;
v___y_610_ = v_sentMessage_641_;
v___y_611_ = v_fst_647_;
v___y_612_ = v___x_652_;
goto v___jp_601_;
}
else
{
size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = ((size_t)0ULL);
v___x_654_ = lean_usize_of_nat(v___x_650_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_646_, v___x_653_, v___x_654_, v___x_649_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_fst_646_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___y_602_ = v_messageHead_640_;
v___y_603_ = v_snd_648_;
v___y_604_ = v_outputData_637_;
v___y_605_ = v_state_638_;
v___y_606_ = v_omitBody_643_;
v___y_607_ = v_userClosedBody_642_;
v___y_608_ = v_userDataBytes_644_;
v___y_609_ = v_knownSize_639_;
v___y_610_ = v_sentMessage_641_;
v___y_611_ = v_fst_647_;
v___y_612_ = v___x_656_;
goto v___jp_601_;
}
}
v___jp_657_:
{
lean_object* v_snd_659_; lean_object* v_fst_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; 
v_snd_659_ = lean_ctor_get(v___y_658_, 1);
lean_inc(v_snd_659_);
v_fst_660_ = lean_ctor_get(v___y_658_, 0);
lean_inc(v_fst_660_);
lean_dec_ref(v___y_658_);
v_fst_661_ = lean_ctor_get(v_snd_659_, 0);
lean_inc(v_fst_661_);
v_snd_662_ = lean_ctor_get(v_snd_659_, 1);
lean_inc(v_snd_662_);
lean_dec(v_snd_659_);
v_fst_646_ = v_fst_660_;
v_fst_647_ = v_fst_661_;
v_snd_648_ = v_snd_662_;
goto v___jp_645_;
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_677_, lean_object* v_writer_678_, lean_object* v_limitSize_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_678_, v_limitSize_679_);
return v___x_680_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_writeFixedBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_677_ = stack[0].m_num;
lean_object* v_writer_678_ = stack[1].m_obj;
lean_object* v_limitSize_679_ = stack[2].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_677_, v_writer_678_, v_limitSize_679_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_682_, lean_object* v_writer_683_, lean_object* v_limitSize_684_){
_start:
{
uint8_t v_dir_boxed_685_; lean_object* v_res_686_; 
v_dir_boxed_685_ = lean_unbox(v_dir_682_);
v_res_686_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_685_, v_writer_683_, v_limitSize_684_);
return v_res_686_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_687_, size_t v_i_688_, size_t v_stop_689_, lean_object* v_b_690_){
_start:
{
lean_object* v___y_692_; uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_eq(v_i_688_, v_stop_689_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v_data_698_; uint8_t v___x_699_; 
v___x_697_ = lean_array_uget_borrowed(v_as_687_, v_i_688_);
v_data_698_ = lean_ctor_get(v___x_697_, 0);
v___x_699_ = l_ByteArray_isEmpty(v_data_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_inc(v___x_697_);
v___x_700_ = lean_array_push(v_b_690_, v___x_697_);
v___y_692_ = v___x_700_;
goto v___jp_691_;
}
else
{
v___y_692_ = v_b_690_;
goto v___jp_691_;
}
}
else
{
return v_b_690_;
}
v___jp_691_:
{
size_t v___x_693_; size_t v___x_694_; 
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_add(v_i_688_, v___x_693_);
v_i_688_ = v___x_694_;
v_b_690_ = v___y_692_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_687_ = stack[0].m_obj;
size_t v_i_688_ = stack[1].m_num;
size_t v_stop_689_ = stack[2].m_num;
lean_object* v_b_690_ = stack[3].m_obj;
lean_object* v_res_701_;
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_687_, v_i_688_, v_stop_689_, v_b_690_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_702_, lean_object* v_i_703_, lean_object* v_stop_704_, lean_object* v_b_705_){
_start:
{
size_t v_i_boxed_706_; size_t v_stop_boxed_707_; lean_object* v_res_708_; 
v_i_boxed_706_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_stop_boxed_707_ = lean_unbox_usize(v_stop_704_);
lean_dec(v_stop_704_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_702_, v_i_boxed_706_, v_stop_boxed_707_, v_b_705_);
lean_dec_ref(v_as_702_);
return v_res_708_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_709_, size_t v_i_710_, lean_object* v_bs_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_lt(v_i_710_, v_sz_709_);
if (v___x_712_ == 0)
{
return v_bs_711_;
}
else
{
lean_object* v_v_713_; lean_object* v___x_714_; lean_object* v_bs_x27_715_; uint32_t v___x_716_; uint8_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_v_713_ = lean_array_uget(v_bs_711_, v_i_710_);
v___x_714_ = lean_unsigned_to_nat(0u);
v_bs_x27_715_ = lean_array_uset(v_bs_711_, v_i_710_, v___x_714_);
v___x_716_ = lean_unbox_uint32(v_v_713_);
lean_dec(v_v_713_);
v___x_717_ = lean_uint32_to_uint8(v___x_716_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_710_, v___x_718_);
v___x_720_ = lean_box(v___x_717_);
v___x_721_ = lean_array_uset(v_bs_x27_715_, v_i_710_, v___x_720_);
v_i_710_ = v___x_719_;
v_bs_711_ = v___x_721_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_709_ = stack[0].m_num;
size_t v_i_710_ = stack[1].m_num;
lean_object* v_bs_711_ = stack[2].m_obj;
lean_object* v_res_723_;
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_709_, v_i_710_, v_bs_711_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_724_, lean_object* v_i_725_, lean_object* v_bs_726_){
_start:
{
size_t v_sz_boxed_727_; size_t v_i_boxed_728_; lean_object* v_res_729_; 
v_sz_boxed_727_ = lean_unbox_usize(v_sz_724_);
lean_dec(v_sz_724_);
v_i_boxed_728_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_727_, v_i_boxed_728_, v_bs_726_);
return v_res_729_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_732_, size_t v_i_733_, size_t v_stop_734_, lean_object* v_b_735_){
_start:
{
lean_object* v___y_737_; uint8_t v___x_741_; 
v___x_741_ = lean_usize_dec_eq(v_i_733_, v_stop_734_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_742_ = lean_array_uget_borrowed(v_as_732_, v_i_733_);
v_fst_743_ = lean_ctor_get(v___x_742_, 0);
v_snd_744_ = lean_ctor_get(v___x_742_, 1);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_746_ = lean_string_append(v_b_735_, v___x_745_);
v___x_747_ = lean_string_append(v___x_746_, v_fst_743_);
if (lean_obj_tag(v_snd_744_) == 0)
{
v___y_737_ = v___x_747_;
goto v___jp_736_;
}
else
{
lean_object* v_val_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_val_748_ = lean_ctor_get(v_snd_744_, 0);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_748_);
v___x_750_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_748_);
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_string_append(v___x_747_, v___x_751_);
lean_dec_ref(v___x_751_);
v___y_737_ = v___x_752_;
goto v___jp_736_;
}
}
else
{
return v_b_735_;
}
v___jp_736_:
{
size_t v___x_738_; size_t v___x_739_; 
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_add(v_i_733_, v___x_738_);
v_i_733_ = v___x_739_;
v_b_735_ = v___y_737_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_732_ = stack[0].m_obj;
size_t v_i_733_ = stack[1].m_num;
size_t v_stop_734_ = stack[2].m_num;
lean_object* v_b_735_ = stack[3].m_obj;
lean_object* v_res_753_;
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_732_, v_i_733_, v_stop_734_, v_b_735_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_754_, lean_object* v_i_755_, lean_object* v_stop_756_, lean_object* v_b_757_){
_start:
{
size_t v_i_boxed_758_; size_t v_stop_boxed_759_; lean_object* v_res_760_; 
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_stop_boxed_759_ = lean_unbox_usize(v_stop_756_);
lean_dec(v_stop_756_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_754_, v_i_boxed_758_, v_stop_boxed_759_, v_b_757_);
lean_dec_ref(v_as_754_);
return v_res_760_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_763_ = lean_string_to_utf8(v___x_762_);
return v___x_763_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_765_, size_t v_i_766_, size_t v_stop_767_, lean_object* v_b_768_){
_start:
{
lean_object* v___y_770_; uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_eq(v_i_766_, v_stop_767_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v_data_789_; lean_object* v_extensions_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_831_; 
v___x_788_ = lean_array_uget(v_as_765_, v_i_766_);
v_data_789_ = lean_ctor_get(v___x_788_, 0);
v_extensions_790_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_831_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_831_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_extensions_790_);
lean_inc(v_data_789_);
lean_dec(v___x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_831_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_chunkLen_794_; lean_object* v___y_796_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_chunkLen_794_ = lean_byte_array_size(v_data_789_);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_array_get_size(v_extensions_790_);
v___x_827_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_dec_ref(v_extensions_790_);
v___y_796_ = v___x_824_;
goto v___jp_795_;
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_826_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_790_, v___x_828_, v___x_829_, v___x_824_);
lean_dec_ref(v_extensions_790_);
v___y_796_ = v___x_830_;
goto v___jp_795_;
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v_size_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_797_ = lean_unsigned_to_nat(16u);
v___x_798_ = l_Nat_toDigits(v___x_797_, v_chunkLen_794_);
v___x_799_ = lean_array_mk(v___x_798_);
v_sz_800_ = lean_array_size(v___x_799_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_800_, v___x_801_, v___x_799_);
v_size_803_ = lean_byte_array_mk(v___x_802_);
v___x_804_ = lean_string_to_utf8(v___y_796_);
lean_dec_ref(v___y_796_);
v___x_805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_806_ = lean_unsigned_to_nat(5u);
v___x_807_ = lean_mk_empty_array_with_capacity(v___x_806_);
v___x_808_ = lean_array_push(v___x_807_, v_size_803_);
v___x_809_ = lean_array_push(v___x_808_, v___x_804_);
v___x_810_ = lean_array_push(v___x_809_, v___x_805_);
v___x_811_ = lean_array_push(v___x_810_, v_data_789_);
v___x_812_ = lean_array_push(v___x_811_, v___x_805_);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_array_get_size(v___x_812_);
v___x_815_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_817_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_813_);
lean_ctor_set(v___x_792_, 0, v___x_812_);
v___x_817_ = v___x_792_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_813_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_770_ = v___x_817_;
goto v___jp_769_;
}
}
else
{
size_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = lean_usize_of_nat(v___x_814_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_812_, v___x_801_, v___x_819_, v___x_813_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_820_);
lean_ctor_set(v___x_792_, 0, v___x_812_);
v___x_822_ = v___x_792_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v___y_770_ = v___x_822_;
goto v___jp_769_;
}
}
}
}
}
else
{
return v_b_768_;
}
v___jp_769_:
{
lean_object* v_data_771_; lean_object* v_size_772_; lean_object* v_data_773_; lean_object* v_size_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
v_data_771_ = lean_ctor_get(v_b_768_, 0);
lean_inc_ref(v_data_771_);
v_size_772_ = lean_ctor_get(v_b_768_, 1);
lean_inc(v_size_772_);
lean_dec_ref(v_b_768_);
v_data_773_ = lean_ctor_get(v___y_770_, 0);
v_size_774_ = lean_ctor_get(v___y_770_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___y_770_);
if (v_isSharedCheck_786_ == 0)
{
v___x_776_ = v___y_770_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_size_774_);
lean_inc(v_data_773_);
lean_dec(v___y_770_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = l_Array_append___redArg(v_data_771_, v_data_773_);
lean_dec_ref(v_data_773_);
v___x_779_ = lean_nat_add(v_size_772_, v_size_774_);
lean_dec(v_size_774_);
lean_dec(v_size_772_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_779_);
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
size_t v___x_782_; size_t v___x_783_; 
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_add(v_i_766_, v___x_782_);
v_i_766_ = v___x_783_;
v_b_768_ = v___x_781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_765_ = stack[0].m_obj;
size_t v_i_766_ = stack[1].m_num;
size_t v_stop_767_ = stack[2].m_num;
lean_object* v_b_768_ = stack[3].m_obj;
lean_object* v_res_832_;
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_765_, v_i_766_, v_stop_767_, v_b_768_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_833_, lean_object* v_i_834_, lean_object* v_stop_835_, lean_object* v_b_836_){
_start:
{
size_t v_i_boxed_837_; size_t v_stop_boxed_838_; lean_object* v_res_839_; 
v_i_boxed_837_ = lean_unbox_usize(v_i_834_);
lean_dec(v_i_834_);
v_stop_boxed_838_ = lean_unbox_usize(v_stop_835_);
lean_dec(v_stop_835_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_833_, v_i_boxed_837_, v_stop_boxed_838_, v_b_836_);
lean_dec_ref(v_as_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_842_){
_start:
{
lean_object* v_userData_843_; lean_object* v_outputData_844_; lean_object* v_state_845_; lean_object* v_knownSize_846_; lean_object* v_messageHead_847_; uint8_t v_sentMessage_848_; uint8_t v_userClosedBody_849_; uint8_t v_omitBody_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___y_854_; uint8_t v___x_869_; 
v_userData_843_ = lean_ctor_get(v_writer_842_, 0);
v_outputData_844_ = lean_ctor_get(v_writer_842_, 1);
v_state_845_ = lean_ctor_get(v_writer_842_, 2);
v_knownSize_846_ = lean_ctor_get(v_writer_842_, 3);
v_messageHead_847_ = lean_ctor_get(v_writer_842_, 4);
v_sentMessage_848_ = lean_ctor_get_uint8(v_writer_842_, sizeof(void*)*6);
v_userClosedBody_849_ = lean_ctor_get_uint8(v_writer_842_, sizeof(void*)*6 + 1);
v_omitBody_850_ = lean_ctor_get_uint8(v_writer_842_, sizeof(void*)*6 + 2);
v___x_851_ = lean_array_get_size(v_userData_843_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_nat_dec_eq(v___x_851_, v___x_852_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; uint8_t v___x_871_; 
lean_inc(v_messageHead_847_);
lean_inc(v_knownSize_846_);
lean_inc(v_state_845_);
lean_inc_ref(v_outputData_844_);
lean_inc_ref(v_userData_843_);
lean_dec_ref(v_writer_842_);
v___x_870_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_871_ = lean_nat_dec_lt(v___x_852_, v___x_851_);
if (v___x_871_ == 0)
{
lean_dec_ref(v_userData_843_);
v___y_854_ = v___x_870_;
goto v___jp_853_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = lean_nat_dec_le(v___x_851_, v___x_851_);
if (v___x_872_ == 0)
{
if (v___x_871_ == 0)
{
lean_dec_ref(v_userData_843_);
v___y_854_ = v___x_870_;
goto v___jp_853_;
}
else
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((size_t)0ULL);
v___x_874_ = lean_usize_of_nat(v___x_851_);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_843_, v___x_873_, v___x_874_, v___x_870_);
lean_dec_ref(v_userData_843_);
v___y_854_ = v___x_875_;
goto v___jp_853_;
}
}
else
{
size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; 
v___x_876_ = ((size_t)0ULL);
v___x_877_ = lean_usize_of_nat(v___x_851_);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_843_, v___x_876_, v___x_877_, v___x_870_);
lean_dec_ref(v_userData_843_);
v___y_854_ = v___x_878_;
goto v___jp_853_;
}
}
}
else
{
return v_writer_842_;
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_856_ = lean_array_get_size(v___y_854_);
v___x_857_ = lean_nat_dec_lt(v___x_852_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec_ref(v___y_854_);
v___x_858_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_858_, 0, v___x_855_);
lean_ctor_set(v___x_858_, 1, v_outputData_844_);
lean_ctor_set(v___x_858_, 2, v_state_845_);
lean_ctor_set(v___x_858_, 3, v_knownSize_846_);
lean_ctor_set(v___x_858_, 4, v_messageHead_847_);
lean_ctor_set(v___x_858_, 5, v___x_852_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*6, v_sentMessage_848_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*6 + 1, v_userClosedBody_849_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*6 + 2, v_omitBody_850_);
return v___x_858_;
}
else
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_le(v___x_856_, v___x_856_);
if (v___x_859_ == 0)
{
if (v___x_857_ == 0)
{
lean_object* v___x_860_; 
lean_dec_ref(v___y_854_);
v___x_860_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_860_, 0, v___x_855_);
lean_ctor_set(v___x_860_, 1, v_outputData_844_);
lean_ctor_set(v___x_860_, 2, v_state_845_);
lean_ctor_set(v___x_860_, 3, v_knownSize_846_);
lean_ctor_set(v___x_860_, 4, v_messageHead_847_);
lean_ctor_set(v___x_860_, 5, v___x_852_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*6, v_sentMessage_848_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*6 + 1, v_userClosedBody_849_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*6 + 2, v_omitBody_850_);
return v___x_860_;
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_856_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_854_, v___x_861_, v___x_862_, v_outputData_844_);
lean_dec_ref(v___y_854_);
v___x_864_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_864_, 0, v___x_855_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
lean_ctor_set(v___x_864_, 2, v_state_845_);
lean_ctor_set(v___x_864_, 3, v_knownSize_846_);
lean_ctor_set(v___x_864_, 4, v_messageHead_847_);
lean_ctor_set(v___x_864_, 5, v___x_852_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*6, v_sentMessage_848_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*6 + 1, v_userClosedBody_849_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*6 + 2, v_omitBody_850_);
return v___x_864_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_856_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_854_, v___x_865_, v___x_866_, v_outputData_844_);
lean_dec_ref(v___y_854_);
v___x_868_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_868_, 0, v___x_855_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
lean_ctor_set(v___x_868_, 2, v_state_845_);
lean_ctor_set(v___x_868_, 3, v_knownSize_846_);
lean_ctor_set(v___x_868_, 4, v_messageHead_847_);
lean_ctor_set(v___x_868_, 5, v___x_852_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*6, v_sentMessage_848_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*6 + 1, v_userClosedBody_849_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*6 + 2, v_omitBody_850_);
return v___x_868_;
}
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_879_, lean_object* v_writer_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_880_);
return v___x_881_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_writeChunkedBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_879_ = stack[0].m_num;
lean_object* v_writer_880_ = stack[1].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_879_, v_writer_880_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_883_, lean_object* v_writer_884_){
_start:
{
uint8_t v_dir_boxed_885_; lean_object* v_res_886_; 
v_dir_boxed_885_ = lean_unbox(v_dir_883_);
v_res_886_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_885_, v_writer_884_);
return v_res_886_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_889_ = lean_string_to_utf8(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_891_ = lean_byte_array_size(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_892_){
_start:
{
lean_object* v_writer_893_; lean_object* v_outputData_894_; lean_object* v_userData_895_; lean_object* v_knownSize_896_; lean_object* v_messageHead_897_; uint8_t v_sentMessage_898_; uint8_t v_userClosedBody_899_; uint8_t v_omitBody_900_; lean_object* v_userDataBytes_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_922_; 
v_writer_893_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_892_);
v_outputData_894_ = lean_ctor_get(v_writer_893_, 1);
v_userData_895_ = lean_ctor_get(v_writer_893_, 0);
v_knownSize_896_ = lean_ctor_get(v_writer_893_, 3);
v_messageHead_897_ = lean_ctor_get(v_writer_893_, 4);
v_sentMessage_898_ = lean_ctor_get_uint8(v_writer_893_, sizeof(void*)*6);
v_userClosedBody_899_ = lean_ctor_get_uint8(v_writer_893_, sizeof(void*)*6 + 1);
v_omitBody_900_ = lean_ctor_get_uint8(v_writer_893_, sizeof(void*)*6 + 2);
v_userDataBytes_901_ = lean_ctor_get(v_writer_893_, 5);
v_isSharedCheck_922_ = !lean_is_exclusive(v_writer_893_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_writer_893_, 2);
lean_dec(v_unused_923_);
v___x_903_ = v_writer_893_;
v_isShared_904_ = v_isSharedCheck_922_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_userDataBytes_901_);
lean_inc(v_messageHead_897_);
lean_inc(v_knownSize_896_);
lean_inc(v_outputData_894_);
lean_inc(v_userData_895_);
lean_dec(v_writer_893_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_922_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_data_905_; lean_object* v_size_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_921_; 
v_data_905_ = lean_ctor_get(v_outputData_894_, 0);
v_size_906_ = lean_ctor_get(v_outputData_894_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_outputData_894_);
if (v_isSharedCheck_921_ == 0)
{
v___x_908_ = v_outputData_894_;
v_isShared_909_ = v_isSharedCheck_921_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_size_906_);
lean_inc(v_data_905_);
lean_dec(v_outputData_894_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_921_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_910_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_911_ = lean_array_push(v_data_905_, v___x_910_);
v___x_912_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_913_ = lean_nat_add(v_size_906_, v___x_912_);
lean_dec(v_size_906_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v___x_913_);
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_915_ = v___x_908_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_920_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_box(6);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_916_);
lean_ctor_set(v___x_903_, 1, v___x_915_);
v___x_918_ = v___x_903_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_userData_895_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_knownSize_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_messageHead_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_userDataBytes_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6, v_sentMessage_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6 + 1, v_userClosedBody_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6 + 2, v_omitBody_900_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_924_, lean_object* v_writer_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_925_);
return v___x_926_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_writeFinalChunk_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_924_ = stack[0].m_num;
lean_object* v_writer_925_ = stack[1].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_924_, v_writer_925_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_928_, lean_object* v_writer_929_){
_start:
{
uint8_t v_dir_boxed_930_; lean_object* v_res_931_; 
v_dir_boxed_930_ = lean_unbox(v_dir_928_);
v_res_931_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_930_, v_writer_929_);
return v_res_931_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_932_, size_t v_i_933_, size_t v_stop_934_, lean_object* v_b_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_eq(v_i_933_, v_stop_934_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v_data_938_; lean_object* v_data_939_; lean_object* v_size_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_953_; 
v___x_937_ = lean_array_uget_borrowed(v_as_932_, v_i_933_);
v_data_938_ = lean_ctor_get(v___x_937_, 0);
v_data_939_ = lean_ctor_get(v_b_935_, 0);
v_size_940_ = lean_ctor_get(v_b_935_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_b_935_);
if (v_isSharedCheck_953_ == 0)
{
v___x_942_ = v_b_935_;
v_isShared_943_ = v_isSharedCheck_953_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_size_940_);
lean_inc(v_data_939_);
lean_dec(v_b_935_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_953_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc_ref(v_data_938_);
v___x_944_ = lean_array_push(v_data_939_, v_data_938_);
v___x_945_ = lean_byte_array_size(v_data_938_);
v___x_946_ = lean_nat_add(v_size_940_, v___x_945_);
lean_dec(v_size_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_946_);
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_948_ = v___x_942_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
size_t v___x_949_; size_t v___x_950_; 
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_add(v_i_933_, v___x_949_);
v_i_933_ = v___x_950_;
v_b_935_ = v___x_948_;
goto _start;
}
}
}
else
{
return v_b_935_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_932_ = stack[0].m_obj;
size_t v_i_933_ = stack[1].m_num;
size_t v_stop_934_ = stack[2].m_num;
lean_object* v_b_935_ = stack[3].m_obj;
lean_object* v_res_954_;
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_932_, v_i_933_, v_stop_934_, v_b_935_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_955_, lean_object* v_i_956_, lean_object* v_stop_957_, lean_object* v_b_958_){
_start:
{
size_t v_i_boxed_959_; size_t v_stop_boxed_960_; lean_object* v_res_961_; 
v_i_boxed_959_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_stop_boxed_960_ = lean_unbox_usize(v_stop_957_);
lean_dec(v_stop_957_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_955_, v_i_boxed_959_, v_stop_boxed_960_, v_b_958_);
lean_dec_ref(v_as_955_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_962_){
_start:
{
lean_object* v_userData_963_; lean_object* v_outputData_964_; lean_object* v_state_965_; lean_object* v_knownSize_966_; lean_object* v_messageHead_967_; uint8_t v_sentMessage_968_; uint8_t v_userClosedBody_969_; uint8_t v_omitBody_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_997_; 
v_userData_963_ = lean_ctor_get(v_writer_962_, 0);
v_outputData_964_ = lean_ctor_get(v_writer_962_, 1);
v_state_965_ = lean_ctor_get(v_writer_962_, 2);
v_knownSize_966_ = lean_ctor_get(v_writer_962_, 3);
v_messageHead_967_ = lean_ctor_get(v_writer_962_, 4);
v_sentMessage_968_ = lean_ctor_get_uint8(v_writer_962_, sizeof(void*)*6);
v_userClosedBody_969_ = lean_ctor_get_uint8(v_writer_962_, sizeof(void*)*6 + 1);
v_omitBody_970_ = lean_ctor_get_uint8(v_writer_962_, sizeof(void*)*6 + 2);
v_isSharedCheck_997_ = !lean_is_exclusive(v_writer_962_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_writer_962_, 5);
lean_dec(v_unused_998_);
v___x_972_ = v_writer_962_;
v_isShared_973_ = v_isSharedCheck_997_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_messageHead_967_);
lean_inc(v_knownSize_966_);
lean_inc(v_state_965_);
lean_inc(v_outputData_964_);
lean_inc(v_userData_963_);
lean_dec(v_writer_962_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_997_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_976_ = lean_array_get_size(v_userData_963_);
v___x_977_ = lean_nat_dec_lt(v___x_974_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_979_; 
lean_dec_ref(v_userData_963_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 5, v___x_974_);
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_979_ = v___x_972_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_outputData_964_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_state_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_knownSize_966_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_messageHead_967_);
lean_ctor_set(v_reuseFailAlloc_980_, 5, v___x_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_980_, sizeof(void*)*6, v_sentMessage_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_980_, sizeof(void*)*6 + 1, v_userClosedBody_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_980_, sizeof(void*)*6 + 2, v_omitBody_970_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
uint8_t v___x_981_; 
v___x_981_ = lean_nat_dec_le(v___x_976_, v___x_976_);
if (v___x_981_ == 0)
{
if (v___x_977_ == 0)
{
lean_object* v___x_983_; 
lean_dec_ref(v_userData_963_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 5, v___x_974_);
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_983_ = v___x_972_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_outputData_964_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_state_965_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_knownSize_966_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_messageHead_967_);
lean_ctor_set(v_reuseFailAlloc_984_, 5, v___x_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*6, v_sentMessage_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*6 + 1, v_userClosedBody_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*6 + 2, v_omitBody_970_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_985_ = ((size_t)0ULL);
v___x_986_ = lean_usize_of_nat(v___x_976_);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_963_, v___x_985_, v___x_986_, v_outputData_964_);
lean_dec_ref(v_userData_963_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 5, v___x_974_);
lean_ctor_set(v___x_972_, 1, v___x_987_);
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_989_ = v___x_972_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_state_965_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_knownSize_966_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_messageHead_967_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v___x_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*6, v_sentMessage_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*6 + 1, v_userClosedBody_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*6 + 2, v_omitBody_970_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_of_nat(v___x_976_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_963_, v___x_991_, v___x_992_, v_outputData_964_);
lean_dec_ref(v_userData_963_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 5, v___x_974_);
lean_ctor_set(v___x_972_, 1, v___x_993_);
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_995_ = v___x_972_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_state_965_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_knownSize_966_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_messageHead_967_);
lean_ctor_set(v_reuseFailAlloc_996_, 5, v___x_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6, v_sentMessage_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6 + 1, v_userClosedBody_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6 + 2, v_omitBody_970_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_999_, lean_object* v_writer_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_writeRawBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_999_ = stack[0].m_num;
lean_object* v_writer_1000_ = stack[1].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_999_, v_writer_1000_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_1003_, lean_object* v_writer_1004_){
_start:
{
uint8_t v_dir_boxed_1005_; lean_object* v_res_1006_; 
v_dir_boxed_1005_ = lean_unbox(v_dir_1003_);
v_res_1006_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_1005_, v_writer_1004_);
return v_res_1006_;
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_1007_, lean_object* v_x1_1008_, lean_object* v_x2_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_byte_array_size(v_x1_1008_);
v___x_1012_ = lean_byte_array_size(v_x2_1009_);
v___x_1013_ = lean_byte_array_copy_slice(v_x2_1009_, v___x_1010_, v_x1_1008_, v___x_1011_, v___x_1012_, v___x_1007_);
return v___x_1013_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1007_ = stack[0].m_num;
lean_object* v_x1_1008_ = stack[1].m_obj;
lean_object* v_x2_1009_ = stack[2].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_1007_, v_x1_1008_, v_x2_1009_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_1015_, lean_object* v_x1_1016_, lean_object* v_x2_1017_){
_start:
{
uint8_t v___x_115__boxed_1018_; lean_object* v_res_1019_; 
v___x_115__boxed_1018_ = lean_unbox(v___x_1015_);
v_res_1019_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_115__boxed_1018_, v_x1_1016_, v_x2_1017_);
lean_dec_ref(v_x2_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_1023_){
_start:
{
lean_object* v_userData_1024_; lean_object* v_outputData_1025_; lean_object* v_state_1026_; lean_object* v_knownSize_1027_; lean_object* v_messageHead_1028_; uint8_t v_sentMessage_1029_; uint8_t v_userClosedBody_1030_; uint8_t v_omitBody_1031_; lean_object* v_userDataBytes_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1060_; 
v_userData_1024_ = lean_ctor_get(v_writer_1023_, 0);
v_outputData_1025_ = lean_ctor_get(v_writer_1023_, 1);
v_state_1026_ = lean_ctor_get(v_writer_1023_, 2);
v_knownSize_1027_ = lean_ctor_get(v_writer_1023_, 3);
v_messageHead_1028_ = lean_ctor_get(v_writer_1023_, 4);
v_sentMessage_1029_ = lean_ctor_get_uint8(v_writer_1023_, sizeof(void*)*6);
v_userClosedBody_1030_ = lean_ctor_get_uint8(v_writer_1023_, sizeof(void*)*6 + 1);
v_omitBody_1031_ = lean_ctor_get_uint8(v_writer_1023_, sizeof(void*)*6 + 2);
v_userDataBytes_1032_ = lean_ctor_get(v_writer_1023_, 5);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_writer_1023_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1034_ = v_writer_1023_;
v_isShared_1035_ = v_isSharedCheck_1060_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_userDataBytes_1032_);
lean_inc(v_messageHead_1028_);
lean_inc(v_knownSize_1027_);
lean_inc(v_state_1026_);
lean_inc(v_outputData_1025_);
lean_inc(v_userData_1024_);
lean_dec(v_writer_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1060_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___y_1037_; lean_object* v_data_1044_; lean_object* v_size_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_data_1044_ = lean_ctor_get(v_outputData_1025_, 0);
lean_inc_ref(v_data_1044_);
v_size_1045_ = lean_ctor_get(v_outputData_1025_, 1);
lean_inc(v_size_1045_);
lean_dec_ref(v_outputData_1025_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_array_get_size(v_data_1044_);
v___x_1048_ = lean_nat_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1049_ = lean_mk_empty_byte_array(v_size_1045_);
lean_dec(v_size_1045_);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1052_ = lean_nat_dec_lt(v___x_1050_, v___x_1047_);
if (v___x_1052_ == 0)
{
lean_dec_ref(v_data_1044_);
v___y_1037_ = v___x_1049_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1053_; lean_object* v___f_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v___x_1053_ = lean_box(v___x_1048_);
v___f_1054_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1054_, 0, v___x_1053_);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = lean_usize_of_nat(v___x_1047_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1051_, v___f_1054_, v_data_1044_, v___x_1055_, v___x_1056_, v___x_1049_);
v___y_1037_ = v___x_1057_;
goto v___jp_1036_;
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v_size_1045_);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_array_fget(v_data_1044_, v___x_1058_);
lean_dec_ref(v_data_1044_);
v___y_1037_ = v___x_1059_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_userData_1024_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_state_1026_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_knownSize_1027_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_messageHead_1028_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v_userDataBytes_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*6, v_sentMessage_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*6 + 1, v_userClosedBody_1030_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*6 + 2, v_omitBody_1031_);
v___x_1040_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___y_1037_);
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1061_, lean_object* v_writer_1062_){
_start:
{
lean_object* v_userData_1063_; lean_object* v_outputData_1064_; lean_object* v_state_1065_; lean_object* v_knownSize_1066_; lean_object* v_messageHead_1067_; uint8_t v_sentMessage_1068_; uint8_t v_userClosedBody_1069_; uint8_t v_omitBody_1070_; lean_object* v_userDataBytes_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1099_; 
v_userData_1063_ = lean_ctor_get(v_writer_1062_, 0);
v_outputData_1064_ = lean_ctor_get(v_writer_1062_, 1);
v_state_1065_ = lean_ctor_get(v_writer_1062_, 2);
v_knownSize_1066_ = lean_ctor_get(v_writer_1062_, 3);
v_messageHead_1067_ = lean_ctor_get(v_writer_1062_, 4);
v_sentMessage_1068_ = lean_ctor_get_uint8(v_writer_1062_, sizeof(void*)*6);
v_userClosedBody_1069_ = lean_ctor_get_uint8(v_writer_1062_, sizeof(void*)*6 + 1);
v_omitBody_1070_ = lean_ctor_get_uint8(v_writer_1062_, sizeof(void*)*6 + 2);
v_userDataBytes_1071_ = lean_ctor_get(v_writer_1062_, 5);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_writer_1062_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1073_ = v_writer_1062_;
v_isShared_1074_ = v_isSharedCheck_1099_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_userDataBytes_1071_);
lean_inc(v_messageHead_1067_);
lean_inc(v_knownSize_1066_);
lean_inc(v_state_1065_);
lean_inc(v_outputData_1064_);
lean_inc(v_userData_1063_);
lean_dec(v_writer_1062_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1099_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___y_1076_; lean_object* v_data_1083_; lean_object* v_size_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_data_1083_ = lean_ctor_get(v_outputData_1064_, 0);
lean_inc_ref(v_data_1083_);
v_size_1084_ = lean_ctor_get(v_outputData_1064_, 1);
lean_inc(v_size_1084_);
lean_dec_ref(v_outputData_1064_);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_array_get_size(v_data_1083_);
v___x_1087_ = lean_nat_dec_eq(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1088_ = lean_mk_empty_byte_array(v_size_1084_);
lean_dec(v_size_1084_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1091_ = lean_nat_dec_lt(v___x_1089_, v___x_1086_);
if (v___x_1091_ == 0)
{
lean_dec_ref(v_data_1083_);
v___y_1076_ = v___x_1088_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1092_; lean_object* v___f_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1092_ = lean_box(v___x_1087_);
v___f_1093_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1093_, 0, v___x_1092_);
v___x_1094_ = ((size_t)0ULL);
v___x_1095_ = lean_usize_of_nat(v___x_1086_);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1090_, v___f_1093_, v_data_1083_, v___x_1094_, v___x_1095_, v___x_1088_);
v___y_1076_ = v___x_1096_;
goto v___jp_1075_;
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_size_1084_);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_array_fget(v_data_1083_, v___x_1097_);
lean_dec_ref(v_data_1083_);
v___y_1076_ = v___x_1098_;
goto v___jp_1075_;
}
v___jp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1077_);
v___x_1079_ = v___x_1073_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_userData_1063_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_state_1065_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_knownSize_1066_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_messageHead_1067_);
lean_ctor_set(v_reuseFailAlloc_1082_, 5, v_userDataBytes_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*6, v_sentMessage_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*6 + 1, v_userClosedBody_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*6 + 2, v_omitBody_1070_);
v___x_1079_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___y_1076_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_takeOutput_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1061_ = stack[0].m_num;
lean_object* v_writer_1062_ = stack[1].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_1061_, v_writer_1062_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1101_, lean_object* v_writer_1102_){
_start:
{
uint8_t v_dir_boxed_1103_; lean_object* v_res_1104_; 
v_dir_boxed_1103_ = lean_unbox(v_dir_1101_);
v_res_1104_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1103_, v_writer_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1105_, lean_object* v_writer_1106_){
_start:
{
lean_object* v_userData_1107_; lean_object* v_outputData_1108_; lean_object* v_knownSize_1109_; lean_object* v_messageHead_1110_; uint8_t v_sentMessage_1111_; uint8_t v_userClosedBody_1112_; uint8_t v_omitBody_1113_; lean_object* v_userDataBytes_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_userData_1107_ = lean_ctor_get(v_writer_1106_, 0);
v_outputData_1108_ = lean_ctor_get(v_writer_1106_, 1);
v_knownSize_1109_ = lean_ctor_get(v_writer_1106_, 3);
v_messageHead_1110_ = lean_ctor_get(v_writer_1106_, 4);
v_sentMessage_1111_ = lean_ctor_get_uint8(v_writer_1106_, sizeof(void*)*6);
v_userClosedBody_1112_ = lean_ctor_get_uint8(v_writer_1106_, sizeof(void*)*6 + 1);
v_omitBody_1113_ = lean_ctor_get_uint8(v_writer_1106_, sizeof(void*)*6 + 2);
v_userDataBytes_1114_ = lean_ctor_get(v_writer_1106_, 5);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_writer_1106_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_writer_1106_, 2);
lean_dec(v_unused_1122_);
v___x_1116_ = v_writer_1106_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_userDataBytes_1114_);
lean_inc(v_messageHead_1110_);
lean_inc(v_knownSize_1109_);
lean_inc(v_outputData_1108_);
lean_inc(v_userData_1107_);
lean_dec(v_writer_1106_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 2, v_state_1105_);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_userData_1107_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_outputData_1108_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_state_1105_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_knownSize_1109_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_messageHead_1110_);
lean_ctor_set(v_reuseFailAlloc_1120_, 5, v_userDataBytes_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*6, v_sentMessage_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*6 + 1, v_userClosedBody_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*6 + 2, v_omitBody_1113_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1123_, lean_object* v_state_1124_, lean_object* v_writer_1125_){
_start:
{
lean_object* v_userData_1126_; lean_object* v_outputData_1127_; lean_object* v_knownSize_1128_; lean_object* v_messageHead_1129_; uint8_t v_sentMessage_1130_; uint8_t v_userClosedBody_1131_; uint8_t v_omitBody_1132_; lean_object* v_userDataBytes_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_userData_1126_ = lean_ctor_get(v_writer_1125_, 0);
v_outputData_1127_ = lean_ctor_get(v_writer_1125_, 1);
v_knownSize_1128_ = lean_ctor_get(v_writer_1125_, 3);
v_messageHead_1129_ = lean_ctor_get(v_writer_1125_, 4);
v_sentMessage_1130_ = lean_ctor_get_uint8(v_writer_1125_, sizeof(void*)*6);
v_userClosedBody_1131_ = lean_ctor_get_uint8(v_writer_1125_, sizeof(void*)*6 + 1);
v_omitBody_1132_ = lean_ctor_get_uint8(v_writer_1125_, sizeof(void*)*6 + 2);
v_userDataBytes_1133_ = lean_ctor_get(v_writer_1125_, 5);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_writer_1125_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v_writer_1125_, 2);
lean_dec(v_unused_1141_);
v___x_1135_ = v_writer_1125_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_userDataBytes_1133_);
lean_inc(v_messageHead_1129_);
lean_inc(v_knownSize_1128_);
lean_inc(v_outputData_1127_);
lean_inc(v_userData_1126_);
lean_dec(v_writer_1125_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 2, v_state_1124_);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_userData_1126_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_outputData_1127_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_state_1124_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_knownSize_1128_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_messageHead_1129_);
lean_ctor_set(v_reuseFailAlloc_1139_, 5, v_userDataBytes_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1139_, sizeof(void*)*6, v_sentMessage_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1139_, sizeof(void*)*6 + 1, v_userClosedBody_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1139_, sizeof(void*)*6 + 2, v_omitBody_1132_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_setState_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1123_ = stack[0].m_num;
lean_object* v_state_1124_ = stack[1].m_obj;
lean_object* v_writer_1125_ = stack[2].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_1123_, v_state_1124_, v_writer_1125_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1143_, lean_object* v_state_1144_, lean_object* v_writer_1145_){
_start:
{
uint8_t v_dir_boxed_1146_; lean_object* v_res_1147_; 
v_dir_boxed_1146_ = lean_unbox(v_dir_1143_);
v_res_1147_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1146_, v_state_1144_, v_writer_1145_);
return v_res_1147_;
}
}
lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1148_, lean_object* v_messageHead_1149_, lean_object* v_writer_1150_){
_start:
{
lean_object* v_userData_1151_; lean_object* v_outputData_1152_; lean_object* v_state_1153_; lean_object* v_knownSize_1154_; lean_object* v_messageHead_1155_; uint8_t v_sentMessage_1156_; uint8_t v_userClosedBody_1157_; uint8_t v_omitBody_1158_; lean_object* v_userDataBytes_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1172_; 
v_userData_1151_ = lean_ctor_get(v_writer_1150_, 0);
v_outputData_1152_ = lean_ctor_get(v_writer_1150_, 1);
v_state_1153_ = lean_ctor_get(v_writer_1150_, 2);
v_knownSize_1154_ = lean_ctor_get(v_writer_1150_, 3);
v_messageHead_1155_ = lean_ctor_get(v_writer_1150_, 4);
v_sentMessage_1156_ = lean_ctor_get_uint8(v_writer_1150_, sizeof(void*)*6);
v_userClosedBody_1157_ = lean_ctor_get_uint8(v_writer_1150_, sizeof(void*)*6 + 1);
v_omitBody_1158_ = lean_ctor_get_uint8(v_writer_1150_, sizeof(void*)*6 + 2);
v_userDataBytes_1159_ = lean_ctor_get(v_writer_1150_, 5);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_writer_1150_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1161_ = v_writer_1150_;
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_userDataBytes_1159_);
lean_inc(v_messageHead_1155_);
lean_inc(v_knownSize_1154_);
lean_inc(v_state_1153_);
lean_inc(v_outputData_1152_);
lean_inc(v_userData_1151_);
lean_dec(v_writer_1150_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
uint8_t v___y_1164_; 
if (v_dir_1148_ == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = 1;
v___y_1164_ = v___x_1170_;
goto v___jp_1163_;
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = 0;
v___y_1164_ = v___x_1171_;
goto v___jp_1163_;
}
v___jp_1163_:
{
lean_object* v___x_6__overap_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_6__overap_1165_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1164_);
v___x_1166_ = lean_apply_2(v___x_6__overap_1165_, v_outputData_1152_, v_messageHead_1149_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1166_);
v___x_1168_ = v___x_1161_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_userData_1151_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_state_1153_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_knownSize_1154_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_messageHead_1155_);
lean_ctor_set(v_reuseFailAlloc_1169_, 5, v_userDataBytes_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*6, v_sentMessage_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*6 + 1, v_userClosedBody_1157_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*6 + 2, v_omitBody_1158_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1148_ = stack[0].m_num;
lean_object* v_messageHead_1149_ = stack[1].m_obj;
lean_object* v_writer_1150_ = stack[2].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_1148_, v_messageHead_1149_, v_writer_1150_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1174_, lean_object* v_messageHead_1175_, lean_object* v_writer_1176_){
_start:
{
uint8_t v_dir_boxed_1177_; lean_object* v_res_1178_; 
v_dir_boxed_1177_ = lean_unbox(v_dir_1174_);
v_res_1178_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1177_, v_messageHead_1175_, v_writer_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(lean_object* v_a_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_key_1181_; lean_object* v_value_1182_; lean_object* v_tail_1183_; uint8_t v___x_1184_; 
v_key_1181_ = lean_ctor_get(v_x_1180_, 0);
v_value_1182_ = lean_ctor_get(v_x_1180_, 1);
v_tail_1183_ = lean_ctor_get(v_x_1180_, 2);
v___x_1184_ = lean_string_dec_eq(v_key_1181_, v_a_1179_);
if (v___x_1184_ == 0)
{
v_x_1180_ = v_tail_1183_;
goto _start;
}
else
{
lean_inc(v_value_1182_);
return v_value_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg___boxed(lean_object* v_a_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1186_, v_x_1187_);
lean_dec(v_x_1187_);
lean_dec_ref(v_a_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(lean_object* v_m_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_buckets_1191_; lean_object* v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; uint64_t v___x_1195_; uint64_t v_fold_1196_; uint64_t v___x_1197_; uint64_t v___x_1198_; uint64_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_buckets_1191_ = lean_ctor_get(v_m_1189_, 1);
v___x_1192_ = lean_array_get_size(v_buckets_1191_);
v___x_1193_ = lean_string_hash(v_a_1190_);
v___x_1194_ = 32ULL;
v___x_1195_ = lean_uint64_shift_right(v___x_1193_, v___x_1194_);
v_fold_1196_ = lean_uint64_xor(v___x_1193_, v___x_1195_);
v___x_1197_ = 16ULL;
v___x_1198_ = lean_uint64_shift_right(v_fold_1196_, v___x_1197_);
v___x_1199_ = lean_uint64_xor(v_fold_1196_, v___x_1198_);
v___x_1200_ = lean_uint64_to_usize(v___x_1199_);
v___x_1201_ = lean_usize_of_nat(v___x_1192_);
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_sub(v___x_1201_, v___x_1202_);
v___x_1204_ = lean_usize_land(v___x_1200_, v___x_1203_);
v___x_1205_ = lean_array_uget_borrowed(v_buckets_1191_, v___x_1204_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1190_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg___boxed(lean_object* v_m_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1207_, v_a_1208_);
lean_dec_ref(v_a_1208_);
lean_dec_ref(v_m_1207_);
return v_res_1209_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
else
{
lean_object* v_key_1213_; lean_object* v_tail_1214_; uint8_t v___x_1215_; 
v_key_1213_ = lean_ctor_get(v_x_1211_, 0);
v_tail_1214_ = lean_ctor_get(v_x_1211_, 2);
v___x_1215_ = lean_string_dec_eq(v_key_1213_, v_a_1210_);
if (v___x_1215_ == 0)
{
v_x_1211_ = v_tail_1214_;
goto _start;
}
else
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1210_ = stack[0].m_obj;
lean_object* v_x_1211_ = stack[1].m_obj;
uint8_t v_res_1217_;
v_res_1217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1210_, v_x_1211_);
stack->m_num = v_res_1217_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1218_, lean_object* v_x_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1218_, v_x_1219_);
lean_dec(v_x_1219_);
lean_dec_ref(v_a_1218_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_buckets_1224_; lean_object* v___x_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v_fold_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_buckets_1224_ = lean_ctor_get(v_m_1222_, 1);
v___x_1225_ = lean_array_get_size(v_buckets_1224_);
v___x_1226_ = lean_string_hash(v_a_1223_);
v___x_1227_ = 32ULL;
v___x_1228_ = lean_uint64_shift_right(v___x_1226_, v___x_1227_);
v_fold_1229_ = lean_uint64_xor(v___x_1226_, v___x_1228_);
v___x_1230_ = 16ULL;
v___x_1231_ = lean_uint64_shift_right(v_fold_1229_, v___x_1230_);
v___x_1232_ = lean_uint64_xor(v_fold_1229_, v___x_1231_);
v___x_1233_ = lean_uint64_to_usize(v___x_1232_);
v___x_1234_ = lean_usize_of_nat(v___x_1225_);
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_sub(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_usize_land(v___x_1233_, v___x_1236_);
v___x_1238_ = lean_array_uget_borrowed(v_buckets_1224_, v___x_1237_);
v___x_1239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1223_, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1222_ = stack[0].m_obj;
lean_object* v_a_1223_ = stack[1].m_obj;
uint8_t v_res_1240_;
v_res_1240_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1222_, v_a_1223_);
stack->m_num = v_res_1240_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1241_, lean_object* v_a_1242_){
_start:
{
uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_res_1243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1241_, v_a_1242_);
lean_dec_ref(v_a_1242_);
lean_dec_ref(v_m_1241_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(lean_object* v_s_1245_, lean_object* v_p_1246_){
_start:
{
uint32_t v___y_1248_; lean_object* v___x_1253_; uint8_t v_decide_1254_; 
v___x_1253_ = lean_string_utf8_byte_size(v_s_1245_);
v_decide_1254_ = lean_nat_dec_eq(v_p_1246_, v___x_1253_);
if (v_decide_1254_ == 0)
{
uint32_t v___x_1255_; uint32_t v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = lean_string_utf8_get_fast(v_s_1245_, v_p_1246_);
v___x_1256_ = 65;
v___x_1257_ = lean_uint32_dec_le(v___x_1256_, v___x_1255_);
if (v___x_1257_ == 0)
{
v___y_1248_ = v___x_1255_;
goto v___jp_1247_;
}
else
{
uint32_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = 90;
v___x_1259_ = lean_uint32_dec_le(v___x_1255_, v___x_1258_);
if (v___x_1259_ == 0)
{
v___y_1248_ = v___x_1255_;
goto v___jp_1247_;
}
else
{
uint32_t v___x_1260_; uint32_t v___x_1261_; 
v___x_1260_ = 32;
v___x_1261_ = lean_uint32_add(v___x_1255_, v___x_1260_);
v___y_1248_ = v___x_1261_;
goto v___jp_1247_;
}
}
}
else
{
lean_dec(v_p_1246_);
return v_s_1245_;
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_inc(v_p_1246_);
v___x_1249_ = lean_string_utf8_set(v_s_1245_, v_p_1246_, v___y_1248_);
v___x_1250_ = l_Char_utf8Size(v___y_1248_);
v___x_1251_ = lean_nat_add(v_p_1246_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v_p_1246_);
v_s_1245_ = v___x_1249_;
v_p_1246_ = v___x_1251_;
goto _start;
}
}
}
uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1263_, lean_object* v_writer_1264_){
_start:
{
uint8_t v___y_1266_; 
if (v_dir_1263_ == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = 1;
v___y_1266_ = v___x_1283_;
goto v___jp_1265_;
}
else
{
uint8_t v___x_1284_; 
v___x_1284_ = 0;
v___y_1266_ = v___x_1284_;
goto v___jp_1265_;
}
v___jp_1265_:
{
lean_object* v_messageHead_1267_; lean_object* v___x_1268_; lean_object* v_entries_1269_; lean_object* v_indexes_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_messageHead_1267_ = lean_ctor_get(v_writer_1264_, 4);
v___x_1268_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1266_, v_messageHead_1267_);
v_entries_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_ref(v_entries_1269_);
v_indexes_1270_ = lean_ctor_get(v___x_1268_, 1);
lean_inc_ref(v_indexes_1270_);
lean_dec_ref(v___x_1268_);
v___x_1271_ = l_Std_Http_Header_Name_connection;
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
lean_dec_ref(v_indexes_1270_);
lean_dec_ref(v_entries_1269_);
v___x_1273_ = 1;
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_entry_1276_; lean_object* v___x_1277_; lean_object* v_snd_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_indexes_1270_, v___x_1271_);
lean_dec_ref(v_indexes_1270_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v_entry_1276_ = lean_array_fget(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_array_fget(v_entries_1269_, v_entry_1276_);
lean_dec(v_entry_1276_);
lean_dec_ref(v_entries_1269_);
v_snd_1278_ = lean_ctor_get(v___x_1277_, 1);
lean_inc(v_snd_1278_);
lean_dec(v___x_1277_);
v___x_1279_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(v_snd_1278_, v___x_1275_);
v___x_1280_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_1281_ = lean_string_dec_eq(v___x_1279_, v___x_1280_);
lean_dec_ref(v___x_1279_);
if (v___x_1281_ == 0)
{
return v___x_1272_;
}
else
{
uint8_t v___x_1282_; 
v___x_1282_ = 0;
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_shouldKeepAlive_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1263_ = stack[0].m_num;
lean_object* v_writer_1264_ = stack[1].m_obj;
uint8_t v_res_1285_;
v_res_1285_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_1263_, v_writer_1264_);
stack->m_num = v_res_1285_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1286_, lean_object* v_writer_1287_){
_start:
{
uint8_t v_dir_boxed_1288_; uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_dir_boxed_1288_ = lean_unbox(v_dir_1286_);
v_res_1289_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1288_, v_writer_1287_);
lean_dec_ref(v_writer_1287_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1291_, lean_object* v_m_1292_, lean_object* v_a_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1292_, v_a_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1292_ = stack[1].m_obj;
lean_object* v_a_1293_ = stack[2].m_obj;
uint8_t v_res_1295_;
v_res_1295_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_box(0), v_m_1292_, v_a_1293_);
stack->m_num = v_res_1295_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_m_1297_, lean_object* v_a_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1296_, v_m_1297_, v_a_1298_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_m_1297_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_00_u03b2_1301_, lean_object* v_m_1302_, lean_object* v_a_1303_, lean_object* v_hma_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1302_, v_a_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___boxed(lean_object* v_00_u03b2_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_, lean_object* v_hma_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_00_u03b2_1306_, v_m_1307_, v_a_1308_, v_hma_1309_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v_m_1307_);
return v_res_1310_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1311_, lean_object* v_a_1312_, lean_object* v_x_1313_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1312_, v_x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1312_ = stack[1].m_obj;
lean_object* v_x_1313_ = stack[2].m_obj;
uint8_t v_res_1315_;
v_res_1315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_box(0), v_a_1312_, v_x_1313_);
stack->m_num = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_a_1317_, lean_object* v_x_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1316_, v_a_1317_, v_x_1318_);
lean_dec(v_x_1318_);
lean_dec_ref(v_a_1317_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(lean_object* v_00_u03b2_1321_, lean_object* v_a_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1322_, v_x_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1326_, lean_object* v_a_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(v_00_u03b2_1326_, v_a_1327_, v_x_1328_, v_x_1329_);
lean_dec(v_x_1328_);
lean_dec_ref(v_a_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1331_){
_start:
{
lean_object* v_userData_1332_; lean_object* v_outputData_1333_; lean_object* v_knownSize_1334_; lean_object* v_messageHead_1335_; uint8_t v_sentMessage_1336_; uint8_t v_userClosedBody_1337_; uint8_t v_omitBody_1338_; lean_object* v_userDataBytes_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_userData_1332_ = lean_ctor_get(v_writer_1331_, 0);
v_outputData_1333_ = lean_ctor_get(v_writer_1331_, 1);
v_knownSize_1334_ = lean_ctor_get(v_writer_1331_, 3);
v_messageHead_1335_ = lean_ctor_get(v_writer_1331_, 4);
v_sentMessage_1336_ = lean_ctor_get_uint8(v_writer_1331_, sizeof(void*)*6);
v_userClosedBody_1337_ = lean_ctor_get_uint8(v_writer_1331_, sizeof(void*)*6 + 1);
v_omitBody_1338_ = lean_ctor_get_uint8(v_writer_1331_, sizeof(void*)*6 + 2);
v_userDataBytes_1339_ = lean_ctor_get(v_writer_1331_, 5);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_writer_1331_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_writer_1331_, 2);
lean_dec(v_unused_1348_);
v___x_1341_ = v_writer_1331_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_userDataBytes_1339_);
lean_inc(v_messageHead_1335_);
lean_inc(v_knownSize_1334_);
lean_inc(v_outputData_1333_);
lean_inc(v_userData_1332_);
lean_dec(v_writer_1331_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = lean_box(7);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 2, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_userData_1332_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_outputData_1333_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_knownSize_1334_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_messageHead_1335_);
lean_ctor_set(v_reuseFailAlloc_1346_, 5, v_userDataBytes_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*6, v_sentMessage_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*6 + 1, v_userClosedBody_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*6 + 2, v_omitBody_1338_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1349_, lean_object* v_writer_1350_){
_start:
{
lean_object* v_userData_1351_; lean_object* v_outputData_1352_; lean_object* v_knownSize_1353_; lean_object* v_messageHead_1354_; uint8_t v_sentMessage_1355_; uint8_t v_userClosedBody_1356_; uint8_t v_omitBody_1357_; lean_object* v_userDataBytes_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_userData_1351_ = lean_ctor_get(v_writer_1350_, 0);
v_outputData_1352_ = lean_ctor_get(v_writer_1350_, 1);
v_knownSize_1353_ = lean_ctor_get(v_writer_1350_, 3);
v_messageHead_1354_ = lean_ctor_get(v_writer_1350_, 4);
v_sentMessage_1355_ = lean_ctor_get_uint8(v_writer_1350_, sizeof(void*)*6);
v_userClosedBody_1356_ = lean_ctor_get_uint8(v_writer_1350_, sizeof(void*)*6 + 1);
v_omitBody_1357_ = lean_ctor_get_uint8(v_writer_1350_, sizeof(void*)*6 + 2);
v_userDataBytes_1358_ = lean_ctor_get(v_writer_1350_, 5);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_writer_1350_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v_writer_1350_, 2);
lean_dec(v_unused_1367_);
v___x_1360_ = v_writer_1350_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_userDataBytes_1358_);
lean_inc(v_messageHead_1354_);
lean_inc(v_knownSize_1353_);
lean_inc(v_outputData_1352_);
lean_inc(v_userData_1351_);
lean_dec(v_writer_1350_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_box(7);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 2, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_userData_1351_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_outputData_1352_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_knownSize_1353_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_messageHead_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_userDataBytes_1358_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*6, v_sentMessage_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*6 + 1, v_userClosedBody_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*6 + 2, v_omitBody_1357_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Writer_close_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1349_ = stack[0].m_num;
lean_object* v_writer_1350_ = stack[1].m_obj;
lean_object* v_res_1368_;
v_res_1368_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_1349_, v_writer_1350_);
stack->m_obj
 = v_res_1368_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1369_, lean_object* v_writer_1370_){
_start:
{
uint8_t v_dir_boxed_1371_; lean_object* v_res_1372_; 
v_dir_boxed_1371_ = lean_unbox(v_dir_1369_);
v_res_1372_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1371_, v_writer_1370_);
return v_res_1372_;
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
