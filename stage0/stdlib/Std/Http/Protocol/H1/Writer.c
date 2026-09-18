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
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
default: 
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Http_Protocol_H1_Writer_State_ctorIdx(v_x_10_);
lean_dec(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
if (lean_obj_tag(v_t_12_) == 3)
{
lean_object* v_n_14_; lean_object* v___x_15_; 
v_n_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_n_14_);
lean_dec_ref_known(v_t_12_, 1);
v___x_15_ = lean_apply_1(v_k_13_, v_n_14_);
return v___x_15_;
}
else
{
lean_dec(v_t_12_);
return v_k_13_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_24_, v_h_25_, v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim___redArg(lean_object* v_t_28_, lean_object* v_pending_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_28_, v_pending_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_pending_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_32_, v_pending_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim___redArg(lean_object* v_t_36_, lean_object* v_waitingHeaders_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_36_, v_waitingHeaders_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_waitingHeaders_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_40_, v_waitingHeaders_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim___redArg(lean_object* v_t_44_, lean_object* v_waitingForFlush_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_44_, v_waitingForFlush_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_waitingForFlush_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_48_, v_waitingForFlush_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim___redArg(lean_object* v_t_52_, lean_object* v_writingBodyFixed_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_52_, v_writingBodyFixed_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyFixed_elim(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_writingBodyFixed_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_56_, v_writingBodyFixed_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim___redArg(lean_object* v_t_60_, lean_object* v_writingBodyChunked_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_60_, v_writingBodyChunked_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyChunked_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_writingBodyChunked_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_64_, v_writingBodyChunked_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim___redArg(lean_object* v_t_68_, lean_object* v_writingBodyClosingFrame_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_68_, v_writingBodyClosingFrame_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBodyClosingFrame_elim(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_writingBodyClosingFrame_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_72_, v_writingBodyClosingFrame_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim___redArg(lean_object* v_t_76_, lean_object* v_complete_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_76_, v_complete_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim(lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_complete_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_80_, v_complete_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim___redArg(lean_object* v_t_84_, lean_object* v_closed_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_84_, v_closed_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim(lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_closed_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_88_, v_closed_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(2u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_to_int(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr(lean_object* v_x_125_, lean_object* v_prec_126_){
_start:
{
lean_object* v___y_128_; lean_object* v___y_135_; lean_object* v___y_142_; lean_object* v___y_149_; lean_object* v___y_156_; lean_object* v___y_163_; lean_object* v___y_170_; 
switch(lean_obj_tag(v_x_125_))
{
case 0:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_126_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_142_ = v___x_178_;
goto v___jp_141_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_142_ = v___x_179_;
goto v___jp_141_;
}
}
case 1:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_126_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_135_ = v___x_182_;
goto v___jp_134_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_135_ = v___x_183_;
goto v___jp_134_;
}
}
case 2:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_126_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_128_ = v___x_186_;
goto v___jp_127_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_128_ = v___x_187_;
goto v___jp_127_;
}
}
case 3:
{
lean_object* v_n_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_208_; 
v_n_188_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_208_ == 0)
{
v___x_190_ = v_x_125_;
v_isShared_191_ = v_isSharedCheck_208_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_n_188_);
lean_dec(v_x_125_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_208_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___y_193_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(1024u);
v___x_205_ = lean_nat_dec_le(v___x_204_, v_prec_126_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_193_ = v___x_206_;
goto v___jp_192_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_193_ = v___x_207_;
goto v___jp_192_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__18));
v___x_195_ = l_Nat_reprFast(v_n_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_195_);
v___x_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_203_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_194_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
lean_inc(v___y_193_);
v___x_199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_199_, 0, v___y_193_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = 0;
v___x_201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*1, v___x_200_);
v___x_202_ = l_Repr_addAppParen(v___x_201_, v_prec_126_);
return v___x_202_;
}
}
}
}
case 4:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(1024u);
v___x_210_ = lean_nat_dec_le(v___x_209_, v_prec_126_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_149_ = v___x_211_;
goto v___jp_148_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_149_ = v___x_212_;
goto v___jp_148_;
}
}
case 5:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1024u);
v___x_214_ = lean_nat_dec_le(v___x_213_, v_prec_126_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_156_ = v___x_215_;
goto v___jp_155_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_156_ = v___x_216_;
goto v___jp_155_;
}
}
case 6:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(1024u);
v___x_218_ = lean_nat_dec_le(v___x_217_, v_prec_126_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_163_ = v___x_219_;
goto v___jp_162_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_163_ = v___x_220_;
goto v___jp_162_;
}
}
default: 
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(1024u);
v___x_222_ = lean_nat_dec_le(v___x_221_, v_prec_126_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14);
v___y_170_ = v___x_223_;
goto v___jp_169_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__15);
v___y_170_ = v___x_224_;
goto v___jp_169_;
}
}
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1));
lean_inc(v___y_128_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___y_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = l_Repr_addAppParen(v___x_132_, v_prec_126_);
return v___x_133_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3));
lean_inc(v___y_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_126_);
return v___x_140_;
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5));
lean_inc(v___y_142_);
v___x_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_126_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7));
lean_inc(v___y_149_);
v___x_151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_151_, 0, v___y_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_152_);
v___x_154_ = l_Repr_addAppParen(v___x_153_, v_prec_126_);
return v___x_154_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9));
lean_inc(v___y_156_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___y_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = 0;
v___x_160_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_159_);
v___x_161_ = l_Repr_addAppParen(v___x_160_, v_prec_126_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11));
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = l_Repr_addAppParen(v___x_167_, v_prec_126_);
return v___x_168_;
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13));
lean_inc(v___y_170_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___y_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = 0;
v___x_174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1, v___x_173_);
v___x_175_ = l_Repr_addAppParen(v___x_174_, v_prec_126_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed(lean_object* v_x_225_, lean_object* v_prec_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr(v_x_225_, v_prec_226_);
lean_dec(v_prec_226_);
return v_res_227_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
switch(lean_obj_tag(v_x_230_))
{
case 0:
{
if (lean_obj_tag(v_x_231_) == 0)
{
uint8_t v___x_232_; 
v___x_232_ = 1;
return v___x_232_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
case 1:
{
if (lean_obj_tag(v_x_231_) == 1)
{
uint8_t v___x_234_; 
v___x_234_ = 1;
return v___x_234_;
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
case 2:
{
if (lean_obj_tag(v_x_231_) == 2)
{
uint8_t v___x_236_; 
v___x_236_ = 1;
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
case 3:
{
if (lean_obj_tag(v_x_231_) == 3)
{
lean_object* v_n_238_; lean_object* v_n_239_; uint8_t v___x_240_; 
v_n_238_ = lean_ctor_get(v_x_230_, 0);
v_n_239_ = lean_ctor_get(v_x_231_, 0);
v___x_240_ = lean_nat_dec_eq(v_n_238_, v_n_239_);
return v___x_240_;
}
else
{
uint8_t v___x_241_; 
v___x_241_ = 0;
return v___x_241_;
}
}
case 4:
{
if (lean_obj_tag(v_x_231_) == 4)
{
uint8_t v___x_242_; 
v___x_242_ = 1;
return v___x_242_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 0;
return v___x_243_;
}
}
case 5:
{
if (lean_obj_tag(v_x_231_) == 5)
{
uint8_t v___x_244_; 
v___x_244_ = 1;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
case 6:
{
if (lean_obj_tag(v_x_231_) == 6)
{
uint8_t v___x_246_; 
v___x_246_ = 1;
return v___x_246_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
default: 
{
if (lean_obj_tag(v_x_231_) == 7)
{
uint8_t v___x_248_; 
v___x_248_ = 1;
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_x_250_, v_x_251_);
lean_dec(v_x_251_);
lean_dec(v_x_250_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(lean_object* v_writer_256_){
_start:
{
lean_object* v_state_257_; 
v_state_257_ = lean_ctor_get(v_writer_256_, 2);
switch(lean_obj_tag(v_state_257_))
{
case 7:
{
uint8_t v___x_258_; 
v___x_258_ = 1;
return v___x_258_;
}
case 6:
{
uint8_t v___x_259_; 
v___x_259_ = 1;
return v___x_259_;
}
default: 
{
uint8_t v_userClosedBody_260_; 
v_userClosedBody_260_ = lean_ctor_get_uint8(v_writer_256_, sizeof(void*)*6 + 1);
return v_userClosedBody_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(lean_object* v_writer_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_261_);
lean_dec_ref(v_writer_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData(uint8_t v_dir_264_, lean_object* v_writer_265_){
_start:
{
lean_object* v_state_266_; 
v_state_266_ = lean_ctor_get(v_writer_265_, 2);
switch(lean_obj_tag(v_state_266_))
{
case 7:
{
uint8_t v___x_267_; 
v___x_267_ = 1;
return v___x_267_;
}
case 6:
{
uint8_t v___x_268_; 
v___x_268_ = 1;
return v___x_268_;
}
default: 
{
uint8_t v_userClosedBody_269_; 
v_userClosedBody_269_ = lean_ctor_get_uint8(v_writer_265_, sizeof(void*)*6 + 1);
return v_userClosedBody_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(lean_object* v_dir_270_, lean_object* v_writer_271_){
_start:
{
uint8_t v_dir_boxed_272_; uint8_t v_res_273_; lean_object* v_r_274_; 
v_dir_boxed_272_ = lean_unbox(v_dir_270_);
v_res_273_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_boxed_272_, v_writer_271_);
lean_dec_ref(v_writer_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed___redArg(lean_object* v_writer_275_){
_start:
{
lean_object* v_state_276_; 
v_state_276_ = lean_ctor_get(v_writer_275_, 2);
if (lean_obj_tag(v_state_276_) == 7)
{
uint8_t v___x_277_; 
v___x_277_ = 1;
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(lean_object* v_writer_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_279_);
lean_dec_ref(v_writer_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed(uint8_t v_dir_282_, lean_object* v_writer_283_){
_start:
{
lean_object* v_state_284_; 
v_state_284_ = lean_ctor_get(v_writer_283_, 2);
if (lean_obj_tag(v_state_284_) == 7)
{
uint8_t v___x_285_; 
v___x_285_ = 1;
return v___x_285_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___boxed(lean_object* v_dir_287_, lean_object* v_writer_288_){
_start:
{
uint8_t v_dir_boxed_289_; uint8_t v_res_290_; lean_object* v_r_291_; 
v_dir_boxed_289_ = lean_unbox(v_dir_287_);
v_res_290_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_boxed_289_, v_writer_288_);
lean_dec_ref(v_writer_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete___redArg(lean_object* v_writer_292_){
_start:
{
lean_object* v_state_293_; 
v_state_293_ = lean_ctor_get(v_writer_292_, 2);
if (lean_obj_tag(v_state_293_) == 6)
{
uint8_t v___x_294_; 
v___x_294_ = 1;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(lean_object* v_writer_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_296_);
lean_dec_ref(v_writer_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete(uint8_t v_dir_299_, lean_object* v_writer_300_){
_start:
{
lean_object* v_state_301_; 
v_state_301_ = lean_ctor_get(v_writer_300_, 2);
if (lean_obj_tag(v_state_301_) == 6)
{
uint8_t v___x_302_; 
v___x_302_ = 1;
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = 0;
return v___x_303_;
}
}
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
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(lean_object* v_writer_309_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(lean_object* v_writer_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_320_);
lean_dec_ref(v_writer_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData(uint8_t v_dir_323_, lean_object* v_writer_324_){
_start:
{
lean_object* v_state_325_; uint8_t v_userClosedBody_326_; 
v_state_325_ = lean_ctor_get(v_writer_324_, 2);
v_userClosedBody_326_ = lean_ctor_get_uint8(v_writer_324_, sizeof(void*)*6 + 1);
switch(lean_obj_tag(v_state_325_))
{
case 1:
{
uint8_t v___x_330_; 
v___x_330_ = 1;
return v___x_330_;
}
case 2:
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
case 3:
{
if (v_userClosedBody_326_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = 1;
return v___x_332_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = 0;
return v___x_333_;
}
}
case 4:
{
goto v___jp_327_;
}
case 5:
{
goto v___jp_327_;
}
default: 
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
}
}
v___jp_327_:
{
if (v_userClosedBody_326_ == 0)
{
uint8_t v___x_328_; 
v___x_328_ = 1;
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(lean_object* v_dir_335_, lean_object* v_writer_336_){
_start:
{
uint8_t v_dir_boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_dir_boxed_337_ = lean_unbox(v_dir_335_);
v_res_338_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_boxed_337_, v_writer_336_);
lean_dec_ref(v_writer_336_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___redArg(lean_object* v_writer_340_){
_start:
{
lean_object* v_userData_341_; lean_object* v_outputData_342_; lean_object* v_state_343_; lean_object* v_knownSize_344_; lean_object* v_messageHead_345_; uint8_t v_sentMessage_346_; uint8_t v_omitBody_347_; lean_object* v_userDataBytes_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_userData_341_ = lean_ctor_get(v_writer_340_, 0);
v_outputData_342_ = lean_ctor_get(v_writer_340_, 1);
v_state_343_ = lean_ctor_get(v_writer_340_, 2);
v_knownSize_344_ = lean_ctor_get(v_writer_340_, 3);
v_messageHead_345_ = lean_ctor_get(v_writer_340_, 4);
v_sentMessage_346_ = lean_ctor_get_uint8(v_writer_340_, sizeof(void*)*6);
v_omitBody_347_ = lean_ctor_get_uint8(v_writer_340_, sizeof(void*)*6 + 2);
v_userDataBytes_348_ = lean_ctor_get(v_writer_340_, 5);
v_isSharedCheck_356_ = !lean_is_exclusive(v_writer_340_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v_writer_340_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_userDataBytes_348_);
lean_inc(v_messageHead_345_);
lean_inc(v_knownSize_344_);
lean_inc(v_state_343_);
lean_inc(v_outputData_342_);
lean_inc(v_userData_341_);
lean_dec(v_writer_340_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; lean_object* v___x_354_; 
v___x_352_ = 1;
if (v_isShared_351_ == 0)
{
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_userData_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_outputData_342_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_state_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_knownSize_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_messageHead_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_userDataBytes_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*6, v_sentMessage_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*6 + 2, v_omitBody_347_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*6 + 1, v___x_352_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody(uint8_t v_dir_357_, lean_object* v_writer_358_){
_start:
{
lean_object* v_userData_359_; lean_object* v_outputData_360_; lean_object* v_state_361_; lean_object* v_knownSize_362_; lean_object* v_messageHead_363_; uint8_t v_sentMessage_364_; uint8_t v_omitBody_365_; lean_object* v_userDataBytes_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_userData_359_ = lean_ctor_get(v_writer_358_, 0);
v_outputData_360_ = lean_ctor_get(v_writer_358_, 1);
v_state_361_ = lean_ctor_get(v_writer_358_, 2);
v_knownSize_362_ = lean_ctor_get(v_writer_358_, 3);
v_messageHead_363_ = lean_ctor_get(v_writer_358_, 4);
v_sentMessage_364_ = lean_ctor_get_uint8(v_writer_358_, sizeof(void*)*6);
v_omitBody_365_ = lean_ctor_get_uint8(v_writer_358_, sizeof(void*)*6 + 2);
v_userDataBytes_366_ = lean_ctor_get(v_writer_358_, 5);
v_isSharedCheck_374_ = !lean_is_exclusive(v_writer_358_);
if (v_isSharedCheck_374_ == 0)
{
v___x_368_ = v_writer_358_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_userDataBytes_366_);
lean_inc(v_messageHead_363_);
lean_inc(v_knownSize_362_);
lean_inc(v_state_361_);
lean_inc(v_outputData_360_);
lean_inc(v_userData_359_);
lean_dec(v_writer_358_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; lean_object* v___x_372_; 
v___x_370_ = 1;
if (v_isShared_369_ == 0)
{
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_userData_359_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_outputData_360_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_state_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_knownSize_362_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_messageHead_363_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_userDataBytes_366_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*6, v_sentMessage_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*6 + 2, v_omitBody_365_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*6 + 1, v___x_370_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___boxed(lean_object* v_dir_375_, lean_object* v_writer_376_){
_start:
{
uint8_t v_dir_boxed_377_; lean_object* v_res_378_; 
v_dir_boxed_377_ = lean_unbox(v_dir_375_);
v_res_378_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_boxed_377_, v_writer_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(lean_object* v_writer_379_){
_start:
{
lean_object* v_knownSize_380_; 
v_knownSize_380_ = lean_ctor_get(v_writer_379_, 3);
if (lean_obj_tag(v_knownSize_380_) == 1)
{
lean_object* v_val_381_; 
v_val_381_ = lean_ctor_get(v_knownSize_380_, 0);
lean_inc(v_val_381_);
return v_val_381_;
}
else
{
uint8_t v_userClosedBody_382_; 
v_userClosedBody_382_ = lean_ctor_get_uint8(v_writer_379_, sizeof(void*)*6 + 1);
if (v_userClosedBody_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v_userDataBytes_384_; lean_object* v___x_385_; 
v_userDataBytes_384_ = lean_ctor_get(v_writer_379_, 5);
lean_inc(v_userDataBytes_384_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_userDataBytes_384_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(lean_object* v_writer_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_386_);
lean_dec_ref(v_writer_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode(uint8_t v_dir_388_, lean_object* v_writer_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(lean_object* v_dir_391_, lean_object* v_writer_392_){
_start:
{
uint8_t v_dir_boxed_393_; lean_object* v_res_394_; 
v_dir_boxed_393_ = lean_unbox(v_dir_391_);
v_res_394_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_boxed_393_, v_writer_392_);
lean_dec_ref(v_writer_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(lean_object* v_x1_395_, lean_object* v_x2_396_){
_start:
{
lean_object* v_data_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_data_397_ = lean_ctor_get(v_x2_396_, 0);
v___x_398_ = lean_byte_array_size(v_data_397_);
v___x_399_ = lean_nat_add(v_x1_395_, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(lean_object* v_x1_400_, lean_object* v_x2_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(v_x1_400_, v_x2_401_);
lean_dec_ref(v_x2_401_);
lean_dec(v_x1_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg(lean_object* v_data_423_, lean_object* v_writer_424_){
_start:
{
lean_object* v_userData_425_; lean_object* v_outputData_426_; lean_object* v_state_427_; lean_object* v_knownSize_428_; lean_object* v_messageHead_429_; uint8_t v_sentMessage_430_; uint8_t v_userClosedBody_431_; uint8_t v_omitBody_432_; lean_object* v_userDataBytes_433_; lean_object* v___y_435_; lean_object* v___f_439_; 
v_userData_425_ = lean_ctor_get(v_writer_424_, 0);
v_outputData_426_ = lean_ctor_get(v_writer_424_, 1);
v_state_427_ = lean_ctor_get(v_writer_424_, 2);
v_knownSize_428_ = lean_ctor_get(v_writer_424_, 3);
v_messageHead_429_ = lean_ctor_get(v_writer_424_, 4);
v_sentMessage_430_ = lean_ctor_get_uint8(v_writer_424_, sizeof(void*)*6);
v_userClosedBody_431_ = lean_ctor_get_uint8(v_writer_424_, sizeof(void*)*6 + 1);
v_omitBody_432_ = lean_ctor_get_uint8(v_writer_424_, sizeof(void*)*6 + 2);
v_userDataBytes_433_ = lean_ctor_get(v_writer_424_, 5);
v___f_439_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_427_))
{
case 1:
{
lean_inc(v_state_427_);
lean_inc(v_userDataBytes_433_);
lean_inc(v_messageHead_429_);
lean_inc(v_knownSize_428_);
lean_inc_ref(v_outputData_426_);
lean_inc_ref(v_userData_425_);
lean_dec_ref(v_writer_424_);
goto v___jp_440_;
}
case 2:
{
lean_inc(v_state_427_);
lean_inc(v_userDataBytes_433_);
lean_inc(v_messageHead_429_);
lean_inc(v_knownSize_428_);
lean_inc_ref(v_outputData_426_);
lean_inc_ref(v_userData_425_);
lean_dec_ref(v_writer_424_);
goto v___jp_440_;
}
case 3:
{
if (v_userClosedBody_431_ == 0)
{
lean_inc_ref(v_state_427_);
lean_inc(v_userDataBytes_433_);
lean_inc(v_messageHead_429_);
lean_inc(v_knownSize_428_);
lean_inc_ref(v_outputData_426_);
lean_inc_ref(v_userData_425_);
lean_dec_ref(v_writer_424_);
goto v___jp_440_;
}
else
{
lean_dec_ref(v_data_423_);
return v_writer_424_;
}
}
case 4:
{
goto v___jp_452_;
}
case 5:
{
goto v___jp_452_;
}
default: 
{
lean_dec_ref(v_data_423_);
return v_writer_424_;
}
}
v___jp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = l_Array_append___redArg(v_userData_425_, v_data_423_);
lean_dec_ref(v_data_423_);
v___x_437_ = lean_nat_add(v_userDataBytes_433_, v___y_435_);
lean_dec(v___y_435_);
lean_dec(v_userDataBytes_433_);
v___x_438_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v_outputData_426_);
lean_ctor_set(v___x_438_, 2, v_state_427_);
lean_ctor_set(v___x_438_, 3, v_knownSize_428_);
lean_ctor_set(v___x_438_, 4, v_messageHead_429_);
lean_ctor_set(v___x_438_, 5, v___x_437_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*6, v_sentMessage_430_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*6 + 1, v_userClosedBody_431_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*6 + 2, v_omitBody_432_);
return v___x_438_;
}
v___jp_440_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_array_get_size(v_data_423_);
v___x_443_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_444_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_444_ == 0)
{
v___y_435_ = v___x_441_;
goto v___jp_434_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = lean_nat_dec_le(v___x_442_, v___x_442_);
if (v___x_445_ == 0)
{
if (v___x_444_ == 0)
{
v___y_435_ = v___x_441_;
goto v___jp_434_;
}
else
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((size_t)0ULL);
v___x_447_ = lean_usize_of_nat(v___x_442_);
lean_inc_ref(v_data_423_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_443_, v___f_439_, v_data_423_, v___x_446_, v___x_447_, v___x_441_);
v___y_435_ = v___x_448_;
goto v___jp_434_;
}
}
else
{
size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = ((size_t)0ULL);
v___x_450_ = lean_usize_of_nat(v___x_442_);
lean_inc_ref(v_data_423_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_443_, v___f_439_, v_data_423_, v___x_449_, v___x_450_, v___x_441_);
v___y_435_ = v___x_451_;
goto v___jp_434_;
}
}
}
v___jp_452_:
{
if (v_userClosedBody_431_ == 0)
{
lean_inc(v_userDataBytes_433_);
lean_inc(v_messageHead_429_);
lean_inc(v_knownSize_428_);
lean_inc(v_state_427_);
lean_inc_ref(v_outputData_426_);
lean_inc_ref(v_userData_425_);
lean_dec_ref(v_writer_424_);
goto v___jp_440_;
}
else
{
lean_dec_ref(v_data_423_);
return v_writer_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_453_, lean_object* v_data_454_, lean_object* v_writer_455_){
_start:
{
lean_object* v_userData_456_; lean_object* v_outputData_457_; lean_object* v_state_458_; lean_object* v_knownSize_459_; lean_object* v_messageHead_460_; uint8_t v_sentMessage_461_; uint8_t v_userClosedBody_462_; uint8_t v_omitBody_463_; lean_object* v_userDataBytes_464_; lean_object* v___y_466_; lean_object* v___f_470_; 
v_userData_456_ = lean_ctor_get(v_writer_455_, 0);
v_outputData_457_ = lean_ctor_get(v_writer_455_, 1);
v_state_458_ = lean_ctor_get(v_writer_455_, 2);
v_knownSize_459_ = lean_ctor_get(v_writer_455_, 3);
v_messageHead_460_ = lean_ctor_get(v_writer_455_, 4);
v_sentMessage_461_ = lean_ctor_get_uint8(v_writer_455_, sizeof(void*)*6);
v_userClosedBody_462_ = lean_ctor_get_uint8(v_writer_455_, sizeof(void*)*6 + 1);
v_omitBody_463_ = lean_ctor_get_uint8(v_writer_455_, sizeof(void*)*6 + 2);
v_userDataBytes_464_ = lean_ctor_get(v_writer_455_, 5);
v___f_470_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_458_))
{
case 1:
{
lean_inc(v_state_458_);
lean_inc(v_userDataBytes_464_);
lean_inc(v_messageHead_460_);
lean_inc(v_knownSize_459_);
lean_inc_ref(v_outputData_457_);
lean_inc_ref(v_userData_456_);
lean_dec_ref(v_writer_455_);
goto v___jp_471_;
}
case 2:
{
lean_inc(v_state_458_);
lean_inc(v_userDataBytes_464_);
lean_inc(v_messageHead_460_);
lean_inc(v_knownSize_459_);
lean_inc_ref(v_outputData_457_);
lean_inc_ref(v_userData_456_);
lean_dec_ref(v_writer_455_);
goto v___jp_471_;
}
case 3:
{
if (v_userClosedBody_462_ == 0)
{
lean_inc_ref(v_state_458_);
lean_inc(v_userDataBytes_464_);
lean_inc(v_messageHead_460_);
lean_inc(v_knownSize_459_);
lean_inc_ref(v_outputData_457_);
lean_inc_ref(v_userData_456_);
lean_dec_ref(v_writer_455_);
goto v___jp_471_;
}
else
{
lean_dec_ref(v_data_454_);
return v_writer_455_;
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
lean_dec_ref(v_data_454_);
return v_writer_455_;
}
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = l_Array_append___redArg(v_userData_456_, v_data_454_);
lean_dec_ref(v_data_454_);
v___x_468_ = lean_nat_add(v_userDataBytes_464_, v___y_466_);
lean_dec(v___y_466_);
lean_dec(v_userDataBytes_464_);
v___x_469_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v_outputData_457_);
lean_ctor_set(v___x_469_, 2, v_state_458_);
lean_ctor_set(v___x_469_, 3, v_knownSize_459_);
lean_ctor_set(v___x_469_, 4, v_messageHead_460_);
lean_ctor_set(v___x_469_, 5, v___x_468_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*6, v_sentMessage_461_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*6 + 1, v_userClosedBody_462_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*6 + 2, v_omitBody_463_);
return v___x_469_;
}
v___jp_471_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_array_get_size(v_data_454_);
v___x_474_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_475_ = lean_nat_dec_lt(v___x_472_, v___x_473_);
if (v___x_475_ == 0)
{
v___y_466_ = v___x_472_;
goto v___jp_465_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_le(v___x_473_, v___x_473_);
if (v___x_476_ == 0)
{
if (v___x_475_ == 0)
{
v___y_466_ = v___x_472_;
goto v___jp_465_;
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_473_);
lean_inc_ref(v_data_454_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_474_, v___f_470_, v_data_454_, v___x_477_, v___x_478_, v___x_472_);
v___y_466_ = v___x_479_;
goto v___jp_465_;
}
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_473_);
lean_inc_ref(v_data_454_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_474_, v___f_470_, v_data_454_, v___x_480_, v___x_481_, v___x_472_);
v___y_466_ = v___x_482_;
goto v___jp_465_;
}
}
}
v___jp_483_:
{
if (v_userClosedBody_462_ == 0)
{
lean_inc(v_userDataBytes_464_);
lean_inc(v_messageHead_460_);
lean_inc(v_knownSize_459_);
lean_inc(v_state_458_);
lean_inc_ref(v_outputData_457_);
lean_inc_ref(v_userData_456_);
lean_dec_ref(v_writer_455_);
goto v___jp_471_;
}
else
{
lean_dec_ref(v_data_454_);
return v_writer_455_;
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
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; 
v___x_571_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v___x_572_ = lean_byte_array_size(v___x_571_);
v___x_573_ = lean_nat_add(v_b_569_, v___x_572_);
lean_dec(v_b_569_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_567_, v___x_574_);
v_i_567_ = v___x_575_;
v_b_569_ = v___x_573_;
goto _start;
}
else
{
return v_b_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_577_, lean_object* v_i_578_, lean_object* v_stop_579_, lean_object* v_b_580_){
_start:
{
size_t v_i_boxed_581_; size_t v_stop_boxed_582_; lean_object* v_res_583_; 
v_i_boxed_581_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_stop_boxed_582_ = lean_unbox_usize(v_stop_579_);
lean_dec(v_stop_579_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_577_, v_i_boxed_581_, v_stop_boxed_582_, v_b_580_);
lean_dec_ref(v_as_577_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_592_, lean_object* v_limitSize_593_){
_start:
{
uint8_t v___y_595_; lean_object* v___y_596_; uint8_t v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; uint8_t v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v_userData_629_; lean_object* v_outputData_630_; lean_object* v_state_631_; lean_object* v_knownSize_632_; lean_object* v_messageHead_633_; uint8_t v_sentMessage_634_; uint8_t v_userClosedBody_635_; uint8_t v_omitBody_636_; lean_object* v_userDataBytes_637_; lean_object* v_fst_639_; lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___y_651_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_userData_629_ = lean_ctor_get(v_writer_592_, 0);
v_outputData_630_ = lean_ctor_get(v_writer_592_, 1);
v_state_631_ = lean_ctor_get(v_writer_592_, 2);
v_knownSize_632_ = lean_ctor_get(v_writer_592_, 3);
v_messageHead_633_ = lean_ctor_get(v_writer_592_, 4);
v_sentMessage_634_ = lean_ctor_get_uint8(v_writer_592_, sizeof(void*)*6);
v_userClosedBody_635_ = lean_ctor_get_uint8(v_writer_592_, sizeof(void*)*6 + 1);
v_omitBody_636_ = lean_ctor_get_uint8(v_writer_592_, sizeof(void*)*6 + 2);
v_userDataBytes_637_ = lean_ctor_get(v_writer_592_, 5);
v___x_656_ = lean_array_get_size(v_userData_629_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
lean_inc(v_userDataBytes_637_);
lean_inc(v_messageHead_633_);
lean_inc(v_knownSize_632_);
lean_inc(v_state_631_);
lean_inc_ref(v_outputData_630_);
lean_inc_ref(v_userData_629_);
lean_dec_ref(v_writer_592_);
v___x_659_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_660_ = lean_nat_dec_lt(v___x_657_, v___x_656_);
if (v___x_660_ == 0)
{
lean_dec_ref(v_userData_629_);
v_fst_639_ = v___x_659_;
v_fst_640_ = v___x_659_;
v_snd_641_ = v___x_657_;
goto v___jp_638_;
}
else
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_662_ = lean_nat_dec_le(v___x_656_, v___x_656_);
if (v___x_662_ == 0)
{
if (v___x_660_ == 0)
{
lean_dec_ref(v_userData_629_);
v_fst_639_ = v___x_659_;
v_fst_640_ = v___x_659_;
v_snd_641_ = v___x_657_;
goto v___jp_638_;
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_656_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_593_, v_userData_629_, v___x_663_, v___x_664_, v___x_661_);
lean_dec_ref(v_userData_629_);
v___y_651_ = v___x_665_;
goto v___jp_650_;
}
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_656_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_593_, v_userData_629_, v___x_666_, v___x_667_, v___x_661_);
lean_dec_ref(v_userData_629_);
v___y_651_ = v___x_668_;
goto v___jp_650_;
}
}
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_writer_592_);
lean_ctor_set(v___x_669_, 1, v_limitSize_593_);
return v___x_669_;
}
v___jp_594_:
{
lean_object* v_data_606_; lean_object* v_size_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_628_; 
v_data_606_ = lean_ctor_get(v___y_603_, 0);
v_size_607_ = lean_ctor_get(v___y_603_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___y_603_);
if (v_isSharedCheck_628_ == 0)
{
v___x_609_ = v___y_603_;
v_isShared_610_ = v_isSharedCheck_628_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_size_607_);
lean_inc(v_data_606_);
lean_dec(v___y_603_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_628_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_data_611_; lean_object* v_size_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_627_; 
v_data_611_ = lean_ctor_get(v___y_605_, 0);
v_size_612_ = lean_ctor_get(v___y_605_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v___y_605_);
if (v_isSharedCheck_627_ == 0)
{
v___x_614_ = v___y_605_;
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_size_612_);
lean_inc(v_data_611_);
lean_dec(v___y_605_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_outputData_619_; 
v___x_616_ = l_Array_append___redArg(v_data_606_, v_data_611_);
lean_dec_ref(v_data_611_);
v___x_617_ = lean_nat_add(v_size_607_, v_size_612_);
lean_dec(v_size_612_);
lean_dec(v_size_607_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_617_);
lean_ctor_set(v___x_614_, 0, v___x_616_);
v_outputData_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_617_);
v_outputData_619_ = v_reuseFailAlloc_626_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v_remaining_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v_remaining_620_ = lean_nat_sub(v_limitSize_593_, v___y_602_);
lean_dec(v_limitSize_593_);
v___x_621_ = lean_nat_sub(v___y_598_, v___y_602_);
lean_dec(v___y_602_);
lean_dec(v___y_598_);
v___x_622_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_622_, 0, v___y_599_);
lean_ctor_set(v___x_622_, 1, v_outputData_619_);
lean_ctor_set(v___x_622_, 2, v___y_596_);
lean_ctor_set(v___x_622_, 3, v___y_600_);
lean_ctor_set(v___x_622_, 4, v___y_604_);
lean_ctor_set(v___x_622_, 5, v___x_621_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*6, v___y_601_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*6 + 1, v___y_595_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*6 + 2, v___y_597_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_remaining_620_);
lean_ctor_set(v___x_609_, 0, v___x_622_);
v___x_624_ = v___x_609_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_remaining_620_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
v___jp_638_:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v_fst_639_);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_fst_639_);
lean_ctor_set(v___x_645_, 1, v___x_642_);
v___y_595_ = v_userClosedBody_635_;
v___y_596_ = v_state_631_;
v___y_597_ = v_omitBody_636_;
v___y_598_ = v_userDataBytes_637_;
v___y_599_ = v_fst_640_;
v___y_600_ = v_knownSize_632_;
v___y_601_ = v_sentMessage_634_;
v___y_602_ = v_snd_641_;
v___y_603_ = v_outputData_630_;
v___y_604_ = v_messageHead_633_;
v___y_605_ = v___x_645_;
goto v___jp_594_;
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_643_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_639_, v___x_646_, v___x_647_, v___x_642_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v_fst_639_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___y_595_ = v_userClosedBody_635_;
v___y_596_ = v_state_631_;
v___y_597_ = v_omitBody_636_;
v___y_598_ = v_userDataBytes_637_;
v___y_599_ = v_fst_640_;
v___y_600_ = v_knownSize_632_;
v___y_601_ = v_sentMessage_634_;
v___y_602_ = v_snd_641_;
v___y_603_ = v_outputData_630_;
v___y_604_ = v_messageHead_633_;
v___y_605_ = v___x_649_;
goto v___jp_594_;
}
}
v___jp_650_:
{
lean_object* v_snd_652_; lean_object* v_fst_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; 
v_snd_652_ = lean_ctor_get(v___y_651_, 1);
lean_inc(v_snd_652_);
v_fst_653_ = lean_ctor_get(v___y_651_, 0);
lean_inc(v_fst_653_);
lean_dec_ref(v___y_651_);
v_fst_654_ = lean_ctor_get(v_snd_652_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_snd_652_, 1);
lean_inc(v_snd_655_);
lean_dec(v_snd_652_);
v_fst_639_ = v_fst_653_;
v_fst_640_ = v_fst_654_;
v_snd_641_ = v_snd_655_;
goto v___jp_638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_670_, lean_object* v_writer_671_, lean_object* v_limitSize_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_671_, v_limitSize_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_674_, lean_object* v_writer_675_, lean_object* v_limitSize_676_){
_start:
{
uint8_t v_dir_boxed_677_; lean_object* v_res_678_; 
v_dir_boxed_677_ = lean_unbox(v_dir_674_);
v_res_678_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_677_, v_writer_675_, v_limitSize_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_679_, size_t v_i_680_, size_t v_stop_681_, lean_object* v_b_682_){
_start:
{
lean_object* v___y_684_; uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_eq(v_i_680_, v_stop_681_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v_data_690_; uint8_t v___x_691_; 
v___x_689_ = lean_array_uget_borrowed(v_as_679_, v_i_680_);
v_data_690_ = lean_ctor_get(v___x_689_, 0);
v___x_691_ = l_ByteArray_isEmpty(v_data_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
lean_inc(v___x_689_);
v___x_692_ = lean_array_push(v_b_682_, v___x_689_);
v___y_684_ = v___x_692_;
goto v___jp_683_;
}
else
{
v___y_684_ = v_b_682_;
goto v___jp_683_;
}
}
else
{
return v_b_682_;
}
v___jp_683_:
{
size_t v___x_685_; size_t v___x_686_; 
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_add(v_i_680_, v___x_685_);
v_i_680_ = v___x_686_;
v_b_682_ = v___y_684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_stop_695_, lean_object* v_b_696_){
_start:
{
size_t v_i_boxed_697_; size_t v_stop_boxed_698_; lean_object* v_res_699_; 
v_i_boxed_697_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_stop_boxed_698_ = lean_unbox_usize(v_stop_695_);
lean_dec(v_stop_695_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_693_, v_i_boxed_697_, v_stop_boxed_698_, v_b_696_);
lean_dec_ref(v_as_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_700_, size_t v_i_701_, lean_object* v_bs_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_lt(v_i_701_, v_sz_700_);
if (v___x_703_ == 0)
{
return v_bs_702_;
}
else
{
lean_object* v_v_704_; lean_object* v___x_705_; lean_object* v_bs_x27_706_; uint32_t v___x_707_; uint8_t v___x_708_; size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_v_704_ = lean_array_uget(v_bs_702_, v_i_701_);
v___x_705_ = lean_unsigned_to_nat(0u);
v_bs_x27_706_ = lean_array_uset(v_bs_702_, v_i_701_, v___x_705_);
v___x_707_ = lean_unbox_uint32(v_v_704_);
lean_dec(v_v_704_);
v___x_708_ = lean_uint32_to_uint8(v___x_707_);
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_add(v_i_701_, v___x_709_);
v___x_711_ = lean_box(v___x_708_);
v___x_712_ = lean_array_uset(v_bs_x27_706_, v_i_701_, v___x_711_);
v_i_701_ = v___x_710_;
v_bs_702_ = v___x_712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_714_, lean_object* v_i_715_, lean_object* v_bs_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_714_);
lean_dec(v_sz_714_);
v_i_boxed_718_ = lean_unbox_usize(v_i_715_);
lean_dec(v_i_715_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_717_, v_i_boxed_718_, v_bs_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_722_, size_t v_i_723_, size_t v_stop_724_, lean_object* v_b_725_){
_start:
{
lean_object* v___y_727_; uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_eq(v_i_723_, v_stop_724_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = lean_array_uget_borrowed(v_as_722_, v_i_723_);
v_fst_733_ = lean_ctor_get(v___x_732_, 0);
v_snd_734_ = lean_ctor_get(v___x_732_, 1);
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_736_ = lean_string_append(v_b_725_, v___x_735_);
v___x_737_ = lean_string_append(v___x_736_, v_fst_733_);
if (lean_obj_tag(v_snd_734_) == 0)
{
v___y_727_ = v___x_737_;
goto v___jp_726_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_val_738_ = lean_ctor_get(v_snd_734_, 0);
v___x_739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_738_);
v___x_740_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_738_);
v___x_741_ = lean_string_append(v___x_739_, v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = lean_string_append(v___x_737_, v___x_741_);
lean_dec_ref(v___x_741_);
v___y_727_ = v___x_742_;
goto v___jp_726_;
}
}
else
{
return v_b_725_;
}
v___jp_726_:
{
size_t v___x_728_; size_t v___x_729_; 
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_723_, v___x_728_);
v_i_723_ = v___x_729_;
v_b_725_ = v___y_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_stop_745_, lean_object* v_b_746_){
_start:
{
size_t v_i_boxed_747_; size_t v_stop_boxed_748_; lean_object* v_res_749_; 
v_i_boxed_747_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_stop_boxed_748_ = lean_unbox_usize(v_stop_745_);
lean_dec(v_stop_745_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_743_, v_i_boxed_747_, v_stop_boxed_748_, v_b_746_);
lean_dec_ref(v_as_743_);
return v_res_749_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_752_ = lean_string_to_utf8(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, lean_object* v_b_757_){
_start:
{
lean_object* v___y_759_; uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v_data_778_; lean_object* v_extensions_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_820_; 
v___x_777_ = lean_array_uget(v_as_754_, v_i_755_);
v_data_778_ = lean_ctor_get(v___x_777_, 0);
v_extensions_779_ = lean_ctor_get(v___x_777_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_820_ == 0)
{
v___x_781_ = v___x_777_;
v_isShared_782_ = v_isSharedCheck_820_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_extensions_779_);
lean_inc(v_data_778_);
lean_dec(v___x_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_820_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_chunkLen_783_; lean_object* v___y_785_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_chunkLen_783_ = lean_byte_array_size(v_data_778_);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_array_get_size(v_extensions_779_);
v___x_816_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_dec_ref(v_extensions_779_);
v___y_785_ = v___x_813_;
goto v___jp_784_;
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_815_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_779_, v___x_817_, v___x_818_, v___x_813_);
lean_dec_ref(v_extensions_779_);
v___y_785_ = v___x_819_;
goto v___jp_784_;
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; size_t v_sz_789_; size_t v___x_790_; lean_object* v___x_791_; lean_object* v_size_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_786_ = lean_unsigned_to_nat(16u);
v___x_787_ = l_Nat_toDigits(v___x_786_, v_chunkLen_783_);
v___x_788_ = lean_array_mk(v___x_787_);
v_sz_789_ = lean_array_size(v___x_788_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_789_, v___x_790_, v___x_788_);
v_size_792_ = lean_byte_array_mk(v___x_791_);
v___x_793_ = lean_string_to_utf8(v___y_785_);
lean_dec_ref(v___y_785_);
v___x_794_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_795_ = lean_unsigned_to_nat(5u);
v___x_796_ = lean_mk_empty_array_with_capacity(v___x_795_);
v___x_797_ = lean_array_push(v___x_796_, v_size_792_);
v___x_798_ = lean_array_push(v___x_797_, v___x_793_);
v___x_799_ = lean_array_push(v___x_798_, v___x_794_);
v___x_800_ = lean_array_push(v___x_799_, v_data_778_);
v___x_801_ = lean_array_push(v___x_800_, v___x_794_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_array_get_size(v___x_801_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_806_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_802_);
lean_ctor_set(v___x_781_, 0, v___x_801_);
v___x_806_ = v___x_781_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_802_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_759_ = v___x_806_;
goto v___jp_758_;
}
}
else
{
size_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = lean_usize_of_nat(v___x_803_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_801_, v___x_790_, v___x_808_, v___x_802_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_809_);
lean_ctor_set(v___x_781_, 0, v___x_801_);
v___x_811_ = v___x_781_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_759_ = v___x_811_;
goto v___jp_758_;
}
}
}
}
}
else
{
return v_b_757_;
}
v___jp_758_:
{
lean_object* v_data_760_; lean_object* v_size_761_; lean_object* v_data_762_; lean_object* v_size_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_775_; 
v_data_760_ = lean_ctor_get(v_b_757_, 0);
lean_inc_ref(v_data_760_);
v_size_761_ = lean_ctor_get(v_b_757_, 1);
lean_inc(v_size_761_);
lean_dec_ref(v_b_757_);
v_data_762_ = lean_ctor_get(v___y_759_, 0);
v_size_763_ = lean_ctor_get(v___y_759_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___y_759_);
if (v_isSharedCheck_775_ == 0)
{
v___x_765_ = v___y_759_;
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_size_763_);
lean_inc(v_data_762_);
lean_dec(v___y_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = l_Array_append___redArg(v_data_760_, v_data_762_);
lean_dec_ref(v_data_762_);
v___x_768_ = lean_nat_add(v_size_761_, v_size_763_);
lean_dec(v_size_763_);
lean_dec(v_size_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_768_);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_755_, v___x_771_);
v_i_755_ = v___x_772_;
v_b_757_ = v___x_770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_821_, lean_object* v_i_822_, lean_object* v_stop_823_, lean_object* v_b_824_){
_start:
{
size_t v_i_boxed_825_; size_t v_stop_boxed_826_; lean_object* v_res_827_; 
v_i_boxed_825_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_stop_boxed_826_ = lean_unbox_usize(v_stop_823_);
lean_dec(v_stop_823_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_821_, v_i_boxed_825_, v_stop_boxed_826_, v_b_824_);
lean_dec_ref(v_as_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_830_){
_start:
{
lean_object* v_userData_831_; lean_object* v_outputData_832_; lean_object* v_state_833_; lean_object* v_knownSize_834_; lean_object* v_messageHead_835_; uint8_t v_sentMessage_836_; uint8_t v_userClosedBody_837_; uint8_t v_omitBody_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___y_842_; uint8_t v___x_857_; 
v_userData_831_ = lean_ctor_get(v_writer_830_, 0);
v_outputData_832_ = lean_ctor_get(v_writer_830_, 1);
v_state_833_ = lean_ctor_get(v_writer_830_, 2);
v_knownSize_834_ = lean_ctor_get(v_writer_830_, 3);
v_messageHead_835_ = lean_ctor_get(v_writer_830_, 4);
v_sentMessage_836_ = lean_ctor_get_uint8(v_writer_830_, sizeof(void*)*6);
v_userClosedBody_837_ = lean_ctor_get_uint8(v_writer_830_, sizeof(void*)*6 + 1);
v_omitBody_838_ = lean_ctor_get_uint8(v_writer_830_, sizeof(void*)*6 + 2);
v___x_839_ = lean_array_get_size(v_userData_831_);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_nat_dec_eq(v___x_839_, v___x_840_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; uint8_t v___x_859_; 
lean_inc(v_messageHead_835_);
lean_inc(v_knownSize_834_);
lean_inc(v_state_833_);
lean_inc_ref(v_outputData_832_);
lean_inc_ref(v_userData_831_);
lean_dec_ref(v_writer_830_);
v___x_858_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_859_ = lean_nat_dec_lt(v___x_840_, v___x_839_);
if (v___x_859_ == 0)
{
lean_dec_ref(v_userData_831_);
v___y_842_ = v___x_858_;
goto v___jp_841_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_le(v___x_839_, v___x_839_);
if (v___x_860_ == 0)
{
if (v___x_859_ == 0)
{
lean_dec_ref(v_userData_831_);
v___y_842_ = v___x_858_;
goto v___jp_841_;
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_839_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_831_, v___x_861_, v___x_862_, v___x_858_);
lean_dec_ref(v_userData_831_);
v___y_842_ = v___x_863_;
goto v___jp_841_;
}
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_839_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_831_, v___x_864_, v___x_865_, v___x_858_);
lean_dec_ref(v_userData_831_);
v___y_842_ = v___x_866_;
goto v___jp_841_;
}
}
}
else
{
return v_writer_830_;
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_844_ = lean_array_get_size(v___y_842_);
v___x_845_ = lean_nat_dec_lt(v___x_840_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec_ref(v___y_842_);
v___x_846_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_846_, 0, v___x_843_);
lean_ctor_set(v___x_846_, 1, v_outputData_832_);
lean_ctor_set(v___x_846_, 2, v_state_833_);
lean_ctor_set(v___x_846_, 3, v_knownSize_834_);
lean_ctor_set(v___x_846_, 4, v_messageHead_835_);
lean_ctor_set(v___x_846_, 5, v___x_840_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*6, v_sentMessage_836_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*6 + 1, v_userClosedBody_837_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*6 + 2, v_omitBody_838_);
return v___x_846_;
}
else
{
uint8_t v___x_847_; 
v___x_847_ = lean_nat_dec_le(v___x_844_, v___x_844_);
if (v___x_847_ == 0)
{
if (v___x_845_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v___y_842_);
v___x_848_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_848_, 0, v___x_843_);
lean_ctor_set(v___x_848_, 1, v_outputData_832_);
lean_ctor_set(v___x_848_, 2, v_state_833_);
lean_ctor_set(v___x_848_, 3, v_knownSize_834_);
lean_ctor_set(v___x_848_, 4, v_messageHead_835_);
lean_ctor_set(v___x_848_, 5, v___x_840_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*6, v_sentMessage_836_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*6 + 1, v_userClosedBody_837_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*6 + 2, v_omitBody_838_);
return v___x_848_;
}
else
{
size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_849_ = ((size_t)0ULL);
v___x_850_ = lean_usize_of_nat(v___x_844_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_842_, v___x_849_, v___x_850_, v_outputData_832_);
lean_dec_ref(v___y_842_);
v___x_852_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_852_, 0, v___x_843_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
lean_ctor_set(v___x_852_, 2, v_state_833_);
lean_ctor_set(v___x_852_, 3, v_knownSize_834_);
lean_ctor_set(v___x_852_, 4, v_messageHead_835_);
lean_ctor_set(v___x_852_, 5, v___x_840_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*6, v_sentMessage_836_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*6 + 1, v_userClosedBody_837_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*6 + 2, v_omitBody_838_);
return v___x_852_;
}
}
else
{
size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = ((size_t)0ULL);
v___x_854_ = lean_usize_of_nat(v___x_844_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_842_, v___x_853_, v___x_854_, v_outputData_832_);
lean_dec_ref(v___y_842_);
v___x_856_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_856_, 0, v___x_843_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_ctor_set(v___x_856_, 2, v_state_833_);
lean_ctor_set(v___x_856_, 3, v_knownSize_834_);
lean_ctor_set(v___x_856_, 4, v_messageHead_835_);
lean_ctor_set(v___x_856_, 5, v___x_840_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*6, v_sentMessage_836_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*6 + 1, v_userClosedBody_837_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*6 + 2, v_omitBody_838_);
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_867_, lean_object* v_writer_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_870_, lean_object* v_writer_871_){
_start:
{
uint8_t v_dir_boxed_872_; lean_object* v_res_873_; 
v_dir_boxed_872_ = lean_unbox(v_dir_870_);
v_res_873_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_872_, v_writer_871_);
return v_res_873_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_876_ = lean_string_to_utf8(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_878_ = lean_byte_array_size(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_879_){
_start:
{
lean_object* v_writer_880_; lean_object* v_outputData_881_; lean_object* v_userData_882_; lean_object* v_knownSize_883_; lean_object* v_messageHead_884_; uint8_t v_sentMessage_885_; uint8_t v_userClosedBody_886_; uint8_t v_omitBody_887_; lean_object* v_userDataBytes_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_909_; 
v_writer_880_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_879_);
v_outputData_881_ = lean_ctor_get(v_writer_880_, 1);
v_userData_882_ = lean_ctor_get(v_writer_880_, 0);
v_knownSize_883_ = lean_ctor_get(v_writer_880_, 3);
v_messageHead_884_ = lean_ctor_get(v_writer_880_, 4);
v_sentMessage_885_ = lean_ctor_get_uint8(v_writer_880_, sizeof(void*)*6);
v_userClosedBody_886_ = lean_ctor_get_uint8(v_writer_880_, sizeof(void*)*6 + 1);
v_omitBody_887_ = lean_ctor_get_uint8(v_writer_880_, sizeof(void*)*6 + 2);
v_userDataBytes_888_ = lean_ctor_get(v_writer_880_, 5);
v_isSharedCheck_909_ = !lean_is_exclusive(v_writer_880_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_writer_880_, 2);
lean_dec(v_unused_910_);
v___x_890_ = v_writer_880_;
v_isShared_891_ = v_isSharedCheck_909_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_userDataBytes_888_);
lean_inc(v_messageHead_884_);
lean_inc(v_knownSize_883_);
lean_inc(v_outputData_881_);
lean_inc(v_userData_882_);
lean_dec(v_writer_880_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_909_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_data_892_; lean_object* v_size_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_908_; 
v_data_892_ = lean_ctor_get(v_outputData_881_, 0);
v_size_893_ = lean_ctor_get(v_outputData_881_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_outputData_881_);
if (v_isSharedCheck_908_ == 0)
{
v___x_895_ = v_outputData_881_;
v_isShared_896_ = v_isSharedCheck_908_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_size_893_);
lean_inc(v_data_892_);
lean_dec(v_outputData_881_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_908_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_897_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_898_ = lean_array_push(v_data_892_, v___x_897_);
v___x_899_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_900_ = lean_nat_add(v_size_893_, v___x_899_);
lean_dec(v_size_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___x_900_);
lean_ctor_set(v___x_895_, 0, v___x_898_);
v___x_902_ = v___x_895_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_907_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_box(6);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 2, v___x_903_);
lean_ctor_set(v___x_890_, 1, v___x_902_);
v___x_905_ = v___x_890_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_userData_882_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_knownSize_883_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_messageHead_884_);
lean_ctor_set(v_reuseFailAlloc_906_, 5, v_userDataBytes_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*6, v_sentMessage_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*6 + 1, v_userClosedBody_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*6 + 2, v_omitBody_887_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_911_, lean_object* v_writer_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_914_, lean_object* v_writer_915_){
_start:
{
uint8_t v_dir_boxed_916_; lean_object* v_res_917_; 
v_dir_boxed_916_ = lean_unbox(v_dir_914_);
v_res_917_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_916_, v_writer_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_918_, size_t v_i_919_, size_t v_stop_920_, lean_object* v_b_921_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_eq(v_i_919_, v_stop_920_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v_data_924_; lean_object* v_data_925_; lean_object* v_size_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_939_; 
v___x_923_ = lean_array_uget_borrowed(v_as_918_, v_i_919_);
v_data_924_ = lean_ctor_get(v___x_923_, 0);
v_data_925_ = lean_ctor_get(v_b_921_, 0);
v_size_926_ = lean_ctor_get(v_b_921_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_b_921_);
if (v_isSharedCheck_939_ == 0)
{
v___x_928_ = v_b_921_;
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_size_926_);
lean_inc(v_data_925_);
lean_dec(v_b_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
lean_inc_ref(v_data_924_);
v___x_930_ = lean_array_push(v_data_925_, v_data_924_);
v___x_931_ = lean_byte_array_size(v_data_924_);
v___x_932_ = lean_nat_add(v_size_926_, v___x_931_);
lean_dec(v_size_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_932_);
lean_ctor_set(v___x_928_, 0, v___x_930_);
v___x_934_ = v___x_928_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_932_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_919_, v___x_935_);
v_i_919_ = v___x_936_;
v_b_921_ = v___x_934_;
goto _start;
}
}
}
else
{
return v_b_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_940_, lean_object* v_i_941_, lean_object* v_stop_942_, lean_object* v_b_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; lean_object* v_res_946_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_942_);
lean_dec(v_stop_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_940_, v_i_boxed_944_, v_stop_boxed_945_, v_b_943_);
lean_dec_ref(v_as_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_947_){
_start:
{
lean_object* v_userData_948_; lean_object* v_outputData_949_; lean_object* v_state_950_; lean_object* v_knownSize_951_; lean_object* v_messageHead_952_; uint8_t v_sentMessage_953_; uint8_t v_userClosedBody_954_; uint8_t v_omitBody_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_982_; 
v_userData_948_ = lean_ctor_get(v_writer_947_, 0);
v_outputData_949_ = lean_ctor_get(v_writer_947_, 1);
v_state_950_ = lean_ctor_get(v_writer_947_, 2);
v_knownSize_951_ = lean_ctor_get(v_writer_947_, 3);
v_messageHead_952_ = lean_ctor_get(v_writer_947_, 4);
v_sentMessage_953_ = lean_ctor_get_uint8(v_writer_947_, sizeof(void*)*6);
v_userClosedBody_954_ = lean_ctor_get_uint8(v_writer_947_, sizeof(void*)*6 + 1);
v_omitBody_955_ = lean_ctor_get_uint8(v_writer_947_, sizeof(void*)*6 + 2);
v_isSharedCheck_982_ = !lean_is_exclusive(v_writer_947_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_writer_947_, 5);
lean_dec(v_unused_983_);
v___x_957_ = v_writer_947_;
v_isShared_958_ = v_isSharedCheck_982_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_messageHead_952_);
lean_inc(v_knownSize_951_);
lean_inc(v_state_950_);
lean_inc(v_outputData_949_);
lean_inc(v_userData_948_);
lean_dec(v_writer_947_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_982_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_961_ = lean_array_get_size(v_userData_948_);
v___x_962_ = lean_nat_dec_lt(v___x_959_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v_userData_948_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 5, v___x_959_);
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_964_ = v___x_957_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_outputData_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_state_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_knownSize_951_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_messageHead_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v___x_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*6, v_sentMessage_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*6 + 1, v_userClosedBody_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*6 + 2, v_omitBody_955_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
uint8_t v___x_966_; 
v___x_966_ = lean_nat_dec_le(v___x_961_, v___x_961_);
if (v___x_966_ == 0)
{
if (v___x_962_ == 0)
{
lean_object* v___x_968_; 
lean_dec_ref(v_userData_948_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 5, v___x_959_);
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_968_ = v___x_957_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_outputData_949_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_state_950_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_knownSize_951_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_messageHead_952_);
lean_ctor_set(v_reuseFailAlloc_969_, 5, v___x_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*6, v_sentMessage_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*6 + 1, v_userClosedBody_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*6 + 2, v_omitBody_955_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_970_ = ((size_t)0ULL);
v___x_971_ = lean_usize_of_nat(v___x_961_);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_948_, v___x_970_, v___x_971_, v_outputData_949_);
lean_dec_ref(v_userData_948_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 5, v___x_959_);
lean_ctor_set(v___x_957_, 1, v___x_972_);
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_974_ = v___x_957_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_state_950_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_knownSize_951_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_messageHead_952_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v___x_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*6, v_sentMessage_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*6 + 1, v_userClosedBody_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*6 + 2, v_omitBody_955_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_976_ = ((size_t)0ULL);
v___x_977_ = lean_usize_of_nat(v___x_961_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_948_, v___x_976_, v___x_977_, v_outputData_949_);
lean_dec_ref(v_userData_948_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 5, v___x_959_);
lean_ctor_set(v___x_957_, 1, v___x_978_);
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_980_ = v___x_957_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_state_950_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_knownSize_951_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_messageHead_952_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v___x_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*6, v_sentMessage_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*6 + 1, v_userClosedBody_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*6 + 2, v_omitBody_955_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_984_, lean_object* v_writer_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_987_, lean_object* v_writer_988_){
_start:
{
uint8_t v_dir_boxed_989_; lean_object* v_res_990_; 
v_dir_boxed_989_ = lean_unbox(v_dir_987_);
v_res_990_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_989_, v_writer_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_991_, lean_object* v_x1_992_, lean_object* v_x2_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_byte_array_size(v_x1_992_);
v___x_996_ = lean_byte_array_size(v_x2_993_);
v___x_997_ = lean_byte_array_copy_slice(v_x2_993_, v___x_994_, v_x1_992_, v___x_995_, v___x_996_, v___x_991_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_998_, lean_object* v_x1_999_, lean_object* v_x2_1000_){
_start:
{
uint8_t v___x_115__boxed_1001_; lean_object* v_res_1002_; 
v___x_115__boxed_1001_ = lean_unbox(v___x_998_);
v_res_1002_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_115__boxed_1001_, v_x1_999_, v_x2_1000_);
lean_dec_ref(v_x2_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_1006_){
_start:
{
lean_object* v_userData_1007_; lean_object* v_outputData_1008_; lean_object* v_state_1009_; lean_object* v_knownSize_1010_; lean_object* v_messageHead_1011_; uint8_t v_sentMessage_1012_; uint8_t v_userClosedBody_1013_; uint8_t v_omitBody_1014_; lean_object* v_userDataBytes_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1043_; 
v_userData_1007_ = lean_ctor_get(v_writer_1006_, 0);
v_outputData_1008_ = lean_ctor_get(v_writer_1006_, 1);
v_state_1009_ = lean_ctor_get(v_writer_1006_, 2);
v_knownSize_1010_ = lean_ctor_get(v_writer_1006_, 3);
v_messageHead_1011_ = lean_ctor_get(v_writer_1006_, 4);
v_sentMessage_1012_ = lean_ctor_get_uint8(v_writer_1006_, sizeof(void*)*6);
v_userClosedBody_1013_ = lean_ctor_get_uint8(v_writer_1006_, sizeof(void*)*6 + 1);
v_omitBody_1014_ = lean_ctor_get_uint8(v_writer_1006_, sizeof(void*)*6 + 2);
v_userDataBytes_1015_ = lean_ctor_get(v_writer_1006_, 5);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_writer_1006_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1017_ = v_writer_1006_;
v_isShared_1018_ = v_isSharedCheck_1043_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_userDataBytes_1015_);
lean_inc(v_messageHead_1011_);
lean_inc(v_knownSize_1010_);
lean_inc(v_state_1009_);
lean_inc(v_outputData_1008_);
lean_inc(v_userData_1007_);
lean_dec(v_writer_1006_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1043_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___y_1020_; lean_object* v_data_1027_; lean_object* v_size_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_data_1027_ = lean_ctor_get(v_outputData_1008_, 0);
lean_inc_ref(v_data_1027_);
v_size_1028_ = lean_ctor_get(v_outputData_1008_, 1);
lean_inc(v_size_1028_);
lean_dec_ref(v_outputData_1008_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_array_get_size(v_data_1027_);
v___x_1031_ = lean_nat_dec_eq(v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1032_ = lean_mk_empty_byte_array(v_size_1028_);
lean_dec(v_size_1028_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1035_ = lean_nat_dec_lt(v___x_1033_, v___x_1030_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v_data_1027_);
v___y_1020_ = v___x_1032_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1036_; lean_object* v___f_1037_; size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1036_ = lean_box(v___x_1031_);
v___f_1037_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1037_, 0, v___x_1036_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = lean_usize_of_nat(v___x_1030_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1034_, v___f_1037_, v_data_1027_, v___x_1038_, v___x_1039_, v___x_1032_);
v___y_1020_ = v___x_1040_;
goto v___jp_1019_;
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v_size_1028_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_array_fget(v_data_1027_, v___x_1041_);
lean_dec_ref(v_data_1027_);
v___y_1020_ = v___x_1042_;
goto v___jp_1019_;
}
v___jp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v___x_1021_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_userData_1007_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_state_1009_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_knownSize_1010_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v_messageHead_1011_);
lean_ctor_set(v_reuseFailAlloc_1026_, 5, v_userDataBytes_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1026_, sizeof(void*)*6, v_sentMessage_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1026_, sizeof(void*)*6 + 1, v_userClosedBody_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1026_, sizeof(void*)*6 + 2, v_omitBody_1014_);
v___x_1023_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___y_1020_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1044_, lean_object* v_writer_1045_){
_start:
{
lean_object* v_userData_1046_; lean_object* v_outputData_1047_; lean_object* v_state_1048_; lean_object* v_knownSize_1049_; lean_object* v_messageHead_1050_; uint8_t v_sentMessage_1051_; uint8_t v_userClosedBody_1052_; uint8_t v_omitBody_1053_; lean_object* v_userDataBytes_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1082_; 
v_userData_1046_ = lean_ctor_get(v_writer_1045_, 0);
v_outputData_1047_ = lean_ctor_get(v_writer_1045_, 1);
v_state_1048_ = lean_ctor_get(v_writer_1045_, 2);
v_knownSize_1049_ = lean_ctor_get(v_writer_1045_, 3);
v_messageHead_1050_ = lean_ctor_get(v_writer_1045_, 4);
v_sentMessage_1051_ = lean_ctor_get_uint8(v_writer_1045_, sizeof(void*)*6);
v_userClosedBody_1052_ = lean_ctor_get_uint8(v_writer_1045_, sizeof(void*)*6 + 1);
v_omitBody_1053_ = lean_ctor_get_uint8(v_writer_1045_, sizeof(void*)*6 + 2);
v_userDataBytes_1054_ = lean_ctor_get(v_writer_1045_, 5);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_writer_1045_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1056_ = v_writer_1045_;
v_isShared_1057_ = v_isSharedCheck_1082_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_userDataBytes_1054_);
lean_inc(v_messageHead_1050_);
lean_inc(v_knownSize_1049_);
lean_inc(v_state_1048_);
lean_inc(v_outputData_1047_);
lean_inc(v_userData_1046_);
lean_dec(v_writer_1045_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1082_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___y_1059_; lean_object* v_data_1066_; lean_object* v_size_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_data_1066_ = lean_ctor_get(v_outputData_1047_, 0);
lean_inc_ref(v_data_1066_);
v_size_1067_ = lean_ctor_get(v_outputData_1047_, 1);
lean_inc(v_size_1067_);
lean_dec_ref(v_outputData_1047_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_array_get_size(v_data_1066_);
v___x_1070_ = lean_nat_dec_eq(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1071_ = lean_mk_empty_byte_array(v_size_1067_);
lean_dec(v_size_1067_);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1074_ = lean_nat_dec_lt(v___x_1072_, v___x_1069_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_data_1066_);
v___y_1059_ = v___x_1071_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1075_; lean_object* v___f_1076_; size_t v___x_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1075_ = lean_box(v___x_1070_);
v___f_1076_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1076_, 0, v___x_1075_);
v___x_1077_ = ((size_t)0ULL);
v___x_1078_ = lean_usize_of_nat(v___x_1069_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1073_, v___f_1076_, v_data_1066_, v___x_1077_, v___x_1078_, v___x_1071_);
v___y_1059_ = v___x_1079_;
goto v___jp_1058_;
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v_size_1067_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_array_fget(v_data_1066_, v___x_1080_);
lean_dec_ref(v_data_1066_);
v___y_1059_ = v___x_1081_;
goto v___jp_1058_;
}
v___jp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1060_);
v___x_1062_ = v___x_1056_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_userData_1046_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_state_1048_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_knownSize_1049_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_messageHead_1050_);
lean_ctor_set(v_reuseFailAlloc_1065_, 5, v_userDataBytes_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1065_, sizeof(void*)*6, v_sentMessage_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1065_, sizeof(void*)*6 + 1, v_userClosedBody_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1065_, sizeof(void*)*6 + 2, v_omitBody_1053_);
v___x_1062_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___y_1059_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1083_, lean_object* v_writer_1084_){
_start:
{
uint8_t v_dir_boxed_1085_; lean_object* v_res_1086_; 
v_dir_boxed_1085_ = lean_unbox(v_dir_1083_);
v_res_1086_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1085_, v_writer_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1087_, lean_object* v_writer_1088_){
_start:
{
lean_object* v_userData_1089_; lean_object* v_outputData_1090_; lean_object* v_knownSize_1091_; lean_object* v_messageHead_1092_; uint8_t v_sentMessage_1093_; uint8_t v_userClosedBody_1094_; uint8_t v_omitBody_1095_; lean_object* v_userDataBytes_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_userData_1089_ = lean_ctor_get(v_writer_1088_, 0);
v_outputData_1090_ = lean_ctor_get(v_writer_1088_, 1);
v_knownSize_1091_ = lean_ctor_get(v_writer_1088_, 3);
v_messageHead_1092_ = lean_ctor_get(v_writer_1088_, 4);
v_sentMessage_1093_ = lean_ctor_get_uint8(v_writer_1088_, sizeof(void*)*6);
v_userClosedBody_1094_ = lean_ctor_get_uint8(v_writer_1088_, sizeof(void*)*6 + 1);
v_omitBody_1095_ = lean_ctor_get_uint8(v_writer_1088_, sizeof(void*)*6 + 2);
v_userDataBytes_1096_ = lean_ctor_get(v_writer_1088_, 5);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_writer_1088_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; 
v_unused_1104_ = lean_ctor_get(v_writer_1088_, 2);
lean_dec(v_unused_1104_);
v___x_1098_ = v_writer_1088_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_userDataBytes_1096_);
lean_inc(v_messageHead_1092_);
lean_inc(v_knownSize_1091_);
lean_inc(v_outputData_1090_);
lean_inc(v_userData_1089_);
lean_dec(v_writer_1088_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v_state_1087_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_userData_1089_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_outputData_1090_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_state_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_knownSize_1091_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_messageHead_1092_);
lean_ctor_set(v_reuseFailAlloc_1102_, 5, v_userDataBytes_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*6, v_sentMessage_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*6 + 1, v_userClosedBody_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*6 + 2, v_omitBody_1095_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1105_, lean_object* v_state_1106_, lean_object* v_writer_1107_){
_start:
{
lean_object* v_userData_1108_; lean_object* v_outputData_1109_; lean_object* v_knownSize_1110_; lean_object* v_messageHead_1111_; uint8_t v_sentMessage_1112_; uint8_t v_userClosedBody_1113_; uint8_t v_omitBody_1114_; lean_object* v_userDataBytes_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_userData_1108_ = lean_ctor_get(v_writer_1107_, 0);
v_outputData_1109_ = lean_ctor_get(v_writer_1107_, 1);
v_knownSize_1110_ = lean_ctor_get(v_writer_1107_, 3);
v_messageHead_1111_ = lean_ctor_get(v_writer_1107_, 4);
v_sentMessage_1112_ = lean_ctor_get_uint8(v_writer_1107_, sizeof(void*)*6);
v_userClosedBody_1113_ = lean_ctor_get_uint8(v_writer_1107_, sizeof(void*)*6 + 1);
v_omitBody_1114_ = lean_ctor_get_uint8(v_writer_1107_, sizeof(void*)*6 + 2);
v_userDataBytes_1115_ = lean_ctor_get(v_writer_1107_, 5);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_writer_1107_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_writer_1107_, 2);
lean_dec(v_unused_1123_);
v___x_1117_ = v_writer_1107_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_userDataBytes_1115_);
lean_inc(v_messageHead_1111_);
lean_inc(v_knownSize_1110_);
lean_inc(v_outputData_1109_);
lean_inc(v_userData_1108_);
lean_dec(v_writer_1107_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 2, v_state_1106_);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_userData_1108_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_outputData_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_state_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_knownSize_1110_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_messageHead_1111_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_userDataBytes_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6, v_sentMessage_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6 + 1, v_userClosedBody_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6 + 2, v_omitBody_1114_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1124_, lean_object* v_state_1125_, lean_object* v_writer_1126_){
_start:
{
uint8_t v_dir_boxed_1127_; lean_object* v_res_1128_; 
v_dir_boxed_1127_ = lean_unbox(v_dir_1124_);
v_res_1128_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1127_, v_state_1125_, v_writer_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1129_, lean_object* v_messageHead_1130_, lean_object* v_writer_1131_){
_start:
{
lean_object* v_userData_1132_; lean_object* v_outputData_1133_; lean_object* v_state_1134_; lean_object* v_knownSize_1135_; lean_object* v_messageHead_1136_; uint8_t v_sentMessage_1137_; uint8_t v_userClosedBody_1138_; uint8_t v_omitBody_1139_; lean_object* v_userDataBytes_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1153_; 
v_userData_1132_ = lean_ctor_get(v_writer_1131_, 0);
v_outputData_1133_ = lean_ctor_get(v_writer_1131_, 1);
v_state_1134_ = lean_ctor_get(v_writer_1131_, 2);
v_knownSize_1135_ = lean_ctor_get(v_writer_1131_, 3);
v_messageHead_1136_ = lean_ctor_get(v_writer_1131_, 4);
v_sentMessage_1137_ = lean_ctor_get_uint8(v_writer_1131_, sizeof(void*)*6);
v_userClosedBody_1138_ = lean_ctor_get_uint8(v_writer_1131_, sizeof(void*)*6 + 1);
v_omitBody_1139_ = lean_ctor_get_uint8(v_writer_1131_, sizeof(void*)*6 + 2);
v_userDataBytes_1140_ = lean_ctor_get(v_writer_1131_, 5);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_writer_1131_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1142_ = v_writer_1131_;
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_userDataBytes_1140_);
lean_inc(v_messageHead_1136_);
lean_inc(v_knownSize_1135_);
lean_inc(v_state_1134_);
lean_inc(v_outputData_1133_);
lean_inc(v_userData_1132_);
lean_dec(v_writer_1131_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v___y_1145_; 
if (v_dir_1129_ == 0)
{
uint8_t v___x_1151_; 
v___x_1151_ = 1;
v___y_1145_ = v___x_1151_;
goto v___jp_1144_;
}
else
{
uint8_t v___x_1152_; 
v___x_1152_ = 0;
v___y_1145_ = v___x_1152_;
goto v___jp_1144_;
}
v___jp_1144_:
{
lean_object* v___x_6__overap_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_6__overap_1146_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1145_);
v___x_1147_ = lean_apply_2(v___x_6__overap_1146_, v_outputData_1133_, v_messageHead_1130_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1147_);
v___x_1149_ = v___x_1142_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_userData_1132_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_state_1134_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_knownSize_1135_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_messageHead_1136_);
lean_ctor_set(v_reuseFailAlloc_1150_, 5, v_userDataBytes_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, sizeof(void*)*6, v_sentMessage_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, sizeof(void*)*6 + 1, v_userClosedBody_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, sizeof(void*)*6 + 2, v_omitBody_1139_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1154_, lean_object* v_messageHead_1155_, lean_object* v_writer_1156_){
_start:
{
uint8_t v_dir_boxed_1157_; lean_object* v_res_1158_; 
v_dir_boxed_1157_ = lean_unbox(v_dir_1154_);
v_res_1158_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1157_, v_messageHead_1155_, v_writer_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_key_1161_; lean_object* v_value_1162_; lean_object* v_tail_1163_; uint8_t v___x_1164_; 
v_key_1161_ = lean_ctor_get(v_x_1160_, 0);
v_value_1162_ = lean_ctor_get(v_x_1160_, 1);
v_tail_1163_ = lean_ctor_get(v_x_1160_, 2);
v___x_1164_ = lean_string_dec_eq(v_key_1161_, v_a_1159_);
if (v___x_1164_ == 0)
{
v_x_1160_ = v_tail_1163_;
goto _start;
}
else
{
lean_inc(v_value_1162_);
return v_value_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg___boxed(lean_object* v_a_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1166_, v_x_1167_);
lean_dec(v_x_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(lean_object* v_m_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_buckets_1171_; lean_object* v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v_fold_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_buckets_1171_ = lean_ctor_get(v_m_1169_, 1);
v___x_1172_ = lean_array_get_size(v_buckets_1171_);
v___x_1173_ = lean_string_hash(v_a_1170_);
v___x_1174_ = 32ULL;
v___x_1175_ = lean_uint64_shift_right(v___x_1173_, v___x_1174_);
v_fold_1176_ = lean_uint64_xor(v___x_1173_, v___x_1175_);
v___x_1177_ = 16ULL;
v___x_1178_ = lean_uint64_shift_right(v_fold_1176_, v___x_1177_);
v___x_1179_ = lean_uint64_xor(v_fold_1176_, v___x_1178_);
v___x_1180_ = lean_uint64_to_usize(v___x_1179_);
v___x_1181_ = lean_usize_of_nat(v___x_1172_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_sub(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_usize_land(v___x_1180_, v___x_1183_);
v___x_1185_ = lean_array_uget_borrowed(v_buckets_1171_, v___x_1184_);
v___x_1186_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1170_, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg___boxed(lean_object* v_m_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1187_, v_a_1188_);
lean_dec_ref(v_a_1188_);
lean_dec_ref(v_m_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1190_, lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = 0;
return v___x_1192_;
}
else
{
lean_object* v_key_1193_; lean_object* v_tail_1194_; uint8_t v___x_1195_; 
v_key_1193_ = lean_ctor_get(v_x_1191_, 0);
v_tail_1194_ = lean_ctor_get(v_x_1191_, 2);
v___x_1195_ = lean_string_dec_eq(v_key_1193_, v_a_1190_);
if (v___x_1195_ == 0)
{
v_x_1191_ = v_tail_1194_;
goto _start;
}
else
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1197_, lean_object* v_x_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_a_1197_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_buckets_1203_; lean_object* v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v_fold_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_buckets_1203_ = lean_ctor_get(v_m_1201_, 1);
v___x_1204_ = lean_array_get_size(v_buckets_1203_);
v___x_1205_ = lean_string_hash(v_a_1202_);
v___x_1206_ = 32ULL;
v___x_1207_ = lean_uint64_shift_right(v___x_1205_, v___x_1206_);
v_fold_1208_ = lean_uint64_xor(v___x_1205_, v___x_1207_);
v___x_1209_ = 16ULL;
v___x_1210_ = lean_uint64_shift_right(v_fold_1208_, v___x_1209_);
v___x_1211_ = lean_uint64_xor(v_fold_1208_, v___x_1210_);
v___x_1212_ = lean_uint64_to_usize(v___x_1211_);
v___x_1213_ = lean_usize_of_nat(v___x_1204_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_sub(v___x_1213_, v___x_1214_);
v___x_1216_ = lean_usize_land(v___x_1212_, v___x_1215_);
v___x_1217_ = lean_array_uget_borrowed(v_buckets_1203_, v___x_1216_);
v___x_1218_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1202_, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1219_, v_a_1220_);
lean_dec_ref(v_a_1220_);
lean_dec_ref(v_m_1219_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(lean_object* v_s_1223_, lean_object* v_p_1224_){
_start:
{
uint32_t v___y_1226_; lean_object* v___x_1231_; uint8_t v_decide_1232_; 
v___x_1231_ = lean_string_utf8_byte_size(v_s_1223_);
v_decide_1232_ = lean_nat_dec_eq(v_p_1224_, v___x_1231_);
if (v_decide_1232_ == 0)
{
uint32_t v___x_1233_; uint8_t v___y_1235_; uint32_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1233_ = lean_string_utf8_get_fast(v_s_1223_, v_p_1224_);
v___x_1238_ = 65;
v___x_1239_ = lean_uint32_dec_le(v___x_1238_, v___x_1233_);
if (v___x_1239_ == 0)
{
v___y_1235_ = v___x_1239_;
goto v___jp_1234_;
}
else
{
uint32_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = 90;
v___x_1241_ = lean_uint32_dec_le(v___x_1233_, v___x_1240_);
v___y_1235_ = v___x_1241_;
goto v___jp_1234_;
}
v___jp_1234_:
{
if (v___y_1235_ == 0)
{
v___y_1226_ = v___x_1233_;
goto v___jp_1225_;
}
else
{
uint32_t v___x_1236_; uint32_t v___x_1237_; 
v___x_1236_ = 32;
v___x_1237_ = lean_uint32_add(v___x_1233_, v___x_1236_);
v___y_1226_ = v___x_1237_;
goto v___jp_1225_;
}
}
}
else
{
lean_dec(v_p_1224_);
return v_s_1223_;
}
v___jp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_inc(v_p_1224_);
v___x_1227_ = lean_string_utf8_set(v_s_1223_, v_p_1224_, v___y_1226_);
v___x_1228_ = l_Char_utf8Size(v___y_1226_);
v___x_1229_ = lean_nat_add(v_p_1224_, v___x_1228_);
lean_dec(v___x_1228_);
lean_dec(v_p_1224_);
v_s_1223_ = v___x_1227_;
v_p_1224_ = v___x_1229_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1243_, lean_object* v_writer_1244_){
_start:
{
uint8_t v___y_1246_; 
if (v_dir_1243_ == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = 1;
v___y_1246_ = v___x_1263_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
v___y_1246_ = v___x_1264_;
goto v___jp_1245_;
}
v___jp_1245_:
{
lean_object* v_messageHead_1247_; lean_object* v___x_1248_; lean_object* v_entries_1249_; lean_object* v_indexes_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_messageHead_1247_ = lean_ctor_get(v_writer_1244_, 4);
v___x_1248_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1246_, v_messageHead_1247_);
v_entries_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_entries_1249_);
v_indexes_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_indexes_1250_);
lean_dec_ref(v___x_1248_);
v___x_1251_ = l_Std_Http_Header_Name_connection;
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
uint8_t v___x_1253_; 
lean_dec_ref(v_indexes_1250_);
lean_dec_ref(v_entries_1249_);
v___x_1253_ = 1;
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_entry_1256_; lean_object* v___x_1257_; lean_object* v_snd_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_indexes_1250_, v___x_1251_);
lean_dec_ref(v_indexes_1250_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v_entry_1256_ = lean_array_fget(v___x_1254_, v___x_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_array_fget(v_entries_1249_, v_entry_1256_);
lean_dec(v_entry_1256_);
lean_dec_ref(v_entries_1249_);
v_snd_1258_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_snd_1258_);
lean_dec(v___x_1257_);
v___x_1259_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(v_snd_1258_, v___x_1255_);
v___x_1260_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_1261_ = lean_string_dec_eq(v___x_1259_, v___x_1260_);
lean_dec_ref(v___x_1259_);
if (v___x_1261_ == 0)
{
return v___x_1252_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = 0;
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1265_, lean_object* v_writer_1266_){
_start:
{
uint8_t v_dir_boxed_1267_; uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_dir_boxed_1267_ = lean_unbox(v_dir_1265_);
v_res_1268_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1267_, v_writer_1266_);
lean_dec_ref(v_writer_1266_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1270_, lean_object* v_m_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1271_, v_a_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_){
_start:
{
uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_res_1277_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1274_, v_m_1275_, v_a_1276_);
lean_dec_ref(v_a_1276_);
lean_dec_ref(v_m_1275_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_00_u03b2_1279_, lean_object* v_m_1280_, lean_object* v_a_1281_, lean_object* v_hma_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1280_, v_a_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___boxed(lean_object* v_00_u03b2_1284_, lean_object* v_m_1285_, lean_object* v_a_1286_, lean_object* v_hma_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_00_u03b2_1284_, v_m_1285_, v_a_1286_, v_hma_1287_);
lean_dec_ref(v_a_1286_);
lean_dec_ref(v_m_1285_);
return v_res_1288_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1289_, lean_object* v_a_1290_, lean_object* v_x_1291_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1290_, v_x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1293_, lean_object* v_a_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1293_, v_a_1294_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec_ref(v_a_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(lean_object* v_00_u03b2_1298_, lean_object* v_a_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1299_, v_x_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1303_, lean_object* v_a_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(v_00_u03b2_1303_, v_a_1304_, v_x_1305_, v_x_1306_);
lean_dec(v_x_1305_);
lean_dec_ref(v_a_1304_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1308_){
_start:
{
lean_object* v_userData_1309_; lean_object* v_outputData_1310_; lean_object* v_knownSize_1311_; lean_object* v_messageHead_1312_; uint8_t v_sentMessage_1313_; uint8_t v_userClosedBody_1314_; uint8_t v_omitBody_1315_; lean_object* v_userDataBytes_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_userData_1309_ = lean_ctor_get(v_writer_1308_, 0);
v_outputData_1310_ = lean_ctor_get(v_writer_1308_, 1);
v_knownSize_1311_ = lean_ctor_get(v_writer_1308_, 3);
v_messageHead_1312_ = lean_ctor_get(v_writer_1308_, 4);
v_sentMessage_1313_ = lean_ctor_get_uint8(v_writer_1308_, sizeof(void*)*6);
v_userClosedBody_1314_ = lean_ctor_get_uint8(v_writer_1308_, sizeof(void*)*6 + 1);
v_omitBody_1315_ = lean_ctor_get_uint8(v_writer_1308_, sizeof(void*)*6 + 2);
v_userDataBytes_1316_ = lean_ctor_get(v_writer_1308_, 5);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_writer_1308_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_writer_1308_, 2);
lean_dec(v_unused_1325_);
v___x_1318_ = v_writer_1308_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_userDataBytes_1316_);
lean_inc(v_messageHead_1312_);
lean_inc(v_knownSize_1311_);
lean_inc(v_outputData_1310_);
lean_inc(v_userData_1309_);
lean_dec(v_writer_1308_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(7);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 2, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_userData_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_outputData_1310_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_knownSize_1311_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_messageHead_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_userDataBytes_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*6, v_sentMessage_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*6 + 1, v_userClosedBody_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*6 + 2, v_omitBody_1315_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1326_, lean_object* v_writer_1327_){
_start:
{
lean_object* v_userData_1328_; lean_object* v_outputData_1329_; lean_object* v_knownSize_1330_; lean_object* v_messageHead_1331_; uint8_t v_sentMessage_1332_; uint8_t v_userClosedBody_1333_; uint8_t v_omitBody_1334_; lean_object* v_userDataBytes_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_userData_1328_ = lean_ctor_get(v_writer_1327_, 0);
v_outputData_1329_ = lean_ctor_get(v_writer_1327_, 1);
v_knownSize_1330_ = lean_ctor_get(v_writer_1327_, 3);
v_messageHead_1331_ = lean_ctor_get(v_writer_1327_, 4);
v_sentMessage_1332_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6);
v_userClosedBody_1333_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6 + 1);
v_omitBody_1334_ = lean_ctor_get_uint8(v_writer_1327_, sizeof(void*)*6 + 2);
v_userDataBytes_1335_ = lean_ctor_get(v_writer_1327_, 5);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_writer_1327_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_writer_1327_, 2);
lean_dec(v_unused_1344_);
v___x_1337_ = v_writer_1327_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_userDataBytes_1335_);
lean_inc(v_messageHead_1331_);
lean_inc(v_knownSize_1330_);
lean_inc(v_outputData_1329_);
lean_inc(v_userData_1328_);
lean_dec(v_writer_1327_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_box(7);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 2, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_userData_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_outputData_1329_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_knownSize_1330_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_messageHead_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 5, v_userDataBytes_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*6, v_sentMessage_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*6 + 1, v_userClosedBody_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*6 + 2, v_omitBody_1334_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1345_, lean_object* v_writer_1346_){
_start:
{
uint8_t v_dir_boxed_1347_; lean_object* v_res_1348_; 
v_dir_boxed_1347_ = lean_unbox(v_dir_1345_);
v_res_1348_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1347_, v_writer_1346_);
return v_res_1348_;
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
