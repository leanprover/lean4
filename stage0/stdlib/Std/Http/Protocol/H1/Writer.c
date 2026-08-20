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
lean_object* v_snd_500_; lean_object* v_fst_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_558_; 
v_snd_500_ = lean_ctor_get(v_b_493_, 1);
v_fst_501_ = lean_ctor_get(v_b_493_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_b_493_);
if (v_isSharedCheck_558_ == 0)
{
v___x_503_ = v_b_493_;
v_isShared_504_ = v_isSharedCheck_558_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snd_500_);
lean_inc(v_fst_501_);
lean_dec(v_b_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_558_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_557_; 
v_fst_505_ = lean_ctor_get(v_snd_500_, 0);
v_snd_506_ = lean_ctor_get(v_snd_500_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_snd_500_);
if (v_isSharedCheck_557_ == 0)
{
v___x_508_ = v_snd_500_;
v_isShared_509_ = v_isSharedCheck_557_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_inc(v_fst_505_);
lean_dec(v_snd_500_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_557_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_array_uget(v_as_490_, v_i_491_);
v___x_511_ = lean_nat_dec_le(v_limitSize_489_, v_snd_506_);
if (v___x_511_ == 0)
{
lean_object* v_data_512_; lean_object* v_extensions_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_549_; 
v_data_512_ = lean_ctor_get(v___x_510_, 0);
v_extensions_513_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_549_ == 0)
{
v___x_515_ = v___x_510_;
v_isShared_516_ = v_isSharedCheck_549_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_extensions_513_);
lean_inc(v_data_512_);
lean_dec(v___x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_549_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v_remaining_518_; lean_object* v___x_519_; uint8_t v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_543_; uint8_t v___x_548_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v_remaining_518_ = lean_nat_sub(v_limitSize_489_, v_snd_506_);
v___x_519_ = lean_byte_array_size(v_data_512_);
v___x_548_ = lean_nat_dec_le(v___x_519_, v_remaining_518_);
if (v___x_548_ == 0)
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
lean_object* v_size_524_; 
v_size_524_ = lean_nat_add(v_snd_506_, v___y_522_);
lean_dec(v_snd_506_);
if (v___y_521_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v___y_522_);
lean_del_object(v___x_515_);
lean_dec_ref(v_extensions_513_);
lean_dec_ref(v_data_512_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_size_524_);
v___x_526_ = v___x_508_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_505_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_size_524_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_526_);
lean_ctor_set(v___x_503_, 0, v___y_523_);
v___x_528_ = v___x_503_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___y_523_);
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
v___x_531_ = l_ByteArray_extract(v_data_512_, v___y_522_, v___x_519_);
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
lean_ctor_set(v___x_508_, 1, v_size_524_);
lean_ctor_set(v___x_508_, 0, v___x_534_);
v___x_536_ = v___x_508_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_size_524_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_536_);
lean_ctor_set(v___x_503_, 0, v___y_523_);
v___x_538_ = v___x_503_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___y_523_);
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
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_nat_dec_eq(v___y_543_, v___x_517_);
v___x_545_ = lean_nat_dec_lt(v___y_543_, v___x_519_);
if (v___x_544_ == 0)
{
lean_object* v_dataPart_546_; lean_object* v___x_547_; 
v_dataPart_546_ = l_ByteArray_extract(v_data_512_, v___x_517_, v___y_543_);
v___x_547_ = lean_array_push(v_fst_501_, v_dataPart_546_);
v___y_521_ = v___x_545_;
v___y_522_ = v___y_543_;
v___y_523_ = v___x_547_;
goto v___jp_520_;
}
else
{
v___y_521_ = v___x_545_;
v___y_522_ = v___y_543_;
v___y_523_ = v_fst_501_;
goto v___jp_520_;
}
}
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_array_push(v_fst_505_, v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_550_);
v___x_552_ = v___x_508_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_snd_506_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_552_);
v___x_554_ = v___x_503_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_fst_501_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v___y_495_ = v___x_554_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_559_, lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_stop_562_, lean_object* v_b_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_stop_boxed_565_; lean_object* v_res_566_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_565_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_559_, v_as_560_, v_i_boxed_564_, v_stop_boxed_565_, v_b_563_);
lean_dec_ref(v_as_560_);
lean_dec(v_limitSize_559_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_567_, size_t v_i_568_, size_t v_stop_569_, lean_object* v_b_570_){
_start:
{
uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_eq(v_i_568_, v_stop_569_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; 
v___x_572_ = lean_array_uget_borrowed(v_as_567_, v_i_568_);
v___x_573_ = lean_byte_array_size(v___x_572_);
v___x_574_ = lean_nat_add(v_b_570_, v___x_573_);
lean_dec(v_b_570_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_568_, v___x_575_);
v_i_568_ = v___x_576_;
v_b_570_ = v___x_574_;
goto _start;
}
else
{
return v_b_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_578_, lean_object* v_i_579_, lean_object* v_stop_580_, lean_object* v_b_581_){
_start:
{
size_t v_i_boxed_582_; size_t v_stop_boxed_583_; lean_object* v_res_584_; 
v_i_boxed_582_ = lean_unbox_usize(v_i_579_);
lean_dec(v_i_579_);
v_stop_boxed_583_ = lean_unbox_usize(v_stop_580_);
lean_dec(v_stop_580_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_578_, v_i_boxed_582_, v_stop_boxed_583_, v_b_581_);
lean_dec_ref(v_as_578_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_593_, lean_object* v_limitSize_594_){
_start:
{
lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; uint8_t v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v_userData_630_; lean_object* v_outputData_631_; lean_object* v_state_632_; lean_object* v_knownSize_633_; lean_object* v_messageHead_634_; uint8_t v_sentMessage_635_; uint8_t v_userClosedBody_636_; uint8_t v_omitBody_637_; lean_object* v_userDataBytes_638_; lean_object* v_fst_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___y_652_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_userData_630_ = lean_ctor_get(v_writer_593_, 0);
v_outputData_631_ = lean_ctor_get(v_writer_593_, 1);
v_state_632_ = lean_ctor_get(v_writer_593_, 2);
v_knownSize_633_ = lean_ctor_get(v_writer_593_, 3);
v_messageHead_634_ = lean_ctor_get(v_writer_593_, 4);
v_sentMessage_635_ = lean_ctor_get_uint8(v_writer_593_, sizeof(void*)*6);
v_userClosedBody_636_ = lean_ctor_get_uint8(v_writer_593_, sizeof(void*)*6 + 1);
v_omitBody_637_ = lean_ctor_get_uint8(v_writer_593_, sizeof(void*)*6 + 2);
v_userDataBytes_638_ = lean_ctor_get(v_writer_593_, 5);
v___x_657_ = lean_array_get_size(v_userData_630_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
lean_inc(v_userDataBytes_638_);
lean_inc(v_messageHead_634_);
lean_inc(v_knownSize_633_);
lean_inc(v_state_632_);
lean_inc_ref(v_outputData_631_);
lean_inc_ref(v_userData_630_);
lean_dec_ref(v_writer_593_);
v___x_660_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_661_ = lean_nat_dec_lt(v___x_658_, v___x_657_);
if (v___x_661_ == 0)
{
lean_dec_ref(v_userData_630_);
v_fst_640_ = v___x_660_;
v_fst_641_ = v___x_660_;
v_snd_642_ = v___x_658_;
goto v___jp_639_;
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_663_ = lean_nat_dec_le(v___x_657_, v___x_657_);
if (v___x_663_ == 0)
{
if (v___x_661_ == 0)
{
lean_dec_ref(v_userData_630_);
v_fst_640_ = v___x_660_;
v_fst_641_ = v___x_660_;
v_snd_642_ = v___x_658_;
goto v___jp_639_;
}
else
{
size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_657_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_594_, v_userData_630_, v___x_664_, v___x_665_, v___x_662_);
lean_dec_ref(v_userData_630_);
v___y_652_ = v___x_666_;
goto v___jp_651_;
}
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_657_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_594_, v_userData_630_, v___x_667_, v___x_668_, v___x_662_);
lean_dec_ref(v_userData_630_);
v___y_652_ = v___x_669_;
goto v___jp_651_;
}
}
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_writer_593_);
lean_ctor_set(v___x_670_, 1, v_limitSize_594_);
return v___x_670_;
}
v___jp_595_:
{
lean_object* v_data_607_; lean_object* v_size_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_629_; 
v_data_607_ = lean_ctor_get(v___y_599_, 0);
v_size_608_ = lean_ctor_get(v___y_599_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v___y_599_);
if (v_isSharedCheck_629_ == 0)
{
v___x_610_ = v___y_599_;
v_isShared_611_ = v_isSharedCheck_629_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_size_608_);
lean_inc(v_data_607_);
lean_dec(v___y_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_629_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_data_612_; lean_object* v_size_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_628_; 
v_data_612_ = lean_ctor_get(v___y_606_, 0);
v_size_613_ = lean_ctor_get(v___y_606_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___y_606_);
if (v_isSharedCheck_628_ == 0)
{
v___x_615_ = v___y_606_;
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_size_613_);
lean_inc(v_data_612_);
lean_dec(v___y_606_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_outputData_620_; 
v___x_617_ = l_Array_append___redArg(v_data_607_, v_data_612_);
lean_dec_ref(v_data_612_);
v___x_618_ = lean_nat_add(v_size_608_, v_size_613_);
lean_dec(v_size_613_);
lean_dec(v_size_608_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___x_618_);
lean_ctor_set(v___x_615_, 0, v___x_617_);
v_outputData_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_618_);
v_outputData_620_ = v_reuseFailAlloc_627_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v_remaining_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_remaining_621_ = lean_nat_sub(v_limitSize_594_, v___y_597_);
lean_dec(v_limitSize_594_);
v___x_622_ = lean_nat_sub(v___y_605_, v___y_597_);
lean_dec(v___y_597_);
lean_dec(v___y_605_);
v___x_623_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_623_, 0, v___y_601_);
lean_ctor_set(v___x_623_, 1, v_outputData_620_);
lean_ctor_set(v___x_623_, 2, v___y_603_);
lean_ctor_set(v___x_623_, 3, v___y_596_);
lean_ctor_set(v___x_623_, 4, v___y_598_);
lean_ctor_set(v___x_623_, 5, v___x_622_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*6, v___y_600_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*6 + 1, v___y_604_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*6 + 2, v___y_602_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v_remaining_621_);
lean_ctor_set(v___x_610_, 0, v___x_623_);
v___x_625_ = v___x_610_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_remaining_621_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
v___jp_639_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_array_get_size(v_fst_640_);
v___x_645_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_fst_640_);
lean_ctor_set(v___x_646_, 1, v___x_643_);
v___y_596_ = v_knownSize_633_;
v___y_597_ = v_snd_642_;
v___y_598_ = v_messageHead_634_;
v___y_599_ = v_outputData_631_;
v___y_600_ = v_sentMessage_635_;
v___y_601_ = v_fst_641_;
v___y_602_ = v_omitBody_637_;
v___y_603_ = v_state_632_;
v___y_604_ = v_userClosedBody_636_;
v___y_605_ = v_userDataBytes_638_;
v___y_606_ = v___x_646_;
goto v___jp_595_;
}
else
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = ((size_t)0ULL);
v___x_648_ = lean_usize_of_nat(v___x_644_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_640_, v___x_647_, v___x_648_, v___x_643_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_fst_640_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___y_596_ = v_knownSize_633_;
v___y_597_ = v_snd_642_;
v___y_598_ = v_messageHead_634_;
v___y_599_ = v_outputData_631_;
v___y_600_ = v_sentMessage_635_;
v___y_601_ = v_fst_641_;
v___y_602_ = v_omitBody_637_;
v___y_603_ = v_state_632_;
v___y_604_ = v_userClosedBody_636_;
v___y_605_ = v_userDataBytes_638_;
v___y_606_ = v___x_650_;
goto v___jp_595_;
}
}
v___jp_651_:
{
lean_object* v_snd_653_; lean_object* v_fst_654_; lean_object* v_fst_655_; lean_object* v_snd_656_; 
v_snd_653_ = lean_ctor_get(v___y_652_, 1);
lean_inc(v_snd_653_);
v_fst_654_ = lean_ctor_get(v___y_652_, 0);
lean_inc(v_fst_654_);
lean_dec_ref(v___y_652_);
v_fst_655_ = lean_ctor_get(v_snd_653_, 0);
lean_inc(v_fst_655_);
v_snd_656_ = lean_ctor_get(v_snd_653_, 1);
lean_inc(v_snd_656_);
lean_dec(v_snd_653_);
v_fst_640_ = v_fst_654_;
v_fst_641_ = v_fst_655_;
v_snd_642_ = v_snd_656_;
goto v___jp_639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_671_, lean_object* v_writer_672_, lean_object* v_limitSize_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_672_, v_limitSize_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_675_, lean_object* v_writer_676_, lean_object* v_limitSize_677_){
_start:
{
uint8_t v_dir_boxed_678_; lean_object* v_res_679_; 
v_dir_boxed_678_ = lean_unbox(v_dir_675_);
v_res_679_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_678_, v_writer_676_, v_limitSize_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_, lean_object* v_b_683_){
_start:
{
lean_object* v___y_685_; uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v_data_691_; uint8_t v___x_692_; 
v___x_690_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
v_data_691_ = lean_ctor_get(v___x_690_, 0);
v___x_692_ = l_ByteArray_isEmpty(v_data_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_inc(v___x_690_);
v___x_693_ = lean_array_push(v_b_683_, v___x_690_);
v___y_685_ = v___x_693_;
goto v___jp_684_;
}
else
{
v___y_685_ = v_b_683_;
goto v___jp_684_;
}
}
else
{
return v_b_683_;
}
v___jp_684_:
{
size_t v___x_686_; size_t v___x_687_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_681_, v___x_686_);
v_i_681_ = v___x_687_;
v_b_683_ = v___y_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_694_, lean_object* v_i_695_, lean_object* v_stop_696_, lean_object* v_b_697_){
_start:
{
size_t v_i_boxed_698_; size_t v_stop_boxed_699_; lean_object* v_res_700_; 
v_i_boxed_698_ = lean_unbox_usize(v_i_695_);
lean_dec(v_i_695_);
v_stop_boxed_699_ = lean_unbox_usize(v_stop_696_);
lean_dec(v_stop_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_694_, v_i_boxed_698_, v_stop_boxed_699_, v_b_697_);
lean_dec_ref(v_as_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_701_, size_t v_i_702_, lean_object* v_bs_703_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = lean_usize_dec_lt(v_i_702_, v_sz_701_);
if (v___x_704_ == 0)
{
return v_bs_703_;
}
else
{
lean_object* v_v_705_; lean_object* v___x_706_; lean_object* v_bs_x27_707_; uint32_t v___x_708_; uint8_t v___x_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_v_705_ = lean_array_uget(v_bs_703_, v_i_702_);
v___x_706_ = lean_unsigned_to_nat(0u);
v_bs_x27_707_ = lean_array_uset(v_bs_703_, v_i_702_, v___x_706_);
v___x_708_ = lean_unbox_uint32(v_v_705_);
lean_dec(v_v_705_);
v___x_709_ = lean_uint32_to_uint8(v___x_708_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_add(v_i_702_, v___x_710_);
v___x_712_ = lean_box(v___x_709_);
v___x_713_ = lean_array_uset(v_bs_x27_707_, v_i_702_, v___x_712_);
v_i_702_ = v___x_711_;
v_bs_703_ = v___x_713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_715_, lean_object* v_i_716_, lean_object* v_bs_717_){
_start:
{
size_t v_sz_boxed_718_; size_t v_i_boxed_719_; lean_object* v_res_720_; 
v_sz_boxed_718_ = lean_unbox_usize(v_sz_715_);
lean_dec(v_sz_715_);
v_i_boxed_719_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_718_, v_i_boxed_719_, v_bs_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_723_, size_t v_i_724_, size_t v_stop_725_, lean_object* v_b_726_){
_start:
{
lean_object* v___y_728_; uint8_t v___x_732_; 
v___x_732_ = lean_usize_dec_eq(v_i_724_, v_stop_725_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_733_ = lean_array_uget_borrowed(v_as_723_, v_i_724_);
v_fst_734_ = lean_ctor_get(v___x_733_, 0);
v_snd_735_ = lean_ctor_get(v___x_733_, 1);
v___x_736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_737_ = lean_string_append(v_b_726_, v___x_736_);
v___x_738_ = lean_string_append(v___x_737_, v_fst_734_);
if (lean_obj_tag(v_snd_735_) == 0)
{
v___y_728_ = v___x_738_;
goto v___jp_727_;
}
else
{
lean_object* v_val_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_val_739_ = lean_ctor_get(v_snd_735_, 0);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_739_);
v___x_741_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_739_);
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = lean_string_append(v___x_738_, v___x_742_);
lean_dec_ref(v___x_742_);
v___y_728_ = v___x_743_;
goto v___jp_727_;
}
}
else
{
return v_b_726_;
}
v___jp_727_:
{
size_t v___x_729_; size_t v___x_730_; 
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_724_, v___x_729_);
v_i_724_ = v___x_730_;
v_b_726_ = v___y_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_744_, lean_object* v_i_745_, lean_object* v_stop_746_, lean_object* v_b_747_){
_start:
{
size_t v_i_boxed_748_; size_t v_stop_boxed_749_; lean_object* v_res_750_; 
v_i_boxed_748_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_stop_boxed_749_ = lean_unbox_usize(v_stop_746_);
lean_dec(v_stop_746_);
v_res_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_744_, v_i_boxed_748_, v_stop_boxed_749_, v_b_747_);
lean_dec_ref(v_as_744_);
return v_res_750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_753_ = lean_string_to_utf8(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_755_, size_t v_i_756_, size_t v_stop_757_, lean_object* v_b_758_){
_start:
{
lean_object* v___y_760_; uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_756_, v_stop_757_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v_data_779_; lean_object* v_extensions_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_821_; 
v___x_778_ = lean_array_uget(v_as_755_, v_i_756_);
v_data_779_ = lean_ctor_get(v___x_778_, 0);
v_extensions_780_ = lean_ctor_get(v___x_778_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_821_ == 0)
{
v___x_782_ = v___x_778_;
v_isShared_783_ = v_isSharedCheck_821_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_extensions_780_);
lean_inc(v_data_779_);
lean_dec(v___x_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_821_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_chunkLen_784_; lean_object* v___y_786_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_chunkLen_784_ = lean_byte_array_size(v_data_779_);
v___x_814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_array_get_size(v_extensions_780_);
v___x_817_ = lean_nat_dec_lt(v___x_815_, v___x_816_);
if (v___x_817_ == 0)
{
lean_dec_ref(v_extensions_780_);
v___y_786_ = v___x_814_;
goto v___jp_785_;
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((size_t)0ULL);
v___x_819_ = lean_usize_of_nat(v___x_816_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_780_, v___x_818_, v___x_819_, v___x_814_);
lean_dec_ref(v_extensions_780_);
v___y_786_ = v___x_820_;
goto v___jp_785_;
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; size_t v_sz_790_; size_t v___x_791_; lean_object* v___x_792_; lean_object* v_size_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_787_ = lean_unsigned_to_nat(16u);
v___x_788_ = l_Nat_toDigits(v___x_787_, v_chunkLen_784_);
v___x_789_ = lean_array_mk(v___x_788_);
v_sz_790_ = lean_array_size(v___x_789_);
v___x_791_ = ((size_t)0ULL);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_790_, v___x_791_, v___x_789_);
v_size_793_ = lean_byte_array_mk(v___x_792_);
v___x_794_ = lean_string_to_utf8(v___y_786_);
lean_dec_ref(v___y_786_);
v___x_795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_796_ = lean_unsigned_to_nat(5u);
v___x_797_ = lean_mk_empty_array_with_capacity(v___x_796_);
v___x_798_ = lean_array_push(v___x_797_, v_size_793_);
v___x_799_ = lean_array_push(v___x_798_, v___x_794_);
v___x_800_ = lean_array_push(v___x_799_, v___x_795_);
v___x_801_ = lean_array_push(v___x_800_, v_data_779_);
v___x_802_ = lean_array_push(v___x_801_, v___x_795_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_array_get_size(v___x_802_);
v___x_805_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_807_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_803_);
lean_ctor_set(v___x_782_, 0, v___x_802_);
v___x_807_ = v___x_782_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_803_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
v___y_760_ = v___x_807_;
goto v___jp_759_;
}
}
else
{
size_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_809_ = lean_usize_of_nat(v___x_804_);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_802_, v___x_791_, v___x_809_, v___x_803_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_810_);
lean_ctor_set(v___x_782_, 0, v___x_802_);
v___x_812_ = v___x_782_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v___y_760_ = v___x_812_;
goto v___jp_759_;
}
}
}
}
}
else
{
return v_b_758_;
}
v___jp_759_:
{
lean_object* v_data_761_; lean_object* v_size_762_; lean_object* v_data_763_; lean_object* v_size_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_776_; 
v_data_761_ = lean_ctor_get(v_b_758_, 0);
lean_inc_ref(v_data_761_);
v_size_762_ = lean_ctor_get(v_b_758_, 1);
lean_inc(v_size_762_);
lean_dec_ref(v_b_758_);
v_data_763_ = lean_ctor_get(v___y_760_, 0);
v_size_764_ = lean_ctor_get(v___y_760_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___y_760_);
if (v_isSharedCheck_776_ == 0)
{
v___x_766_ = v___y_760_;
v_isShared_767_ = v_isSharedCheck_776_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_size_764_);
lean_inc(v_data_763_);
lean_dec(v___y_760_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_776_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_768_ = l_Array_append___redArg(v_data_761_, v_data_763_);
lean_dec_ref(v_data_763_);
v___x_769_ = lean_nat_add(v_size_762_, v_size_764_);
lean_dec(v_size_764_);
lean_dec(v_size_762_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_769_);
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_756_, v___x_772_);
v_i_756_ = v___x_773_;
v_b_758_ = v___x_771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_822_, lean_object* v_i_823_, lean_object* v_stop_824_, lean_object* v_b_825_){
_start:
{
size_t v_i_boxed_826_; size_t v_stop_boxed_827_; lean_object* v_res_828_; 
v_i_boxed_826_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_stop_boxed_827_ = lean_unbox_usize(v_stop_824_);
lean_dec(v_stop_824_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_822_, v_i_boxed_826_, v_stop_boxed_827_, v_b_825_);
lean_dec_ref(v_as_822_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_831_){
_start:
{
lean_object* v_userData_832_; lean_object* v_outputData_833_; lean_object* v_state_834_; lean_object* v_knownSize_835_; lean_object* v_messageHead_836_; uint8_t v_sentMessage_837_; uint8_t v_userClosedBody_838_; uint8_t v_omitBody_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___y_843_; uint8_t v___x_858_; 
v_userData_832_ = lean_ctor_get(v_writer_831_, 0);
v_outputData_833_ = lean_ctor_get(v_writer_831_, 1);
v_state_834_ = lean_ctor_get(v_writer_831_, 2);
v_knownSize_835_ = lean_ctor_get(v_writer_831_, 3);
v_messageHead_836_ = lean_ctor_get(v_writer_831_, 4);
v_sentMessage_837_ = lean_ctor_get_uint8(v_writer_831_, sizeof(void*)*6);
v_userClosedBody_838_ = lean_ctor_get_uint8(v_writer_831_, sizeof(void*)*6 + 1);
v_omitBody_839_ = lean_ctor_get_uint8(v_writer_831_, sizeof(void*)*6 + 2);
v___x_840_ = lean_array_get_size(v_userData_832_);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_nat_dec_eq(v___x_840_, v___x_841_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; uint8_t v___x_860_; 
lean_inc(v_messageHead_836_);
lean_inc(v_knownSize_835_);
lean_inc(v_state_834_);
lean_inc_ref(v_outputData_833_);
lean_inc_ref(v_userData_832_);
lean_dec_ref(v_writer_831_);
v___x_859_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_860_ = lean_nat_dec_lt(v___x_841_, v___x_840_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_userData_832_);
v___y_843_ = v___x_859_;
goto v___jp_842_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_le(v___x_840_, v___x_840_);
if (v___x_861_ == 0)
{
if (v___x_860_ == 0)
{
lean_dec_ref(v_userData_832_);
v___y_843_ = v___x_859_;
goto v___jp_842_;
}
else
{
size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_840_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_832_, v___x_862_, v___x_863_, v___x_859_);
lean_dec_ref(v_userData_832_);
v___y_843_ = v___x_864_;
goto v___jp_842_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_840_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_832_, v___x_865_, v___x_866_, v___x_859_);
lean_dec_ref(v_userData_832_);
v___y_843_ = v___x_867_;
goto v___jp_842_;
}
}
}
else
{
return v_writer_831_;
}
v___jp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_845_ = lean_array_get_size(v___y_843_);
v___x_846_ = lean_nat_dec_lt(v___x_841_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec_ref(v___y_843_);
v___x_847_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_847_, 0, v___x_844_);
lean_ctor_set(v___x_847_, 1, v_outputData_833_);
lean_ctor_set(v___x_847_, 2, v_state_834_);
lean_ctor_set(v___x_847_, 3, v_knownSize_835_);
lean_ctor_set(v___x_847_, 4, v_messageHead_836_);
lean_ctor_set(v___x_847_, 5, v___x_841_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*6, v_sentMessage_837_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*6 + 1, v_userClosedBody_838_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*6 + 2, v_omitBody_839_);
return v___x_847_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = lean_nat_dec_le(v___x_845_, v___x_845_);
if (v___x_848_ == 0)
{
if (v___x_846_ == 0)
{
lean_object* v___x_849_; 
lean_dec_ref(v___y_843_);
v___x_849_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_849_, 0, v___x_844_);
lean_ctor_set(v___x_849_, 1, v_outputData_833_);
lean_ctor_set(v___x_849_, 2, v_state_834_);
lean_ctor_set(v___x_849_, 3, v_knownSize_835_);
lean_ctor_set(v___x_849_, 4, v_messageHead_836_);
lean_ctor_set(v___x_849_, 5, v___x_841_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6, v_sentMessage_837_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6 + 1, v_userClosedBody_838_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6 + 2, v_omitBody_839_);
return v___x_849_;
}
else
{
size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_850_ = ((size_t)0ULL);
v___x_851_ = lean_usize_of_nat(v___x_845_);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_843_, v___x_850_, v___x_851_, v_outputData_833_);
lean_dec_ref(v___y_843_);
v___x_853_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_853_, 0, v___x_844_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
lean_ctor_set(v___x_853_, 2, v_state_834_);
lean_ctor_set(v___x_853_, 3, v_knownSize_835_);
lean_ctor_set(v___x_853_, 4, v_messageHead_836_);
lean_ctor_set(v___x_853_, 5, v___x_841_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*6, v_sentMessage_837_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*6 + 1, v_userClosedBody_838_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*6 + 2, v_omitBody_839_);
return v___x_853_;
}
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_845_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_843_, v___x_854_, v___x_855_, v_outputData_833_);
lean_dec_ref(v___y_843_);
v___x_857_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_857_, 0, v___x_844_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set(v___x_857_, 2, v_state_834_);
lean_ctor_set(v___x_857_, 3, v_knownSize_835_);
lean_ctor_set(v___x_857_, 4, v_messageHead_836_);
lean_ctor_set(v___x_857_, 5, v___x_841_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*6, v_sentMessage_837_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*6 + 1, v_userClosedBody_838_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*6 + 2, v_omitBody_839_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_868_, lean_object* v_writer_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_871_, lean_object* v_writer_872_){
_start:
{
uint8_t v_dir_boxed_873_; lean_object* v_res_874_; 
v_dir_boxed_873_ = lean_unbox(v_dir_871_);
v_res_874_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_873_, v_writer_872_);
return v_res_874_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_877_ = lean_string_to_utf8(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_879_ = lean_byte_array_size(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_880_){
_start:
{
lean_object* v_writer_881_; lean_object* v_outputData_882_; lean_object* v_userData_883_; lean_object* v_knownSize_884_; lean_object* v_messageHead_885_; uint8_t v_sentMessage_886_; uint8_t v_userClosedBody_887_; uint8_t v_omitBody_888_; lean_object* v_userDataBytes_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_910_; 
v_writer_881_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_880_);
v_outputData_882_ = lean_ctor_get(v_writer_881_, 1);
v_userData_883_ = lean_ctor_get(v_writer_881_, 0);
v_knownSize_884_ = lean_ctor_get(v_writer_881_, 3);
v_messageHead_885_ = lean_ctor_get(v_writer_881_, 4);
v_sentMessage_886_ = lean_ctor_get_uint8(v_writer_881_, sizeof(void*)*6);
v_userClosedBody_887_ = lean_ctor_get_uint8(v_writer_881_, sizeof(void*)*6 + 1);
v_omitBody_888_ = lean_ctor_get_uint8(v_writer_881_, sizeof(void*)*6 + 2);
v_userDataBytes_889_ = lean_ctor_get(v_writer_881_, 5);
v_isSharedCheck_910_ = !lean_is_exclusive(v_writer_881_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_writer_881_, 2);
lean_dec(v_unused_911_);
v___x_891_ = v_writer_881_;
v_isShared_892_ = v_isSharedCheck_910_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_userDataBytes_889_);
lean_inc(v_messageHead_885_);
lean_inc(v_knownSize_884_);
lean_inc(v_outputData_882_);
lean_inc(v_userData_883_);
lean_dec(v_writer_881_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_910_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_data_893_; lean_object* v_size_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_909_; 
v_data_893_ = lean_ctor_get(v_outputData_882_, 0);
v_size_894_ = lean_ctor_get(v_outputData_882_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_outputData_882_);
if (v_isSharedCheck_909_ == 0)
{
v___x_896_ = v_outputData_882_;
v_isShared_897_ = v_isSharedCheck_909_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_size_894_);
lean_inc(v_data_893_);
lean_dec(v_outputData_882_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_909_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_898_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_899_ = lean_array_push(v_data_893_, v___x_898_);
v___x_900_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_901_ = lean_nat_add(v_size_894_, v___x_900_);
lean_dec(v_size_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_901_);
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_903_ = v___x_896_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_908_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_box(6);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v___x_904_);
lean_ctor_set(v___x_891_, 1, v___x_903_);
v___x_906_ = v___x_891_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_userData_883_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_knownSize_884_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_messageHead_885_);
lean_ctor_set(v_reuseFailAlloc_907_, 5, v_userDataBytes_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*6, v_sentMessage_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*6 + 1, v_userClosedBody_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*6 + 2, v_omitBody_888_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_912_, lean_object* v_writer_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_915_, lean_object* v_writer_916_){
_start:
{
uint8_t v_dir_boxed_917_; lean_object* v_res_918_; 
v_dir_boxed_917_ = lean_unbox(v_dir_915_);
v_res_918_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_917_, v_writer_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_919_, size_t v_i_920_, size_t v_stop_921_, lean_object* v_b_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_eq(v_i_920_, v_stop_921_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v_data_925_; lean_object* v_data_926_; lean_object* v_size_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_940_; 
v___x_924_ = lean_array_uget_borrowed(v_as_919_, v_i_920_);
v_data_925_ = lean_ctor_get(v___x_924_, 0);
v_data_926_ = lean_ctor_get(v_b_922_, 0);
v_size_927_ = lean_ctor_get(v_b_922_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_b_922_);
if (v_isSharedCheck_940_ == 0)
{
v___x_929_ = v_b_922_;
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_size_927_);
lean_inc(v_data_926_);
lean_dec(v_b_922_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
lean_inc_ref(v_data_925_);
v___x_931_ = lean_array_push(v_data_926_, v_data_925_);
v___x_932_ = lean_byte_array_size(v_data_925_);
v___x_933_ = lean_nat_add(v_size_927_, v___x_932_);
lean_dec(v_size_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_933_);
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_935_ = v___x_929_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
size_t v___x_936_; size_t v___x_937_; 
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_920_, v___x_936_);
v_i_920_ = v___x_937_;
v_b_922_ = v___x_935_;
goto _start;
}
}
}
else
{
return v_b_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_941_, lean_object* v_i_942_, lean_object* v_stop_943_, lean_object* v_b_944_){
_start:
{
size_t v_i_boxed_945_; size_t v_stop_boxed_946_; lean_object* v_res_947_; 
v_i_boxed_945_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_stop_boxed_946_ = lean_unbox_usize(v_stop_943_);
lean_dec(v_stop_943_);
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_941_, v_i_boxed_945_, v_stop_boxed_946_, v_b_944_);
lean_dec_ref(v_as_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_948_){
_start:
{
lean_object* v_userData_949_; lean_object* v_outputData_950_; lean_object* v_state_951_; lean_object* v_knownSize_952_; lean_object* v_messageHead_953_; uint8_t v_sentMessage_954_; uint8_t v_userClosedBody_955_; uint8_t v_omitBody_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_983_; 
v_userData_949_ = lean_ctor_get(v_writer_948_, 0);
v_outputData_950_ = lean_ctor_get(v_writer_948_, 1);
v_state_951_ = lean_ctor_get(v_writer_948_, 2);
v_knownSize_952_ = lean_ctor_get(v_writer_948_, 3);
v_messageHead_953_ = lean_ctor_get(v_writer_948_, 4);
v_sentMessage_954_ = lean_ctor_get_uint8(v_writer_948_, sizeof(void*)*6);
v_userClosedBody_955_ = lean_ctor_get_uint8(v_writer_948_, sizeof(void*)*6 + 1);
v_omitBody_956_ = lean_ctor_get_uint8(v_writer_948_, sizeof(void*)*6 + 2);
v_isSharedCheck_983_ = !lean_is_exclusive(v_writer_948_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_writer_948_, 5);
lean_dec(v_unused_984_);
v___x_958_ = v_writer_948_;
v_isShared_959_ = v_isSharedCheck_983_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_messageHead_953_);
lean_inc(v_knownSize_952_);
lean_inc(v_state_951_);
lean_inc(v_outputData_950_);
lean_inc(v_userData_949_);
lean_dec(v_writer_948_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_983_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_962_ = lean_array_get_size(v_userData_949_);
v___x_963_ = lean_nat_dec_lt(v___x_960_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; 
lean_dec_ref(v_userData_949_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 5, v___x_960_);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_965_ = v___x_958_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_outputData_950_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_state_951_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_knownSize_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_messageHead_953_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v___x_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*6, v_sentMessage_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*6 + 1, v_userClosedBody_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*6 + 2, v_omitBody_956_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_le(v___x_962_, v___x_962_);
if (v___x_967_ == 0)
{
if (v___x_963_ == 0)
{
lean_object* v___x_969_; 
lean_dec_ref(v_userData_949_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 5, v___x_960_);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_969_ = v___x_958_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_outputData_950_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_state_951_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_knownSize_952_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_messageHead_953_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v___x_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*6, v_sentMessage_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*6 + 1, v_userClosedBody_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*6 + 2, v_omitBody_956_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_971_ = ((size_t)0ULL);
v___x_972_ = lean_usize_of_nat(v___x_962_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_949_, v___x_971_, v___x_972_, v_outputData_950_);
lean_dec_ref(v_userData_949_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 5, v___x_960_);
lean_ctor_set(v___x_958_, 1, v___x_973_);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_975_ = v___x_958_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_state_951_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_knownSize_952_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_messageHead_953_);
lean_ctor_set(v_reuseFailAlloc_976_, 5, v___x_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*6, v_sentMessage_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*6 + 1, v_userClosedBody_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*6 + 2, v_omitBody_956_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_962_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_949_, v___x_977_, v___x_978_, v_outputData_950_);
lean_dec_ref(v_userData_949_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 5, v___x_960_);
lean_ctor_set(v___x_958_, 1, v___x_979_);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_981_ = v___x_958_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_state_951_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_knownSize_952_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_messageHead_953_);
lean_ctor_set(v_reuseFailAlloc_982_, 5, v___x_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*6, v_sentMessage_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*6 + 1, v_userClosedBody_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*6 + 2, v_omitBody_956_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_985_, lean_object* v_writer_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_988_, lean_object* v_writer_989_){
_start:
{
uint8_t v_dir_boxed_990_; lean_object* v_res_991_; 
v_dir_boxed_990_ = lean_unbox(v_dir_988_);
v_res_991_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_990_, v_writer_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_992_, lean_object* v_x1_993_, lean_object* v_x2_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_byte_array_size(v_x1_993_);
v___x_997_ = lean_byte_array_size(v_x2_994_);
v___x_998_ = lean_byte_array_copy_slice(v_x2_994_, v___x_995_, v_x1_993_, v___x_996_, v___x_997_, v___x_992_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_999_, lean_object* v_x1_1000_, lean_object* v_x2_1001_){
_start:
{
uint8_t v___x_115__boxed_1002_; lean_object* v_res_1003_; 
v___x_115__boxed_1002_ = lean_unbox(v___x_999_);
v_res_1003_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_115__boxed_1002_, v_x1_1000_, v_x2_1001_);
lean_dec_ref(v_x2_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_1007_){
_start:
{
lean_object* v_userData_1008_; lean_object* v_outputData_1009_; lean_object* v_state_1010_; lean_object* v_knownSize_1011_; lean_object* v_messageHead_1012_; uint8_t v_sentMessage_1013_; uint8_t v_userClosedBody_1014_; uint8_t v_omitBody_1015_; lean_object* v_userDataBytes_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1044_; 
v_userData_1008_ = lean_ctor_get(v_writer_1007_, 0);
v_outputData_1009_ = lean_ctor_get(v_writer_1007_, 1);
v_state_1010_ = lean_ctor_get(v_writer_1007_, 2);
v_knownSize_1011_ = lean_ctor_get(v_writer_1007_, 3);
v_messageHead_1012_ = lean_ctor_get(v_writer_1007_, 4);
v_sentMessage_1013_ = lean_ctor_get_uint8(v_writer_1007_, sizeof(void*)*6);
v_userClosedBody_1014_ = lean_ctor_get_uint8(v_writer_1007_, sizeof(void*)*6 + 1);
v_omitBody_1015_ = lean_ctor_get_uint8(v_writer_1007_, sizeof(void*)*6 + 2);
v_userDataBytes_1016_ = lean_ctor_get(v_writer_1007_, 5);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_writer_1007_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1018_ = v_writer_1007_;
v_isShared_1019_ = v_isSharedCheck_1044_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_userDataBytes_1016_);
lean_inc(v_messageHead_1012_);
lean_inc(v_knownSize_1011_);
lean_inc(v_state_1010_);
lean_inc(v_outputData_1009_);
lean_inc(v_userData_1008_);
lean_dec(v_writer_1007_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1044_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___y_1021_; lean_object* v_data_1028_; lean_object* v_size_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_data_1028_ = lean_ctor_get(v_outputData_1009_, 0);
lean_inc_ref(v_data_1028_);
v_size_1029_ = lean_ctor_get(v_outputData_1009_, 1);
lean_inc(v_size_1029_);
lean_dec_ref(v_outputData_1009_);
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_array_get_size(v_data_1028_);
v___x_1032_ = lean_nat_dec_eq(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1033_ = lean_mk_empty_byte_array(v_size_1029_);
lean_dec(v_size_1029_);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1036_ = lean_nat_dec_lt(v___x_1034_, v___x_1031_);
if (v___x_1036_ == 0)
{
lean_dec_ref(v_data_1028_);
v___y_1021_ = v___x_1033_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1037_; lean_object* v___f_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1037_ = lean_box(v___x_1032_);
v___f_1038_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1038_, 0, v___x_1037_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1031_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1035_, v___f_1038_, v_data_1028_, v___x_1039_, v___x_1040_, v___x_1033_);
v___y_1021_ = v___x_1041_;
goto v___jp_1020_;
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v_size_1029_);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_array_fget(v_data_1028_, v___x_1042_);
lean_dec_ref(v_data_1028_);
v___y_1021_ = v___x_1043_;
goto v___jp_1020_;
}
v___jp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_userData_1008_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_state_1010_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_knownSize_1011_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_messageHead_1012_);
lean_ctor_set(v_reuseFailAlloc_1027_, 5, v_userDataBytes_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1027_, sizeof(void*)*6, v_sentMessage_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1027_, sizeof(void*)*6 + 1, v_userClosedBody_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1027_, sizeof(void*)*6 + 2, v_omitBody_1015_);
v___x_1024_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___y_1021_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1045_, lean_object* v_writer_1046_){
_start:
{
lean_object* v_userData_1047_; lean_object* v_outputData_1048_; lean_object* v_state_1049_; lean_object* v_knownSize_1050_; lean_object* v_messageHead_1051_; uint8_t v_sentMessage_1052_; uint8_t v_userClosedBody_1053_; uint8_t v_omitBody_1054_; lean_object* v_userDataBytes_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1083_; 
v_userData_1047_ = lean_ctor_get(v_writer_1046_, 0);
v_outputData_1048_ = lean_ctor_get(v_writer_1046_, 1);
v_state_1049_ = lean_ctor_get(v_writer_1046_, 2);
v_knownSize_1050_ = lean_ctor_get(v_writer_1046_, 3);
v_messageHead_1051_ = lean_ctor_get(v_writer_1046_, 4);
v_sentMessage_1052_ = lean_ctor_get_uint8(v_writer_1046_, sizeof(void*)*6);
v_userClosedBody_1053_ = lean_ctor_get_uint8(v_writer_1046_, sizeof(void*)*6 + 1);
v_omitBody_1054_ = lean_ctor_get_uint8(v_writer_1046_, sizeof(void*)*6 + 2);
v_userDataBytes_1055_ = lean_ctor_get(v_writer_1046_, 5);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_writer_1046_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1057_ = v_writer_1046_;
v_isShared_1058_ = v_isSharedCheck_1083_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_userDataBytes_1055_);
lean_inc(v_messageHead_1051_);
lean_inc(v_knownSize_1050_);
lean_inc(v_state_1049_);
lean_inc(v_outputData_1048_);
lean_inc(v_userData_1047_);
lean_dec(v_writer_1046_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1083_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___y_1060_; lean_object* v_data_1067_; lean_object* v_size_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_data_1067_ = lean_ctor_get(v_outputData_1048_, 0);
lean_inc_ref(v_data_1067_);
v_size_1068_ = lean_ctor_get(v_outputData_1048_, 1);
lean_inc(v_size_1068_);
lean_dec_ref(v_outputData_1048_);
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_array_get_size(v_data_1067_);
v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1072_ = lean_mk_empty_byte_array(v_size_1068_);
lean_dec(v_size_1068_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1075_ = lean_nat_dec_lt(v___x_1073_, v___x_1070_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_data_1067_);
v___y_1060_ = v___x_1072_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1076_; lean_object* v___f_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1076_ = lean_box(v___x_1071_);
v___f_1077_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1077_, 0, v___x_1076_);
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = lean_usize_of_nat(v___x_1070_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1074_, v___f_1077_, v_data_1067_, v___x_1078_, v___x_1079_, v___x_1072_);
v___y_1060_ = v___x_1080_;
goto v___jp_1059_;
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v_size_1068_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_array_fget(v_data_1067_, v___x_1081_);
lean_dec_ref(v_data_1067_);
v___y_1060_ = v___x_1082_;
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1061_);
v___x_1063_ = v___x_1057_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_userData_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_state_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_knownSize_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_messageHead_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_userDataBytes_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*6, v_sentMessage_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*6 + 1, v_userClosedBody_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*6 + 2, v_omitBody_1054_);
v___x_1063_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___y_1060_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1084_, lean_object* v_writer_1085_){
_start:
{
uint8_t v_dir_boxed_1086_; lean_object* v_res_1087_; 
v_dir_boxed_1086_ = lean_unbox(v_dir_1084_);
v_res_1087_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1086_, v_writer_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1088_, lean_object* v_writer_1089_){
_start:
{
lean_object* v_userData_1090_; lean_object* v_outputData_1091_; lean_object* v_knownSize_1092_; lean_object* v_messageHead_1093_; uint8_t v_sentMessage_1094_; uint8_t v_userClosedBody_1095_; uint8_t v_omitBody_1096_; lean_object* v_userDataBytes_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_userData_1090_ = lean_ctor_get(v_writer_1089_, 0);
v_outputData_1091_ = lean_ctor_get(v_writer_1089_, 1);
v_knownSize_1092_ = lean_ctor_get(v_writer_1089_, 3);
v_messageHead_1093_ = lean_ctor_get(v_writer_1089_, 4);
v_sentMessage_1094_ = lean_ctor_get_uint8(v_writer_1089_, sizeof(void*)*6);
v_userClosedBody_1095_ = lean_ctor_get_uint8(v_writer_1089_, sizeof(void*)*6 + 1);
v_omitBody_1096_ = lean_ctor_get_uint8(v_writer_1089_, sizeof(void*)*6 + 2);
v_userDataBytes_1097_ = lean_ctor_get(v_writer_1089_, 5);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_writer_1089_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v_writer_1089_, 2);
lean_dec(v_unused_1105_);
v___x_1099_ = v_writer_1089_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_userDataBytes_1097_);
lean_inc(v_messageHead_1093_);
lean_inc(v_knownSize_1092_);
lean_inc(v_outputData_1091_);
lean_inc(v_userData_1090_);
lean_dec(v_writer_1089_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 2, v_state_1088_);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_userData_1090_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_outputData_1091_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_state_1088_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_knownSize_1092_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_messageHead_1093_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_userDataBytes_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*6, v_sentMessage_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*6 + 1, v_userClosedBody_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*6 + 2, v_omitBody_1096_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1106_, lean_object* v_state_1107_, lean_object* v_writer_1108_){
_start:
{
lean_object* v_userData_1109_; lean_object* v_outputData_1110_; lean_object* v_knownSize_1111_; lean_object* v_messageHead_1112_; uint8_t v_sentMessage_1113_; uint8_t v_userClosedBody_1114_; uint8_t v_omitBody_1115_; lean_object* v_userDataBytes_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_userData_1109_ = lean_ctor_get(v_writer_1108_, 0);
v_outputData_1110_ = lean_ctor_get(v_writer_1108_, 1);
v_knownSize_1111_ = lean_ctor_get(v_writer_1108_, 3);
v_messageHead_1112_ = lean_ctor_get(v_writer_1108_, 4);
v_sentMessage_1113_ = lean_ctor_get_uint8(v_writer_1108_, sizeof(void*)*6);
v_userClosedBody_1114_ = lean_ctor_get_uint8(v_writer_1108_, sizeof(void*)*6 + 1);
v_omitBody_1115_ = lean_ctor_get_uint8(v_writer_1108_, sizeof(void*)*6 + 2);
v_userDataBytes_1116_ = lean_ctor_get(v_writer_1108_, 5);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_writer_1108_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_writer_1108_, 2);
lean_dec(v_unused_1124_);
v___x_1118_ = v_writer_1108_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_userDataBytes_1116_);
lean_inc(v_messageHead_1112_);
lean_inc(v_knownSize_1111_);
lean_inc(v_outputData_1110_);
lean_inc(v_userData_1109_);
lean_dec(v_writer_1108_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 2, v_state_1107_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_userData_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_outputData_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_state_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_knownSize_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_messageHead_1112_);
lean_ctor_set(v_reuseFailAlloc_1122_, 5, v_userDataBytes_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*6, v_sentMessage_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*6 + 1, v_userClosedBody_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*6 + 2, v_omitBody_1115_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1125_, lean_object* v_state_1126_, lean_object* v_writer_1127_){
_start:
{
uint8_t v_dir_boxed_1128_; lean_object* v_res_1129_; 
v_dir_boxed_1128_ = lean_unbox(v_dir_1125_);
v_res_1129_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1128_, v_state_1126_, v_writer_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1130_, lean_object* v_messageHead_1131_, lean_object* v_writer_1132_){
_start:
{
lean_object* v_userData_1133_; lean_object* v_outputData_1134_; lean_object* v_state_1135_; lean_object* v_knownSize_1136_; lean_object* v_messageHead_1137_; uint8_t v_sentMessage_1138_; uint8_t v_userClosedBody_1139_; uint8_t v_omitBody_1140_; lean_object* v_userDataBytes_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_userData_1133_ = lean_ctor_get(v_writer_1132_, 0);
v_outputData_1134_ = lean_ctor_get(v_writer_1132_, 1);
v_state_1135_ = lean_ctor_get(v_writer_1132_, 2);
v_knownSize_1136_ = lean_ctor_get(v_writer_1132_, 3);
v_messageHead_1137_ = lean_ctor_get(v_writer_1132_, 4);
v_sentMessage_1138_ = lean_ctor_get_uint8(v_writer_1132_, sizeof(void*)*6);
v_userClosedBody_1139_ = lean_ctor_get_uint8(v_writer_1132_, sizeof(void*)*6 + 1);
v_omitBody_1140_ = lean_ctor_get_uint8(v_writer_1132_, sizeof(void*)*6 + 2);
v_userDataBytes_1141_ = lean_ctor_get(v_writer_1132_, 5);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_writer_1132_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1143_ = v_writer_1132_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_userDataBytes_1141_);
lean_inc(v_messageHead_1137_);
lean_inc(v_knownSize_1136_);
lean_inc(v_state_1135_);
lean_inc(v_outputData_1134_);
lean_inc(v_userData_1133_);
lean_dec(v_writer_1132_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___y_1146_; 
if (v_dir_1130_ == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = 1;
v___y_1146_ = v___x_1152_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
v___y_1146_ = v___x_1153_;
goto v___jp_1145_;
}
v___jp_1145_:
{
lean_object* v___x_6__overap_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_6__overap_1147_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1146_);
v___x_1148_ = lean_apply_2(v___x_6__overap_1147_, v_outputData_1134_, v_messageHead_1131_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1148_);
v___x_1150_ = v___x_1143_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_userData_1133_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_state_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_knownSize_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_messageHead_1137_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_userDataBytes_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, sizeof(void*)*6, v_sentMessage_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, sizeof(void*)*6 + 1, v_userClosedBody_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, sizeof(void*)*6 + 2, v_omitBody_1140_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1155_, lean_object* v_messageHead_1156_, lean_object* v_writer_1157_){
_start:
{
uint8_t v_dir_boxed_1158_; lean_object* v_res_1159_; 
v_dir_boxed_1158_ = lean_unbox(v_dir_1155_);
v_res_1159_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1158_, v_messageHead_1156_, v_writer_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_key_1162_; lean_object* v_value_1163_; lean_object* v_tail_1164_; uint8_t v___x_1165_; 
v_key_1162_ = lean_ctor_get(v_x_1161_, 0);
v_value_1163_ = lean_ctor_get(v_x_1161_, 1);
v_tail_1164_ = lean_ctor_get(v_x_1161_, 2);
v___x_1165_ = lean_string_dec_eq(v_key_1162_, v_a_1160_);
if (v___x_1165_ == 0)
{
v_x_1161_ = v_tail_1164_;
goto _start;
}
else
{
lean_inc(v_value_1163_);
return v_value_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg___boxed(lean_object* v_a_1167_, lean_object* v_x_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1167_, v_x_1168_);
lean_dec(v_x_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(lean_object* v_m_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_buckets_1172_; lean_object* v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; uint64_t v_fold_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_buckets_1172_ = lean_ctor_get(v_m_1170_, 1);
v___x_1173_ = lean_array_get_size(v_buckets_1172_);
v___x_1174_ = lean_string_hash(v_a_1171_);
v___x_1175_ = 32ULL;
v___x_1176_ = lean_uint64_shift_right(v___x_1174_, v___x_1175_);
v_fold_1177_ = lean_uint64_xor(v___x_1174_, v___x_1176_);
v___x_1178_ = 16ULL;
v___x_1179_ = lean_uint64_shift_right(v_fold_1177_, v___x_1178_);
v___x_1180_ = lean_uint64_xor(v_fold_1177_, v___x_1179_);
v___x_1181_ = lean_uint64_to_usize(v___x_1180_);
v___x_1182_ = lean_usize_of_nat(v___x_1173_);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_sub(v___x_1182_, v___x_1183_);
v___x_1185_ = lean_usize_land(v___x_1181_, v___x_1184_);
v___x_1186_ = lean_array_uget_borrowed(v_buckets_1172_, v___x_1185_);
v___x_1187_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1171_, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg___boxed(lean_object* v_m_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1188_, v_a_1189_);
lean_dec_ref(v_a_1189_);
lean_dec_ref(v_m_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = 0;
return v___x_1193_;
}
else
{
lean_object* v_key_1194_; lean_object* v_tail_1195_; uint8_t v___x_1196_; 
v_key_1194_ = lean_ctor_get(v_x_1192_, 0);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
v___x_1196_ = lean_string_dec_eq(v_key_1194_, v_a_1191_);
if (v___x_1196_ == 0)
{
v_x_1192_ = v_tail_1195_;
goto _start;
}
else
{
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1198_, lean_object* v_x_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1198_, v_x_1199_);
lean_dec(v_x_1199_);
lean_dec_ref(v_a_1198_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_buckets_1204_; lean_object* v___x_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; uint64_t v_fold_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; uint64_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_buckets_1204_ = lean_ctor_get(v_m_1202_, 1);
v___x_1205_ = lean_array_get_size(v_buckets_1204_);
v___x_1206_ = lean_string_hash(v_a_1203_);
v___x_1207_ = 32ULL;
v___x_1208_ = lean_uint64_shift_right(v___x_1206_, v___x_1207_);
v_fold_1209_ = lean_uint64_xor(v___x_1206_, v___x_1208_);
v___x_1210_ = 16ULL;
v___x_1211_ = lean_uint64_shift_right(v_fold_1209_, v___x_1210_);
v___x_1212_ = lean_uint64_xor(v_fold_1209_, v___x_1211_);
v___x_1213_ = lean_uint64_to_usize(v___x_1212_);
v___x_1214_ = lean_usize_of_nat(v___x_1205_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_sub(v___x_1214_, v___x_1215_);
v___x_1217_ = lean_usize_land(v___x_1213_, v___x_1216_);
v___x_1218_ = lean_array_uget_borrowed(v_buckets_1204_, v___x_1217_);
v___x_1219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1203_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1220_, lean_object* v_a_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1220_, v_a_1221_);
lean_dec_ref(v_a_1221_);
lean_dec_ref(v_m_1220_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(lean_object* v_s_1224_, lean_object* v_p_1225_){
_start:
{
uint32_t v___y_1227_; lean_object* v___x_1232_; uint8_t v_decide_1233_; 
v___x_1232_ = lean_string_utf8_byte_size(v_s_1224_);
v_decide_1233_ = lean_nat_dec_eq(v_p_1225_, v___x_1232_);
if (v_decide_1233_ == 0)
{
uint32_t v___x_1234_; uint8_t v___y_1236_; uint32_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1234_ = lean_string_utf8_get_fast(v_s_1224_, v_p_1225_);
v___x_1239_ = 65;
v___x_1240_ = lean_uint32_dec_le(v___x_1239_, v___x_1234_);
if (v___x_1240_ == 0)
{
v___y_1236_ = v___x_1240_;
goto v___jp_1235_;
}
else
{
uint32_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = 90;
v___x_1242_ = lean_uint32_dec_le(v___x_1234_, v___x_1241_);
v___y_1236_ = v___x_1242_;
goto v___jp_1235_;
}
v___jp_1235_:
{
if (v___y_1236_ == 0)
{
v___y_1227_ = v___x_1234_;
goto v___jp_1226_;
}
else
{
uint32_t v___x_1237_; uint32_t v___x_1238_; 
v___x_1237_ = 32;
v___x_1238_ = lean_uint32_add(v___x_1234_, v___x_1237_);
v___y_1227_ = v___x_1238_;
goto v___jp_1226_;
}
}
}
else
{
lean_dec(v_p_1225_);
return v_s_1224_;
}
v___jp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_inc(v_p_1225_);
v___x_1228_ = lean_string_utf8_set(v_s_1224_, v_p_1225_, v___y_1227_);
v___x_1229_ = l_Char_utf8Size(v___y_1227_);
v___x_1230_ = lean_nat_add(v_p_1225_, v___x_1229_);
lean_dec(v___x_1229_);
lean_dec(v_p_1225_);
v_s_1224_ = v___x_1228_;
v_p_1225_ = v___x_1230_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1244_, lean_object* v_writer_1245_){
_start:
{
uint8_t v___y_1247_; 
if (v_dir_1244_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 1;
v___y_1247_ = v___x_1264_;
goto v___jp_1246_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
v___y_1247_ = v___x_1265_;
goto v___jp_1246_;
}
v___jp_1246_:
{
lean_object* v_messageHead_1248_; lean_object* v___x_1249_; lean_object* v_entries_1250_; lean_object* v_indexes_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_messageHead_1248_ = lean_ctor_get(v_writer_1245_, 4);
v___x_1249_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1247_, v_messageHead_1248_);
v_entries_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc_ref(v_entries_1250_);
v_indexes_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc_ref(v_indexes_1251_);
lean_dec_ref(v___x_1249_);
v___x_1252_ = l_Std_Http_Header_Name_connection;
v___x_1253_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
lean_dec_ref(v_indexes_1251_);
lean_dec_ref(v_entries_1250_);
v___x_1254_ = 1;
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_entry_1257_; lean_object* v___x_1258_; lean_object* v_snd_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_indexes_1251_, v___x_1252_);
lean_dec_ref(v_indexes_1251_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v_entry_1257_ = lean_array_fget(v___x_1255_, v___x_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_array_fget(v_entries_1250_, v_entry_1257_);
lean_dec(v_entry_1257_);
lean_dec_ref(v_entries_1250_);
v_snd_1259_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_snd_1259_);
lean_dec(v___x_1258_);
v___x_1260_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(v_snd_1259_, v___x_1256_);
v___x_1261_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_1262_ = lean_string_dec_eq(v___x_1260_, v___x_1261_);
lean_dec_ref(v___x_1260_);
if (v___x_1262_ == 0)
{
return v___x_1253_;
}
else
{
uint8_t v___x_1263_; 
v___x_1263_ = 0;
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1266_, lean_object* v_writer_1267_){
_start:
{
uint8_t v_dir_boxed_1268_; uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_dir_boxed_1268_ = lean_unbox(v_dir_1266_);
v_res_1269_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1268_, v_writer_1267_);
lean_dec_ref(v_writer_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1271_, lean_object* v_m_1272_, lean_object* v_a_1273_){
_start:
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1272_, v_a_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1275_, v_m_1276_, v_a_1277_);
lean_dec_ref(v_a_1277_);
lean_dec_ref(v_m_1276_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_, lean_object* v_hma_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1281_, v_a_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___boxed(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_, lean_object* v_hma_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_00_u03b2_1285_, v_m_1286_, v_a_1287_, v_hma_1288_);
lean_dec_ref(v_a_1287_);
lean_dec_ref(v_m_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1294_, v_a_1295_, v_x_1296_);
lean_dec(v_x_1296_);
lean_dec_ref(v_a_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(lean_object* v_00_u03b2_1299_, lean_object* v_a_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1300_, v_x_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1304_, lean_object* v_a_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(v_00_u03b2_1304_, v_a_1305_, v_x_1306_, v_x_1307_);
lean_dec(v_x_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1309_){
_start:
{
lean_object* v_userData_1310_; lean_object* v_outputData_1311_; lean_object* v_knownSize_1312_; lean_object* v_messageHead_1313_; uint8_t v_sentMessage_1314_; uint8_t v_userClosedBody_1315_; uint8_t v_omitBody_1316_; lean_object* v_userDataBytes_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_userData_1310_ = lean_ctor_get(v_writer_1309_, 0);
v_outputData_1311_ = lean_ctor_get(v_writer_1309_, 1);
v_knownSize_1312_ = lean_ctor_get(v_writer_1309_, 3);
v_messageHead_1313_ = lean_ctor_get(v_writer_1309_, 4);
v_sentMessage_1314_ = lean_ctor_get_uint8(v_writer_1309_, sizeof(void*)*6);
v_userClosedBody_1315_ = lean_ctor_get_uint8(v_writer_1309_, sizeof(void*)*6 + 1);
v_omitBody_1316_ = lean_ctor_get_uint8(v_writer_1309_, sizeof(void*)*6 + 2);
v_userDataBytes_1317_ = lean_ctor_get(v_writer_1309_, 5);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_writer_1309_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_writer_1309_, 2);
lean_dec(v_unused_1326_);
v___x_1319_ = v_writer_1309_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_userDataBytes_1317_);
lean_inc(v_messageHead_1313_);
lean_inc(v_knownSize_1312_);
lean_inc(v_outputData_1311_);
lean_inc(v_userData_1310_);
lean_dec(v_writer_1309_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_box(7);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 2, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_userData_1310_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_outputData_1311_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_knownSize_1312_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v_messageHead_1313_);
lean_ctor_set(v_reuseFailAlloc_1324_, 5, v_userDataBytes_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1324_, sizeof(void*)*6, v_sentMessage_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1324_, sizeof(void*)*6 + 1, v_userClosedBody_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1324_, sizeof(void*)*6 + 2, v_omitBody_1316_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1327_, lean_object* v_writer_1328_){
_start:
{
lean_object* v_userData_1329_; lean_object* v_outputData_1330_; lean_object* v_knownSize_1331_; lean_object* v_messageHead_1332_; uint8_t v_sentMessage_1333_; uint8_t v_userClosedBody_1334_; uint8_t v_omitBody_1335_; lean_object* v_userDataBytes_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1344_; 
v_userData_1329_ = lean_ctor_get(v_writer_1328_, 0);
v_outputData_1330_ = lean_ctor_get(v_writer_1328_, 1);
v_knownSize_1331_ = lean_ctor_get(v_writer_1328_, 3);
v_messageHead_1332_ = lean_ctor_get(v_writer_1328_, 4);
v_sentMessage_1333_ = lean_ctor_get_uint8(v_writer_1328_, sizeof(void*)*6);
v_userClosedBody_1334_ = lean_ctor_get_uint8(v_writer_1328_, sizeof(void*)*6 + 1);
v_omitBody_1335_ = lean_ctor_get_uint8(v_writer_1328_, sizeof(void*)*6 + 2);
v_userDataBytes_1336_ = lean_ctor_get(v_writer_1328_, 5);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_writer_1328_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_writer_1328_, 2);
lean_dec(v_unused_1345_);
v___x_1338_ = v_writer_1328_;
v_isShared_1339_ = v_isSharedCheck_1344_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_userDataBytes_1336_);
lean_inc(v_messageHead_1332_);
lean_inc(v_knownSize_1331_);
lean_inc(v_outputData_1330_);
lean_inc(v_userData_1329_);
lean_dec(v_writer_1328_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1344_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(7);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 2, v___x_1340_);
v___x_1342_ = v___x_1338_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_userData_1329_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_outputData_1330_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_knownSize_1331_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_messageHead_1332_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v_userDataBytes_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6, v_sentMessage_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6 + 1, v_userClosedBody_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6 + 2, v_omitBody_1335_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1346_, lean_object* v_writer_1347_){
_start:
{
uint8_t v_dir_boxed_1348_; lean_object* v_res_1349_; 
v_dir_boxed_1348_ = lean_unbox(v_dir_1346_);
v_res_1349_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1348_, v_writer_1347_);
return v_res_1349_;
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
