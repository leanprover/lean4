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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_12_);
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
lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; uint8_t v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v_userData_629_; lean_object* v_outputData_630_; lean_object* v_state_631_; lean_object* v_knownSize_632_; lean_object* v_messageHead_633_; uint8_t v_sentMessage_634_; uint8_t v_userClosedBody_635_; uint8_t v_omitBody_636_; lean_object* v_userDataBytes_637_; lean_object* v_fst_639_; lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___y_657_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_userData_629_ = lean_ctor_get(v_writer_592_, 0);
v_outputData_630_ = lean_ctor_get(v_writer_592_, 1);
v_state_631_ = lean_ctor_get(v_writer_592_, 2);
v_knownSize_632_ = lean_ctor_get(v_writer_592_, 3);
v_messageHead_633_ = lean_ctor_get(v_writer_592_, 4);
v_sentMessage_634_ = lean_ctor_get_uint8(v_writer_592_, sizeof(void*)*6);
v_userClosedBody_635_ = lean_ctor_get_uint8(v_writer_592_, sizeof(void*)*6 + 1);
v_omitBody_636_ = lean_ctor_get_uint8(v_writer_592_, sizeof(void*)*6 + 2);
v_userDataBytes_637_ = lean_ctor_get(v_writer_592_, 5);
v___x_662_ = lean_array_get_size(v_userData_629_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_eq(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; uint8_t v___x_666_; 
lean_inc(v_userDataBytes_637_);
lean_inc(v_messageHead_633_);
lean_inc(v_knownSize_632_);
lean_inc(v_state_631_);
lean_inc_ref(v_outputData_630_);
lean_inc_ref(v_userData_629_);
lean_dec_ref(v_writer_592_);
v___x_665_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_666_ = lean_nat_dec_lt(v___x_663_, v___x_662_);
if (v___x_666_ == 0)
{
lean_dec_ref(v_userData_629_);
v_fst_639_ = v___x_665_;
v_fst_640_ = v___x_665_;
v_snd_641_ = v___x_663_;
goto v___jp_638_;
}
else
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_668_ = lean_nat_dec_le(v___x_662_, v___x_662_);
if (v___x_668_ == 0)
{
if (v___x_666_ == 0)
{
lean_dec_ref(v_userData_629_);
v_fst_639_ = v___x_665_;
v_fst_640_ = v___x_665_;
v_snd_641_ = v___x_663_;
goto v___jp_638_;
}
else
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((size_t)0ULL);
v___x_670_ = lean_usize_of_nat(v___x_662_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_593_, v_userData_629_, v___x_669_, v___x_670_, v___x_667_);
lean_dec_ref(v_userData_629_);
v___y_657_ = v___x_671_;
goto v___jp_656_;
}
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_662_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_593_, v_userData_629_, v___x_672_, v___x_673_, v___x_667_);
lean_dec_ref(v_userData_629_);
v___y_657_ = v___x_674_;
goto v___jp_656_;
}
}
}
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_writer_592_);
lean_ctor_set(v___x_675_, 1, v_limitSize_593_);
return v___x_675_;
}
v___jp_594_:
{
lean_object* v_data_606_; lean_object* v_size_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_628_; 
v_data_606_ = lean_ctor_get(v___y_596_, 0);
v_size_607_ = lean_ctor_get(v___y_596_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___y_596_);
if (v_isSharedCheck_628_ == 0)
{
v___x_609_ = v___y_596_;
v_isShared_610_ = v_isSharedCheck_628_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_size_607_);
lean_inc(v_data_606_);
lean_dec(v___y_596_);
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
v_remaining_620_ = lean_nat_sub(v_limitSize_593_, v___y_603_);
lean_dec(v_limitSize_593_);
v___x_621_ = lean_nat_sub(v___y_597_, v___y_603_);
lean_dec(v___y_603_);
lean_dec(v___y_597_);
v___x_622_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_622_, 0, v___y_602_);
lean_ctor_set(v___x_622_, 1, v_outputData_619_);
lean_ctor_set(v___x_622_, 2, v___y_595_);
lean_ctor_set(v___x_622_, 3, v___y_601_);
lean_ctor_set(v___x_622_, 4, v___y_598_);
lean_ctor_set(v___x_622_, 5, v___x_621_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*6, v___y_600_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*6 + 1, v___y_604_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*6 + 2, v___y_599_);
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
v___y_595_ = v_state_631_;
v___y_596_ = v_outputData_630_;
v___y_597_ = v_userDataBytes_637_;
v___y_598_ = v_messageHead_633_;
v___y_599_ = v_omitBody_636_;
v___y_600_ = v_sentMessage_634_;
v___y_601_ = v_knownSize_632_;
v___y_602_ = v_fst_640_;
v___y_603_ = v_snd_641_;
v___y_604_ = v_userClosedBody_635_;
v___y_605_ = v___x_645_;
goto v___jp_594_;
}
else
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_le(v___x_643_, v___x_643_);
if (v___x_646_ == 0)
{
if (v___x_644_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_fst_639_);
lean_ctor_set(v___x_647_, 1, v___x_642_);
v___y_595_ = v_state_631_;
v___y_596_ = v_outputData_630_;
v___y_597_ = v_userDataBytes_637_;
v___y_598_ = v_messageHead_633_;
v___y_599_ = v_omitBody_636_;
v___y_600_ = v_sentMessage_634_;
v___y_601_ = v_knownSize_632_;
v___y_602_ = v_fst_640_;
v___y_603_ = v_snd_641_;
v___y_604_ = v_userClosedBody_635_;
v___y_605_ = v___x_647_;
goto v___jp_594_;
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_643_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_639_, v___x_648_, v___x_649_, v___x_642_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v_fst_639_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___y_595_ = v_state_631_;
v___y_596_ = v_outputData_630_;
v___y_597_ = v_userDataBytes_637_;
v___y_598_ = v_messageHead_633_;
v___y_599_ = v_omitBody_636_;
v___y_600_ = v_sentMessage_634_;
v___y_601_ = v_knownSize_632_;
v___y_602_ = v_fst_640_;
v___y_603_ = v_snd_641_;
v___y_604_ = v_userClosedBody_635_;
v___y_605_ = v___x_651_;
goto v___jp_594_;
}
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_643_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_639_, v___x_652_, v___x_653_, v___x_642_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_fst_639_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___y_595_ = v_state_631_;
v___y_596_ = v_outputData_630_;
v___y_597_ = v_userDataBytes_637_;
v___y_598_ = v_messageHead_633_;
v___y_599_ = v_omitBody_636_;
v___y_600_ = v_sentMessage_634_;
v___y_601_ = v_knownSize_632_;
v___y_602_ = v_fst_640_;
v___y_603_ = v_snd_641_;
v___y_604_ = v_userClosedBody_635_;
v___y_605_ = v___x_655_;
goto v___jp_594_;
}
}
}
v___jp_656_:
{
lean_object* v_snd_658_; lean_object* v_fst_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; 
v_snd_658_ = lean_ctor_get(v___y_657_, 1);
lean_inc(v_snd_658_);
v_fst_659_ = lean_ctor_get(v___y_657_, 0);
lean_inc(v_fst_659_);
lean_dec_ref(v___y_657_);
v_fst_660_ = lean_ctor_get(v_snd_658_, 0);
lean_inc(v_fst_660_);
v_snd_661_ = lean_ctor_get(v_snd_658_, 1);
lean_inc(v_snd_661_);
lean_dec(v_snd_658_);
v_fst_639_ = v_fst_659_;
v_fst_640_ = v_fst_660_;
v_snd_641_ = v_snd_661_;
goto v___jp_638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_676_, lean_object* v_writer_677_, lean_object* v_limitSize_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_677_, v_limitSize_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_680_, lean_object* v_writer_681_, lean_object* v_limitSize_682_){
_start:
{
uint8_t v_dir_boxed_683_; lean_object* v_res_684_; 
v_dir_boxed_683_ = lean_unbox(v_dir_680_);
v_res_684_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_683_, v_writer_681_, v_limitSize_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_685_, size_t v_i_686_, size_t v_stop_687_, lean_object* v_b_688_){
_start:
{
lean_object* v___y_690_; uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_eq(v_i_686_, v_stop_687_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v_data_696_; uint8_t v___x_697_; 
v___x_695_ = lean_array_uget_borrowed(v_as_685_, v_i_686_);
v_data_696_ = lean_ctor_get(v___x_695_, 0);
v___x_697_ = l_ByteArray_isEmpty(v_data_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_inc(v___x_695_);
v___x_698_ = lean_array_push(v_b_688_, v___x_695_);
v___y_690_ = v___x_698_;
goto v___jp_689_;
}
else
{
v___y_690_ = v_b_688_;
goto v___jp_689_;
}
}
else
{
return v_b_688_;
}
v___jp_689_:
{
size_t v___x_691_; size_t v___x_692_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_686_, v___x_691_);
v_i_686_ = v___x_692_;
v_b_688_ = v___y_690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_699_, lean_object* v_i_700_, lean_object* v_stop_701_, lean_object* v_b_702_){
_start:
{
size_t v_i_boxed_703_; size_t v_stop_boxed_704_; lean_object* v_res_705_; 
v_i_boxed_703_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_stop_boxed_704_ = lean_unbox_usize(v_stop_701_);
lean_dec(v_stop_701_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_699_, v_i_boxed_703_, v_stop_boxed_704_, v_b_702_);
lean_dec_ref(v_as_699_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_706_, size_t v_i_707_, lean_object* v_bs_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_lt(v_i_707_, v_sz_706_);
if (v___x_709_ == 0)
{
return v_bs_708_;
}
else
{
lean_object* v_v_710_; lean_object* v___x_711_; lean_object* v_bs_x27_712_; uint32_t v___x_713_; uint8_t v___x_714_; size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_v_710_ = lean_array_uget(v_bs_708_, v_i_707_);
v___x_711_ = lean_unsigned_to_nat(0u);
v_bs_x27_712_ = lean_array_uset(v_bs_708_, v_i_707_, v___x_711_);
v___x_713_ = lean_unbox_uint32(v_v_710_);
lean_dec(v_v_710_);
v___x_714_ = lean_uint32_to_uint8(v___x_713_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_add(v_i_707_, v___x_715_);
v___x_717_ = lean_box(v___x_714_);
v___x_718_ = lean_array_uset(v_bs_x27_712_, v_i_707_, v___x_717_);
v_i_707_ = v___x_716_;
v_bs_708_ = v___x_718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_720_, lean_object* v_i_721_, lean_object* v_bs_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_720_);
lean_dec(v_sz_720_);
v_i_boxed_724_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_723_, v_i_boxed_724_, v_bs_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_728_, size_t v_i_729_, size_t v_stop_730_, lean_object* v_b_731_){
_start:
{
lean_object* v___y_733_; uint8_t v___x_737_; 
v___x_737_ = lean_usize_dec_eq(v_i_729_, v_stop_730_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v_fst_739_; lean_object* v_snd_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = lean_array_uget_borrowed(v_as_728_, v_i_729_);
v_fst_739_ = lean_ctor_get(v___x_738_, 0);
v_snd_740_ = lean_ctor_get(v___x_738_, 1);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_742_ = lean_string_append(v_b_731_, v___x_741_);
v___x_743_ = lean_string_append(v___x_742_, v_fst_739_);
if (lean_obj_tag(v_snd_740_) == 0)
{
v___y_733_ = v___x_743_;
goto v___jp_732_;
}
else
{
lean_object* v_val_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_val_744_ = lean_ctor_get(v_snd_740_, 0);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_744_);
v___x_746_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_744_);
v___x_747_ = lean_string_append(v___x_745_, v___x_746_);
lean_dec_ref(v___x_746_);
v___x_748_ = lean_string_append(v___x_743_, v___x_747_);
lean_dec_ref(v___x_747_);
v___y_733_ = v___x_748_;
goto v___jp_732_;
}
}
else
{
return v_b_731_;
}
v___jp_732_:
{
size_t v___x_734_; size_t v___x_735_; 
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_729_, v___x_734_);
v_i_729_ = v___x_735_;
v_b_731_ = v___y_733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_stop_751_, lean_object* v_b_752_){
_start:
{
size_t v_i_boxed_753_; size_t v_stop_boxed_754_; lean_object* v_res_755_; 
v_i_boxed_753_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_stop_boxed_754_ = lean_unbox_usize(v_stop_751_);
lean_dec(v_stop_751_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_749_, v_i_boxed_753_, v_stop_boxed_754_, v_b_752_);
lean_dec_ref(v_as_749_);
return v_res_755_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_758_ = lean_string_to_utf8(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_760_, size_t v_i_761_, size_t v_stop_762_, lean_object* v_b_763_){
_start:
{
lean_object* v___y_765_; uint8_t v___x_782_; 
v___x_782_ = lean_usize_dec_eq(v_i_761_, v_stop_762_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v_data_784_; lean_object* v_extensions_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_839_; 
v___x_783_ = lean_array_uget(v_as_760_, v_i_761_);
v_data_784_ = lean_ctor_get(v___x_783_, 0);
v_extensions_785_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_839_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_839_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_extensions_785_);
lean_inc(v_data_784_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_839_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_chunkLen_789_; lean_object* v___y_791_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_chunkLen_789_ = lean_byte_array_size(v_data_784_);
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_array_get_size(v_extensions_785_);
v___x_831_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_dec_ref(v_extensions_785_);
v___y_791_ = v___x_828_;
goto v___jp_790_;
}
else
{
uint8_t v___x_832_; 
v___x_832_ = lean_nat_dec_le(v___x_830_, v___x_830_);
if (v___x_832_ == 0)
{
if (v___x_831_ == 0)
{
lean_dec_ref(v_extensions_785_);
v___y_791_ = v___x_828_;
goto v___jp_790_;
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_of_nat(v___x_830_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_785_, v___x_833_, v___x_834_, v___x_828_);
lean_dec_ref(v_extensions_785_);
v___y_791_ = v___x_835_;
goto v___jp_790_;
}
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_830_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_785_, v___x_836_, v___x_837_, v___x_828_);
lean_dec_ref(v_extensions_785_);
v___y_791_ = v___x_838_;
goto v___jp_790_;
}
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; lean_object* v_size_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_792_ = lean_unsigned_to_nat(16u);
v___x_793_ = l_Nat_toDigits(v___x_792_, v_chunkLen_789_);
v___x_794_ = lean_array_mk(v___x_793_);
v_sz_795_ = lean_array_size(v___x_794_);
v___x_796_ = ((size_t)0ULL);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_795_, v___x_796_, v___x_794_);
v_size_798_ = lean_byte_array_mk(v___x_797_);
v___x_799_ = lean_string_to_utf8(v___y_791_);
lean_dec_ref(v___y_791_);
v___x_800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_801_ = lean_unsigned_to_nat(5u);
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_803_ = lean_array_push(v___x_802_, v_size_798_);
v___x_804_ = lean_array_push(v___x_803_, v___x_799_);
v___x_805_ = lean_array_push(v___x_804_, v___x_800_);
v___x_806_ = lean_array_push(v___x_805_, v_data_784_);
v___x_807_ = lean_array_push(v___x_806_, v___x_800_);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_array_get_size(v___x_807_);
v___x_810_ = lean_nat_dec_lt(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_812_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_808_);
lean_ctor_set(v___x_787_, 0, v___x_807_);
v___x_812_ = v___x_787_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_808_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v___y_765_ = v___x_812_;
goto v___jp_764_;
}
}
else
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_le(v___x_809_, v___x_809_);
if (v___x_814_ == 0)
{
if (v___x_810_ == 0)
{
lean_object* v___x_816_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_808_);
lean_ctor_set(v___x_787_, 0, v___x_807_);
v___x_816_ = v___x_787_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_808_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v___y_765_ = v___x_816_;
goto v___jp_764_;
}
}
else
{
size_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = lean_usize_of_nat(v___x_809_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_807_, v___x_796_, v___x_818_, v___x_808_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_819_);
lean_ctor_set(v___x_787_, 0, v___x_807_);
v___x_821_ = v___x_787_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v___y_765_ = v___x_821_;
goto v___jp_764_;
}
}
}
else
{
size_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_823_ = lean_usize_of_nat(v___x_809_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_807_, v___x_796_, v___x_823_, v___x_808_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_824_);
lean_ctor_set(v___x_787_, 0, v___x_807_);
v___x_826_ = v___x_787_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v___y_765_ = v___x_826_;
goto v___jp_764_;
}
}
}
}
}
}
else
{
return v_b_763_;
}
v___jp_764_:
{
lean_object* v_data_766_; lean_object* v_size_767_; lean_object* v_data_768_; lean_object* v_size_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_781_; 
v_data_766_ = lean_ctor_get(v_b_763_, 0);
lean_inc_ref(v_data_766_);
v_size_767_ = lean_ctor_get(v_b_763_, 1);
lean_inc(v_size_767_);
lean_dec_ref(v_b_763_);
v_data_768_ = lean_ctor_get(v___y_765_, 0);
v_size_769_ = lean_ctor_get(v___y_765_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v___y_765_);
if (v_isSharedCheck_781_ == 0)
{
v___x_771_ = v___y_765_;
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_size_769_);
lean_inc(v_data_768_);
lean_dec(v___y_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = l_Array_append___redArg(v_data_766_, v_data_768_);
lean_dec_ref(v_data_768_);
v___x_774_ = lean_nat_add(v_size_767_, v_size_769_);
lean_dec(v_size_769_);
lean_dec(v_size_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_774_);
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
size_t v___x_777_; size_t v___x_778_; 
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_i_761_, v___x_777_);
v_i_761_ = v___x_778_;
v_b_763_ = v___x_776_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_840_, lean_object* v_i_841_, lean_object* v_stop_842_, lean_object* v_b_843_){
_start:
{
size_t v_i_boxed_844_; size_t v_stop_boxed_845_; lean_object* v_res_846_; 
v_i_boxed_844_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_stop_boxed_845_ = lean_unbox_usize(v_stop_842_);
lean_dec(v_stop_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_840_, v_i_boxed_844_, v_stop_boxed_845_, v_b_843_);
lean_dec_ref(v_as_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_849_){
_start:
{
lean_object* v_userData_850_; lean_object* v_outputData_851_; lean_object* v_state_852_; lean_object* v_knownSize_853_; lean_object* v_messageHead_854_; uint8_t v_sentMessage_855_; uint8_t v_userClosedBody_856_; uint8_t v_omitBody_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___y_861_; uint8_t v___x_876_; 
v_userData_850_ = lean_ctor_get(v_writer_849_, 0);
v_outputData_851_ = lean_ctor_get(v_writer_849_, 1);
v_state_852_ = lean_ctor_get(v_writer_849_, 2);
v_knownSize_853_ = lean_ctor_get(v_writer_849_, 3);
v_messageHead_854_ = lean_ctor_get(v_writer_849_, 4);
v_sentMessage_855_ = lean_ctor_get_uint8(v_writer_849_, sizeof(void*)*6);
v_userClosedBody_856_ = lean_ctor_get_uint8(v_writer_849_, sizeof(void*)*6 + 1);
v_omitBody_857_ = lean_ctor_get_uint8(v_writer_849_, sizeof(void*)*6 + 2);
v___x_858_ = lean_array_get_size(v_userData_850_);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_nat_dec_eq(v___x_858_, v___x_859_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; uint8_t v___x_878_; 
lean_inc(v_messageHead_854_);
lean_inc(v_knownSize_853_);
lean_inc(v_state_852_);
lean_inc_ref(v_outputData_851_);
lean_inc_ref(v_userData_850_);
lean_dec_ref(v_writer_849_);
v___x_877_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_878_ = lean_nat_dec_lt(v___x_859_, v___x_858_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_userData_850_);
v___y_861_ = v___x_877_;
goto v___jp_860_;
}
else
{
uint8_t v___x_879_; 
v___x_879_ = lean_nat_dec_le(v___x_858_, v___x_858_);
if (v___x_879_ == 0)
{
if (v___x_878_ == 0)
{
lean_dec_ref(v_userData_850_);
v___y_861_ = v___x_877_;
goto v___jp_860_;
}
else
{
size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((size_t)0ULL);
v___x_881_ = lean_usize_of_nat(v___x_858_);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_850_, v___x_880_, v___x_881_, v___x_877_);
lean_dec_ref(v_userData_850_);
v___y_861_ = v___x_882_;
goto v___jp_860_;
}
}
else
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((size_t)0ULL);
v___x_884_ = lean_usize_of_nat(v___x_858_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_850_, v___x_883_, v___x_884_, v___x_877_);
lean_dec_ref(v_userData_850_);
v___y_861_ = v___x_885_;
goto v___jp_860_;
}
}
}
else
{
return v_writer_849_;
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_863_ = lean_array_get_size(v___y_861_);
v___x_864_ = lean_nat_dec_lt(v___x_859_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec_ref(v___y_861_);
v___x_865_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_865_, 0, v___x_862_);
lean_ctor_set(v___x_865_, 1, v_outputData_851_);
lean_ctor_set(v___x_865_, 2, v_state_852_);
lean_ctor_set(v___x_865_, 3, v_knownSize_853_);
lean_ctor_set(v___x_865_, 4, v_messageHead_854_);
lean_ctor_set(v___x_865_, 5, v___x_859_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*6, v_sentMessage_855_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*6 + 1, v_userClosedBody_856_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*6 + 2, v_omitBody_857_);
return v___x_865_;
}
else
{
uint8_t v___x_866_; 
v___x_866_ = lean_nat_dec_le(v___x_863_, v___x_863_);
if (v___x_866_ == 0)
{
if (v___x_864_ == 0)
{
lean_object* v___x_867_; 
lean_dec_ref(v___y_861_);
v___x_867_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_867_, 0, v___x_862_);
lean_ctor_set(v___x_867_, 1, v_outputData_851_);
lean_ctor_set(v___x_867_, 2, v_state_852_);
lean_ctor_set(v___x_867_, 3, v_knownSize_853_);
lean_ctor_set(v___x_867_, 4, v_messageHead_854_);
lean_ctor_set(v___x_867_, 5, v___x_859_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*6, v_sentMessage_855_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*6 + 1, v_userClosedBody_856_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*6 + 2, v_omitBody_857_);
return v___x_867_;
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = ((size_t)0ULL);
v___x_869_ = lean_usize_of_nat(v___x_863_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_861_, v___x_868_, v___x_869_, v_outputData_851_);
lean_dec_ref(v___y_861_);
v___x_871_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_871_, 0, v___x_862_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
lean_ctor_set(v___x_871_, 2, v_state_852_);
lean_ctor_set(v___x_871_, 3, v_knownSize_853_);
lean_ctor_set(v___x_871_, 4, v_messageHead_854_);
lean_ctor_set(v___x_871_, 5, v___x_859_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*6, v_sentMessage_855_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*6 + 1, v_userClosedBody_856_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*6 + 2, v_omitBody_857_);
return v___x_871_;
}
}
else
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = ((size_t)0ULL);
v___x_873_ = lean_usize_of_nat(v___x_863_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_861_, v___x_872_, v___x_873_, v_outputData_851_);
lean_dec_ref(v___y_861_);
v___x_875_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_875_, 0, v___x_862_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
lean_ctor_set(v___x_875_, 2, v_state_852_);
lean_ctor_set(v___x_875_, 3, v_knownSize_853_);
lean_ctor_set(v___x_875_, 4, v_messageHead_854_);
lean_ctor_set(v___x_875_, 5, v___x_859_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*6, v_sentMessage_855_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*6 + 1, v_userClosedBody_856_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*6 + 2, v_omitBody_857_);
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_886_, lean_object* v_writer_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_889_, lean_object* v_writer_890_){
_start:
{
uint8_t v_dir_boxed_891_; lean_object* v_res_892_; 
v_dir_boxed_891_ = lean_unbox(v_dir_889_);
v_res_892_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_891_, v_writer_890_);
return v_res_892_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_895_ = lean_string_to_utf8(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_897_ = lean_byte_array_size(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_898_){
_start:
{
lean_object* v_writer_899_; lean_object* v_outputData_900_; lean_object* v_userData_901_; lean_object* v_knownSize_902_; lean_object* v_messageHead_903_; uint8_t v_sentMessage_904_; uint8_t v_userClosedBody_905_; uint8_t v_omitBody_906_; lean_object* v_userDataBytes_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_928_; 
v_writer_899_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_898_);
v_outputData_900_ = lean_ctor_get(v_writer_899_, 1);
v_userData_901_ = lean_ctor_get(v_writer_899_, 0);
v_knownSize_902_ = lean_ctor_get(v_writer_899_, 3);
v_messageHead_903_ = lean_ctor_get(v_writer_899_, 4);
v_sentMessage_904_ = lean_ctor_get_uint8(v_writer_899_, sizeof(void*)*6);
v_userClosedBody_905_ = lean_ctor_get_uint8(v_writer_899_, sizeof(void*)*6 + 1);
v_omitBody_906_ = lean_ctor_get_uint8(v_writer_899_, sizeof(void*)*6 + 2);
v_userDataBytes_907_ = lean_ctor_get(v_writer_899_, 5);
v_isSharedCheck_928_ = !lean_is_exclusive(v_writer_899_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_writer_899_, 2);
lean_dec(v_unused_929_);
v___x_909_ = v_writer_899_;
v_isShared_910_ = v_isSharedCheck_928_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_userDataBytes_907_);
lean_inc(v_messageHead_903_);
lean_inc(v_knownSize_902_);
lean_inc(v_outputData_900_);
lean_inc(v_userData_901_);
lean_dec(v_writer_899_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_928_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_data_911_; lean_object* v_size_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_927_; 
v_data_911_ = lean_ctor_get(v_outputData_900_, 0);
v_size_912_ = lean_ctor_get(v_outputData_900_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_outputData_900_);
if (v_isSharedCheck_927_ == 0)
{
v___x_914_ = v_outputData_900_;
v_isShared_915_ = v_isSharedCheck_927_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_size_912_);
lean_inc(v_data_911_);
lean_dec(v_outputData_900_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_927_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_916_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_917_ = lean_array_push(v_data_911_, v___x_916_);
v___x_918_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_919_ = lean_nat_add(v_size_912_, v___x_918_);
lean_dec(v_size_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_919_);
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_926_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_box(6);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 2, v___x_922_);
lean_ctor_set(v___x_909_, 1, v___x_921_);
v___x_924_ = v___x_909_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_userData_901_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_knownSize_902_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_messageHead_903_);
lean_ctor_set(v_reuseFailAlloc_925_, 5, v_userDataBytes_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*6, v_sentMessage_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*6 + 1, v_userClosedBody_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*6 + 2, v_omitBody_906_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_930_, lean_object* v_writer_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_933_, lean_object* v_writer_934_){
_start:
{
uint8_t v_dir_boxed_935_; lean_object* v_res_936_; 
v_dir_boxed_935_ = lean_unbox(v_dir_933_);
v_res_936_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_935_, v_writer_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_937_, size_t v_i_938_, size_t v_stop_939_, lean_object* v_b_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_eq(v_i_938_, v_stop_939_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v_data_943_; lean_object* v_data_944_; lean_object* v_size_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_958_; 
v___x_942_ = lean_array_uget_borrowed(v_as_937_, v_i_938_);
v_data_943_ = lean_ctor_get(v___x_942_, 0);
v_data_944_ = lean_ctor_get(v_b_940_, 0);
v_size_945_ = lean_ctor_get(v_b_940_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_b_940_);
if (v_isSharedCheck_958_ == 0)
{
v___x_947_ = v_b_940_;
v_isShared_948_ = v_isSharedCheck_958_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_size_945_);
lean_inc(v_data_944_);
lean_dec(v_b_940_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_958_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_inc_ref(v_data_943_);
v___x_949_ = lean_array_push(v_data_944_, v_data_943_);
v___x_950_ = lean_byte_array_size(v_data_943_);
v___x_951_ = lean_nat_add(v_size_945_, v___x_950_);
lean_dec(v_size_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_951_);
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
size_t v___x_954_; size_t v___x_955_; 
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_938_, v___x_954_);
v_i_938_ = v___x_955_;
v_b_940_ = v___x_953_;
goto _start;
}
}
}
else
{
return v_b_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_959_, lean_object* v_i_960_, lean_object* v_stop_961_, lean_object* v_b_962_){
_start:
{
size_t v_i_boxed_963_; size_t v_stop_boxed_964_; lean_object* v_res_965_; 
v_i_boxed_963_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_stop_boxed_964_ = lean_unbox_usize(v_stop_961_);
lean_dec(v_stop_961_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_959_, v_i_boxed_963_, v_stop_boxed_964_, v_b_962_);
lean_dec_ref(v_as_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_966_){
_start:
{
lean_object* v_userData_967_; lean_object* v_outputData_968_; lean_object* v_state_969_; lean_object* v_knownSize_970_; lean_object* v_messageHead_971_; uint8_t v_sentMessage_972_; uint8_t v_userClosedBody_973_; uint8_t v_omitBody_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1001_; 
v_userData_967_ = lean_ctor_get(v_writer_966_, 0);
v_outputData_968_ = lean_ctor_get(v_writer_966_, 1);
v_state_969_ = lean_ctor_get(v_writer_966_, 2);
v_knownSize_970_ = lean_ctor_get(v_writer_966_, 3);
v_messageHead_971_ = lean_ctor_get(v_writer_966_, 4);
v_sentMessage_972_ = lean_ctor_get_uint8(v_writer_966_, sizeof(void*)*6);
v_userClosedBody_973_ = lean_ctor_get_uint8(v_writer_966_, sizeof(void*)*6 + 1);
v_omitBody_974_ = lean_ctor_get_uint8(v_writer_966_, sizeof(void*)*6 + 2);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_writer_966_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v_writer_966_, 5);
lean_dec(v_unused_1002_);
v___x_976_ = v_writer_966_;
v_isShared_977_ = v_isSharedCheck_1001_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_messageHead_971_);
lean_inc(v_knownSize_970_);
lean_inc(v_state_969_);
lean_inc(v_outputData_968_);
lean_inc(v_userData_967_);
lean_dec(v_writer_966_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1001_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_980_ = lean_array_get_size(v_userData_967_);
v___x_981_ = lean_nat_dec_lt(v___x_978_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; 
lean_dec_ref(v_userData_967_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 5, v___x_978_);
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_983_ = v___x_976_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_outputData_968_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_state_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_knownSize_970_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_messageHead_971_);
lean_ctor_set(v_reuseFailAlloc_984_, 5, v___x_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*6, v_sentMessage_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*6 + 1, v_userClosedBody_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*6 + 2, v_omitBody_974_);
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
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_985_ == 0)
{
if (v___x_981_ == 0)
{
lean_object* v___x_987_; 
lean_dec_ref(v_userData_967_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 5, v___x_978_);
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_987_ = v___x_976_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_outputData_968_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_state_969_);
lean_ctor_set(v_reuseFailAlloc_988_, 3, v_knownSize_970_);
lean_ctor_set(v_reuseFailAlloc_988_, 4, v_messageHead_971_);
lean_ctor_set(v_reuseFailAlloc_988_, 5, v___x_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*6, v_sentMessage_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*6 + 1, v_userClosedBody_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*6 + 2, v_omitBody_974_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_980_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_967_, v___x_989_, v___x_990_, v_outputData_968_);
lean_dec_ref(v_userData_967_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 5, v___x_978_);
lean_ctor_set(v___x_976_, 1, v___x_991_);
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_993_ = v___x_976_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_state_969_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_knownSize_970_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_messageHead_971_);
lean_ctor_set(v_reuseFailAlloc_994_, 5, v___x_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*6, v_sentMessage_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*6 + 1, v_userClosedBody_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*6 + 2, v_omitBody_974_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_995_ = ((size_t)0ULL);
v___x_996_ = lean_usize_of_nat(v___x_980_);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_967_, v___x_995_, v___x_996_, v_outputData_968_);
lean_dec_ref(v_userData_967_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 5, v___x_978_);
lean_ctor_set(v___x_976_, 1, v___x_997_);
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_999_ = v___x_976_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_state_969_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_knownSize_970_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_messageHead_971_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v___x_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*6, v_sentMessage_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*6 + 1, v_userClosedBody_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*6 + 2, v_omitBody_974_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_1003_, lean_object* v_writer_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_1006_, lean_object* v_writer_1007_){
_start:
{
uint8_t v_dir_boxed_1008_; lean_object* v_res_1009_; 
v_dir_boxed_1008_ = lean_unbox(v_dir_1006_);
v_res_1009_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_1008_, v_writer_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_1010_, lean_object* v_x1_1011_, lean_object* v_x2_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_byte_array_size(v_x1_1011_);
v___x_1015_ = lean_byte_array_size(v_x2_1012_);
v___x_1016_ = lean_byte_array_copy_slice(v_x2_1012_, v___x_1013_, v_x1_1011_, v___x_1014_, v___x_1015_, v___x_1010_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_1017_, lean_object* v_x1_1018_, lean_object* v_x2_1019_){
_start:
{
uint8_t v___x_120__boxed_1020_; lean_object* v_res_1021_; 
v___x_120__boxed_1020_ = lean_unbox(v___x_1017_);
v_res_1021_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_120__boxed_1020_, v_x1_1018_, v_x2_1019_);
lean_dec_ref(v_x2_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_1025_){
_start:
{
lean_object* v_userData_1026_; lean_object* v_outputData_1027_; lean_object* v_state_1028_; lean_object* v_knownSize_1029_; lean_object* v_messageHead_1030_; uint8_t v_sentMessage_1031_; uint8_t v_userClosedBody_1032_; uint8_t v_omitBody_1033_; lean_object* v_userDataBytes_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1066_; 
v_userData_1026_ = lean_ctor_get(v_writer_1025_, 0);
v_outputData_1027_ = lean_ctor_get(v_writer_1025_, 1);
v_state_1028_ = lean_ctor_get(v_writer_1025_, 2);
v_knownSize_1029_ = lean_ctor_get(v_writer_1025_, 3);
v_messageHead_1030_ = lean_ctor_get(v_writer_1025_, 4);
v_sentMessage_1031_ = lean_ctor_get_uint8(v_writer_1025_, sizeof(void*)*6);
v_userClosedBody_1032_ = lean_ctor_get_uint8(v_writer_1025_, sizeof(void*)*6 + 1);
v_omitBody_1033_ = lean_ctor_get_uint8(v_writer_1025_, sizeof(void*)*6 + 2);
v_userDataBytes_1034_ = lean_ctor_get(v_writer_1025_, 5);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_writer_1025_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1036_ = v_writer_1025_;
v_isShared_1037_ = v_isSharedCheck_1066_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_userDataBytes_1034_);
lean_inc(v_messageHead_1030_);
lean_inc(v_knownSize_1029_);
lean_inc(v_state_1028_);
lean_inc(v_outputData_1027_);
lean_inc(v_userData_1026_);
lean_dec(v_writer_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1066_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___y_1039_; lean_object* v_data_1046_; lean_object* v_size_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_data_1046_ = lean_ctor_get(v_outputData_1027_, 0);
lean_inc_ref(v_data_1046_);
v_size_1047_ = lean_ctor_get(v_outputData_1027_, 1);
lean_inc(v_size_1047_);
lean_dec_ref(v_outputData_1027_);
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_array_get_size(v_data_1046_);
v___x_1050_ = lean_nat_dec_eq(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1051_ = lean_mk_empty_byte_array(v_size_1047_);
lean_dec(v_size_1047_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v___x_1049_);
if (v___x_1054_ == 0)
{
lean_dec_ref(v_data_1046_);
v___y_1039_ = v___x_1051_;
goto v___jp_1038_;
}
else
{
lean_object* v___x_1055_; lean_object* v___f_1056_; uint8_t v___x_1057_; 
v___x_1055_ = lean_box(v___x_1050_);
v___f_1056_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1056_, 0, v___x_1055_);
v___x_1057_ = lean_nat_dec_le(v___x_1049_, v___x_1049_);
if (v___x_1057_ == 0)
{
if (v___x_1054_ == 0)
{
lean_dec_ref(v___f_1056_);
lean_dec_ref(v_data_1046_);
v___y_1039_ = v___x_1051_;
goto v___jp_1038_;
}
else
{
size_t v___x_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = lean_usize_of_nat(v___x_1049_);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1053_, v___f_1056_, v_data_1046_, v___x_1058_, v___x_1059_, v___x_1051_);
v___y_1039_ = v___x_1060_;
goto v___jp_1038_;
}
}
else
{
size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = lean_usize_of_nat(v___x_1049_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1053_, v___f_1056_, v_data_1046_, v___x_1061_, v___x_1062_, v___x_1051_);
v___y_1039_ = v___x_1063_;
goto v___jp_1038_;
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v_size_1047_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_array_fget(v_data_1046_, v___x_1064_);
lean_dec_ref(v_data_1046_);
v___y_1039_ = v___x_1065_;
goto v___jp_1038_;
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1040_);
v___x_1042_ = v___x_1036_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_userData_1026_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_state_1028_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_knownSize_1029_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_messageHead_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_userDataBytes_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*6, v_sentMessage_1031_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*6 + 1, v_userClosedBody_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*6 + 2, v_omitBody_1033_);
v___x_1042_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___y_1039_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1067_, lean_object* v_writer_1068_){
_start:
{
lean_object* v_userData_1069_; lean_object* v_outputData_1070_; lean_object* v_state_1071_; lean_object* v_knownSize_1072_; lean_object* v_messageHead_1073_; uint8_t v_sentMessage_1074_; uint8_t v_userClosedBody_1075_; uint8_t v_omitBody_1076_; lean_object* v_userDataBytes_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1109_; 
v_userData_1069_ = lean_ctor_get(v_writer_1068_, 0);
v_outputData_1070_ = lean_ctor_get(v_writer_1068_, 1);
v_state_1071_ = lean_ctor_get(v_writer_1068_, 2);
v_knownSize_1072_ = lean_ctor_get(v_writer_1068_, 3);
v_messageHead_1073_ = lean_ctor_get(v_writer_1068_, 4);
v_sentMessage_1074_ = lean_ctor_get_uint8(v_writer_1068_, sizeof(void*)*6);
v_userClosedBody_1075_ = lean_ctor_get_uint8(v_writer_1068_, sizeof(void*)*6 + 1);
v_omitBody_1076_ = lean_ctor_get_uint8(v_writer_1068_, sizeof(void*)*6 + 2);
v_userDataBytes_1077_ = lean_ctor_get(v_writer_1068_, 5);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_writer_1068_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1079_ = v_writer_1068_;
v_isShared_1080_ = v_isSharedCheck_1109_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_userDataBytes_1077_);
lean_inc(v_messageHead_1073_);
lean_inc(v_knownSize_1072_);
lean_inc(v_state_1071_);
lean_inc(v_outputData_1070_);
lean_inc(v_userData_1069_);
lean_dec(v_writer_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1109_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___y_1082_; lean_object* v_data_1089_; lean_object* v_size_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_data_1089_ = lean_ctor_get(v_outputData_1070_, 0);
lean_inc_ref(v_data_1089_);
v_size_1090_ = lean_ctor_get(v_outputData_1070_, 1);
lean_inc(v_size_1090_);
lean_dec_ref(v_outputData_1070_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_array_get_size(v_data_1089_);
v___x_1093_ = lean_nat_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1094_ = lean_mk_empty_byte_array(v_size_1090_);
lean_dec(v_size_1090_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1097_ = lean_nat_dec_lt(v___x_1095_, v___x_1092_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v_data_1089_);
v___y_1082_ = v___x_1094_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1098_; lean_object* v___f_1099_; uint8_t v___x_1100_; 
v___x_1098_ = lean_box(v___x_1093_);
v___f_1099_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1099_, 0, v___x_1098_);
v___x_1100_ = lean_nat_dec_le(v___x_1092_, v___x_1092_);
if (v___x_1100_ == 0)
{
if (v___x_1097_ == 0)
{
lean_dec_ref(v___f_1099_);
lean_dec_ref(v_data_1089_);
v___y_1082_ = v___x_1094_;
goto v___jp_1081_;
}
else
{
size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = lean_usize_of_nat(v___x_1092_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1096_, v___f_1099_, v_data_1089_, v___x_1101_, v___x_1102_, v___x_1094_);
v___y_1082_ = v___x_1103_;
goto v___jp_1081_;
}
}
else
{
size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = ((size_t)0ULL);
v___x_1105_ = lean_usize_of_nat(v___x_1092_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1096_, v___f_1099_, v_data_1089_, v___x_1104_, v___x_1105_, v___x_1094_);
v___y_1082_ = v___x_1106_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_size_1090_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_array_fget(v_data_1089_, v___x_1107_);
lean_dec_ref(v_data_1089_);
v___y_1082_ = v___x_1108_;
goto v___jp_1081_;
}
v___jp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1083_);
v___x_1085_ = v___x_1079_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_userData_1069_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_state_1071_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_knownSize_1072_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_messageHead_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 5, v_userDataBytes_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*6, v_sentMessage_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*6 + 1, v_userClosedBody_1075_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*6 + 2, v_omitBody_1076_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___y_1082_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1110_, lean_object* v_writer_1111_){
_start:
{
uint8_t v_dir_boxed_1112_; lean_object* v_res_1113_; 
v_dir_boxed_1112_ = lean_unbox(v_dir_1110_);
v_res_1113_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1112_, v_writer_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1114_, lean_object* v_writer_1115_){
_start:
{
lean_object* v_userData_1116_; lean_object* v_outputData_1117_; lean_object* v_knownSize_1118_; lean_object* v_messageHead_1119_; uint8_t v_sentMessage_1120_; uint8_t v_userClosedBody_1121_; uint8_t v_omitBody_1122_; lean_object* v_userDataBytes_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_userData_1116_ = lean_ctor_get(v_writer_1115_, 0);
v_outputData_1117_ = lean_ctor_get(v_writer_1115_, 1);
v_knownSize_1118_ = lean_ctor_get(v_writer_1115_, 3);
v_messageHead_1119_ = lean_ctor_get(v_writer_1115_, 4);
v_sentMessage_1120_ = lean_ctor_get_uint8(v_writer_1115_, sizeof(void*)*6);
v_userClosedBody_1121_ = lean_ctor_get_uint8(v_writer_1115_, sizeof(void*)*6 + 1);
v_omitBody_1122_ = lean_ctor_get_uint8(v_writer_1115_, sizeof(void*)*6 + 2);
v_userDataBytes_1123_ = lean_ctor_get(v_writer_1115_, 5);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_writer_1115_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_writer_1115_, 2);
lean_dec(v_unused_1131_);
v___x_1125_ = v_writer_1115_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_userDataBytes_1123_);
lean_inc(v_messageHead_1119_);
lean_inc(v_knownSize_1118_);
lean_inc(v_outputData_1117_);
lean_inc(v_userData_1116_);
lean_dec(v_writer_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 2, v_state_1114_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_userData_1116_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_outputData_1117_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_state_1114_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_knownSize_1118_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v_messageHead_1119_);
lean_ctor_set(v_reuseFailAlloc_1129_, 5, v_userDataBytes_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*6, v_sentMessage_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*6 + 1, v_userClosedBody_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*6 + 2, v_omitBody_1122_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1132_, lean_object* v_state_1133_, lean_object* v_writer_1134_){
_start:
{
lean_object* v_userData_1135_; lean_object* v_outputData_1136_; lean_object* v_knownSize_1137_; lean_object* v_messageHead_1138_; uint8_t v_sentMessage_1139_; uint8_t v_userClosedBody_1140_; uint8_t v_omitBody_1141_; lean_object* v_userDataBytes_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_userData_1135_ = lean_ctor_get(v_writer_1134_, 0);
v_outputData_1136_ = lean_ctor_get(v_writer_1134_, 1);
v_knownSize_1137_ = lean_ctor_get(v_writer_1134_, 3);
v_messageHead_1138_ = lean_ctor_get(v_writer_1134_, 4);
v_sentMessage_1139_ = lean_ctor_get_uint8(v_writer_1134_, sizeof(void*)*6);
v_userClosedBody_1140_ = lean_ctor_get_uint8(v_writer_1134_, sizeof(void*)*6 + 1);
v_omitBody_1141_ = lean_ctor_get_uint8(v_writer_1134_, sizeof(void*)*6 + 2);
v_userDataBytes_1142_ = lean_ctor_get(v_writer_1134_, 5);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_writer_1134_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_writer_1134_, 2);
lean_dec(v_unused_1150_);
v___x_1144_ = v_writer_1134_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_userDataBytes_1142_);
lean_inc(v_messageHead_1138_);
lean_inc(v_knownSize_1137_);
lean_inc(v_outputData_1136_);
lean_inc(v_userData_1135_);
lean_dec(v_writer_1134_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 2, v_state_1133_);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_userData_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_outputData_1136_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_state_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_knownSize_1137_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_messageHead_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v_userDataBytes_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1148_, sizeof(void*)*6, v_sentMessage_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1148_, sizeof(void*)*6 + 1, v_userClosedBody_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1148_, sizeof(void*)*6 + 2, v_omitBody_1141_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1151_, lean_object* v_state_1152_, lean_object* v_writer_1153_){
_start:
{
uint8_t v_dir_boxed_1154_; lean_object* v_res_1155_; 
v_dir_boxed_1154_ = lean_unbox(v_dir_1151_);
v_res_1155_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1154_, v_state_1152_, v_writer_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1156_, lean_object* v_messageHead_1157_, lean_object* v_writer_1158_){
_start:
{
lean_object* v_userData_1159_; lean_object* v_outputData_1160_; lean_object* v_state_1161_; lean_object* v_knownSize_1162_; lean_object* v_messageHead_1163_; uint8_t v_sentMessage_1164_; uint8_t v_userClosedBody_1165_; uint8_t v_omitBody_1166_; lean_object* v_userDataBytes_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1180_; 
v_userData_1159_ = lean_ctor_get(v_writer_1158_, 0);
v_outputData_1160_ = lean_ctor_get(v_writer_1158_, 1);
v_state_1161_ = lean_ctor_get(v_writer_1158_, 2);
v_knownSize_1162_ = lean_ctor_get(v_writer_1158_, 3);
v_messageHead_1163_ = lean_ctor_get(v_writer_1158_, 4);
v_sentMessage_1164_ = lean_ctor_get_uint8(v_writer_1158_, sizeof(void*)*6);
v_userClosedBody_1165_ = lean_ctor_get_uint8(v_writer_1158_, sizeof(void*)*6 + 1);
v_omitBody_1166_ = lean_ctor_get_uint8(v_writer_1158_, sizeof(void*)*6 + 2);
v_userDataBytes_1167_ = lean_ctor_get(v_writer_1158_, 5);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_writer_1158_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1169_ = v_writer_1158_;
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_userDataBytes_1167_);
lean_inc(v_messageHead_1163_);
lean_inc(v_knownSize_1162_);
lean_inc(v_state_1161_);
lean_inc(v_outputData_1160_);
lean_inc(v_userData_1159_);
lean_dec(v_writer_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v___y_1172_; 
if (v_dir_1156_ == 0)
{
uint8_t v___x_1178_; 
v___x_1178_ = 1;
v___y_1172_ = v___x_1178_;
goto v___jp_1171_;
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = 0;
v___y_1172_ = v___x_1179_;
goto v___jp_1171_;
}
v___jp_1171_:
{
lean_object* v___x_6__overap_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_6__overap_1173_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1172_);
v___x_1174_ = lean_apply_2(v___x_6__overap_1173_, v_outputData_1160_, v_messageHead_1157_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1174_);
v___x_1176_ = v___x_1169_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_userData_1159_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_state_1161_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_knownSize_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_messageHead_1163_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_userDataBytes_1167_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*6, v_sentMessage_1164_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*6 + 1, v_userClosedBody_1165_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*6 + 2, v_omitBody_1166_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1181_, lean_object* v_messageHead_1182_, lean_object* v_writer_1183_){
_start:
{
uint8_t v_dir_boxed_1184_; lean_object* v_res_1185_; 
v_dir_boxed_1184_ = lean_unbox(v_dir_1181_);
v_res_1185_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1184_, v_messageHead_1182_, v_writer_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v_key_1188_; lean_object* v_value_1189_; lean_object* v_tail_1190_; uint8_t v___x_1191_; 
v_key_1188_ = lean_ctor_get(v_x_1187_, 0);
v_value_1189_ = lean_ctor_get(v_x_1187_, 1);
v_tail_1190_ = lean_ctor_get(v_x_1187_, 2);
v___x_1191_ = lean_string_dec_eq(v_key_1188_, v_a_1186_);
if (v___x_1191_ == 0)
{
v_x_1187_ = v_tail_1190_;
goto _start;
}
else
{
lean_inc(v_value_1189_);
return v_value_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1193_, v_x_1194_);
lean_dec(v_x_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_buckets_1198_; lean_object* v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v_fold_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_buckets_1198_ = lean_ctor_get(v_m_1196_, 1);
v___x_1199_ = lean_array_get_size(v_buckets_1198_);
v___x_1200_ = lean_string_hash(v_a_1197_);
v___x_1201_ = 32ULL;
v___x_1202_ = lean_uint64_shift_right(v___x_1200_, v___x_1201_);
v_fold_1203_ = lean_uint64_xor(v___x_1200_, v___x_1202_);
v___x_1204_ = 16ULL;
v___x_1205_ = lean_uint64_shift_right(v_fold_1203_, v___x_1204_);
v___x_1206_ = lean_uint64_xor(v_fold_1203_, v___x_1205_);
v___x_1207_ = lean_uint64_to_usize(v___x_1206_);
v___x_1208_ = lean_usize_of_nat(v___x_1199_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_sub(v___x_1208_, v___x_1209_);
v___x_1211_ = lean_usize_land(v___x_1207_, v___x_1210_);
v___x_1212_ = lean_array_uget_borrowed(v_buckets_1198_, v___x_1211_);
v___x_1213_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1197_, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1214_, v_a_1215_);
lean_dec_ref(v_a_1215_);
lean_dec_ref(v_m_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_s_1217_, lean_object* v_p_1218_){
_start:
{
uint32_t v___y_1220_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_string_utf8_byte_size(v_s_1217_);
v___x_1226_ = lean_nat_dec_eq(v_p_1218_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint32_t v___x_1227_; uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = lean_string_utf8_get_fast(v_s_1217_, v_p_1218_);
v___x_1228_ = 65;
v___x_1229_ = lean_uint32_dec_le(v___x_1228_, v___x_1227_);
if (v___x_1229_ == 0)
{
v___y_1220_ = v___x_1227_;
goto v___jp_1219_;
}
else
{
uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 90;
v___x_1231_ = lean_uint32_dec_le(v___x_1227_, v___x_1230_);
if (v___x_1231_ == 0)
{
v___y_1220_ = v___x_1227_;
goto v___jp_1219_;
}
else
{
uint32_t v___x_1232_; uint32_t v___x_1233_; 
v___x_1232_ = 32;
v___x_1233_ = lean_uint32_add(v___x_1227_, v___x_1232_);
v___y_1220_ = v___x_1233_;
goto v___jp_1219_;
}
}
}
else
{
lean_dec(v_p_1218_);
return v_s_1217_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_inc(v_p_1218_);
v___x_1221_ = lean_string_utf8_set(v_s_1217_, v_p_1218_, v___y_1220_);
v___x_1222_ = l_Char_utf8Size(v___y_1220_);
v___x_1223_ = lean_nat_add(v_p_1218_, v___x_1222_);
lean_dec(v___x_1222_);
lean_dec(v_p_1218_);
v_s_1217_ = v___x_1221_;
v_p_1218_ = v___x_1223_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1237_, lean_object* v_writer_1238_){
_start:
{
uint8_t v___y_1240_; 
if (v_dir_1237_ == 0)
{
uint8_t v___x_1259_; 
v___x_1259_ = 1;
v___y_1240_ = v___x_1259_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = 0;
v___y_1240_ = v___x_1260_;
goto v___jp_1239_;
}
v___jp_1239_:
{
lean_object* v_messageHead_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; uint8_t v___x_1246_; 
v_messageHead_1241_ = lean_ctor_get(v_writer_1238_, 4);
v___x_1242_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1240_, v_messageHead_1241_);
v___x_1243_ = l_Std_Http_Header_Name_connection;
v___f_1244_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___f_1245_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1));
v___x_1246_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1244_, v___f_1245_, v___x_1243_, v___x_1242_);
if (v___x_1246_ == 0)
{
uint8_t v___x_1247_; 
lean_dec_ref(v___x_1242_);
v___x_1247_ = 1;
return v___x_1247_;
}
else
{
lean_object* v_entries_1248_; lean_object* v_indexes_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_entry_1252_; lean_object* v___x_1253_; lean_object* v_snd_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_entries_1248_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_entries_1248_);
v_indexes_1249_ = lean_ctor_get(v___x_1242_, 1);
lean_inc_ref(v_indexes_1249_);
lean_dec_ref(v___x_1242_);
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1249_, v___x_1243_);
lean_dec_ref(v_indexes_1249_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v_entry_1252_ = lean_array_fget(v___x_1250_, v___x_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_array_fget(v_entries_1248_, v_entry_1252_);
lean_dec(v_entry_1252_);
lean_dec_ref(v_entries_1248_);
v_snd_1254_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_snd_1254_);
lean_dec(v___x_1253_);
v___x_1255_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_snd_1254_, v___x_1251_);
v___x_1256_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2));
v___x_1257_ = lean_string_dec_eq(v___x_1255_, v___x_1256_);
lean_dec_ref(v___x_1255_);
if (v___x_1257_ == 0)
{
return v___x_1246_;
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = 0;
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1261_, lean_object* v_writer_1262_){
_start:
{
uint8_t v_dir_boxed_1263_; uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_dir_boxed_1263_ = lean_unbox(v_dir_1261_);
v_res_1264_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1263_, v_writer_1262_);
lean_dec_ref(v_writer_1262_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1266_, lean_object* v_m_1267_, lean_object* v_a_1268_, lean_object* v_hma_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1267_, v_a_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1271_, lean_object* v_m_1272_, lean_object* v_a_1273_, lean_object* v_hma_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1271_, v_m_1272_, v_a_1273_, v_hma_1274_);
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_m_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1276_, lean_object* v_a_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1277_, v_x_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1281_, lean_object* v_a_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1281_, v_a_1282_, v_x_1283_, v_x_1284_);
lean_dec(v_x_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1286_){
_start:
{
lean_object* v_userData_1287_; lean_object* v_outputData_1288_; lean_object* v_knownSize_1289_; lean_object* v_messageHead_1290_; uint8_t v_sentMessage_1291_; uint8_t v_userClosedBody_1292_; uint8_t v_omitBody_1293_; lean_object* v_userDataBytes_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_userData_1287_ = lean_ctor_get(v_writer_1286_, 0);
v_outputData_1288_ = lean_ctor_get(v_writer_1286_, 1);
v_knownSize_1289_ = lean_ctor_get(v_writer_1286_, 3);
v_messageHead_1290_ = lean_ctor_get(v_writer_1286_, 4);
v_sentMessage_1291_ = lean_ctor_get_uint8(v_writer_1286_, sizeof(void*)*6);
v_userClosedBody_1292_ = lean_ctor_get_uint8(v_writer_1286_, sizeof(void*)*6 + 1);
v_omitBody_1293_ = lean_ctor_get_uint8(v_writer_1286_, sizeof(void*)*6 + 2);
v_userDataBytes_1294_ = lean_ctor_get(v_writer_1286_, 5);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_writer_1286_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_writer_1286_, 2);
lean_dec(v_unused_1303_);
v___x_1296_ = v_writer_1286_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_userDataBytes_1294_);
lean_inc(v_messageHead_1290_);
lean_inc(v_knownSize_1289_);
lean_inc(v_outputData_1288_);
lean_inc(v_userData_1287_);
lean_dec(v_writer_1286_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_box(7);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 2, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_userData_1287_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_outputData_1288_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v_knownSize_1289_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v_messageHead_1290_);
lean_ctor_set(v_reuseFailAlloc_1301_, 5, v_userDataBytes_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*6, v_sentMessage_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*6 + 1, v_userClosedBody_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*6 + 2, v_omitBody_1293_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1304_, lean_object* v_writer_1305_){
_start:
{
lean_object* v_userData_1306_; lean_object* v_outputData_1307_; lean_object* v_knownSize_1308_; lean_object* v_messageHead_1309_; uint8_t v_sentMessage_1310_; uint8_t v_userClosedBody_1311_; uint8_t v_omitBody_1312_; lean_object* v_userDataBytes_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
v_userData_1306_ = lean_ctor_get(v_writer_1305_, 0);
v_outputData_1307_ = lean_ctor_get(v_writer_1305_, 1);
v_knownSize_1308_ = lean_ctor_get(v_writer_1305_, 3);
v_messageHead_1309_ = lean_ctor_get(v_writer_1305_, 4);
v_sentMessage_1310_ = lean_ctor_get_uint8(v_writer_1305_, sizeof(void*)*6);
v_userClosedBody_1311_ = lean_ctor_get_uint8(v_writer_1305_, sizeof(void*)*6 + 1);
v_omitBody_1312_ = lean_ctor_get_uint8(v_writer_1305_, sizeof(void*)*6 + 2);
v_userDataBytes_1313_ = lean_ctor_get(v_writer_1305_, 5);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_writer_1305_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_writer_1305_, 2);
lean_dec(v_unused_1322_);
v___x_1315_ = v_writer_1305_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_userDataBytes_1313_);
lean_inc(v_messageHead_1309_);
lean_inc(v_knownSize_1308_);
lean_inc(v_outputData_1307_);
lean_inc(v_userData_1306_);
lean_dec(v_writer_1305_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_box(7);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 2, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_userData_1306_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_outputData_1307_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_knownSize_1308_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_messageHead_1309_);
lean_ctor_set(v_reuseFailAlloc_1320_, 5, v_userDataBytes_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*6, v_sentMessage_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*6 + 1, v_userClosedBody_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*6 + 2, v_omitBody_1312_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1323_, lean_object* v_writer_1324_){
_start:
{
uint8_t v_dir_boxed_1325_; lean_object* v_res_1326_; 
v_dir_boxed_1325_ = lean_unbox(v_dir_1323_);
v_res_1326_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1325_, v_writer_1324_);
return v_res_1326_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
