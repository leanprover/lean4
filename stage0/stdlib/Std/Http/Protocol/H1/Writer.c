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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_state_310_; 
v_state_310_ = lean_ctor_get(v_writer_309_, 2);
switch(lean_obj_tag(v_state_310_))
{
case 1:
{
uint8_t v___x_311_; 
v___x_311_ = 1;
return v___x_311_;
}
case 2:
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
case 3:
{
uint8_t v_userClosedBody_313_; uint8_t v___x_314_; 
v_userClosedBody_313_ = lean_ctor_get_uint8(v_writer_309_, sizeof(void*)*6 + 1);
v___x_314_ = lean_bool_not(v_userClosedBody_313_);
return v___x_314_;
}
case 4:
{
uint8_t v_userClosedBody_315_; uint8_t v___x_316_; 
v_userClosedBody_315_ = lean_ctor_get_uint8(v_writer_309_, sizeof(void*)*6 + 1);
v___x_316_ = lean_bool_not(v_userClosedBody_315_);
return v___x_316_;
}
case 5:
{
uint8_t v_userClosedBody_317_; uint8_t v___x_318_; 
v_userClosedBody_317_ = lean_ctor_get_uint8(v_writer_309_, sizeof(void*)*6 + 1);
v___x_318_ = lean_bool_not(v_userClosedBody_317_);
return v___x_318_;
}
default: 
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
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
lean_object* v_state_325_; 
v_state_325_ = lean_ctor_get(v_writer_324_, 2);
switch(lean_obj_tag(v_state_325_))
{
case 1:
{
uint8_t v___x_326_; 
v___x_326_ = 1;
return v___x_326_;
}
case 2:
{
uint8_t v___x_327_; 
v___x_327_ = 1;
return v___x_327_;
}
case 3:
{
uint8_t v_userClosedBody_328_; uint8_t v___x_329_; 
v_userClosedBody_328_ = lean_ctor_get_uint8(v_writer_324_, sizeof(void*)*6 + 1);
v___x_329_ = lean_bool_not(v_userClosedBody_328_);
return v___x_329_;
}
case 4:
{
uint8_t v_userClosedBody_330_; uint8_t v___x_331_; 
v_userClosedBody_330_ = lean_ctor_get_uint8(v_writer_324_, sizeof(void*)*6 + 1);
v___x_331_ = lean_bool_not(v_userClosedBody_330_);
return v___x_331_;
}
case 5:
{
uint8_t v_userClosedBody_332_; uint8_t v___x_333_; 
v_userClosedBody_332_ = lean_ctor_get_uint8(v_writer_324_, sizeof(void*)*6 + 1);
v___x_333_ = lean_bool_not(v_userClosedBody_332_);
return v___x_333_;
}
default: 
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
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
lean_object* v_userData_425_; lean_object* v_outputData_426_; lean_object* v_state_427_; lean_object* v_knownSize_428_; lean_object* v_messageHead_429_; uint8_t v_sentMessage_430_; uint8_t v_userClosedBody_431_; uint8_t v_omitBody_432_; lean_object* v_userDataBytes_433_; lean_object* v___y_435_; lean_object* v___f_439_; uint8_t v___y_453_; 
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
uint8_t v___x_456_; 
v___x_456_ = lean_bool_not(v_userClosedBody_431_);
v___y_453_ = v___x_456_;
goto v___jp_452_;
}
case 4:
{
goto v___jp_454_;
}
case 5:
{
goto v___jp_454_;
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
if (v___y_453_ == 0)
{
lean_dec_ref(v_data_423_);
return v_writer_424_;
}
else
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
}
v___jp_454_:
{
uint8_t v___x_455_; 
v___x_455_ = lean_bool_not(v_userClosedBody_431_);
v___y_453_ = v___x_455_;
goto v___jp_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_457_, lean_object* v_data_458_, lean_object* v_writer_459_){
_start:
{
lean_object* v_userData_460_; lean_object* v_outputData_461_; lean_object* v_state_462_; lean_object* v_knownSize_463_; lean_object* v_messageHead_464_; uint8_t v_sentMessage_465_; uint8_t v_userClosedBody_466_; uint8_t v_omitBody_467_; lean_object* v_userDataBytes_468_; lean_object* v___y_470_; lean_object* v___f_474_; uint8_t v___y_488_; 
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
uint8_t v___x_491_; 
v___x_491_ = lean_bool_not(v_userClosedBody_466_);
v___y_488_ = v___x_491_;
goto v___jp_487_;
}
case 4:
{
goto v___jp_489_;
}
case 5:
{
goto v___jp_489_;
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
if (v___y_488_ == 0)
{
lean_dec_ref(v_data_458_);
return v_writer_459_;
}
else
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
}
v___jp_489_:
{
uint8_t v___x_490_; 
v___x_490_ = lean_bool_not(v_userClosedBody_466_);
v___y_488_ = v___x_490_;
goto v___jp_487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object* v_dir_492_, lean_object* v_data_493_, lean_object* v_writer_494_){
_start:
{
uint8_t v_dir_boxed_495_; lean_object* v_res_496_; 
v_dir_boxed_495_ = lean_unbox(v_dir_492_);
v_res_496_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_495_, v_data_493_, v_writer_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object* v_limitSize_497_, lean_object* v_as_498_, size_t v_i_499_, size_t v_stop_500_, lean_object* v_b_501_){
_start:
{
lean_object* v___y_503_; uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_eq(v_i_499_, v_stop_500_);
if (v___x_507_ == 0)
{
lean_object* v_snd_508_; lean_object* v_fst_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_565_; 
v_snd_508_ = lean_ctor_get(v_b_501_, 1);
v_fst_509_ = lean_ctor_get(v_b_501_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_b_501_);
if (v_isSharedCheck_565_ == 0)
{
v___x_511_ = v_b_501_;
v_isShared_512_ = v_isSharedCheck_565_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_508_);
lean_inc(v_fst_509_);
lean_dec(v_b_501_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_565_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_564_; 
v_fst_513_ = lean_ctor_get(v_snd_508_, 0);
v_snd_514_ = lean_ctor_get(v_snd_508_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_snd_508_);
if (v_isSharedCheck_564_ == 0)
{
v___x_516_ = v_snd_508_;
v_isShared_517_ = v_isSharedCheck_564_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_inc(v_fst_513_);
lean_dec(v_snd_508_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_564_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_uget(v_as_498_, v_i_499_);
v___x_519_ = lean_nat_dec_le(v_limitSize_497_, v_snd_514_);
if (v___x_519_ == 0)
{
lean_object* v_data_520_; lean_object* v_extensions_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_556_; 
v_data_520_ = lean_ctor_get(v___x_518_, 0);
v_extensions_521_ = lean_ctor_get(v___x_518_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_556_ == 0)
{
v___x_523_ = v___x_518_;
v_isShared_524_ = v_isSharedCheck_556_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_extensions_521_);
lean_inc(v_data_520_);
lean_dec(v___x_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_556_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v_remaining_526_; lean_object* v___x_527_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_551_; uint8_t v___x_555_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v_remaining_526_ = lean_nat_sub(v_limitSize_497_, v_snd_514_);
v___x_527_ = lean_byte_array_size(v_data_520_);
v___x_555_ = lean_nat_dec_le(v___x_527_, v_remaining_526_);
if (v___x_555_ == 0)
{
v___y_551_ = v_remaining_526_;
goto v___jp_550_;
}
else
{
lean_dec(v_remaining_526_);
v___y_551_ = v___x_527_;
goto v___jp_550_;
}
v___jp_528_:
{
lean_object* v_size_531_; uint8_t v___x_532_; 
v_size_531_ = lean_nat_add(v_snd_514_, v___y_529_);
lean_dec(v_snd_514_);
v___x_532_ = lean_nat_dec_lt(v___y_529_, v___x_527_);
if (v___x_532_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v___y_529_);
lean_del_object(v___x_523_);
lean_dec_ref(v_extensions_521_);
lean_dec_ref(v_data_520_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_size_531_);
v___x_534_ = v___x_516_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_fst_513_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_size_531_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_534_);
lean_ctor_set(v___x_511_, 0, v___y_530_);
v___x_536_ = v___x_511_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___y_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v___y_503_ = v___x_536_;
goto v___jp_502_;
}
}
}
else
{
lean_object* v___x_539_; lean_object* v_pendingChunk_541_; 
v___x_539_ = l_ByteArray_extract(v_data_520_, v___y_529_, v___x_527_);
lean_dec_ref(v_data_520_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_539_);
v_pendingChunk_541_ = v___x_523_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_extensions_521_);
v_pendingChunk_541_ = v_reuseFailAlloc_549_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_array_push(v_fst_513_, v_pendingChunk_541_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_size_531_);
lean_ctor_set(v___x_516_, 0, v___x_542_);
v___x_544_ = v___x_516_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_size_531_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_544_);
lean_ctor_set(v___x_511_, 0, v___y_530_);
v___x_546_ = v___x_511_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___y_530_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v___y_503_ = v___x_546_;
goto v___jp_502_;
}
}
}
}
}
v___jp_550_:
{
uint8_t v___x_552_; 
v___x_552_ = lean_nat_dec_eq(v___y_551_, v___x_525_);
if (v___x_552_ == 0)
{
lean_object* v_dataPart_553_; lean_object* v___x_554_; 
v_dataPart_553_ = l_ByteArray_extract(v_data_520_, v___x_525_, v___y_551_);
v___x_554_ = lean_array_push(v_fst_509_, v_dataPart_553_);
v___y_529_ = v___y_551_;
v___y_530_ = v___x_554_;
goto v___jp_528_;
}
else
{
v___y_529_ = v___y_551_;
v___y_530_ = v_fst_509_;
goto v___jp_528_;
}
}
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_array_push(v_fst_513_, v___x_518_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_557_);
v___x_559_ = v___x_516_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_snd_514_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_559_);
v___x_561_ = v___x_511_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fst_509_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_503_ = v___x_561_;
goto v___jp_502_;
}
}
}
}
}
}
else
{
return v_b_501_;
}
v___jp_502_:
{
size_t v___x_504_; size_t v___x_505_; 
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_499_, v___x_504_);
v_i_499_ = v___x_505_;
v_b_501_ = v___y_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_566_, lean_object* v_as_567_, lean_object* v_i_568_, lean_object* v_stop_569_, lean_object* v_b_570_){
_start:
{
size_t v_i_boxed_571_; size_t v_stop_boxed_572_; lean_object* v_res_573_; 
v_i_boxed_571_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_stop_boxed_572_ = lean_unbox_usize(v_stop_569_);
lean_dec(v_stop_569_);
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_566_, v_as_567_, v_i_boxed_571_, v_stop_boxed_572_, v_b_570_);
lean_dec_ref(v_as_567_);
lean_dec(v_limitSize_566_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_, lean_object* v_b_577_){
_start:
{
uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; 
v___x_579_ = lean_array_uget_borrowed(v_as_574_, v_i_575_);
v___x_580_ = lean_byte_array_size(v___x_579_);
v___x_581_ = lean_nat_add(v_b_577_, v___x_580_);
lean_dec(v_b_577_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_575_, v___x_582_);
v_i_575_ = v___x_583_;
v_b_577_ = v___x_581_;
goto _start;
}
else
{
return v_b_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_585_, lean_object* v_i_586_, lean_object* v_stop_587_, lean_object* v_b_588_){
_start:
{
size_t v_i_boxed_589_; size_t v_stop_boxed_590_; lean_object* v_res_591_; 
v_i_boxed_589_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_stop_boxed_590_ = lean_unbox_usize(v_stop_587_);
lean_dec(v_stop_587_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_585_, v_i_boxed_589_, v_stop_boxed_590_, v_b_588_);
lean_dec_ref(v_as_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_600_, lean_object* v_limitSize_601_){
_start:
{
lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; uint8_t v___y_607_; uint8_t v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v_userData_637_; lean_object* v_outputData_638_; lean_object* v_state_639_; lean_object* v_knownSize_640_; lean_object* v_messageHead_641_; uint8_t v_sentMessage_642_; uint8_t v_userClosedBody_643_; uint8_t v_omitBody_644_; lean_object* v_userDataBytes_645_; lean_object* v_fst_647_; lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v___y_665_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_userData_637_ = lean_ctor_get(v_writer_600_, 0);
v_outputData_638_ = lean_ctor_get(v_writer_600_, 1);
v_state_639_ = lean_ctor_get(v_writer_600_, 2);
v_knownSize_640_ = lean_ctor_get(v_writer_600_, 3);
v_messageHead_641_ = lean_ctor_get(v_writer_600_, 4);
v_sentMessage_642_ = lean_ctor_get_uint8(v_writer_600_, sizeof(void*)*6);
v_userClosedBody_643_ = lean_ctor_get_uint8(v_writer_600_, sizeof(void*)*6 + 1);
v_omitBody_644_ = lean_ctor_get_uint8(v_writer_600_, sizeof(void*)*6 + 2);
v_userDataBytes_645_ = lean_ctor_get(v_writer_600_, 5);
v___x_670_ = lean_array_get_size(v_userData_637_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_nat_dec_eq(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; uint8_t v___x_674_; 
lean_inc(v_userDataBytes_645_);
lean_inc(v_messageHead_641_);
lean_inc(v_knownSize_640_);
lean_inc(v_state_639_);
lean_inc_ref(v_outputData_638_);
lean_inc_ref(v_userData_637_);
lean_dec_ref(v_writer_600_);
v___x_673_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_674_ = lean_nat_dec_lt(v___x_671_, v___x_670_);
if (v___x_674_ == 0)
{
lean_dec_ref(v_userData_637_);
v_fst_647_ = v___x_673_;
v_fst_648_ = v___x_673_;
v_snd_649_ = v___x_671_;
goto v___jp_646_;
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_676_ = lean_nat_dec_le(v___x_670_, v___x_670_);
if (v___x_676_ == 0)
{
if (v___x_674_ == 0)
{
lean_dec_ref(v_userData_637_);
v_fst_647_ = v___x_673_;
v_fst_648_ = v___x_673_;
v_snd_649_ = v___x_671_;
goto v___jp_646_;
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_670_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_601_, v_userData_637_, v___x_677_, v___x_678_, v___x_675_);
lean_dec_ref(v_userData_637_);
v___y_665_ = v___x_679_;
goto v___jp_664_;
}
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_670_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_601_, v_userData_637_, v___x_680_, v___x_681_, v___x_675_);
lean_dec_ref(v_userData_637_);
v___y_665_ = v___x_682_;
goto v___jp_664_;
}
}
}
else
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_writer_600_);
lean_ctor_set(v___x_683_, 1, v_limitSize_601_);
return v___x_683_;
}
v___jp_602_:
{
lean_object* v_data_614_; lean_object* v_size_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_636_; 
v_data_614_ = lean_ctor_get(v___y_610_, 0);
v_size_615_ = lean_ctor_get(v___y_610_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v___y_610_);
if (v_isSharedCheck_636_ == 0)
{
v___x_617_ = v___y_610_;
v_isShared_618_ = v_isSharedCheck_636_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_size_615_);
lean_inc(v_data_614_);
lean_dec(v___y_610_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_636_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_data_619_; lean_object* v_size_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_635_; 
v_data_619_ = lean_ctor_get(v___y_613_, 0);
v_size_620_ = lean_ctor_get(v___y_613_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_613_);
if (v_isSharedCheck_635_ == 0)
{
v___x_622_ = v___y_613_;
v_isShared_623_ = v_isSharedCheck_635_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_size_620_);
lean_inc(v_data_619_);
lean_dec(v___y_613_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_635_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_outputData_627_; 
v___x_624_ = l_Array_append___redArg(v_data_614_, v_data_619_);
lean_dec_ref(v_data_619_);
v___x_625_ = lean_nat_add(v_size_615_, v_size_620_);
lean_dec(v_size_620_);
lean_dec(v_size_615_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_625_);
lean_ctor_set(v___x_622_, 0, v___x_624_);
v_outputData_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_625_);
v_outputData_627_ = v_reuseFailAlloc_634_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v_remaining_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v_remaining_628_ = lean_nat_sub(v_limitSize_601_, v___y_606_);
lean_dec(v_limitSize_601_);
v___x_629_ = lean_nat_sub(v___y_612_, v___y_606_);
lean_dec(v___y_606_);
lean_dec(v___y_612_);
v___x_630_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_630_, 0, v___y_609_);
lean_ctor_set(v___x_630_, 1, v_outputData_627_);
lean_ctor_set(v___x_630_, 2, v___y_603_);
lean_ctor_set(v___x_630_, 3, v___y_611_);
lean_ctor_set(v___x_630_, 4, v___y_605_);
lean_ctor_set(v___x_630_, 5, v___x_629_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*6, v___y_608_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*6 + 1, v___y_604_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*6 + 2, v___y_607_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v_remaining_628_);
lean_ctor_set(v___x_617_, 0, v___x_630_);
v___x_632_ = v___x_617_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_remaining_628_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
v___jp_646_:
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_array_get_size(v_fst_647_);
v___x_652_ = lean_nat_dec_lt(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_fst_647_);
lean_ctor_set(v___x_653_, 1, v___x_650_);
v___y_603_ = v_state_639_;
v___y_604_ = v_userClosedBody_643_;
v___y_605_ = v_messageHead_641_;
v___y_606_ = v_snd_649_;
v___y_607_ = v_omitBody_644_;
v___y_608_ = v_sentMessage_642_;
v___y_609_ = v_fst_648_;
v___y_610_ = v_outputData_638_;
v___y_611_ = v_knownSize_640_;
v___y_612_ = v_userDataBytes_645_;
v___y_613_ = v___x_653_;
goto v___jp_602_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_le(v___x_651_, v___x_651_);
if (v___x_654_ == 0)
{
if (v___x_652_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_fst_647_);
lean_ctor_set(v___x_655_, 1, v___x_650_);
v___y_603_ = v_state_639_;
v___y_604_ = v_userClosedBody_643_;
v___y_605_ = v_messageHead_641_;
v___y_606_ = v_snd_649_;
v___y_607_ = v_omitBody_644_;
v___y_608_ = v_sentMessage_642_;
v___y_609_ = v_fst_648_;
v___y_610_ = v_outputData_638_;
v___y_611_ = v_knownSize_640_;
v___y_612_ = v_userDataBytes_645_;
v___y_613_ = v___x_655_;
goto v___jp_602_;
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_651_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_647_, v___x_656_, v___x_657_, v___x_650_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_fst_647_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___y_603_ = v_state_639_;
v___y_604_ = v_userClosedBody_643_;
v___y_605_ = v_messageHead_641_;
v___y_606_ = v_snd_649_;
v___y_607_ = v_omitBody_644_;
v___y_608_ = v_sentMessage_642_;
v___y_609_ = v_fst_648_;
v___y_610_ = v_outputData_638_;
v___y_611_ = v_knownSize_640_;
v___y_612_ = v_userDataBytes_645_;
v___y_613_ = v___x_659_;
goto v___jp_602_;
}
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_651_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_647_, v___x_660_, v___x_661_, v___x_650_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_fst_647_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___y_603_ = v_state_639_;
v___y_604_ = v_userClosedBody_643_;
v___y_605_ = v_messageHead_641_;
v___y_606_ = v_snd_649_;
v___y_607_ = v_omitBody_644_;
v___y_608_ = v_sentMessage_642_;
v___y_609_ = v_fst_648_;
v___y_610_ = v_outputData_638_;
v___y_611_ = v_knownSize_640_;
v___y_612_ = v_userDataBytes_645_;
v___y_613_ = v___x_663_;
goto v___jp_602_;
}
}
}
v___jp_664_:
{
lean_object* v_snd_666_; lean_object* v_fst_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; 
v_snd_666_ = lean_ctor_get(v___y_665_, 1);
lean_inc(v_snd_666_);
v_fst_667_ = lean_ctor_get(v___y_665_, 0);
lean_inc(v_fst_667_);
lean_dec_ref(v___y_665_);
v_fst_668_ = lean_ctor_get(v_snd_666_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v_snd_666_, 1);
lean_inc(v_snd_669_);
lean_dec(v_snd_666_);
v_fst_647_ = v_fst_667_;
v_fst_648_ = v_fst_668_;
v_snd_649_ = v_snd_669_;
goto v___jp_646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_684_, lean_object* v_writer_685_, lean_object* v_limitSize_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_685_, v_limitSize_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_688_, lean_object* v_writer_689_, lean_object* v_limitSize_690_){
_start:
{
uint8_t v_dir_boxed_691_; lean_object* v_res_692_; 
v_dir_boxed_691_ = lean_unbox(v_dir_688_);
v_res_692_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_691_, v_writer_689_, v_limitSize_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_693_, size_t v_i_694_, size_t v_stop_695_, lean_object* v_b_696_){
_start:
{
lean_object* v___y_698_; uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_eq(v_i_694_, v_stop_695_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v_data_704_; uint8_t v___x_705_; uint8_t v___x_706_; 
v___x_703_ = lean_array_uget_borrowed(v_as_693_, v_i_694_);
v_data_704_ = lean_ctor_get(v___x_703_, 0);
v___x_705_ = l_ByteArray_isEmpty(v_data_704_);
v___x_706_ = lean_bool_not(v___x_705_);
if (v___x_706_ == 0)
{
v___y_698_ = v_b_696_;
goto v___jp_697_;
}
else
{
lean_object* v___x_707_; 
lean_inc(v___x_703_);
v___x_707_ = lean_array_push(v_b_696_, v___x_703_);
v___y_698_ = v___x_707_;
goto v___jp_697_;
}
}
else
{
return v_b_696_;
}
v___jp_697_:
{
size_t v___x_699_; size_t v___x_700_; 
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_i_694_, v___x_699_);
v_i_694_ = v___x_700_;
v_b_696_ = v___y_698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_708_, lean_object* v_i_709_, lean_object* v_stop_710_, lean_object* v_b_711_){
_start:
{
size_t v_i_boxed_712_; size_t v_stop_boxed_713_; lean_object* v_res_714_; 
v_i_boxed_712_ = lean_unbox_usize(v_i_709_);
lean_dec(v_i_709_);
v_stop_boxed_713_ = lean_unbox_usize(v_stop_710_);
lean_dec(v_stop_710_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_708_, v_i_boxed_712_, v_stop_boxed_713_, v_b_711_);
lean_dec_ref(v_as_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_715_, size_t v_i_716_, lean_object* v_bs_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_718_ == 0)
{
return v_bs_717_;
}
else
{
lean_object* v_v_719_; lean_object* v___x_720_; lean_object* v_bs_x27_721_; uint32_t v___x_722_; uint8_t v___x_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_v_719_ = lean_array_uget(v_bs_717_, v_i_716_);
v___x_720_ = lean_unsigned_to_nat(0u);
v_bs_x27_721_ = lean_array_uset(v_bs_717_, v_i_716_, v___x_720_);
v___x_722_ = lean_unbox_uint32(v_v_719_);
lean_dec(v_v_719_);
v___x_723_ = lean_uint32_to_uint8(v___x_722_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_716_, v___x_724_);
v___x_726_ = lean_box(v___x_723_);
v___x_727_ = lean_array_uset(v_bs_x27_721_, v_i_716_, v___x_726_);
v_i_716_ = v___x_725_;
v_bs_717_ = v___x_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_729_, lean_object* v_i_730_, lean_object* v_bs_731_){
_start:
{
size_t v_sz_boxed_732_; size_t v_i_boxed_733_; lean_object* v_res_734_; 
v_sz_boxed_732_ = lean_unbox_usize(v_sz_729_);
lean_dec(v_sz_729_);
v_i_boxed_733_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_732_, v_i_boxed_733_, v_bs_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_737_, size_t v_i_738_, size_t v_stop_739_, lean_object* v_b_740_){
_start:
{
lean_object* v___y_742_; uint8_t v___x_746_; 
v___x_746_ = lean_usize_dec_eq(v_i_738_, v_stop_739_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = lean_array_uget_borrowed(v_as_737_, v_i_738_);
v_fst_748_ = lean_ctor_get(v___x_747_, 0);
v_snd_749_ = lean_ctor_get(v___x_747_, 1);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_751_ = lean_string_append(v_b_740_, v___x_750_);
v___x_752_ = lean_string_append(v___x_751_, v_fst_748_);
if (lean_obj_tag(v_snd_749_) == 0)
{
v___y_742_ = v___x_752_;
goto v___jp_741_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_val_753_ = lean_ctor_get(v_snd_749_, 0);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_753_);
v___x_755_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_753_);
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
lean_dec_ref(v___x_755_);
v___x_757_ = lean_string_append(v___x_752_, v___x_756_);
lean_dec_ref(v___x_756_);
v___y_742_ = v___x_757_;
goto v___jp_741_;
}
}
else
{
return v_b_740_;
}
v___jp_741_:
{
size_t v___x_743_; size_t v___x_744_; 
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_add(v_i_738_, v___x_743_);
v_i_738_ = v___x_744_;
v_b_740_ = v___y_742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_758_, lean_object* v_i_759_, lean_object* v_stop_760_, lean_object* v_b_761_){
_start:
{
size_t v_i_boxed_762_; size_t v_stop_boxed_763_; lean_object* v_res_764_; 
v_i_boxed_762_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_stop_boxed_763_ = lean_unbox_usize(v_stop_760_);
lean_dec(v_stop_760_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_758_, v_i_boxed_762_, v_stop_boxed_763_, v_b_761_);
lean_dec_ref(v_as_758_);
return v_res_764_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_767_ = lean_string_to_utf8(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_769_, size_t v_i_770_, size_t v_stop_771_, lean_object* v_b_772_){
_start:
{
lean_object* v___y_774_; uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_eq(v_i_770_, v_stop_771_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v_data_793_; lean_object* v_extensions_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_848_; 
v___x_792_ = lean_array_uget(v_as_769_, v_i_770_);
v_data_793_ = lean_ctor_get(v___x_792_, 0);
v_extensions_794_ = lean_ctor_get(v___x_792_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_848_ == 0)
{
v___x_796_ = v___x_792_;
v_isShared_797_ = v_isSharedCheck_848_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_extensions_794_);
lean_inc(v_data_793_);
lean_dec(v___x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_848_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_chunkLen_798_; lean_object* v___y_800_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_chunkLen_798_ = lean_byte_array_size(v_data_793_);
v___x_837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_array_get_size(v_extensions_794_);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec_ref(v_extensions_794_);
v___y_800_ = v___x_837_;
goto v___jp_799_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_le(v___x_839_, v___x_839_);
if (v___x_841_ == 0)
{
if (v___x_840_ == 0)
{
lean_dec_ref(v_extensions_794_);
v___y_800_ = v___x_837_;
goto v___jp_799_;
}
else
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((size_t)0ULL);
v___x_843_ = lean_usize_of_nat(v___x_839_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_794_, v___x_842_, v___x_843_, v___x_837_);
lean_dec_ref(v_extensions_794_);
v___y_800_ = v___x_844_;
goto v___jp_799_;
}
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_839_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_794_, v___x_845_, v___x_846_, v___x_837_);
lean_dec_ref(v_extensions_794_);
v___y_800_ = v___x_847_;
goto v___jp_799_;
}
}
v___jp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v_size_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_801_ = lean_unsigned_to_nat(16u);
v___x_802_ = l_Nat_toDigits(v___x_801_, v_chunkLen_798_);
v___x_803_ = lean_array_mk(v___x_802_);
v_sz_804_ = lean_array_size(v___x_803_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_804_, v___x_805_, v___x_803_);
v_size_807_ = lean_byte_array_mk(v___x_806_);
v___x_808_ = lean_string_to_utf8(v___y_800_);
lean_dec_ref(v___y_800_);
v___x_809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_810_ = lean_unsigned_to_nat(5u);
v___x_811_ = lean_mk_empty_array_with_capacity(v___x_810_);
v___x_812_ = lean_array_push(v___x_811_, v_size_807_);
v___x_813_ = lean_array_push(v___x_812_, v___x_808_);
v___x_814_ = lean_array_push(v___x_813_, v___x_809_);
v___x_815_ = lean_array_push(v___x_814_, v_data_793_);
v___x_816_ = lean_array_push(v___x_815_, v___x_809_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_array_get_size(v___x_816_);
v___x_819_ = lean_nat_dec_lt(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_821_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_817_);
lean_ctor_set(v___x_796_, 0, v___x_816_);
v___x_821_ = v___x_796_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_817_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v___y_774_ = v___x_821_;
goto v___jp_773_;
}
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v___x_818_, v___x_818_);
if (v___x_823_ == 0)
{
if (v___x_819_ == 0)
{
lean_object* v___x_825_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_817_);
lean_ctor_set(v___x_796_, 0, v___x_816_);
v___x_825_ = v___x_796_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_817_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
v___y_774_ = v___x_825_;
goto v___jp_773_;
}
}
else
{
size_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_usize_of_nat(v___x_818_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_816_, v___x_805_, v___x_827_, v___x_817_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_828_);
lean_ctor_set(v___x_796_, 0, v___x_816_);
v___x_830_ = v___x_796_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v___y_774_ = v___x_830_;
goto v___jp_773_;
}
}
}
else
{
size_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = lean_usize_of_nat(v___x_818_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_816_, v___x_805_, v___x_832_, v___x_817_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_833_);
lean_ctor_set(v___x_796_, 0, v___x_816_);
v___x_835_ = v___x_796_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
v___y_774_ = v___x_835_;
goto v___jp_773_;
}
}
}
}
}
}
else
{
return v_b_772_;
}
v___jp_773_:
{
lean_object* v_data_775_; lean_object* v_size_776_; lean_object* v_data_777_; lean_object* v_size_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_790_; 
v_data_775_ = lean_ctor_get(v_b_772_, 0);
lean_inc_ref(v_data_775_);
v_size_776_ = lean_ctor_get(v_b_772_, 1);
lean_inc(v_size_776_);
lean_dec_ref(v_b_772_);
v_data_777_ = lean_ctor_get(v___y_774_, 0);
v_size_778_ = lean_ctor_get(v___y_774_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___y_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_780_ = v___y_774_;
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_size_778_);
lean_inc(v_data_777_);
lean_dec(v___y_774_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = l_Array_append___redArg(v_data_775_, v_data_777_);
lean_dec_ref(v_data_777_);
v___x_783_ = lean_nat_add(v_size_776_, v_size_778_);
lean_dec(v_size_778_);
lean_dec(v_size_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v___x_783_);
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
size_t v___x_786_; size_t v___x_787_; 
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_i_770_, v___x_786_);
v_i_770_ = v___x_787_;
v_b_772_ = v___x_785_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_849_, lean_object* v_i_850_, lean_object* v_stop_851_, lean_object* v_b_852_){
_start:
{
size_t v_i_boxed_853_; size_t v_stop_boxed_854_; lean_object* v_res_855_; 
v_i_boxed_853_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_stop_boxed_854_ = lean_unbox_usize(v_stop_851_);
lean_dec(v_stop_851_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_849_, v_i_boxed_853_, v_stop_boxed_854_, v_b_852_);
lean_dec_ref(v_as_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_858_){
_start:
{
lean_object* v_userData_859_; lean_object* v_outputData_860_; lean_object* v_state_861_; lean_object* v_knownSize_862_; lean_object* v_messageHead_863_; uint8_t v_sentMessage_864_; uint8_t v_userClosedBody_865_; uint8_t v_omitBody_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___y_870_; uint8_t v___x_885_; 
v_userData_859_ = lean_ctor_get(v_writer_858_, 0);
v_outputData_860_ = lean_ctor_get(v_writer_858_, 1);
v_state_861_ = lean_ctor_get(v_writer_858_, 2);
v_knownSize_862_ = lean_ctor_get(v_writer_858_, 3);
v_messageHead_863_ = lean_ctor_get(v_writer_858_, 4);
v_sentMessage_864_ = lean_ctor_get_uint8(v_writer_858_, sizeof(void*)*6);
v_userClosedBody_865_ = lean_ctor_get_uint8(v_writer_858_, sizeof(void*)*6 + 1);
v_omitBody_866_ = lean_ctor_get_uint8(v_writer_858_, sizeof(void*)*6 + 2);
v___x_867_ = lean_array_get_size(v_userData_859_);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_nat_dec_eq(v___x_867_, v___x_868_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; uint8_t v___x_887_; 
lean_inc(v_messageHead_863_);
lean_inc(v_knownSize_862_);
lean_inc(v_state_861_);
lean_inc_ref(v_outputData_860_);
lean_inc_ref(v_userData_859_);
lean_dec_ref(v_writer_858_);
v___x_886_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_887_ = lean_nat_dec_lt(v___x_868_, v___x_867_);
if (v___x_887_ == 0)
{
lean_dec_ref(v_userData_859_);
v___y_870_ = v___x_886_;
goto v___jp_869_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = lean_nat_dec_le(v___x_867_, v___x_867_);
if (v___x_888_ == 0)
{
if (v___x_887_ == 0)
{
lean_dec_ref(v_userData_859_);
v___y_870_ = v___x_886_;
goto v___jp_869_;
}
else
{
size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; 
v___x_889_ = ((size_t)0ULL);
v___x_890_ = lean_usize_of_nat(v___x_867_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_859_, v___x_889_, v___x_890_, v___x_886_);
lean_dec_ref(v_userData_859_);
v___y_870_ = v___x_891_;
goto v___jp_869_;
}
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_of_nat(v___x_867_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_859_, v___x_892_, v___x_893_, v___x_886_);
lean_dec_ref(v_userData_859_);
v___y_870_ = v___x_894_;
goto v___jp_869_;
}
}
}
else
{
return v_writer_858_;
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_872_ = lean_array_get_size(v___y_870_);
v___x_873_ = lean_nat_dec_lt(v___x_868_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v___y_870_);
v___x_874_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_874_, 0, v___x_871_);
lean_ctor_set(v___x_874_, 1, v_outputData_860_);
lean_ctor_set(v___x_874_, 2, v_state_861_);
lean_ctor_set(v___x_874_, 3, v_knownSize_862_);
lean_ctor_set(v___x_874_, 4, v_messageHead_863_);
lean_ctor_set(v___x_874_, 5, v___x_868_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*6, v_sentMessage_864_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*6 + 1, v_userClosedBody_865_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*6 + 2, v_omitBody_866_);
return v___x_874_;
}
else
{
uint8_t v___x_875_; 
v___x_875_ = lean_nat_dec_le(v___x_872_, v___x_872_);
if (v___x_875_ == 0)
{
if (v___x_873_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref(v___y_870_);
v___x_876_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_876_, 0, v___x_871_);
lean_ctor_set(v___x_876_, 1, v_outputData_860_);
lean_ctor_set(v___x_876_, 2, v_state_861_);
lean_ctor_set(v___x_876_, 3, v_knownSize_862_);
lean_ctor_set(v___x_876_, 4, v_messageHead_863_);
lean_ctor_set(v___x_876_, 5, v___x_868_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*6, v_sentMessage_864_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*6 + 1, v_userClosedBody_865_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*6 + 2, v_omitBody_866_);
return v___x_876_;
}
else
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_877_ = ((size_t)0ULL);
v___x_878_ = lean_usize_of_nat(v___x_872_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_870_, v___x_877_, v___x_878_, v_outputData_860_);
lean_dec_ref(v___y_870_);
v___x_880_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_880_, 0, v___x_871_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
lean_ctor_set(v___x_880_, 2, v_state_861_);
lean_ctor_set(v___x_880_, 3, v_knownSize_862_);
lean_ctor_set(v___x_880_, 4, v_messageHead_863_);
lean_ctor_set(v___x_880_, 5, v___x_868_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*6, v_sentMessage_864_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*6 + 1, v_userClosedBody_865_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*6 + 2, v_omitBody_866_);
return v___x_880_;
}
}
else
{
size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_881_ = ((size_t)0ULL);
v___x_882_ = lean_usize_of_nat(v___x_872_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_870_, v___x_881_, v___x_882_, v_outputData_860_);
lean_dec_ref(v___y_870_);
v___x_884_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_884_, 0, v___x_871_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_ctor_set(v___x_884_, 2, v_state_861_);
lean_ctor_set(v___x_884_, 3, v_knownSize_862_);
lean_ctor_set(v___x_884_, 4, v_messageHead_863_);
lean_ctor_set(v___x_884_, 5, v___x_868_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*6, v_sentMessage_864_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*6 + 1, v_userClosedBody_865_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*6 + 2, v_omitBody_866_);
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_895_, lean_object* v_writer_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_898_, lean_object* v_writer_899_){
_start:
{
uint8_t v_dir_boxed_900_; lean_object* v_res_901_; 
v_dir_boxed_900_ = lean_unbox(v_dir_898_);
v_res_901_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_900_, v_writer_899_);
return v_res_901_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_904_ = lean_string_to_utf8(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_906_ = lean_byte_array_size(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_907_){
_start:
{
lean_object* v_writer_908_; lean_object* v_outputData_909_; lean_object* v_userData_910_; lean_object* v_knownSize_911_; lean_object* v_messageHead_912_; uint8_t v_sentMessage_913_; uint8_t v_userClosedBody_914_; uint8_t v_omitBody_915_; lean_object* v_userDataBytes_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_937_; 
v_writer_908_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_907_);
v_outputData_909_ = lean_ctor_get(v_writer_908_, 1);
v_userData_910_ = lean_ctor_get(v_writer_908_, 0);
v_knownSize_911_ = lean_ctor_get(v_writer_908_, 3);
v_messageHead_912_ = lean_ctor_get(v_writer_908_, 4);
v_sentMessage_913_ = lean_ctor_get_uint8(v_writer_908_, sizeof(void*)*6);
v_userClosedBody_914_ = lean_ctor_get_uint8(v_writer_908_, sizeof(void*)*6 + 1);
v_omitBody_915_ = lean_ctor_get_uint8(v_writer_908_, sizeof(void*)*6 + 2);
v_userDataBytes_916_ = lean_ctor_get(v_writer_908_, 5);
v_isSharedCheck_937_ = !lean_is_exclusive(v_writer_908_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_writer_908_, 2);
lean_dec(v_unused_938_);
v___x_918_ = v_writer_908_;
v_isShared_919_ = v_isSharedCheck_937_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_userDataBytes_916_);
lean_inc(v_messageHead_912_);
lean_inc(v_knownSize_911_);
lean_inc(v_outputData_909_);
lean_inc(v_userData_910_);
lean_dec(v_writer_908_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_937_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_data_920_; lean_object* v_size_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_936_; 
v_data_920_ = lean_ctor_get(v_outputData_909_, 0);
v_size_921_ = lean_ctor_get(v_outputData_909_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_outputData_909_);
if (v_isSharedCheck_936_ == 0)
{
v___x_923_ = v_outputData_909_;
v_isShared_924_ = v_isSharedCheck_936_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_size_921_);
lean_inc(v_data_920_);
lean_dec(v_outputData_909_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_936_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_925_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_926_ = lean_array_push(v_data_920_, v___x_925_);
v___x_927_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_928_ = lean_nat_add(v_size_921_, v___x_927_);
lean_dec(v_size_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___x_928_);
lean_ctor_set(v___x_923_, 0, v___x_926_);
v___x_930_ = v___x_923_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_box(6);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 2, v___x_931_);
lean_ctor_set(v___x_918_, 1, v___x_930_);
v___x_933_ = v___x_918_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_userData_910_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_knownSize_911_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v_messageHead_912_);
lean_ctor_set(v_reuseFailAlloc_934_, 5, v_userDataBytes_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*6, v_sentMessage_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*6 + 1, v_userClosedBody_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*6 + 2, v_omitBody_915_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_939_, lean_object* v_writer_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_942_, lean_object* v_writer_943_){
_start:
{
uint8_t v_dir_boxed_944_; lean_object* v_res_945_; 
v_dir_boxed_944_ = lean_unbox(v_dir_942_);
v_res_945_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_944_, v_writer_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_946_, size_t v_i_947_, size_t v_stop_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_eq(v_i_947_, v_stop_948_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v_data_952_; lean_object* v_data_953_; lean_object* v_size_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_967_; 
v___x_951_ = lean_array_uget_borrowed(v_as_946_, v_i_947_);
v_data_952_ = lean_ctor_get(v___x_951_, 0);
v_data_953_ = lean_ctor_get(v_b_949_, 0);
v_size_954_ = lean_ctor_get(v_b_949_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_b_949_);
if (v_isSharedCheck_967_ == 0)
{
v___x_956_ = v_b_949_;
v_isShared_957_ = v_isSharedCheck_967_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_size_954_);
lean_inc(v_data_953_);
lean_dec(v_b_949_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_967_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_inc_ref(v_data_952_);
v___x_958_ = lean_array_push(v_data_953_, v_data_952_);
v___x_959_ = lean_byte_array_size(v_data_952_);
v___x_960_ = lean_nat_add(v_size_954_, v___x_959_);
lean_dec(v_size_954_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_960_);
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
size_t v___x_963_; size_t v___x_964_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_947_, v___x_963_);
v_i_947_ = v___x_964_;
v_b_949_ = v___x_962_;
goto _start;
}
}
}
else
{
return v_b_949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_stop_970_, lean_object* v_b_971_){
_start:
{
size_t v_i_boxed_972_; size_t v_stop_boxed_973_; lean_object* v_res_974_; 
v_i_boxed_972_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_973_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_968_, v_i_boxed_972_, v_stop_boxed_973_, v_b_971_);
lean_dec_ref(v_as_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_975_){
_start:
{
lean_object* v_userData_976_; lean_object* v_outputData_977_; lean_object* v_state_978_; lean_object* v_knownSize_979_; lean_object* v_messageHead_980_; uint8_t v_sentMessage_981_; uint8_t v_userClosedBody_982_; uint8_t v_omitBody_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1010_; 
v_userData_976_ = lean_ctor_get(v_writer_975_, 0);
v_outputData_977_ = lean_ctor_get(v_writer_975_, 1);
v_state_978_ = lean_ctor_get(v_writer_975_, 2);
v_knownSize_979_ = lean_ctor_get(v_writer_975_, 3);
v_messageHead_980_ = lean_ctor_get(v_writer_975_, 4);
v_sentMessage_981_ = lean_ctor_get_uint8(v_writer_975_, sizeof(void*)*6);
v_userClosedBody_982_ = lean_ctor_get_uint8(v_writer_975_, sizeof(void*)*6 + 1);
v_omitBody_983_ = lean_ctor_get_uint8(v_writer_975_, sizeof(void*)*6 + 2);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_writer_975_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_writer_975_, 5);
lean_dec(v_unused_1011_);
v___x_985_ = v_writer_975_;
v_isShared_986_ = v_isSharedCheck_1010_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_messageHead_980_);
lean_inc(v_knownSize_979_);
lean_inc(v_state_978_);
lean_inc(v_outputData_977_);
lean_inc(v_userData_976_);
lean_dec(v_writer_975_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1010_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_989_ = lean_array_get_size(v_userData_976_);
v___x_990_ = lean_nat_dec_lt(v___x_987_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_992_; 
lean_dec_ref(v_userData_976_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 5, v___x_987_);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_outputData_977_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_state_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_knownSize_979_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_messageHead_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 5, v___x_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_993_, sizeof(void*)*6, v_sentMessage_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_993_, sizeof(void*)*6 + 1, v_userClosedBody_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_993_, sizeof(void*)*6 + 2, v_omitBody_983_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_le(v___x_989_, v___x_989_);
if (v___x_994_ == 0)
{
if (v___x_990_ == 0)
{
lean_object* v___x_996_; 
lean_dec_ref(v_userData_976_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 5, v___x_987_);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_996_ = v___x_985_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_outputData_977_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_state_978_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_knownSize_979_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_messageHead_980_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v___x_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6, v_sentMessage_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6 + 1, v_userClosedBody_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6 + 2, v_omitBody_983_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_998_ = ((size_t)0ULL);
v___x_999_ = lean_usize_of_nat(v___x_989_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_976_, v___x_998_, v___x_999_, v_outputData_977_);
lean_dec_ref(v_userData_976_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 5, v___x_987_);
lean_ctor_set(v___x_985_, 1, v___x_1000_);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_1002_ = v___x_985_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_state_978_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_knownSize_979_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_messageHead_980_);
lean_ctor_set(v_reuseFailAlloc_1003_, 5, v___x_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_1003_, sizeof(void*)*6, v_sentMessage_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1003_, sizeof(void*)*6 + 1, v_userClosedBody_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1003_, sizeof(void*)*6 + 2, v_omitBody_983_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = lean_usize_of_nat(v___x_989_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_976_, v___x_1004_, v___x_1005_, v_outputData_977_);
lean_dec_ref(v_userData_976_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 5, v___x_987_);
lean_ctor_set(v___x_985_, 1, v___x_1006_);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_1008_ = v___x_985_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_state_978_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_knownSize_979_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_messageHead_980_);
lean_ctor_set(v_reuseFailAlloc_1009_, 5, v___x_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_1009_, sizeof(void*)*6, v_sentMessage_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1009_, sizeof(void*)*6 + 1, v_userClosedBody_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1009_, sizeof(void*)*6 + 2, v_omitBody_983_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_1012_, lean_object* v_writer_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_1015_, lean_object* v_writer_1016_){
_start:
{
uint8_t v_dir_boxed_1017_; lean_object* v_res_1018_; 
v_dir_boxed_1017_ = lean_unbox(v_dir_1015_);
v_res_1018_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_1017_, v_writer_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_1019_, lean_object* v_x1_1020_, lean_object* v_x2_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_byte_array_size(v_x1_1020_);
v___x_1024_ = lean_byte_array_size(v_x2_1021_);
v___x_1025_ = lean_byte_array_copy_slice(v_x2_1021_, v___x_1022_, v_x1_1020_, v___x_1023_, v___x_1024_, v___x_1019_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_1026_, lean_object* v_x1_1027_, lean_object* v_x2_1028_){
_start:
{
uint8_t v___x_120__boxed_1029_; lean_object* v_res_1030_; 
v___x_120__boxed_1029_ = lean_unbox(v___x_1026_);
v_res_1030_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_120__boxed_1029_, v_x1_1027_, v_x2_1028_);
lean_dec_ref(v_x2_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_1034_){
_start:
{
lean_object* v_userData_1035_; lean_object* v_outputData_1036_; lean_object* v_state_1037_; lean_object* v_knownSize_1038_; lean_object* v_messageHead_1039_; uint8_t v_sentMessage_1040_; uint8_t v_userClosedBody_1041_; uint8_t v_omitBody_1042_; lean_object* v_userDataBytes_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1075_; 
v_userData_1035_ = lean_ctor_get(v_writer_1034_, 0);
v_outputData_1036_ = lean_ctor_get(v_writer_1034_, 1);
v_state_1037_ = lean_ctor_get(v_writer_1034_, 2);
v_knownSize_1038_ = lean_ctor_get(v_writer_1034_, 3);
v_messageHead_1039_ = lean_ctor_get(v_writer_1034_, 4);
v_sentMessage_1040_ = lean_ctor_get_uint8(v_writer_1034_, sizeof(void*)*6);
v_userClosedBody_1041_ = lean_ctor_get_uint8(v_writer_1034_, sizeof(void*)*6 + 1);
v_omitBody_1042_ = lean_ctor_get_uint8(v_writer_1034_, sizeof(void*)*6 + 2);
v_userDataBytes_1043_ = lean_ctor_get(v_writer_1034_, 5);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_writer_1034_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1045_ = v_writer_1034_;
v_isShared_1046_ = v_isSharedCheck_1075_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_userDataBytes_1043_);
lean_inc(v_messageHead_1039_);
lean_inc(v_knownSize_1038_);
lean_inc(v_state_1037_);
lean_inc(v_outputData_1036_);
lean_inc(v_userData_1035_);
lean_dec(v_writer_1034_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1075_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___y_1048_; lean_object* v_data_1055_; lean_object* v_size_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_data_1055_ = lean_ctor_get(v_outputData_1036_, 0);
lean_inc_ref(v_data_1055_);
v_size_1056_ = lean_ctor_get(v_outputData_1036_, 1);
lean_inc(v_size_1056_);
lean_dec_ref(v_outputData_1036_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_array_get_size(v_data_1055_);
v___x_1059_ = lean_nat_dec_eq(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1060_ = lean_mk_empty_byte_array(v_size_1056_);
lean_dec(v_size_1056_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1058_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v_data_1055_);
v___y_1048_ = v___x_1060_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1064_; lean_object* v___f_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_box(v___x_1059_);
v___f_1065_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1065_, 0, v___x_1064_);
v___x_1066_ = lean_nat_dec_le(v___x_1058_, v___x_1058_);
if (v___x_1066_ == 0)
{
if (v___x_1063_ == 0)
{
lean_dec_ref(v___f_1065_);
lean_dec_ref(v_data_1055_);
v___y_1048_ = v___x_1060_;
goto v___jp_1047_;
}
else
{
size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = ((size_t)0ULL);
v___x_1068_ = lean_usize_of_nat(v___x_1058_);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1062_, v___f_1065_, v_data_1055_, v___x_1067_, v___x_1068_, v___x_1060_);
v___y_1048_ = v___x_1069_;
goto v___jp_1047_;
}
}
else
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = lean_usize_of_nat(v___x_1058_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1062_, v___f_1065_, v_data_1055_, v___x_1070_, v___x_1071_, v___x_1060_);
v___y_1048_ = v___x_1072_;
goto v___jp_1047_;
}
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_size_1056_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_array_fget(v_data_1055_, v___x_1073_);
lean_dec_ref(v_data_1055_);
v___y_1048_ = v___x_1074_;
goto v___jp_1047_;
}
v___jp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_userData_1035_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_state_1037_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_knownSize_1038_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_messageHead_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 5, v_userDataBytes_1043_);
lean_ctor_set_uint8(v_reuseFailAlloc_1054_, sizeof(void*)*6, v_sentMessage_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1054_, sizeof(void*)*6 + 1, v_userClosedBody_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1054_, sizeof(void*)*6 + 2, v_omitBody_1042_);
v___x_1051_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___y_1048_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1076_, lean_object* v_writer_1077_){
_start:
{
lean_object* v_userData_1078_; lean_object* v_outputData_1079_; lean_object* v_state_1080_; lean_object* v_knownSize_1081_; lean_object* v_messageHead_1082_; uint8_t v_sentMessage_1083_; uint8_t v_userClosedBody_1084_; uint8_t v_omitBody_1085_; lean_object* v_userDataBytes_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1118_; 
v_userData_1078_ = lean_ctor_get(v_writer_1077_, 0);
v_outputData_1079_ = lean_ctor_get(v_writer_1077_, 1);
v_state_1080_ = lean_ctor_get(v_writer_1077_, 2);
v_knownSize_1081_ = lean_ctor_get(v_writer_1077_, 3);
v_messageHead_1082_ = lean_ctor_get(v_writer_1077_, 4);
v_sentMessage_1083_ = lean_ctor_get_uint8(v_writer_1077_, sizeof(void*)*6);
v_userClosedBody_1084_ = lean_ctor_get_uint8(v_writer_1077_, sizeof(void*)*6 + 1);
v_omitBody_1085_ = lean_ctor_get_uint8(v_writer_1077_, sizeof(void*)*6 + 2);
v_userDataBytes_1086_ = lean_ctor_get(v_writer_1077_, 5);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_writer_1077_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1088_ = v_writer_1077_;
v_isShared_1089_ = v_isSharedCheck_1118_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_userDataBytes_1086_);
lean_inc(v_messageHead_1082_);
lean_inc(v_knownSize_1081_);
lean_inc(v_state_1080_);
lean_inc(v_outputData_1079_);
lean_inc(v_userData_1078_);
lean_dec(v_writer_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1118_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___y_1091_; lean_object* v_data_1098_; lean_object* v_size_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_data_1098_ = lean_ctor_get(v_outputData_1079_, 0);
lean_inc_ref(v_data_1098_);
v_size_1099_ = lean_ctor_get(v_outputData_1079_, 1);
lean_inc(v_size_1099_);
lean_dec_ref(v_outputData_1079_);
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = lean_array_get_size(v_data_1098_);
v___x_1102_ = lean_nat_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1103_ = lean_mk_empty_byte_array(v_size_1099_);
lean_dec(v_size_1099_);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1106_ = lean_nat_dec_lt(v___x_1104_, v___x_1101_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v_data_1098_);
v___y_1091_ = v___x_1103_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1107_; lean_object* v___f_1108_; uint8_t v___x_1109_; 
v___x_1107_ = lean_box(v___x_1102_);
v___f_1108_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1108_, 0, v___x_1107_);
v___x_1109_ = lean_nat_dec_le(v___x_1101_, v___x_1101_);
if (v___x_1109_ == 0)
{
if (v___x_1106_ == 0)
{
lean_dec_ref(v___f_1108_);
lean_dec_ref(v_data_1098_);
v___y_1091_ = v___x_1103_;
goto v___jp_1090_;
}
else
{
size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = lean_usize_of_nat(v___x_1101_);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1105_, v___f_1108_, v_data_1098_, v___x_1110_, v___x_1111_, v___x_1103_);
v___y_1091_ = v___x_1112_;
goto v___jp_1090_;
}
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1101_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1105_, v___f_1108_, v_data_1098_, v___x_1113_, v___x_1114_, v___x_1103_);
v___y_1091_ = v___x_1115_;
goto v___jp_1090_;
}
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v_size_1099_);
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_array_fget(v_data_1098_, v___x_1116_);
lean_dec_ref(v_data_1098_);
v___y_1091_ = v___x_1117_;
goto v___jp_1090_;
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1092_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_userData_1078_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_state_1080_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_knownSize_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_messageHead_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_userDataBytes_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*6, v_sentMessage_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*6 + 1, v_userClosedBody_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*6 + 2, v_omitBody_1085_);
v___x_1094_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___y_1091_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1119_, lean_object* v_writer_1120_){
_start:
{
uint8_t v_dir_boxed_1121_; lean_object* v_res_1122_; 
v_dir_boxed_1121_ = lean_unbox(v_dir_1119_);
v_res_1122_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1121_, v_writer_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1123_, lean_object* v_writer_1124_){
_start:
{
lean_object* v_userData_1125_; lean_object* v_outputData_1126_; lean_object* v_knownSize_1127_; lean_object* v_messageHead_1128_; uint8_t v_sentMessage_1129_; uint8_t v_userClosedBody_1130_; uint8_t v_omitBody_1131_; lean_object* v_userDataBytes_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_userData_1125_ = lean_ctor_get(v_writer_1124_, 0);
v_outputData_1126_ = lean_ctor_get(v_writer_1124_, 1);
v_knownSize_1127_ = lean_ctor_get(v_writer_1124_, 3);
v_messageHead_1128_ = lean_ctor_get(v_writer_1124_, 4);
v_sentMessage_1129_ = lean_ctor_get_uint8(v_writer_1124_, sizeof(void*)*6);
v_userClosedBody_1130_ = lean_ctor_get_uint8(v_writer_1124_, sizeof(void*)*6 + 1);
v_omitBody_1131_ = lean_ctor_get_uint8(v_writer_1124_, sizeof(void*)*6 + 2);
v_userDataBytes_1132_ = lean_ctor_get(v_writer_1124_, 5);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_writer_1124_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; 
v_unused_1140_ = lean_ctor_get(v_writer_1124_, 2);
lean_dec(v_unused_1140_);
v___x_1134_ = v_writer_1124_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_userDataBytes_1132_);
lean_inc(v_messageHead_1128_);
lean_inc(v_knownSize_1127_);
lean_inc(v_outputData_1126_);
lean_inc(v_userData_1125_);
lean_dec(v_writer_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 2, v_state_1123_);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_userData_1125_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_outputData_1126_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_state_1123_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_knownSize_1127_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_messageHead_1128_);
lean_ctor_set(v_reuseFailAlloc_1138_, 5, v_userDataBytes_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*6, v_sentMessage_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*6 + 1, v_userClosedBody_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*6 + 2, v_omitBody_1131_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1141_, lean_object* v_state_1142_, lean_object* v_writer_1143_){
_start:
{
lean_object* v_userData_1144_; lean_object* v_outputData_1145_; lean_object* v_knownSize_1146_; lean_object* v_messageHead_1147_; uint8_t v_sentMessage_1148_; uint8_t v_userClosedBody_1149_; uint8_t v_omitBody_1150_; lean_object* v_userDataBytes_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_userData_1144_ = lean_ctor_get(v_writer_1143_, 0);
v_outputData_1145_ = lean_ctor_get(v_writer_1143_, 1);
v_knownSize_1146_ = lean_ctor_get(v_writer_1143_, 3);
v_messageHead_1147_ = lean_ctor_get(v_writer_1143_, 4);
v_sentMessage_1148_ = lean_ctor_get_uint8(v_writer_1143_, sizeof(void*)*6);
v_userClosedBody_1149_ = lean_ctor_get_uint8(v_writer_1143_, sizeof(void*)*6 + 1);
v_omitBody_1150_ = lean_ctor_get_uint8(v_writer_1143_, sizeof(void*)*6 + 2);
v_userDataBytes_1151_ = lean_ctor_get(v_writer_1143_, 5);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_writer_1143_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_writer_1143_, 2);
lean_dec(v_unused_1159_);
v___x_1153_ = v_writer_1143_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_userDataBytes_1151_);
lean_inc(v_messageHead_1147_);
lean_inc(v_knownSize_1146_);
lean_inc(v_outputData_1145_);
lean_inc(v_userData_1144_);
lean_dec(v_writer_1143_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 2, v_state_1142_);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_userData_1144_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_outputData_1145_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_state_1142_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_knownSize_1146_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_messageHead_1147_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_userDataBytes_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*6, v_sentMessage_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*6 + 1, v_userClosedBody_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*6 + 2, v_omitBody_1150_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1160_, lean_object* v_state_1161_, lean_object* v_writer_1162_){
_start:
{
uint8_t v_dir_boxed_1163_; lean_object* v_res_1164_; 
v_dir_boxed_1163_ = lean_unbox(v_dir_1160_);
v_res_1164_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1163_, v_state_1161_, v_writer_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1165_, lean_object* v_messageHead_1166_, lean_object* v_writer_1167_){
_start:
{
lean_object* v_userData_1168_; lean_object* v_outputData_1169_; lean_object* v_state_1170_; lean_object* v_knownSize_1171_; lean_object* v_messageHead_1172_; uint8_t v_sentMessage_1173_; uint8_t v_userClosedBody_1174_; uint8_t v_omitBody_1175_; lean_object* v_userDataBytes_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1189_; 
v_userData_1168_ = lean_ctor_get(v_writer_1167_, 0);
v_outputData_1169_ = lean_ctor_get(v_writer_1167_, 1);
v_state_1170_ = lean_ctor_get(v_writer_1167_, 2);
v_knownSize_1171_ = lean_ctor_get(v_writer_1167_, 3);
v_messageHead_1172_ = lean_ctor_get(v_writer_1167_, 4);
v_sentMessage_1173_ = lean_ctor_get_uint8(v_writer_1167_, sizeof(void*)*6);
v_userClosedBody_1174_ = lean_ctor_get_uint8(v_writer_1167_, sizeof(void*)*6 + 1);
v_omitBody_1175_ = lean_ctor_get_uint8(v_writer_1167_, sizeof(void*)*6 + 2);
v_userDataBytes_1176_ = lean_ctor_get(v_writer_1167_, 5);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_writer_1167_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1178_ = v_writer_1167_;
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_userDataBytes_1176_);
lean_inc(v_messageHead_1172_);
lean_inc(v_knownSize_1171_);
lean_inc(v_state_1170_);
lean_inc(v_outputData_1169_);
lean_inc(v_userData_1168_);
lean_dec(v_writer_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint8_t v___y_1181_; 
if (v_dir_1165_ == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = 1;
v___y_1181_ = v___x_1187_;
goto v___jp_1180_;
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = 0;
v___y_1181_ = v___x_1188_;
goto v___jp_1180_;
}
v___jp_1180_:
{
lean_object* v___x_6__overap_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_6__overap_1182_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1181_);
v___x_1183_ = lean_apply_2(v___x_6__overap_1182_, v_outputData_1169_, v_messageHead_1166_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1183_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_userData_1168_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_state_1170_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_knownSize_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_messageHead_1172_);
lean_ctor_set(v_reuseFailAlloc_1186_, 5, v_userDataBytes_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*6, v_sentMessage_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*6 + 1, v_userClosedBody_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*6 + 2, v_omitBody_1175_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1190_, lean_object* v_messageHead_1191_, lean_object* v_writer_1192_){
_start:
{
uint8_t v_dir_boxed_1193_; lean_object* v_res_1194_; 
v_dir_boxed_1193_ = lean_unbox(v_dir_1190_);
v_res_1194_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1193_, v_messageHead_1191_, v_writer_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v_key_1197_; lean_object* v_value_1198_; lean_object* v_tail_1199_; uint8_t v___x_1200_; 
v_key_1197_ = lean_ctor_get(v_x_1196_, 0);
v_value_1198_ = lean_ctor_get(v_x_1196_, 1);
v_tail_1199_ = lean_ctor_get(v_x_1196_, 2);
v___x_1200_ = lean_string_dec_eq(v_key_1197_, v_a_1195_);
if (v___x_1200_ == 0)
{
v_x_1196_ = v_tail_1199_;
goto _start;
}
else
{
lean_inc(v_value_1198_);
return v_value_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1202_, v_x_1203_);
lean_dec(v_x_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_buckets_1207_; lean_object* v___x_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; uint64_t v_fold_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; uint64_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_buckets_1207_ = lean_ctor_get(v_m_1205_, 1);
v___x_1208_ = lean_array_get_size(v_buckets_1207_);
v___x_1209_ = lean_string_hash(v_a_1206_);
v___x_1210_ = 32ULL;
v___x_1211_ = lean_uint64_shift_right(v___x_1209_, v___x_1210_);
v_fold_1212_ = lean_uint64_xor(v___x_1209_, v___x_1211_);
v___x_1213_ = 16ULL;
v___x_1214_ = lean_uint64_shift_right(v_fold_1212_, v___x_1213_);
v___x_1215_ = lean_uint64_xor(v_fold_1212_, v___x_1214_);
v___x_1216_ = lean_uint64_to_usize(v___x_1215_);
v___x_1217_ = lean_usize_of_nat(v___x_1208_);
v___x_1218_ = ((size_t)1ULL);
v___x_1219_ = lean_usize_sub(v___x_1217_, v___x_1218_);
v___x_1220_ = lean_usize_land(v___x_1216_, v___x_1219_);
v___x_1221_ = lean_array_uget_borrowed(v_buckets_1207_, v___x_1220_);
v___x_1222_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1206_, v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1223_, v_a_1224_);
lean_dec_ref(v_a_1224_);
lean_dec_ref(v_m_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_s_1226_, lean_object* v_p_1227_){
_start:
{
uint32_t v___y_1229_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = lean_string_utf8_byte_size(v_s_1226_);
v___x_1235_ = lean_nat_dec_eq(v_p_1227_, v___x_1234_);
if (v___x_1235_ == 0)
{
uint32_t v___x_1236_; uint32_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_string_utf8_get_fast(v_s_1226_, v_p_1227_);
v___x_1237_ = 65;
v___x_1238_ = lean_uint32_dec_le(v___x_1237_, v___x_1236_);
if (v___x_1238_ == 0)
{
v___y_1229_ = v___x_1236_;
goto v___jp_1228_;
}
else
{
uint32_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = 90;
v___x_1240_ = lean_uint32_dec_le(v___x_1236_, v___x_1239_);
if (v___x_1240_ == 0)
{
v___y_1229_ = v___x_1236_;
goto v___jp_1228_;
}
else
{
uint32_t v___x_1241_; uint32_t v___x_1242_; 
v___x_1241_ = 32;
v___x_1242_ = lean_uint32_add(v___x_1236_, v___x_1241_);
v___y_1229_ = v___x_1242_;
goto v___jp_1228_;
}
}
}
else
{
lean_dec(v_p_1227_);
return v_s_1226_;
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_inc(v_p_1227_);
v___x_1230_ = lean_string_utf8_set(v_s_1226_, v_p_1227_, v___y_1229_);
v___x_1231_ = l_Char_utf8Size(v___y_1229_);
v___x_1232_ = lean_nat_add(v_p_1227_, v___x_1231_);
lean_dec(v___x_1231_);
lean_dec(v_p_1227_);
v_s_1226_ = v___x_1230_;
v_p_1227_ = v___x_1232_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1246_, lean_object* v_writer_1247_){
_start:
{
uint8_t v___y_1249_; 
if (v_dir_1246_ == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = 1;
v___y_1249_ = v___x_1268_;
goto v___jp_1248_;
}
else
{
uint8_t v___x_1269_; 
v___x_1269_ = 0;
v___y_1249_ = v___x_1269_;
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v_messageHead_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; uint8_t v___x_1255_; 
v_messageHead_1250_ = lean_ctor_get(v_writer_1247_, 4);
v___x_1251_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1249_, v_messageHead_1250_);
v___x_1252_ = l_Std_Http_Header_Name_connection;
v___f_1253_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___f_1254_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1));
v___x_1255_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1253_, v___f_1254_, v___x_1252_, v___x_1251_);
if (v___x_1255_ == 0)
{
uint8_t v___x_1256_; 
lean_dec_ref(v___x_1251_);
v___x_1256_ = 1;
return v___x_1256_;
}
else
{
lean_object* v_entries_1257_; lean_object* v_indexes_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_entry_1261_; lean_object* v___x_1262_; lean_object* v_snd_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; uint8_t v___x_1267_; 
v_entries_1257_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_ref(v_entries_1257_);
v_indexes_1258_ = lean_ctor_get(v___x_1251_, 1);
lean_inc_ref(v_indexes_1258_);
lean_dec_ref(v___x_1251_);
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1258_, v___x_1252_);
lean_dec_ref(v_indexes_1258_);
v___x_1260_ = lean_unsigned_to_nat(0u);
v_entry_1261_ = lean_array_fget(v___x_1259_, v___x_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_array_fget(v_entries_1257_, v_entry_1261_);
lean_dec(v_entry_1261_);
lean_dec_ref(v_entries_1257_);
v_snd_1263_ = lean_ctor_get(v___x_1262_, 1);
lean_inc(v_snd_1263_);
lean_dec(v___x_1262_);
v___x_1264_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_snd_1263_, v___x_1260_);
v___x_1265_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2));
v___x_1266_ = lean_string_dec_eq(v___x_1264_, v___x_1265_);
lean_dec_ref(v___x_1264_);
v___x_1267_ = lean_bool_not(v___x_1266_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1270_, lean_object* v_writer_1271_){
_start:
{
uint8_t v_dir_boxed_1272_; uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_dir_boxed_1272_ = lean_unbox(v_dir_1270_);
v_res_1273_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1272_, v_writer_1271_);
lean_dec_ref(v_writer_1271_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_, lean_object* v_hma_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1276_, v_a_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_, lean_object* v_hma_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1280_, v_m_1281_, v_a_1282_, v_hma_1283_);
lean_dec_ref(v_a_1282_);
lean_dec_ref(v_m_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1285_, lean_object* v_a_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1286_, v_x_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1290_, v_a_1291_, v_x_1292_, v_x_1293_);
lean_dec(v_x_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1295_){
_start:
{
lean_object* v_userData_1296_; lean_object* v_outputData_1297_; lean_object* v_knownSize_1298_; lean_object* v_messageHead_1299_; uint8_t v_sentMessage_1300_; uint8_t v_userClosedBody_1301_; uint8_t v_omitBody_1302_; lean_object* v_userDataBytes_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
v_userData_1296_ = lean_ctor_get(v_writer_1295_, 0);
v_outputData_1297_ = lean_ctor_get(v_writer_1295_, 1);
v_knownSize_1298_ = lean_ctor_get(v_writer_1295_, 3);
v_messageHead_1299_ = lean_ctor_get(v_writer_1295_, 4);
v_sentMessage_1300_ = lean_ctor_get_uint8(v_writer_1295_, sizeof(void*)*6);
v_userClosedBody_1301_ = lean_ctor_get_uint8(v_writer_1295_, sizeof(void*)*6 + 1);
v_omitBody_1302_ = lean_ctor_get_uint8(v_writer_1295_, sizeof(void*)*6 + 2);
v_userDataBytes_1303_ = lean_ctor_get(v_writer_1295_, 5);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_writer_1295_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_writer_1295_, 2);
lean_dec(v_unused_1312_);
v___x_1305_ = v_writer_1295_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_userDataBytes_1303_);
lean_inc(v_messageHead_1299_);
lean_inc(v_knownSize_1298_);
lean_inc(v_outputData_1297_);
lean_inc(v_userData_1296_);
lean_dec(v_writer_1295_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_box(7);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 2, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_userData_1296_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_outputData_1297_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_knownSize_1298_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_messageHead_1299_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_userDataBytes_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6, v_sentMessage_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6 + 1, v_userClosedBody_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*6 + 2, v_omitBody_1302_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1313_, lean_object* v_writer_1314_){
_start:
{
lean_object* v_userData_1315_; lean_object* v_outputData_1316_; lean_object* v_knownSize_1317_; lean_object* v_messageHead_1318_; uint8_t v_sentMessage_1319_; uint8_t v_userClosedBody_1320_; uint8_t v_omitBody_1321_; lean_object* v_userDataBytes_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_userData_1315_ = lean_ctor_get(v_writer_1314_, 0);
v_outputData_1316_ = lean_ctor_get(v_writer_1314_, 1);
v_knownSize_1317_ = lean_ctor_get(v_writer_1314_, 3);
v_messageHead_1318_ = lean_ctor_get(v_writer_1314_, 4);
v_sentMessage_1319_ = lean_ctor_get_uint8(v_writer_1314_, sizeof(void*)*6);
v_userClosedBody_1320_ = lean_ctor_get_uint8(v_writer_1314_, sizeof(void*)*6 + 1);
v_omitBody_1321_ = lean_ctor_get_uint8(v_writer_1314_, sizeof(void*)*6 + 2);
v_userDataBytes_1322_ = lean_ctor_get(v_writer_1314_, 5);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_writer_1314_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v_writer_1314_, 2);
lean_dec(v_unused_1331_);
v___x_1324_ = v_writer_1314_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_userDataBytes_1322_);
lean_inc(v_messageHead_1318_);
lean_inc(v_knownSize_1317_);
lean_inc(v_outputData_1316_);
lean_inc(v_userData_1315_);
lean_dec(v_writer_1314_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_box(7);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 2, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_userData_1315_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_outputData_1316_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v_knownSize_1317_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v_messageHead_1318_);
lean_ctor_set(v_reuseFailAlloc_1329_, 5, v_userDataBytes_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*6, v_sentMessage_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*6 + 1, v_userClosedBody_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*6 + 2, v_omitBody_1321_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1332_, lean_object* v_writer_1333_){
_start:
{
uint8_t v_dir_boxed_1334_; lean_object* v_res_1335_; 
v_dir_boxed_1334_ = lean_unbox(v_dir_1332_);
v_res_1335_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1334_, v_writer_1333_);
return v_res_1335_;
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
