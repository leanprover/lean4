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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
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
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_eq(v_i_552_, v_stop_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; 
v___x_556_ = lean_array_uget_borrowed(v_as_551_, v_i_552_);
v___x_557_ = lean_byte_array_size(v___x_556_);
v___x_558_ = lean_nat_add(v_b_554_, v___x_557_);
lean_dec(v_b_554_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_552_, v___x_559_);
v_i_552_ = v___x_560_;
v_b_554_ = v___x_558_;
goto _start;
}
else
{
return v_b_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_562_, lean_object* v_i_563_, lean_object* v_stop_564_, lean_object* v_b_565_){
_start:
{
size_t v_i_boxed_566_; size_t v_stop_boxed_567_; lean_object* v_res_568_; 
v_i_boxed_566_ = lean_unbox_usize(v_i_563_);
lean_dec(v_i_563_);
v_stop_boxed_567_ = lean_unbox_usize(v_stop_564_);
lean_dec(v_stop_564_);
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_562_, v_i_boxed_566_, v_stop_boxed_567_, v_b_565_);
lean_dec_ref(v_as_562_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_577_, lean_object* v_limitSize_578_){
_start:
{
lean_object* v___y_580_; uint8_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; uint8_t v___y_586_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v_userData_614_; lean_object* v_outputData_615_; lean_object* v_state_616_; lean_object* v_knownSize_617_; lean_object* v_messageHead_618_; uint8_t v_sentMessage_619_; uint8_t v_userClosedBody_620_; uint8_t v_omitBody_621_; lean_object* v_userDataBytes_622_; lean_object* v_fst_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_userData_614_ = lean_ctor_get(v_writer_577_, 0);
v_outputData_615_ = lean_ctor_get(v_writer_577_, 1);
v_state_616_ = lean_ctor_get(v_writer_577_, 2);
v_knownSize_617_ = lean_ctor_get(v_writer_577_, 3);
v_messageHead_618_ = lean_ctor_get(v_writer_577_, 4);
v_sentMessage_619_ = lean_ctor_get_uint8(v_writer_577_, sizeof(void*)*6);
v_userClosedBody_620_ = lean_ctor_get_uint8(v_writer_577_, sizeof(void*)*6 + 1);
v_omitBody_621_ = lean_ctor_get_uint8(v_writer_577_, sizeof(void*)*6 + 2);
v_userDataBytes_622_ = lean_ctor_get(v_writer_577_, 5);
v___x_635_ = lean_array_get_size(v_userData_614_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; uint8_t v___x_639_; 
lean_inc(v_userDataBytes_622_);
lean_inc(v_messageHead_618_);
lean_inc(v_knownSize_617_);
lean_inc(v_state_616_);
lean_inc_ref(v_outputData_615_);
lean_inc_ref(v_userData_614_);
lean_dec_ref(v_writer_577_);
v___x_638_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_639_ = lean_nat_dec_lt(v___x_636_, v___x_635_);
if (v___x_639_ == 0)
{
lean_dec_ref(v_userData_614_);
v_fst_624_ = v___x_638_;
v_fst_625_ = v___x_638_;
v_snd_626_ = v___x_636_;
goto v___jp_623_;
}
else
{
lean_object* v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; lean_object* v_snd_644_; lean_object* v_fst_645_; lean_object* v_fst_646_; lean_object* v_snd_647_; 
v___x_640_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_635_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_578_, v_userData_614_, v___x_641_, v___x_642_, v___x_640_);
lean_dec_ref(v_userData_614_);
v_snd_644_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_snd_644_);
v_fst_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_fst_645_);
lean_dec_ref(v___x_643_);
v_fst_646_ = lean_ctor_get(v_snd_644_, 0);
lean_inc(v_fst_646_);
v_snd_647_ = lean_ctor_get(v_snd_644_, 1);
lean_inc(v_snd_647_);
lean_dec(v_snd_644_);
v_fst_624_ = v_fst_645_;
v_fst_625_ = v_fst_646_;
v_snd_626_ = v_snd_647_;
goto v___jp_623_;
}
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_writer_577_);
lean_ctor_set(v___x_648_, 1, v_limitSize_578_);
return v___x_648_;
}
v___jp_579_:
{
lean_object* v_data_591_; lean_object* v_size_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_613_; 
v_data_591_ = lean_ctor_get(v___y_587_, 0);
v_size_592_ = lean_ctor_get(v___y_587_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___y_587_);
if (v_isSharedCheck_613_ == 0)
{
v___x_594_ = v___y_587_;
v_isShared_595_ = v_isSharedCheck_613_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_size_592_);
lean_inc(v_data_591_);
lean_dec(v___y_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_613_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_data_596_; lean_object* v_size_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_612_; 
v_data_596_ = lean_ctor_get(v___y_590_, 0);
v_size_597_ = lean_ctor_get(v___y_590_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v___y_590_);
if (v_isSharedCheck_612_ == 0)
{
v___x_599_ = v___y_590_;
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_size_597_);
lean_inc(v_data_596_);
lean_dec(v___y_590_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_outputData_604_; 
v___x_601_ = l_Array_append___redArg(v_data_591_, v_data_596_);
lean_dec_ref(v_data_596_);
v___x_602_ = lean_nat_add(v_size_592_, v_size_597_);
lean_dec(v_size_597_);
lean_dec(v_size_592_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_602_);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v_outputData_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_602_);
v_outputData_604_ = v_reuseFailAlloc_611_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v_remaining_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v_remaining_605_ = lean_nat_sub(v_limitSize_578_, v___y_582_);
lean_dec(v_limitSize_578_);
v___x_606_ = lean_nat_sub(v___y_580_, v___y_582_);
lean_dec(v___y_582_);
lean_dec(v___y_580_);
v___x_607_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_607_, 0, v___y_589_);
lean_ctor_set(v___x_607_, 1, v_outputData_604_);
lean_ctor_set(v___x_607_, 2, v___y_585_);
lean_ctor_set(v___x_607_, 3, v___y_584_);
lean_ctor_set(v___x_607_, 4, v___y_583_);
lean_ctor_set(v___x_607_, 5, v___x_606_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*6, v___y_586_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*6 + 1, v___y_581_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*6 + 2, v___y_588_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v_remaining_605_);
lean_ctor_set(v___x_594_, 0, v___x_607_);
v___x_609_ = v___x_594_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_remaining_605_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
v___jp_623_:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_array_get_size(v_fst_624_);
v___x_629_ = lean_nat_dec_lt(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_fst_624_);
lean_ctor_set(v___x_630_, 1, v___x_627_);
v___y_580_ = v_userDataBytes_622_;
v___y_581_ = v_userClosedBody_620_;
v___y_582_ = v_snd_626_;
v___y_583_ = v_messageHead_618_;
v___y_584_ = v_knownSize_617_;
v___y_585_ = v_state_616_;
v___y_586_ = v_sentMessage_619_;
v___y_587_ = v_outputData_615_;
v___y_588_ = v_omitBody_621_;
v___y_589_ = v_fst_625_;
v___y_590_ = v___x_630_;
goto v___jp_579_;
}
else
{
size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = ((size_t)0ULL);
v___x_632_ = lean_usize_of_nat(v___x_628_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_624_, v___x_631_, v___x_632_, v___x_627_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_fst_624_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___y_580_ = v_userDataBytes_622_;
v___y_581_ = v_userClosedBody_620_;
v___y_582_ = v_snd_626_;
v___y_583_ = v_messageHead_618_;
v___y_584_ = v_knownSize_617_;
v___y_585_ = v_state_616_;
v___y_586_ = v_sentMessage_619_;
v___y_587_ = v_outputData_615_;
v___y_588_ = v_omitBody_621_;
v___y_589_ = v_fst_625_;
v___y_590_ = v___x_634_;
goto v___jp_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_649_, lean_object* v_writer_650_, lean_object* v_limitSize_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_650_, v_limitSize_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_653_, lean_object* v_writer_654_, lean_object* v_limitSize_655_){
_start:
{
uint8_t v_dir_boxed_656_; lean_object* v_res_657_; 
v_dir_boxed_656_ = lean_unbox(v_dir_653_);
v_res_657_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_656_, v_writer_654_, v_limitSize_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(lean_object* v_as_658_, size_t v_i_659_, size_t v_stop_660_, lean_object* v_b_661_){
_start:
{
lean_object* v___y_663_; uint8_t v___x_667_; 
v___x_667_ = lean_usize_dec_eq(v_i_659_, v_stop_660_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v_data_669_; uint8_t v___x_670_; 
v___x_668_ = lean_array_uget_borrowed(v_as_658_, v_i_659_);
v_data_669_ = lean_ctor_get(v___x_668_, 0);
v___x_670_ = l_ByteArray_isEmpty(v_data_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_inc(v___x_668_);
v___x_671_ = lean_array_push(v_b_661_, v___x_668_);
v___y_663_ = v___x_671_;
goto v___jp_662_;
}
else
{
v___y_663_ = v_b_661_;
goto v___jp_662_;
}
}
else
{
return v_b_661_;
}
v___jp_662_:
{
size_t v___x_664_; size_t v___x_665_; 
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_add(v_i_659_, v___x_664_);
v_i_659_ = v___x_665_;
v_b_661_ = v___y_663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3___boxed(lean_object* v_as_672_, lean_object* v_i_673_, lean_object* v_stop_674_, lean_object* v_b_675_){
_start:
{
size_t v_i_boxed_676_; size_t v_stop_boxed_677_; lean_object* v_res_678_; 
v_i_boxed_676_ = lean_unbox_usize(v_i_673_);
lean_dec(v_i_673_);
v_stop_boxed_677_ = lean_unbox_usize(v_stop_674_);
lean_dec(v_stop_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_as_672_, v_i_boxed_676_, v_stop_boxed_677_, v_b_675_);
lean_dec_ref(v_as_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_679_, size_t v_i_680_, lean_object* v_bs_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_682_ == 0)
{
return v_bs_681_;
}
else
{
lean_object* v_v_683_; lean_object* v___x_684_; lean_object* v_bs_x27_685_; uint32_t v___x_686_; uint8_t v___x_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_v_683_ = lean_array_uget(v_bs_681_, v_i_680_);
v___x_684_ = lean_unsigned_to_nat(0u);
v_bs_x27_685_ = lean_array_uset(v_bs_681_, v_i_680_, v___x_684_);
v___x_686_ = lean_unbox_uint32(v_v_683_);
lean_dec(v_v_683_);
v___x_687_ = lean_uint32_to_uint8(v___x_686_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_i_680_, v___x_688_);
v___x_690_ = lean_box(v___x_687_);
v___x_691_ = lean_array_uset(v_bs_x27_685_, v_i_680_, v___x_690_);
v_i_680_ = v___x_689_;
v_bs_681_ = v___x_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_693_, lean_object* v_i_694_, lean_object* v_bs_695_){
_start:
{
size_t v_sz_boxed_696_; size_t v_i_boxed_697_; lean_object* v_res_698_; 
v_sz_boxed_696_ = lean_unbox_usize(v_sz_693_);
lean_dec(v_sz_693_);
v_i_boxed_697_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_696_, v_i_boxed_697_, v_bs_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_701_, size_t v_i_702_, size_t v_stop_703_, lean_object* v_b_704_){
_start:
{
lean_object* v___y_706_; uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_eq(v_i_702_, v_stop_703_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_711_ = lean_array_uget_borrowed(v_as_701_, v_i_702_);
v_fst_712_ = lean_ctor_get(v___x_711_, 0);
v_snd_713_ = lean_ctor_get(v___x_711_, 1);
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_715_ = lean_string_append(v_b_704_, v___x_714_);
v___x_716_ = lean_string_append(v___x_715_, v_fst_712_);
if (lean_obj_tag(v_snd_713_) == 0)
{
v___y_706_ = v___x_716_;
goto v___jp_705_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_val_717_ = lean_ctor_get(v_snd_713_, 0);
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_717_);
v___x_719_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_717_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = lean_string_append(v___x_716_, v___x_720_);
lean_dec_ref(v___x_720_);
v___y_706_ = v___x_721_;
goto v___jp_705_;
}
}
else
{
return v_b_704_;
}
v___jp_705_:
{
size_t v___x_707_; size_t v___x_708_; 
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_702_, v___x_707_);
v_i_702_ = v___x_708_;
v_b_704_ = v___y_706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_722_, lean_object* v_i_723_, lean_object* v_stop_724_, lean_object* v_b_725_){
_start:
{
size_t v_i_boxed_726_; size_t v_stop_boxed_727_; lean_object* v_res_728_; 
v_i_boxed_726_ = lean_unbox_usize(v_i_723_);
lean_dec(v_i_723_);
v_stop_boxed_727_ = lean_unbox_usize(v_stop_724_);
lean_dec(v_stop_724_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_722_, v_i_boxed_726_, v_stop_boxed_727_, v_b_725_);
lean_dec_ref(v_as_722_);
return v_res_728_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_731_ = lean_string_to_utf8(v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_733_, size_t v_i_734_, size_t v_stop_735_, lean_object* v_b_736_){
_start:
{
lean_object* v___y_738_; uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_eq(v_i_734_, v_stop_735_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v_data_757_; lean_object* v_extensions_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_799_; 
v___x_756_ = lean_array_uget(v_as_733_, v_i_734_);
v_data_757_ = lean_ctor_get(v___x_756_, 0);
v_extensions_758_ = lean_ctor_get(v___x_756_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_799_ == 0)
{
v___x_760_ = v___x_756_;
v_isShared_761_ = v_isSharedCheck_799_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_extensions_758_);
lean_inc(v_data_757_);
lean_dec(v___x_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_799_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_chunkLen_762_; lean_object* v___y_764_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_chunkLen_762_ = lean_byte_array_size(v_data_757_);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_array_get_size(v_extensions_758_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec_ref(v_extensions_758_);
v___y_764_ = v___x_792_;
goto v___jp_763_;
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_of_nat(v___x_794_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_758_, v___x_796_, v___x_797_, v___x_792_);
lean_dec_ref(v_extensions_758_);
v___y_764_ = v___x_798_;
goto v___jp_763_;
}
v___jp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; size_t v_sz_768_; size_t v___x_769_; lean_object* v___x_770_; lean_object* v_size_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_765_ = lean_unsigned_to_nat(16u);
v___x_766_ = l_Nat_toDigits(v___x_765_, v_chunkLen_762_);
v___x_767_ = lean_array_mk(v___x_766_);
v_sz_768_ = lean_array_size(v___x_767_);
v___x_769_ = ((size_t)0ULL);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_768_, v___x_769_, v___x_767_);
v_size_771_ = lean_byte_array_mk(v___x_770_);
v___x_772_ = lean_string_to_utf8(v___y_764_);
v___x_773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_774_ = lean_unsigned_to_nat(5u);
v___x_775_ = lean_mk_empty_array_with_capacity(v___x_774_);
v___x_776_ = lean_array_push(v___x_775_, v_size_771_);
v___x_777_ = lean_array_push(v___x_776_, v___x_772_);
v___x_778_ = lean_array_push(v___x_777_, v___x_773_);
v___x_779_ = lean_array_push(v___x_778_, v_data_757_);
v___x_780_ = lean_array_push(v___x_779_, v___x_773_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v___x_780_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_785_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_781_);
lean_ctor_set(v___x_760_, 0, v___x_780_);
v___x_785_ = v___x_760_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_781_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v___y_738_ = v___x_785_;
goto v___jp_737_;
}
}
else
{
size_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_787_ = lean_usize_of_nat(v___x_782_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_780_, v___x_769_, v___x_787_, v___x_781_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_788_);
lean_ctor_set(v___x_760_, 0, v___x_780_);
v___x_790_ = v___x_760_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_738_ = v___x_790_;
goto v___jp_737_;
}
}
}
}
}
else
{
return v_b_736_;
}
v___jp_737_:
{
lean_object* v_data_739_; lean_object* v_size_740_; lean_object* v_data_741_; lean_object* v_size_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_754_; 
v_data_739_ = lean_ctor_get(v_b_736_, 0);
lean_inc_ref(v_data_739_);
v_size_740_ = lean_ctor_get(v_b_736_, 1);
lean_inc(v_size_740_);
lean_dec_ref(v_b_736_);
v_data_741_ = lean_ctor_get(v___y_738_, 0);
v_size_742_ = lean_ctor_get(v___y_738_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___y_738_);
if (v_isSharedCheck_754_ == 0)
{
v___x_744_ = v___y_738_;
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_size_742_);
lean_inc(v_data_741_);
lean_dec(v___y_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = l_Array_append___redArg(v_data_739_, v_data_741_);
lean_dec_ref(v_data_741_);
v___x_747_ = lean_nat_add(v_size_740_, v_size_742_);
lean_dec(v_size_742_);
lean_dec(v_size_740_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_747_);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
size_t v___x_750_; size_t v___x_751_; 
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_734_, v___x_750_);
v_i_734_ = v___x_751_;
v_b_736_ = v___x_749_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_800_, lean_object* v_i_801_, lean_object* v_stop_802_, lean_object* v_b_803_){
_start:
{
size_t v_i_boxed_804_; size_t v_stop_boxed_805_; lean_object* v_res_806_; 
v_i_boxed_804_ = lean_unbox_usize(v_i_801_);
lean_dec(v_i_801_);
v_stop_boxed_805_ = lean_unbox_usize(v_stop_802_);
lean_dec(v_stop_802_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_800_, v_i_boxed_804_, v_stop_boxed_805_, v_b_803_);
lean_dec_ref(v_as_800_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_809_){
_start:
{
lean_object* v_userData_810_; lean_object* v_outputData_811_; lean_object* v_state_812_; lean_object* v_knownSize_813_; lean_object* v_messageHead_814_; uint8_t v_sentMessage_815_; uint8_t v_userClosedBody_816_; uint8_t v_omitBody_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___y_821_; uint8_t v___x_830_; 
v_userData_810_ = lean_ctor_get(v_writer_809_, 0);
v_outputData_811_ = lean_ctor_get(v_writer_809_, 1);
v_state_812_ = lean_ctor_get(v_writer_809_, 2);
v_knownSize_813_ = lean_ctor_get(v_writer_809_, 3);
v_messageHead_814_ = lean_ctor_get(v_writer_809_, 4);
v_sentMessage_815_ = lean_ctor_get_uint8(v_writer_809_, sizeof(void*)*6);
v_userClosedBody_816_ = lean_ctor_get_uint8(v_writer_809_, sizeof(void*)*6 + 1);
v_omitBody_817_ = lean_ctor_get_uint8(v_writer_809_, sizeof(void*)*6 + 2);
v___x_818_ = lean_array_get_size(v_userData_810_);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
lean_inc(v_messageHead_814_);
lean_inc(v_knownSize_813_);
lean_inc(v_state_812_);
lean_inc_ref(v_outputData_811_);
lean_inc_ref(v_userData_810_);
lean_dec_ref(v_writer_809_);
v___x_831_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_832_ = lean_nat_dec_lt(v___x_819_, v___x_818_);
if (v___x_832_ == 0)
{
lean_dec_ref(v_userData_810_);
v___y_821_ = v___x_831_;
goto v___jp_820_;
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_of_nat(v___x_818_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__3(v_userData_810_, v___x_833_, v___x_834_, v___x_831_);
lean_dec_ref(v_userData_810_);
v___y_821_ = v___x_835_;
goto v___jp_820_;
}
}
else
{
return v_writer_809_;
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_822_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_823_ = lean_array_get_size(v___y_821_);
v___x_824_ = lean_nat_dec_lt(v___x_819_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v___y_821_);
v___x_825_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_825_, 0, v___x_822_);
lean_ctor_set(v___x_825_, 1, v_outputData_811_);
lean_ctor_set(v___x_825_, 2, v_state_812_);
lean_ctor_set(v___x_825_, 3, v_knownSize_813_);
lean_ctor_set(v___x_825_, 4, v_messageHead_814_);
lean_ctor_set(v___x_825_, 5, v___x_819_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*6, v_sentMessage_815_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*6 + 1, v_userClosedBody_816_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*6 + 2, v_omitBody_817_);
return v___x_825_;
}
else
{
size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = ((size_t)0ULL);
v___x_827_ = lean_usize_of_nat(v___x_823_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v___y_821_, v___x_826_, v___x_827_, v_outputData_811_);
lean_dec_ref(v___y_821_);
v___x_829_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_829_, 0, v___x_822_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_ctor_set(v___x_829_, 2, v_state_812_);
lean_ctor_set(v___x_829_, 3, v_knownSize_813_);
lean_ctor_set(v___x_829_, 4, v_messageHead_814_);
lean_ctor_set(v___x_829_, 5, v___x_819_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*6, v_sentMessage_815_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*6 + 1, v_userClosedBody_816_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*6 + 2, v_omitBody_817_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_836_, lean_object* v_writer_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_839_, lean_object* v_writer_840_){
_start:
{
uint8_t v_dir_boxed_841_; lean_object* v_res_842_; 
v_dir_boxed_841_ = lean_unbox(v_dir_839_);
v_res_842_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_841_, v_writer_840_);
return v_res_842_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_845_ = lean_string_to_utf8(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_847_ = lean_byte_array_size(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_848_){
_start:
{
lean_object* v_writer_849_; lean_object* v_outputData_850_; lean_object* v_userData_851_; lean_object* v_knownSize_852_; lean_object* v_messageHead_853_; uint8_t v_sentMessage_854_; uint8_t v_userClosedBody_855_; uint8_t v_omitBody_856_; lean_object* v_userDataBytes_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_878_; 
v_writer_849_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_848_);
v_outputData_850_ = lean_ctor_get(v_writer_849_, 1);
v_userData_851_ = lean_ctor_get(v_writer_849_, 0);
v_knownSize_852_ = lean_ctor_get(v_writer_849_, 3);
v_messageHead_853_ = lean_ctor_get(v_writer_849_, 4);
v_sentMessage_854_ = lean_ctor_get_uint8(v_writer_849_, sizeof(void*)*6);
v_userClosedBody_855_ = lean_ctor_get_uint8(v_writer_849_, sizeof(void*)*6 + 1);
v_omitBody_856_ = lean_ctor_get_uint8(v_writer_849_, sizeof(void*)*6 + 2);
v_userDataBytes_857_ = lean_ctor_get(v_writer_849_, 5);
v_isSharedCheck_878_ = !lean_is_exclusive(v_writer_849_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_writer_849_, 2);
lean_dec(v_unused_879_);
v___x_859_ = v_writer_849_;
v_isShared_860_ = v_isSharedCheck_878_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_userDataBytes_857_);
lean_inc(v_messageHead_853_);
lean_inc(v_knownSize_852_);
lean_inc(v_outputData_850_);
lean_inc(v_userData_851_);
lean_dec(v_writer_849_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_878_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_data_861_; lean_object* v_size_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_877_; 
v_data_861_ = lean_ctor_get(v_outputData_850_, 0);
v_size_862_ = lean_ctor_get(v_outputData_850_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_outputData_850_);
if (v_isSharedCheck_877_ == 0)
{
v___x_864_ = v_outputData_850_;
v_isShared_865_ = v_isSharedCheck_877_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_size_862_);
lean_inc(v_data_861_);
lean_dec(v_outputData_850_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_877_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_866_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_867_ = lean_array_push(v_data_861_, v___x_866_);
v___x_868_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_869_ = lean_nat_add(v_size_862_, v___x_868_);
lean_dec(v_size_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_869_);
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_876_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_box(6);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 2, v___x_872_);
lean_ctor_set(v___x_859_, 1, v___x_871_);
v___x_874_ = v___x_859_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_userData_851_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_knownSize_852_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_messageHead_853_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_userDataBytes_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6, v_sentMessage_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6 + 1, v_userClosedBody_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6 + 2, v_omitBody_856_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_880_, lean_object* v_writer_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_883_, lean_object* v_writer_884_){
_start:
{
uint8_t v_dir_boxed_885_; lean_object* v_res_886_; 
v_dir_boxed_885_ = lean_unbox(v_dir_883_);
v_res_886_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_885_, v_writer_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(lean_object* v_as_887_, size_t v_i_888_, size_t v_stop_889_, lean_object* v_b_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_eq(v_i_888_, v_stop_889_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v_data_893_; lean_object* v_data_894_; lean_object* v_size_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_908_; 
v___x_892_ = lean_array_uget_borrowed(v_as_887_, v_i_888_);
v_data_893_ = lean_ctor_get(v___x_892_, 0);
v_data_894_ = lean_ctor_get(v_b_890_, 0);
v_size_895_ = lean_ctor_get(v_b_890_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_b_890_);
if (v_isSharedCheck_908_ == 0)
{
v___x_897_ = v_b_890_;
v_isShared_898_ = v_isSharedCheck_908_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_size_895_);
lean_inc(v_data_894_);
lean_dec(v_b_890_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_908_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
lean_inc_ref(v_data_893_);
v___x_899_ = lean_array_push(v_data_894_, v_data_893_);
v___x_900_ = lean_byte_array_size(v_data_893_);
v___x_901_ = lean_nat_add(v_size_895_, v___x_900_);
lean_dec(v_size_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_901_);
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_903_ = v___x_897_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
size_t v___x_904_; size_t v___x_905_; 
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_888_, v___x_904_);
v_i_888_ = v___x_905_;
v_b_890_ = v___x_903_;
goto _start;
}
}
}
else
{
return v_b_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0___boxed(lean_object* v_as_909_, lean_object* v_i_910_, lean_object* v_stop_911_, lean_object* v_b_912_){
_start:
{
size_t v_i_boxed_913_; size_t v_stop_boxed_914_; lean_object* v_res_915_; 
v_i_boxed_913_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_stop_boxed_914_ = lean_unbox_usize(v_stop_911_);
lean_dec(v_stop_911_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_as_909_, v_i_boxed_913_, v_stop_boxed_914_, v_b_912_);
lean_dec_ref(v_as_909_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(lean_object* v_writer_916_){
_start:
{
lean_object* v_userData_917_; lean_object* v_outputData_918_; lean_object* v_state_919_; lean_object* v_knownSize_920_; lean_object* v_messageHead_921_; uint8_t v_sentMessage_922_; uint8_t v_userClosedBody_923_; uint8_t v_omitBody_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_941_; 
v_userData_917_ = lean_ctor_get(v_writer_916_, 0);
v_outputData_918_ = lean_ctor_get(v_writer_916_, 1);
v_state_919_ = lean_ctor_get(v_writer_916_, 2);
v_knownSize_920_ = lean_ctor_get(v_writer_916_, 3);
v_messageHead_921_ = lean_ctor_get(v_writer_916_, 4);
v_sentMessage_922_ = lean_ctor_get_uint8(v_writer_916_, sizeof(void*)*6);
v_userClosedBody_923_ = lean_ctor_get_uint8(v_writer_916_, sizeof(void*)*6 + 1);
v_omitBody_924_ = lean_ctor_get_uint8(v_writer_916_, sizeof(void*)*6 + 2);
v_isSharedCheck_941_ = !lean_is_exclusive(v_writer_916_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_writer_916_, 5);
lean_dec(v_unused_942_);
v___x_926_ = v_writer_916_;
v_isShared_927_ = v_isSharedCheck_941_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_messageHead_921_);
lean_inc(v_knownSize_920_);
lean_inc(v_state_919_);
lean_inc(v_outputData_918_);
lean_inc(v_userData_917_);
lean_dec(v_writer_916_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_941_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_930_ = lean_array_get_size(v_userData_917_);
v___x_931_ = lean_nat_dec_lt(v___x_928_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_933_; 
lean_dec_ref(v_userData_917_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 5, v___x_928_);
lean_ctor_set(v___x_926_, 0, v___x_929_);
v___x_933_ = v___x_926_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_outputData_918_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_state_919_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_knownSize_920_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v_messageHead_921_);
lean_ctor_set(v_reuseFailAlloc_934_, 5, v___x_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*6, v_sentMessage_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*6 + 1, v_userClosedBody_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*6 + 2, v_omitBody_924_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_935_ = ((size_t)0ULL);
v___x_936_ = lean_usize_of_nat(v___x_930_);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeRawBody_spec__0(v_userData_917_, v___x_935_, v___x_936_, v_outputData_918_);
lean_dec_ref(v_userData_917_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 5, v___x_928_);
lean_ctor_set(v___x_926_, 1, v___x_937_);
lean_ctor_set(v___x_926_, 0, v___x_929_);
v___x_939_ = v___x_926_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_state_919_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_knownSize_920_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_messageHead_921_);
lean_ctor_set(v_reuseFailAlloc_940_, 5, v___x_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*6, v_sentMessage_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*6 + 1, v_userClosedBody_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*6 + 2, v_omitBody_924_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody(uint8_t v_dir_943_, lean_object* v_writer_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_Http_Protocol_H1_Writer_writeRawBody___redArg(v_writer_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeRawBody___boxed(lean_object* v_dir_946_, lean_object* v_writer_947_){
_start:
{
uint8_t v_dir_boxed_948_; lean_object* v_res_949_; 
v_dir_boxed_948_ = lean_unbox(v_dir_946_);
v_res_949_ = l_Std_Http_Protocol_H1_Writer_writeRawBody(v_dir_boxed_948_, v_writer_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_950_, lean_object* v_x1_951_, lean_object* v_x2_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_byte_array_size(v_x1_951_);
v___x_955_ = lean_byte_array_size(v_x2_952_);
v___x_956_ = lean_byte_array_copy_slice(v_x2_952_, v___x_953_, v_x1_951_, v___x_954_, v___x_955_, v___x_950_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_957_, lean_object* v_x1_958_, lean_object* v_x2_959_){
_start:
{
uint8_t v___x_115__boxed_960_; lean_object* v_res_961_; 
v___x_115__boxed_960_ = lean_unbox(v___x_957_);
v_res_961_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_115__boxed_960_, v_x1_958_, v_x2_959_);
lean_dec_ref(v_x2_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_965_){
_start:
{
lean_object* v_userData_966_; lean_object* v_outputData_967_; lean_object* v_state_968_; lean_object* v_knownSize_969_; lean_object* v_messageHead_970_; uint8_t v_sentMessage_971_; uint8_t v_userClosedBody_972_; uint8_t v_omitBody_973_; lean_object* v_userDataBytes_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1002_; 
v_userData_966_ = lean_ctor_get(v_writer_965_, 0);
v_outputData_967_ = lean_ctor_get(v_writer_965_, 1);
v_state_968_ = lean_ctor_get(v_writer_965_, 2);
v_knownSize_969_ = lean_ctor_get(v_writer_965_, 3);
v_messageHead_970_ = lean_ctor_get(v_writer_965_, 4);
v_sentMessage_971_ = lean_ctor_get_uint8(v_writer_965_, sizeof(void*)*6);
v_userClosedBody_972_ = lean_ctor_get_uint8(v_writer_965_, sizeof(void*)*6 + 1);
v_omitBody_973_ = lean_ctor_get_uint8(v_writer_965_, sizeof(void*)*6 + 2);
v_userDataBytes_974_ = lean_ctor_get(v_writer_965_, 5);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_writer_965_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_976_ = v_writer_965_;
v_isShared_977_ = v_isSharedCheck_1002_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_userDataBytes_974_);
lean_inc(v_messageHead_970_);
lean_inc(v_knownSize_969_);
lean_inc(v_state_968_);
lean_inc(v_outputData_967_);
lean_inc(v_userData_966_);
lean_dec(v_writer_965_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1002_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___y_979_; lean_object* v_data_986_; lean_object* v_size_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v_data_986_ = lean_ctor_get(v_outputData_967_, 0);
lean_inc_ref(v_data_986_);
v_size_987_ = lean_ctor_get(v_outputData_967_, 1);
lean_inc(v_size_987_);
lean_dec_ref(v_outputData_967_);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_array_get_size(v_data_986_);
v___x_990_ = lean_nat_dec_eq(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_991_ = lean_mk_empty_byte_array(v_size_987_);
lean_dec(v_size_987_);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_994_ = lean_nat_dec_lt(v___x_992_, v___x_989_);
if (v___x_994_ == 0)
{
lean_dec_ref(v_data_986_);
v___y_979_ = v___x_991_;
goto v___jp_978_;
}
else
{
lean_object* v___x_995_; lean_object* v___f_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_995_ = lean_box(v___x_990_);
v___f_996_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_996_, 0, v___x_995_);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_989_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_993_, v___f_996_, v_data_986_, v___x_997_, v___x_998_, v___x_991_);
v___y_979_ = v___x_999_;
goto v___jp_978_;
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v_size_987_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_array_fget(v_data_986_, v___x_1000_);
lean_dec_ref(v_data_986_);
v___y_979_ = v___x_1001_;
goto v___jp_978_;
}
v___jp_978_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_980_);
v___x_982_ = v___x_976_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_userData_966_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_state_968_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_knownSize_969_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_messageHead_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 5, v_userDataBytes_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*6, v_sentMessage_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*6 + 1, v_userClosedBody_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*6 + 2, v_omitBody_973_);
v___x_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___y_979_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_1003_, lean_object* v_writer_1004_){
_start:
{
lean_object* v_userData_1005_; lean_object* v_outputData_1006_; lean_object* v_state_1007_; lean_object* v_knownSize_1008_; lean_object* v_messageHead_1009_; uint8_t v_sentMessage_1010_; uint8_t v_userClosedBody_1011_; uint8_t v_omitBody_1012_; lean_object* v_userDataBytes_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1041_; 
v_userData_1005_ = lean_ctor_get(v_writer_1004_, 0);
v_outputData_1006_ = lean_ctor_get(v_writer_1004_, 1);
v_state_1007_ = lean_ctor_get(v_writer_1004_, 2);
v_knownSize_1008_ = lean_ctor_get(v_writer_1004_, 3);
v_messageHead_1009_ = lean_ctor_get(v_writer_1004_, 4);
v_sentMessage_1010_ = lean_ctor_get_uint8(v_writer_1004_, sizeof(void*)*6);
v_userClosedBody_1011_ = lean_ctor_get_uint8(v_writer_1004_, sizeof(void*)*6 + 1);
v_omitBody_1012_ = lean_ctor_get_uint8(v_writer_1004_, sizeof(void*)*6 + 2);
v_userDataBytes_1013_ = lean_ctor_get(v_writer_1004_, 5);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_writer_1004_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1015_ = v_writer_1004_;
v_isShared_1016_ = v_isSharedCheck_1041_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_userDataBytes_1013_);
lean_inc(v_messageHead_1009_);
lean_inc(v_knownSize_1008_);
lean_inc(v_state_1007_);
lean_inc(v_outputData_1006_);
lean_inc(v_userData_1005_);
lean_dec(v_writer_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1041_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___y_1018_; lean_object* v_data_1025_; lean_object* v_size_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_data_1025_ = lean_ctor_get(v_outputData_1006_, 0);
lean_inc_ref(v_data_1025_);
v_size_1026_ = lean_ctor_get(v_outputData_1006_, 1);
lean_inc(v_size_1026_);
lean_dec_ref(v_outputData_1006_);
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_array_get_size(v_data_1025_);
v___x_1029_ = lean_nat_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1030_ = lean_mk_empty_byte_array(v_size_1026_);
lean_dec(v_size_1026_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1028_);
if (v___x_1033_ == 0)
{
lean_dec_ref(v_data_1025_);
v___y_1018_ = v___x_1030_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1034_; lean_object* v___f_1035_; size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1034_ = lean_box(v___x_1029_);
v___f_1035_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1035_, 0, v___x_1034_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1032_, v___f_1035_, v_data_1025_, v___x_1036_, v___x_1037_, v___x_1030_);
v___y_1018_ = v___x_1038_;
goto v___jp_1017_;
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v_size_1026_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_fget(v_data_1025_, v___x_1039_);
lean_dec_ref(v_data_1025_);
v___y_1018_ = v___x_1040_;
goto v___jp_1017_;
}
v___jp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 1, v___x_1019_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_userData_1005_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_state_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_knownSize_1008_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_messageHead_1009_);
lean_ctor_set(v_reuseFailAlloc_1024_, 5, v_userDataBytes_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*6, v_sentMessage_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*6 + 1, v_userClosedBody_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*6 + 2, v_omitBody_1012_);
v___x_1021_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___y_1018_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_1042_, lean_object* v_writer_1043_){
_start:
{
uint8_t v_dir_boxed_1044_; lean_object* v_res_1045_; 
v_dir_boxed_1044_ = lean_unbox(v_dir_1042_);
v_res_1045_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_1044_, v_writer_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_1046_, lean_object* v_writer_1047_){
_start:
{
lean_object* v_userData_1048_; lean_object* v_outputData_1049_; lean_object* v_knownSize_1050_; lean_object* v_messageHead_1051_; uint8_t v_sentMessage_1052_; uint8_t v_userClosedBody_1053_; uint8_t v_omitBody_1054_; lean_object* v_userDataBytes_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_userData_1048_ = lean_ctor_get(v_writer_1047_, 0);
v_outputData_1049_ = lean_ctor_get(v_writer_1047_, 1);
v_knownSize_1050_ = lean_ctor_get(v_writer_1047_, 3);
v_messageHead_1051_ = lean_ctor_get(v_writer_1047_, 4);
v_sentMessage_1052_ = lean_ctor_get_uint8(v_writer_1047_, sizeof(void*)*6);
v_userClosedBody_1053_ = lean_ctor_get_uint8(v_writer_1047_, sizeof(void*)*6 + 1);
v_omitBody_1054_ = lean_ctor_get_uint8(v_writer_1047_, sizeof(void*)*6 + 2);
v_userDataBytes_1055_ = lean_ctor_get(v_writer_1047_, 5);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_writer_1047_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_writer_1047_, 2);
lean_dec(v_unused_1063_);
v___x_1057_ = v_writer_1047_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_userDataBytes_1055_);
lean_inc(v_messageHead_1051_);
lean_inc(v_knownSize_1050_);
lean_inc(v_outputData_1049_);
lean_inc(v_userData_1048_);
lean_dec(v_writer_1047_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 2, v_state_1046_);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_userData_1048_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_outputData_1049_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_state_1046_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_knownSize_1050_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_messageHead_1051_);
lean_ctor_set(v_reuseFailAlloc_1061_, 5, v_userDataBytes_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*6, v_sentMessage_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*6 + 1, v_userClosedBody_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*6 + 2, v_omitBody_1054_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_1064_, lean_object* v_state_1065_, lean_object* v_writer_1066_){
_start:
{
lean_object* v_userData_1067_; lean_object* v_outputData_1068_; lean_object* v_knownSize_1069_; lean_object* v_messageHead_1070_; uint8_t v_sentMessage_1071_; uint8_t v_userClosedBody_1072_; uint8_t v_omitBody_1073_; lean_object* v_userDataBytes_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_userData_1067_ = lean_ctor_get(v_writer_1066_, 0);
v_outputData_1068_ = lean_ctor_get(v_writer_1066_, 1);
v_knownSize_1069_ = lean_ctor_get(v_writer_1066_, 3);
v_messageHead_1070_ = lean_ctor_get(v_writer_1066_, 4);
v_sentMessage_1071_ = lean_ctor_get_uint8(v_writer_1066_, sizeof(void*)*6);
v_userClosedBody_1072_ = lean_ctor_get_uint8(v_writer_1066_, sizeof(void*)*6 + 1);
v_omitBody_1073_ = lean_ctor_get_uint8(v_writer_1066_, sizeof(void*)*6 + 2);
v_userDataBytes_1074_ = lean_ctor_get(v_writer_1066_, 5);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_writer_1066_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_writer_1066_, 2);
lean_dec(v_unused_1082_);
v___x_1076_ = v_writer_1066_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_userDataBytes_1074_);
lean_inc(v_messageHead_1070_);
lean_inc(v_knownSize_1069_);
lean_inc(v_outputData_1068_);
lean_inc(v_userData_1067_);
lean_dec(v_writer_1066_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 2, v_state_1065_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_userData_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_outputData_1068_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_state_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_knownSize_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_messageHead_1070_);
lean_ctor_set(v_reuseFailAlloc_1080_, 5, v_userDataBytes_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*6, v_sentMessage_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*6 + 1, v_userClosedBody_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*6 + 2, v_omitBody_1073_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_1083_, lean_object* v_state_1084_, lean_object* v_writer_1085_){
_start:
{
uint8_t v_dir_boxed_1086_; lean_object* v_res_1087_; 
v_dir_boxed_1086_ = lean_unbox(v_dir_1083_);
v_res_1087_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1086_, v_state_1084_, v_writer_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1088_, lean_object* v_messageHead_1089_, lean_object* v_writer_1090_){
_start:
{
lean_object* v_userData_1091_; lean_object* v_outputData_1092_; lean_object* v_state_1093_; lean_object* v_knownSize_1094_; lean_object* v_messageHead_1095_; uint8_t v_sentMessage_1096_; uint8_t v_userClosedBody_1097_; uint8_t v_omitBody_1098_; lean_object* v_userDataBytes_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1112_; 
v_userData_1091_ = lean_ctor_get(v_writer_1090_, 0);
v_outputData_1092_ = lean_ctor_get(v_writer_1090_, 1);
v_state_1093_ = lean_ctor_get(v_writer_1090_, 2);
v_knownSize_1094_ = lean_ctor_get(v_writer_1090_, 3);
v_messageHead_1095_ = lean_ctor_get(v_writer_1090_, 4);
v_sentMessage_1096_ = lean_ctor_get_uint8(v_writer_1090_, sizeof(void*)*6);
v_userClosedBody_1097_ = lean_ctor_get_uint8(v_writer_1090_, sizeof(void*)*6 + 1);
v_omitBody_1098_ = lean_ctor_get_uint8(v_writer_1090_, sizeof(void*)*6 + 2);
v_userDataBytes_1099_ = lean_ctor_get(v_writer_1090_, 5);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_writer_1090_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1101_ = v_writer_1090_;
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_userDataBytes_1099_);
lean_inc(v_messageHead_1095_);
lean_inc(v_knownSize_1094_);
lean_inc(v_state_1093_);
lean_inc(v_outputData_1092_);
lean_inc(v_userData_1091_);
lean_dec(v_writer_1090_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___y_1104_; 
if (v_dir_1088_ == 0)
{
uint8_t v___x_1110_; 
v___x_1110_ = 1;
v___y_1104_ = v___x_1110_;
goto v___jp_1103_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = 0;
v___y_1104_ = v___x_1111_;
goto v___jp_1103_;
}
v___jp_1103_:
{
lean_object* v___x_6__overap_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_6__overap_1105_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1104_);
v___x_1106_ = lean_apply_2(v___x_6__overap_1105_, v_outputData_1092_, v_messageHead_1089_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1106_);
v___x_1108_ = v___x_1101_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_userData_1091_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_state_1093_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_knownSize_1094_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_messageHead_1095_);
lean_ctor_set(v_reuseFailAlloc_1109_, 5, v_userDataBytes_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*6, v_sentMessage_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*6 + 1, v_userClosedBody_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*6 + 2, v_omitBody_1098_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1113_, lean_object* v_messageHead_1114_, lean_object* v_writer_1115_){
_start:
{
uint8_t v_dir_boxed_1116_; lean_object* v_res_1117_; 
v_dir_boxed_1116_ = lean_unbox(v_dir_1113_);
v_res_1117_ = l___private_Std_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1116_, v_messageHead_1114_, v_writer_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(lean_object* v_a_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v_key_1120_; lean_object* v_value_1121_; lean_object* v_tail_1122_; uint8_t v___x_1123_; 
v_key_1120_ = lean_ctor_get(v_x_1119_, 0);
v_value_1121_ = lean_ctor_get(v_x_1119_, 1);
v_tail_1122_ = lean_ctor_get(v_x_1119_, 2);
v___x_1123_ = lean_string_dec_eq(v_key_1120_, v_a_1118_);
if (v___x_1123_ == 0)
{
v_x_1119_ = v_tail_1122_;
goto _start;
}
else
{
lean_inc(v_value_1121_);
return v_value_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg___boxed(lean_object* v_a_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1125_, v_x_1126_);
lean_dec(v_x_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(lean_object* v_m_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_buckets_1130_; lean_object* v___x_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v___x_1134_; uint64_t v_fold_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; uint64_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_buckets_1130_ = lean_ctor_get(v_m_1128_, 1);
v___x_1131_ = lean_array_get_size(v_buckets_1130_);
v___x_1132_ = lean_string_hash(v_a_1129_);
v___x_1133_ = 32ULL;
v___x_1134_ = lean_uint64_shift_right(v___x_1132_, v___x_1133_);
v_fold_1135_ = lean_uint64_xor(v___x_1132_, v___x_1134_);
v___x_1136_ = 16ULL;
v___x_1137_ = lean_uint64_shift_right(v_fold_1135_, v___x_1136_);
v___x_1138_ = lean_uint64_xor(v_fold_1135_, v___x_1137_);
v___x_1139_ = lean_uint64_to_usize(v___x_1138_);
v___x_1140_ = lean_usize_of_nat(v___x_1131_);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_sub(v___x_1140_, v___x_1141_);
v___x_1143_ = lean_usize_land(v___x_1139_, v___x_1142_);
v___x_1144_ = lean_array_uget_borrowed(v_buckets_1130_, v___x_1143_);
v___x_1145_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1129_, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg___boxed(lean_object* v_m_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1146_, v_a_1147_);
lean_dec_ref(v_a_1147_);
lean_dec_ref(v_m_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
uint8_t v___x_1151_; 
v___x_1151_ = 0;
return v___x_1151_;
}
else
{
lean_object* v_key_1152_; lean_object* v_tail_1153_; uint8_t v___x_1154_; 
v_key_1152_ = lean_ctor_get(v_x_1150_, 0);
v_tail_1153_ = lean_ctor_get(v_x_1150_, 2);
v___x_1154_ = lean_string_dec_eq(v_key_1152_, v_a_1149_);
if (v___x_1154_ == 0)
{
v_x_1150_ = v_tail_1153_;
goto _start;
}
else
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec_ref(v_a_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_buckets_1162_; lean_object* v___x_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; uint64_t v_fold_1167_; uint64_t v___x_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_buckets_1162_ = lean_ctor_get(v_m_1160_, 1);
v___x_1163_ = lean_array_get_size(v_buckets_1162_);
v___x_1164_ = lean_string_hash(v_a_1161_);
v___x_1165_ = 32ULL;
v___x_1166_ = lean_uint64_shift_right(v___x_1164_, v___x_1165_);
v_fold_1167_ = lean_uint64_xor(v___x_1164_, v___x_1166_);
v___x_1168_ = 16ULL;
v___x_1169_ = lean_uint64_shift_right(v_fold_1167_, v___x_1168_);
v___x_1170_ = lean_uint64_xor(v_fold_1167_, v___x_1169_);
v___x_1171_ = lean_uint64_to_usize(v___x_1170_);
v___x_1172_ = lean_usize_of_nat(v___x_1163_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_sub(v___x_1172_, v___x_1173_);
v___x_1175_ = lean_usize_land(v___x_1171_, v___x_1174_);
v___x_1176_ = lean_array_uget_borrowed(v_buckets_1162_, v___x_1175_);
v___x_1177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1161_, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1178_, lean_object* v_a_1179_){
_start:
{
uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_res_1180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1178_, v_a_1179_);
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_m_1178_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(lean_object* v_s_1182_, lean_object* v_p_1183_){
_start:
{
lean_object* v___y_1185_; lean_object* v___y_1186_; uint32_t v___y_1190_; lean_object* v___x_1202_; uint8_t v_decide_1203_; 
v___x_1202_ = lean_string_utf8_byte_size(v_s_1182_);
v_decide_1203_ = lean_nat_dec_eq(v_p_1183_, v___x_1202_);
if (v_decide_1203_ == 0)
{
uint32_t v___x_1204_; uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1204_ = lean_string_utf8_get_fast(v_s_1182_, v_p_1183_);
v___x_1205_ = 65;
v___x_1206_ = lean_uint32_dec_le(v___x_1205_, v___x_1204_);
if (v___x_1206_ == 0)
{
v___y_1190_ = v___x_1204_;
goto v___jp_1189_;
}
else
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 90;
v___x_1208_ = lean_uint32_dec_le(v___x_1204_, v___x_1207_);
if (v___x_1208_ == 0)
{
v___y_1190_ = v___x_1204_;
goto v___jp_1189_;
}
else
{
uint32_t v___x_1209_; uint32_t v___x_1210_; 
v___x_1209_ = 32;
v___x_1210_ = lean_uint32_add(v___x_1204_, v___x_1209_);
v___y_1190_ = v___x_1210_;
goto v___jp_1189_;
}
}
}
else
{
lean_dec(v_p_1183_);
return v_s_1182_;
}
v___jp_1184_:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_nat_add(v_p_1183_, v___y_1186_);
lean_dec(v_p_1183_);
v_s_1182_ = v___y_1185_;
v_p_1183_ = v___x_1187_;
goto _start;
}
v___jp_1189_:
{
lean_object* v___x_1191_; uint32_t v___x_1192_; uint8_t v___x_1193_; 
lean_inc(v_p_1183_);
v___x_1191_ = lean_string_utf8_set(v_s_1182_, v_p_1183_, v___y_1190_);
v___x_1192_ = 127;
v___x_1193_ = lean_uint32_dec_le(v___y_1190_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 2047;
v___x_1195_ = lean_uint32_dec_le(v___y_1190_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 65535;
v___x_1197_ = lean_uint32_dec_le(v___y_1190_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_unsigned_to_nat(4u);
v___y_1185_ = v___x_1191_;
v___y_1186_ = v___x_1198_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_unsigned_to_nat(3u);
v___y_1185_ = v___x_1191_;
v___y_1186_ = v___x_1199_;
goto v___jp_1184_;
}
}
else
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_unsigned_to_nat(2u);
v___y_1185_ = v___x_1191_;
v___y_1186_ = v___x_1200_;
goto v___jp_1184_;
}
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_unsigned_to_nat(1u);
v___y_1185_ = v___x_1191_;
v___y_1186_ = v___x_1201_;
goto v___jp_1184_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1212_, lean_object* v_writer_1213_){
_start:
{
uint8_t v___y_1215_; 
if (v_dir_1212_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 1;
v___y_1215_ = v___x_1232_;
goto v___jp_1214_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = 0;
v___y_1215_ = v___x_1233_;
goto v___jp_1214_;
}
v___jp_1214_:
{
lean_object* v_messageHead_1216_; lean_object* v___x_1217_; lean_object* v_entries_1218_; lean_object* v_indexes_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_messageHead_1216_ = lean_ctor_get(v_writer_1213_, 4);
v___x_1217_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1215_, v_messageHead_1216_);
v_entries_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_entries_1218_);
v_indexes_1219_ = lean_ctor_get(v___x_1217_, 1);
lean_inc_ref(v_indexes_1219_);
lean_dec_ref(v___x_1217_);
v___x_1220_ = l_Std_Http_Header_Name_connection;
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint8_t v___x_1222_; 
lean_dec_ref(v_indexes_1219_);
lean_dec_ref(v_entries_1218_);
v___x_1222_ = 1;
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_entry_1225_; lean_object* v___x_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_indexes_1219_, v___x_1220_);
lean_dec_ref(v_indexes_1219_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v_entry_1225_ = lean_array_fget(v___x_1223_, v___x_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_array_fget(v_entries_1218_, v_entry_1225_);
lean_dec(v_entry_1225_);
lean_dec_ref(v_entries_1218_);
v_snd_1227_ = lean_ctor_get(v___x_1226_, 1);
lean_inc(v_snd_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__2(v_snd_1227_, v___x_1224_);
v___x_1229_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___x_1230_ = lean_string_dec_eq(v___x_1228_, v___x_1229_);
lean_dec_ref(v___x_1228_);
if (v___x_1230_ == 0)
{
return v___x_1221_;
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = 0;
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1234_, lean_object* v_writer_1235_){
_start:
{
uint8_t v_dir_boxed_1236_; uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_dir_boxed_1236_ = lean_unbox(v_dir_1234_);
v_res_1237_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1236_, v_writer_1235_);
lean_dec_ref(v_writer_1235_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1240_, v_a_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1243_, v_m_1244_, v_a_1245_);
lean_dec_ref(v_a_1245_);
lean_dec_ref(v_m_1244_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_00_u03b2_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_, lean_object* v_hma_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___redArg(v_m_1249_, v_a_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_m_1254_, lean_object* v_a_1255_, lean_object* v_hma_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_00_u03b2_1253_, v_m_1254_, v_a_1255_, v_hma_1256_);
lean_dec_ref(v_a_1255_);
lean_dec_ref(v_m_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1258_, lean_object* v_a_1259_, lean_object* v_x_1260_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1259_, v_x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1262_, lean_object* v_a_1263_, lean_object* v_x_1264_){
_start:
{
uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_res_1265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1262_, v_a_1263_, v_x_1264_);
lean_dec(v_x_1264_);
lean_dec_ref(v_a_1263_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(lean_object* v_00_u03b2_1267_, lean_object* v_a_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___redArg(v_a_1268_, v_x_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1272_, lean_object* v_a_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1_spec__2(v_00_u03b2_1272_, v_a_1273_, v_x_1274_, v_x_1275_);
lean_dec(v_x_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1277_){
_start:
{
lean_object* v_userData_1278_; lean_object* v_outputData_1279_; lean_object* v_knownSize_1280_; lean_object* v_messageHead_1281_; uint8_t v_sentMessage_1282_; uint8_t v_userClosedBody_1283_; uint8_t v_omitBody_1284_; lean_object* v_userDataBytes_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_userData_1278_ = lean_ctor_get(v_writer_1277_, 0);
v_outputData_1279_ = lean_ctor_get(v_writer_1277_, 1);
v_knownSize_1280_ = lean_ctor_get(v_writer_1277_, 3);
v_messageHead_1281_ = lean_ctor_get(v_writer_1277_, 4);
v_sentMessage_1282_ = lean_ctor_get_uint8(v_writer_1277_, sizeof(void*)*6);
v_userClosedBody_1283_ = lean_ctor_get_uint8(v_writer_1277_, sizeof(void*)*6 + 1);
v_omitBody_1284_ = lean_ctor_get_uint8(v_writer_1277_, sizeof(void*)*6 + 2);
v_userDataBytes_1285_ = lean_ctor_get(v_writer_1277_, 5);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_writer_1277_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v_writer_1277_, 2);
lean_dec(v_unused_1294_);
v___x_1287_ = v_writer_1277_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_userDataBytes_1285_);
lean_inc(v_messageHead_1281_);
lean_inc(v_knownSize_1280_);
lean_inc(v_outputData_1279_);
lean_inc(v_userData_1278_);
lean_dec(v_writer_1277_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_box(7);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 2, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_userData_1278_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_outputData_1279_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_knownSize_1280_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_messageHead_1281_);
lean_ctor_set(v_reuseFailAlloc_1292_, 5, v_userDataBytes_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*6, v_sentMessage_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*6 + 1, v_userClosedBody_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*6 + 2, v_omitBody_1284_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1295_, lean_object* v_writer_1296_){
_start:
{
lean_object* v_userData_1297_; lean_object* v_outputData_1298_; lean_object* v_knownSize_1299_; lean_object* v_messageHead_1300_; uint8_t v_sentMessage_1301_; uint8_t v_userClosedBody_1302_; uint8_t v_omitBody_1303_; lean_object* v_userDataBytes_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
v_userData_1297_ = lean_ctor_get(v_writer_1296_, 0);
v_outputData_1298_ = lean_ctor_get(v_writer_1296_, 1);
v_knownSize_1299_ = lean_ctor_get(v_writer_1296_, 3);
v_messageHead_1300_ = lean_ctor_get(v_writer_1296_, 4);
v_sentMessage_1301_ = lean_ctor_get_uint8(v_writer_1296_, sizeof(void*)*6);
v_userClosedBody_1302_ = lean_ctor_get_uint8(v_writer_1296_, sizeof(void*)*6 + 1);
v_omitBody_1303_ = lean_ctor_get_uint8(v_writer_1296_, sizeof(void*)*6 + 2);
v_userDataBytes_1304_ = lean_ctor_get(v_writer_1296_, 5);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_writer_1296_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_writer_1296_, 2);
lean_dec(v_unused_1313_);
v___x_1306_ = v_writer_1296_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_userDataBytes_1304_);
lean_inc(v_messageHead_1300_);
lean_inc(v_knownSize_1299_);
lean_inc(v_outputData_1298_);
lean_inc(v_userData_1297_);
lean_dec(v_writer_1296_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_box(7);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 2, v___x_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_userData_1297_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_outputData_1298_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_knownSize_1299_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_messageHead_1300_);
lean_ctor_set(v_reuseFailAlloc_1311_, 5, v_userDataBytes_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*6, v_sentMessage_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*6 + 1, v_userClosedBody_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*6 + 2, v_omitBody_1303_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1314_, lean_object* v_writer_1315_){
_start:
{
uint8_t v_dir_boxed_1316_; lean_object* v_res_1317_; 
v_dir_boxed_1316_ = lean_unbox(v_dir_1314_);
v_res_1317_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1316_, v_writer_1315_);
return v_res_1317_;
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
