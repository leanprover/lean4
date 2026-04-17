// Lean compiler output
// Module: Std.Internal.Http.Protocol.H1.Writer
// Imports: public import Std.Time public import Std.Internal.Http.Data public import Std.Internal.Http.Internal public import Std.Internal.Http.Protocol.H1.Parser public import Std.Internal.Http.Protocol.H1.Config public import Std.Internal.Http.Protocol.H1.Message public import Std.Internal.Http.Protocol.H1.Error
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
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_Body_instReprLength_repr(lean_object*, lean_object*);
uint8_t l_Std_Http_Body_instBEqLength_beq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBody_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Writer.State.complete"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__6_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Writer.State.closed"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10;
static lean_once_cell_t l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11;
static const lean_string_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Std.Http.Protocol.H1.Writer.State.writingBody"};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14_value;
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object*, lean_object*, lean_object*);
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
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Http_Protocol_H1_Writer_State_ctorIdx(v_x_8_);
lean_dec(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
if (lean_obj_tag(v_t_10_) == 3)
{
lean_object* v_mode_12_; lean_object* v___x_13_; 
v_mode_12_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_mode_12_);
lean_dec_ref(v_t_10_);
v___x_13_ = lean_apply_1(v_k_11_, v_mode_12_);
return v___x_13_;
}
else
{
lean_dec(v_t_10_);
return v_k_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim___redArg(lean_object* v_t_26_, lean_object* v_pending_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_26_, v_pending_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_pending_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_pending_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_30_, v_pending_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim___redArg(lean_object* v_t_34_, lean_object* v_waitingHeaders_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_34_, v_waitingHeaders_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingHeaders_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_waitingHeaders_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_38_, v_waitingHeaders_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim___redArg(lean_object* v_t_42_, lean_object* v_waitingForFlush_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_42_, v_waitingForFlush_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_waitingForFlush_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_waitingForFlush_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_46_, v_waitingForFlush_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBody_elim___redArg(lean_object* v_t_50_, lean_object* v_writingBody_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_50_, v_writingBody_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_writingBody_elim(lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_writingBody_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_54_, v_writingBody_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim___redArg(lean_object* v_t_58_, lean_object* v_complete_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_58_, v_complete_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_complete_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_complete_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_62_, v_complete_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim___redArg(lean_object* v_t_66_, lean_object* v_closed_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_66_, v_closed_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_State_closed_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_closed_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_Http_Protocol_H1_Writer_State_ctorElim___redArg(v_t_70_, v_closed_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(2u);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
lean_object* v___y_104_; lean_object* v___y_111_; lean_object* v___y_118_; lean_object* v___y_125_; lean_object* v___y_132_; 
switch(lean_obj_tag(v_x_101_))
{
case 0:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1024u);
v___x_139_ = lean_nat_dec_le(v___x_138_, v_prec_102_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10);
v___y_118_ = v___x_140_;
goto v___jp_117_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11);
v___y_118_ = v___x_141_;
goto v___jp_117_;
}
}
case 1:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_102_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10);
v___y_111_ = v___x_144_;
goto v___jp_110_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11);
v___y_111_ = v___x_145_;
goto v___jp_110_;
}
}
case 2:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1024u);
v___x_147_ = lean_nat_dec_le(v___x_146_, v_prec_102_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10);
v___y_104_ = v___x_148_;
goto v___jp_103_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11);
v___y_104_ = v___x_149_;
goto v___jp_103_;
}
}
case 3:
{
lean_object* v_mode_150_; lean_object* v___y_152_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_mode_150_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_mode_150_);
lean_dec_ref(v_x_101_);
v___x_161_ = lean_unsigned_to_nat(1024u);
v___x_162_ = lean_nat_dec_le(v___x_161_, v_prec_102_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10);
v___y_152_ = v___x_163_;
goto v___jp_151_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11);
v___y_152_ = v___x_164_;
goto v___jp_151_;
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_153_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__14));
v___x_154_ = lean_unsigned_to_nat(1024u);
v___x_155_ = l_Std_Http_Body_instReprLength_repr(v_mode_150_, v___x_154_);
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_153_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
lean_inc(v___y_152_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_152_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = 0;
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_prec_102_);
return v___x_160_;
}
}
case 4:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1024u);
v___x_166_ = lean_nat_dec_le(v___x_165_, v_prec_102_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10);
v___y_125_ = v___x_167_;
goto v___jp_124_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11);
v___y_125_ = v___x_168_;
goto v___jp_124_;
}
}
default: 
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1024u);
v___x_170_ = lean_nat_dec_le(v___x_169_, v_prec_102_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__10);
v___y_132_ = v___x_171_;
goto v___jp_131_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11, &l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11_once, _init_l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__11);
v___y_132_ = v___x_172_;
goto v___jp_131_;
}
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__1));
lean_inc(v___y_104_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___y_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
v___x_109_ = l_Repr_addAppParen(v___x_108_, v_prec_102_);
return v___x_109_;
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__3));
lean_inc(v___y_111_);
v___x_113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_113_, 0, v___y_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = 0;
v___x_115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
v___x_116_ = l_Repr_addAppParen(v___x_115_, v_prec_102_);
return v___x_116_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__5));
lean_inc(v___y_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___y_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_121_);
v___x_123_ = l_Repr_addAppParen(v___x_122_, v_prec_102_);
return v___x_123_;
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__7));
lean_inc(v___y_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = l_Repr_addAppParen(v___x_129_, v_prec_102_);
return v___x_130_;
}
v___jp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_instReprState_repr___closed__9));
lean_inc(v___y_132_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___y_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = 0;
v___x_136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_135_);
v___x_137_ = l_Repr_addAppParen(v___x_136_, v_prec_102_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instReprState_repr___boxed(lean_object* v_x_173_, lean_object* v_prec_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Http_Protocol_H1_Writer_instReprState_repr(v_x_173_, v_prec_174_);
lean_dec(v_prec_174_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
switch(lean_obj_tag(v_x_178_))
{
case 0:
{
if (lean_obj_tag(v_x_179_) == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 1;
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
case 1:
{
if (lean_obj_tag(v_x_179_) == 1)
{
uint8_t v___x_182_; 
v___x_182_ = 1;
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
}
case 2:
{
if (lean_obj_tag(v_x_179_) == 2)
{
uint8_t v___x_184_; 
v___x_184_ = 1;
return v___x_184_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
case 3:
{
if (lean_obj_tag(v_x_179_) == 3)
{
lean_object* v_mode_186_; lean_object* v_mode_187_; uint8_t v___x_188_; 
v_mode_186_ = lean_ctor_get(v_x_178_, 0);
v_mode_187_ = lean_ctor_get(v_x_179_, 0);
v___x_188_ = l_Std_Http_Body_instBEqLength_beq(v_mode_186_, v_mode_187_);
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
case 4:
{
if (lean_obj_tag(v_x_179_) == 4)
{
uint8_t v___x_190_; 
v___x_190_ = 1;
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
}
default: 
{
if (lean_obj_tag(v_x_179_) == 5)
{
uint8_t v___x_192_; 
v___x_192_ = 1;
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_instBEqState_beq___boxed(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_x_194_, v_x_195_);
lean_dec(v_x_195_);
lean_dec(v_x_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(lean_object* v_writer_200_){
_start:
{
lean_object* v_state_201_; 
v_state_201_ = lean_ctor_get(v_writer_200_, 2);
switch(lean_obj_tag(v_state_201_))
{
case 5:
{
uint8_t v___x_202_; 
v___x_202_ = 1;
return v___x_202_;
}
case 4:
{
uint8_t v___x_203_; 
v___x_203_ = 1;
return v___x_203_;
}
default: 
{
uint8_t v_userClosedBody_204_; 
v_userClosedBody_204_ = lean_ctor_get_uint8(v_writer_200_, sizeof(void*)*6 + 1);
return v_userClosedBody_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg___boxed(lean_object* v_writer_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData___redArg(v_writer_205_);
lean_dec_ref(v_writer_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_noMoreUserData(uint8_t v_dir_208_, lean_object* v_writer_209_){
_start:
{
lean_object* v_state_210_; 
v_state_210_ = lean_ctor_get(v_writer_209_, 2);
switch(lean_obj_tag(v_state_210_))
{
case 5:
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
case 4:
{
uint8_t v___x_212_; 
v___x_212_ = 1;
return v___x_212_;
}
default: 
{
uint8_t v_userClosedBody_213_; 
v_userClosedBody_213_ = lean_ctor_get_uint8(v_writer_209_, sizeof(void*)*6 + 1);
return v_userClosedBody_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_noMoreUserData___boxed(lean_object* v_dir_214_, lean_object* v_writer_215_){
_start:
{
uint8_t v_dir_boxed_216_; uint8_t v_res_217_; lean_object* v_r_218_; 
v_dir_boxed_216_ = lean_unbox(v_dir_214_);
v_res_217_ = l_Std_Http_Protocol_H1_Writer_noMoreUserData(v_dir_boxed_216_, v_writer_215_);
lean_dec_ref(v_writer_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed___redArg(lean_object* v_writer_219_){
_start:
{
lean_object* v_state_220_; 
v_state_220_ = lean_ctor_get(v_writer_219_, 2);
if (lean_obj_tag(v_state_220_) == 5)
{
uint8_t v___x_221_; 
v___x_221_ = 1;
return v___x_221_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___redArg___boxed(lean_object* v_writer_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Std_Http_Protocol_H1_Writer_isClosed___redArg(v_writer_223_);
lean_dec_ref(v_writer_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isClosed(uint8_t v_dir_226_, lean_object* v_writer_227_){
_start:
{
lean_object* v_state_228_; 
v_state_228_ = lean_ctor_get(v_writer_227_, 2);
if (lean_obj_tag(v_state_228_) == 5)
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
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isClosed___boxed(lean_object* v_dir_231_, lean_object* v_writer_232_){
_start:
{
uint8_t v_dir_boxed_233_; uint8_t v_res_234_; lean_object* v_r_235_; 
v_dir_boxed_233_ = lean_unbox(v_dir_231_);
v_res_234_ = l_Std_Http_Protocol_H1_Writer_isClosed(v_dir_boxed_233_, v_writer_232_);
lean_dec_ref(v_writer_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete___redArg(lean_object* v_writer_236_){
_start:
{
lean_object* v_state_237_; 
v_state_237_ = lean_ctor_get(v_writer_236_, 2);
if (lean_obj_tag(v_state_237_) == 4)
{
uint8_t v___x_238_; 
v___x_238_ = 1;
return v___x_238_;
}
else
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___redArg___boxed(lean_object* v_writer_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_Http_Protocol_H1_Writer_isComplete___redArg(v_writer_240_);
lean_dec_ref(v_writer_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_isComplete(uint8_t v_dir_243_, lean_object* v_writer_244_){
_start:
{
lean_object* v_state_245_; 
v_state_245_ = lean_ctor_get(v_writer_244_, 2);
if (lean_obj_tag(v_state_245_) == 4)
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
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_isComplete___boxed(lean_object* v_dir_248_, lean_object* v_writer_249_){
_start:
{
uint8_t v_dir_boxed_250_; uint8_t v_res_251_; lean_object* v_r_252_; 
v_dir_boxed_250_ = lean_unbox(v_dir_248_);
v_res_251_ = l_Std_Http_Protocol_H1_Writer_isComplete(v_dir_boxed_250_, v_writer_249_);
lean_dec_ref(v_writer_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(lean_object* v_writer_253_){
_start:
{
lean_object* v_state_254_; 
v_state_254_ = lean_ctor_get(v_writer_253_, 2);
switch(lean_obj_tag(v_state_254_))
{
case 1:
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
case 2:
{
uint8_t v___x_256_; 
v___x_256_ = 1;
return v___x_256_;
}
case 3:
{
uint8_t v_userClosedBody_257_; 
v_userClosedBody_257_ = lean_ctor_get_uint8(v_writer_253_, sizeof(void*)*6 + 1);
if (v_userClosedBody_257_ == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 1;
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
default: 
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg___boxed(lean_object* v_writer_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_Http_Protocol_H1_Writer_canAcceptData___redArg(v_writer_261_);
lean_dec_ref(v_writer_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_canAcceptData(uint8_t v_dir_264_, lean_object* v_writer_265_){
_start:
{
lean_object* v_state_266_; 
v_state_266_ = lean_ctor_get(v_writer_265_, 2);
switch(lean_obj_tag(v_state_266_))
{
case 1:
{
uint8_t v___x_267_; 
v___x_267_ = 1;
return v___x_267_;
}
case 2:
{
uint8_t v___x_268_; 
v___x_268_ = 1;
return v___x_268_;
}
case 3:
{
uint8_t v_userClosedBody_269_; 
v_userClosedBody_269_ = lean_ctor_get_uint8(v_writer_265_, sizeof(void*)*6 + 1);
if (v_userClosedBody_269_ == 0)
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
default: 
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_canAcceptData___boxed(lean_object* v_dir_273_, lean_object* v_writer_274_){
_start:
{
uint8_t v_dir_boxed_275_; uint8_t v_res_276_; lean_object* v_r_277_; 
v_dir_boxed_275_ = lean_unbox(v_dir_273_);
v_res_276_ = l_Std_Http_Protocol_H1_Writer_canAcceptData(v_dir_boxed_275_, v_writer_274_);
lean_dec_ref(v_writer_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___redArg(lean_object* v_writer_278_){
_start:
{
lean_object* v_userData_279_; lean_object* v_outputData_280_; lean_object* v_state_281_; lean_object* v_knownSize_282_; lean_object* v_messageHead_283_; uint8_t v_sentMessage_284_; uint8_t v_omitBody_285_; lean_object* v_userDataBytes_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_userData_279_ = lean_ctor_get(v_writer_278_, 0);
v_outputData_280_ = lean_ctor_get(v_writer_278_, 1);
v_state_281_ = lean_ctor_get(v_writer_278_, 2);
v_knownSize_282_ = lean_ctor_get(v_writer_278_, 3);
v_messageHead_283_ = lean_ctor_get(v_writer_278_, 4);
v_sentMessage_284_ = lean_ctor_get_uint8(v_writer_278_, sizeof(void*)*6);
v_omitBody_285_ = lean_ctor_get_uint8(v_writer_278_, sizeof(void*)*6 + 2);
v_userDataBytes_286_ = lean_ctor_get(v_writer_278_, 5);
v_isSharedCheck_294_ = !lean_is_exclusive(v_writer_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_288_ = v_writer_278_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_userDataBytes_286_);
lean_inc(v_messageHead_283_);
lean_inc(v_knownSize_282_);
lean_inc(v_state_281_);
lean_inc(v_outputData_280_);
lean_inc(v_userData_279_);
lean_dec(v_writer_278_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; lean_object* v___x_292_; 
v___x_290_ = 1;
if (v_isShared_289_ == 0)
{
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_userData_279_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_outputData_280_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_state_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_knownSize_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_messageHead_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v_userDataBytes_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*6, v_sentMessage_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*6 + 2, v_omitBody_285_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*6 + 1, v___x_290_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody(uint8_t v_dir_295_, lean_object* v_writer_296_){
_start:
{
lean_object* v_userData_297_; lean_object* v_outputData_298_; lean_object* v_state_299_; lean_object* v_knownSize_300_; lean_object* v_messageHead_301_; uint8_t v_sentMessage_302_; uint8_t v_omitBody_303_; lean_object* v_userDataBytes_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
v_userData_297_ = lean_ctor_get(v_writer_296_, 0);
v_outputData_298_ = lean_ctor_get(v_writer_296_, 1);
v_state_299_ = lean_ctor_get(v_writer_296_, 2);
v_knownSize_300_ = lean_ctor_get(v_writer_296_, 3);
v_messageHead_301_ = lean_ctor_get(v_writer_296_, 4);
v_sentMessage_302_ = lean_ctor_get_uint8(v_writer_296_, sizeof(void*)*6);
v_omitBody_303_ = lean_ctor_get_uint8(v_writer_296_, sizeof(void*)*6 + 2);
v_userDataBytes_304_ = lean_ctor_get(v_writer_296_, 5);
v_isSharedCheck_312_ = !lean_is_exclusive(v_writer_296_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v_writer_296_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_userDataBytes_304_);
lean_inc(v_messageHead_301_);
lean_inc(v_knownSize_300_);
lean_inc(v_state_299_);
lean_inc(v_outputData_298_);
lean_inc(v_userData_297_);
lean_dec(v_writer_296_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; lean_object* v___x_310_; 
v___x_308_ = 1;
if (v_isShared_307_ == 0)
{
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_userData_297_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_outputData_298_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_state_299_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_knownSize_300_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_messageHead_301_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_userDataBytes_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*6, v_sentMessage_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*6 + 2, v_omitBody_303_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*6 + 1, v___x_308_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_closeBody___boxed(lean_object* v_dir_313_, lean_object* v_writer_314_){
_start:
{
uint8_t v_dir_boxed_315_; lean_object* v_res_316_; 
v_dir_boxed_315_ = lean_unbox(v_dir_313_);
v_res_316_ = l_Std_Http_Protocol_H1_Writer_closeBody(v_dir_boxed_315_, v_writer_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(lean_object* v_writer_317_){
_start:
{
lean_object* v_knownSize_318_; 
v_knownSize_318_ = lean_ctor_get(v_writer_317_, 3);
if (lean_obj_tag(v_knownSize_318_) == 1)
{
lean_object* v_val_319_; 
v_val_319_ = lean_ctor_get(v_knownSize_318_, 0);
lean_inc(v_val_319_);
return v_val_319_;
}
else
{
uint8_t v_userClosedBody_320_; 
v_userClosedBody_320_ = lean_ctor_get_uint8(v_writer_317_, sizeof(void*)*6 + 1);
if (v_userClosedBody_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_box(0);
return v___x_321_;
}
else
{
lean_object* v_userDataBytes_322_; lean_object* v___x_323_; 
v_userDataBytes_322_ = lean_ctor_get(v_writer_317_, 5);
lean_inc(v_userDataBytes_322_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_userDataBytes_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg___boxed(lean_object* v_writer_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_324_);
lean_dec_ref(v_writer_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode(uint8_t v_dir_326_, lean_object* v_writer_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode___redArg(v_writer_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_determineTransferMode___boxed(lean_object* v_dir_329_, lean_object* v_writer_330_){
_start:
{
uint8_t v_dir_boxed_331_; lean_object* v_res_332_; 
v_dir_boxed_331_ = lean_unbox(v_dir_329_);
v_res_332_ = l_Std_Http_Protocol_H1_Writer_determineTransferMode(v_dir_boxed_331_, v_writer_330_);
lean_dec_ref(v_writer_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(lean_object* v_x1_333_, lean_object* v_x2_334_){
_start:
{
lean_object* v_data_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_data_335_ = lean_ctor_get(v_x2_334_, 0);
v___x_336_ = lean_byte_array_size(v_data_335_);
v___x_337_ = lean_nat_add(v_x1_333_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0___boxed(lean_object* v_x1_338_, lean_object* v_x2_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Http_Protocol_H1_Writer_addUserData___redArg___lam__0(v_x1_338_, v_x2_339_);
lean_dec_ref(v_x2_339_);
lean_dec(v_x1_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___redArg(lean_object* v_data_361_, lean_object* v_writer_362_){
_start:
{
lean_object* v_userData_363_; lean_object* v_outputData_364_; lean_object* v_state_365_; lean_object* v_knownSize_366_; lean_object* v_messageHead_367_; uint8_t v_sentMessage_368_; uint8_t v_userClosedBody_369_; uint8_t v_omitBody_370_; lean_object* v_userDataBytes_371_; lean_object* v___y_373_; lean_object* v___f_377_; 
v_userData_363_ = lean_ctor_get(v_writer_362_, 0);
v_outputData_364_ = lean_ctor_get(v_writer_362_, 1);
v_state_365_ = lean_ctor_get(v_writer_362_, 2);
v_knownSize_366_ = lean_ctor_get(v_writer_362_, 3);
v_messageHead_367_ = lean_ctor_get(v_writer_362_, 4);
v_sentMessage_368_ = lean_ctor_get_uint8(v_writer_362_, sizeof(void*)*6);
v_userClosedBody_369_ = lean_ctor_get_uint8(v_writer_362_, sizeof(void*)*6 + 1);
v_omitBody_370_ = lean_ctor_get_uint8(v_writer_362_, sizeof(void*)*6 + 2);
v_userDataBytes_371_ = lean_ctor_get(v_writer_362_, 5);
v___f_377_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_365_))
{
case 1:
{
lean_inc(v_state_365_);
lean_inc(v_userDataBytes_371_);
lean_inc(v_messageHead_367_);
lean_inc(v_knownSize_366_);
lean_inc_ref(v_outputData_364_);
lean_inc_ref(v_userData_363_);
lean_dec_ref(v_writer_362_);
goto v___jp_378_;
}
case 2:
{
lean_inc(v_state_365_);
lean_inc(v_userDataBytes_371_);
lean_inc(v_messageHead_367_);
lean_inc(v_knownSize_366_);
lean_inc_ref(v_outputData_364_);
lean_inc_ref(v_userData_363_);
lean_dec_ref(v_writer_362_);
goto v___jp_378_;
}
case 3:
{
if (v_userClosedBody_369_ == 0)
{
lean_inc_ref(v_state_365_);
lean_inc(v_userDataBytes_371_);
lean_inc(v_messageHead_367_);
lean_inc(v_knownSize_366_);
lean_inc_ref(v_outputData_364_);
lean_inc_ref(v_userData_363_);
lean_dec_ref(v_writer_362_);
goto v___jp_378_;
}
else
{
lean_dec_ref(v_data_361_);
return v_writer_362_;
}
}
default: 
{
lean_dec_ref(v_data_361_);
return v_writer_362_;
}
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = l_Array_append___redArg(v_userData_363_, v_data_361_);
lean_dec_ref(v_data_361_);
v___x_375_ = lean_nat_add(v_userDataBytes_371_, v___y_373_);
lean_dec(v___y_373_);
lean_dec(v_userDataBytes_371_);
v___x_376_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v_outputData_364_);
lean_ctor_set(v___x_376_, 2, v_state_365_);
lean_ctor_set(v___x_376_, 3, v_knownSize_366_);
lean_ctor_set(v___x_376_, 4, v_messageHead_367_);
lean_ctor_set(v___x_376_, 5, v___x_375_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*6, v_sentMessage_368_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*6 + 1, v_userClosedBody_369_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*6 + 2, v_omitBody_370_);
return v___x_376_;
}
v___jp_378_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_array_get_size(v_data_361_);
v___x_381_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_382_ = lean_nat_dec_lt(v___x_379_, v___x_380_);
if (v___x_382_ == 0)
{
v___y_373_ = v___x_379_;
goto v___jp_372_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_le(v___x_380_, v___x_380_);
if (v___x_383_ == 0)
{
if (v___x_382_ == 0)
{
v___y_373_ = v___x_379_;
goto v___jp_372_;
}
else
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___x_384_ = ((size_t)0ULL);
v___x_385_ = lean_usize_of_nat(v___x_380_);
lean_inc_ref(v_data_361_);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_381_, v___f_377_, v_data_361_, v___x_384_, v___x_385_, v___x_379_);
v___y_373_ = v___x_386_;
goto v___jp_372_;
}
}
else
{
size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((size_t)0ULL);
v___x_388_ = lean_usize_of_nat(v___x_380_);
lean_inc_ref(v_data_361_);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_381_, v___f_377_, v_data_361_, v___x_387_, v___x_388_, v___x_379_);
v___y_373_ = v___x_389_;
goto v___jp_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData(uint8_t v_dir_390_, lean_object* v_data_391_, lean_object* v_writer_392_){
_start:
{
lean_object* v_userData_393_; lean_object* v_outputData_394_; lean_object* v_state_395_; lean_object* v_knownSize_396_; lean_object* v_messageHead_397_; uint8_t v_sentMessage_398_; uint8_t v_userClosedBody_399_; uint8_t v_omitBody_400_; lean_object* v_userDataBytes_401_; lean_object* v___y_403_; lean_object* v___f_407_; 
v_userData_393_ = lean_ctor_get(v_writer_392_, 0);
v_outputData_394_ = lean_ctor_get(v_writer_392_, 1);
v_state_395_ = lean_ctor_get(v_writer_392_, 2);
v_knownSize_396_ = lean_ctor_get(v_writer_392_, 3);
v_messageHead_397_ = lean_ctor_get(v_writer_392_, 4);
v_sentMessage_398_ = lean_ctor_get_uint8(v_writer_392_, sizeof(void*)*6);
v_userClosedBody_399_ = lean_ctor_get_uint8(v_writer_392_, sizeof(void*)*6 + 1);
v_omitBody_400_ = lean_ctor_get_uint8(v_writer_392_, sizeof(void*)*6 + 2);
v_userDataBytes_401_ = lean_ctor_get(v_writer_392_, 5);
v___f_407_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__0));
switch(lean_obj_tag(v_state_395_))
{
case 1:
{
lean_inc(v_state_395_);
lean_inc(v_userDataBytes_401_);
lean_inc(v_messageHead_397_);
lean_inc(v_knownSize_396_);
lean_inc_ref(v_outputData_394_);
lean_inc_ref(v_userData_393_);
lean_dec_ref(v_writer_392_);
goto v___jp_408_;
}
case 2:
{
lean_inc(v_state_395_);
lean_inc(v_userDataBytes_401_);
lean_inc(v_messageHead_397_);
lean_inc(v_knownSize_396_);
lean_inc_ref(v_outputData_394_);
lean_inc_ref(v_userData_393_);
lean_dec_ref(v_writer_392_);
goto v___jp_408_;
}
case 3:
{
if (v_userClosedBody_399_ == 0)
{
lean_inc_ref(v_state_395_);
lean_inc(v_userDataBytes_401_);
lean_inc(v_messageHead_397_);
lean_inc(v_knownSize_396_);
lean_inc_ref(v_outputData_394_);
lean_inc_ref(v_userData_393_);
lean_dec_ref(v_writer_392_);
goto v___jp_408_;
}
else
{
lean_dec_ref(v_data_391_);
return v_writer_392_;
}
}
default: 
{
lean_dec_ref(v_data_391_);
return v_writer_392_;
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = l_Array_append___redArg(v_userData_393_, v_data_391_);
lean_dec_ref(v_data_391_);
v___x_405_ = lean_nat_add(v_userDataBytes_401_, v___y_403_);
lean_dec(v___y_403_);
lean_dec(v_userDataBytes_401_);
v___x_406_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v_outputData_394_);
lean_ctor_set(v___x_406_, 2, v_state_395_);
lean_ctor_set(v___x_406_, 3, v_knownSize_396_);
lean_ctor_set(v___x_406_, 4, v_messageHead_397_);
lean_ctor_set(v___x_406_, 5, v___x_405_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*6, v_sentMessage_398_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*6 + 1, v_userClosedBody_399_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*6 + 2, v_omitBody_400_);
return v___x_406_;
}
v___jp_408_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_array_get_size(v_data_391_);
v___x_411_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_412_ = lean_nat_dec_lt(v___x_409_, v___x_410_);
if (v___x_412_ == 0)
{
v___y_403_ = v___x_409_;
goto v___jp_402_;
}
else
{
uint8_t v___x_413_; 
v___x_413_ = lean_nat_dec_le(v___x_410_, v___x_410_);
if (v___x_413_ == 0)
{
if (v___x_412_ == 0)
{
v___y_403_ = v___x_409_;
goto v___jp_402_;
}
else
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v___x_414_ = ((size_t)0ULL);
v___x_415_ = lean_usize_of_nat(v___x_410_);
lean_inc_ref(v_data_391_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_411_, v___f_407_, v_data_391_, v___x_414_, v___x_415_, v___x_409_);
v___y_403_ = v___x_416_;
goto v___jp_402_;
}
}
else
{
size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v___x_417_ = ((size_t)0ULL);
v___x_418_ = lean_usize_of_nat(v___x_410_);
lean_inc_ref(v_data_391_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_411_, v___f_407_, v_data_391_, v___x_417_, v___x_418_, v___x_409_);
v___y_403_ = v___x_419_;
goto v___jp_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_addUserData___boxed(lean_object* v_dir_420_, lean_object* v_data_421_, lean_object* v_writer_422_){
_start:
{
uint8_t v_dir_boxed_423_; lean_object* v_res_424_; 
v_dir_boxed_423_ = lean_unbox(v_dir_420_);
v_res_424_ = l_Std_Http_Protocol_H1_Writer_addUserData(v_dir_boxed_423_, v_data_421_, v_writer_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(lean_object* v_limitSize_425_, lean_object* v_as_426_, size_t v_i_427_, size_t v_stop_428_, lean_object* v_b_429_){
_start:
{
lean_object* v___y_431_; uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_eq(v_i_427_, v_stop_428_);
if (v___x_435_ == 0)
{
lean_object* v_snd_436_; lean_object* v_fst_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_493_; 
v_snd_436_ = lean_ctor_get(v_b_429_, 1);
v_fst_437_ = lean_ctor_get(v_b_429_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_b_429_);
if (v_isSharedCheck_493_ == 0)
{
v___x_439_ = v_b_429_;
v_isShared_440_ = v_isSharedCheck_493_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_436_);
lean_inc(v_fst_437_);
lean_dec(v_b_429_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_493_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_492_; 
v_fst_441_ = lean_ctor_get(v_snd_436_, 0);
v_snd_442_ = lean_ctor_get(v_snd_436_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_snd_436_);
if (v_isSharedCheck_492_ == 0)
{
v___x_444_ = v_snd_436_;
v_isShared_445_ = v_isSharedCheck_492_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snd_442_);
lean_inc(v_fst_441_);
lean_dec(v_snd_436_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_492_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_array_uget(v_as_426_, v_i_427_);
v___x_447_ = lean_nat_dec_le(v_limitSize_425_, v_snd_442_);
if (v___x_447_ == 0)
{
lean_object* v_data_448_; lean_object* v_extensions_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_484_; 
v_data_448_ = lean_ctor_get(v___x_446_, 0);
v_extensions_449_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_484_ == 0)
{
v___x_451_ = v___x_446_;
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_extensions_449_);
lean_inc(v_data_448_);
lean_dec(v___x_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v_remaining_454_; lean_object* v___x_455_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_479_; uint8_t v___x_483_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v_remaining_454_ = lean_nat_sub(v_limitSize_425_, v_snd_442_);
v___x_455_ = lean_byte_array_size(v_data_448_);
v___x_483_ = lean_nat_dec_le(v___x_455_, v_remaining_454_);
if (v___x_483_ == 0)
{
v___y_479_ = v_remaining_454_;
goto v___jp_478_;
}
else
{
lean_dec(v_remaining_454_);
v___y_479_ = v___x_455_;
goto v___jp_478_;
}
v___jp_456_:
{
lean_object* v_size_459_; uint8_t v___x_460_; 
v_size_459_ = lean_nat_add(v_snd_442_, v___y_457_);
lean_dec(v_snd_442_);
v___x_460_ = lean_nat_dec_lt(v___y_457_, v___x_455_);
if (v___x_460_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v___y_457_);
lean_del_object(v___x_451_);
lean_dec_ref(v_extensions_449_);
lean_dec_ref(v_data_448_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_size_459_);
v___x_462_ = v___x_444_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_fst_441_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_size_459_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_462_);
lean_ctor_set(v___x_439_, 0, v___y_458_);
v___x_464_ = v___x_439_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___y_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v___y_431_ = v___x_464_;
goto v___jp_430_;
}
}
}
else
{
lean_object* v___x_467_; lean_object* v_pendingChunk_469_; 
v___x_467_ = l_ByteArray_extract(v_data_448_, v___y_457_, v___x_455_);
lean_dec_ref(v_data_448_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_467_);
v_pendingChunk_469_ = v___x_451_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_extensions_449_);
v_pendingChunk_469_ = v_reuseFailAlloc_477_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_array_push(v_fst_441_, v_pendingChunk_469_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_size_459_);
lean_ctor_set(v___x_444_, 0, v___x_470_);
v___x_472_ = v___x_444_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_size_459_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_472_);
lean_ctor_set(v___x_439_, 0, v___y_458_);
v___x_474_ = v___x_439_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___y_458_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
v___y_431_ = v___x_474_;
goto v___jp_430_;
}
}
}
}
}
v___jp_478_:
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_eq(v___y_479_, v___x_453_);
if (v___x_480_ == 0)
{
lean_object* v_dataPart_481_; lean_object* v___x_482_; 
v_dataPart_481_ = l_ByteArray_extract(v_data_448_, v___x_453_, v___y_479_);
v___x_482_ = lean_array_push(v_fst_437_, v_dataPart_481_);
v___y_457_ = v___y_479_;
v___y_458_ = v___x_482_;
goto v___jp_456_;
}
else
{
v___y_457_ = v___y_479_;
v___y_458_ = v_fst_437_;
goto v___jp_456_;
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_array_push(v_fst_441_, v___x_446_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_485_);
v___x_487_ = v___x_444_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_snd_442_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_487_);
v___x_489_ = v___x_439_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_fst_437_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v___y_431_ = v___x_489_;
goto v___jp_430_;
}
}
}
}
}
}
else
{
return v_b_429_;
}
v___jp_430_:
{
size_t v___x_432_; size_t v___x_433_; 
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_427_, v___x_432_);
v_i_427_ = v___x_433_;
v_b_429_ = v___y_431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1___boxed(lean_object* v_limitSize_494_, lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_stop_497_, lean_object* v_b_498_){
_start:
{
size_t v_i_boxed_499_; size_t v_stop_boxed_500_; lean_object* v_res_501_; 
v_i_boxed_499_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_stop_boxed_500_ = lean_unbox_usize(v_stop_497_);
lean_dec(v_stop_497_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_494_, v_as_495_, v_i_boxed_499_, v_stop_boxed_500_, v_b_498_);
lean_dec_ref(v_as_495_);
lean_dec(v_limitSize_494_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(lean_object* v_as_502_, size_t v_i_503_, size_t v_stop_504_, lean_object* v_b_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_eq(v_i_503_, v_stop_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; size_t v___x_510_; size_t v___x_511_; 
v___x_507_ = lean_array_uget_borrowed(v_as_502_, v_i_503_);
v___x_508_ = lean_byte_array_size(v___x_507_);
v___x_509_ = lean_nat_add(v_b_505_, v___x_508_);
lean_dec(v_b_505_);
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_add(v_i_503_, v___x_510_);
v_i_503_ = v___x_511_;
v_b_505_ = v___x_509_;
goto _start;
}
else
{
return v_b_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0___boxed(lean_object* v_as_513_, lean_object* v_i_514_, lean_object* v_stop_515_, lean_object* v_b_516_){
_start:
{
size_t v_i_boxed_517_; size_t v_stop_boxed_518_; lean_object* v_res_519_; 
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_stop_boxed_518_ = lean_unbox_usize(v_stop_515_);
lean_dec(v_stop_515_);
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_as_513_, v_i_boxed_517_, v_stop_boxed_518_, v_b_516_);
lean_dec_ref(v_as_513_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(lean_object* v_writer_528_, lean_object* v_limitSize_529_){
_start:
{
uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_userData_565_; lean_object* v_outputData_566_; lean_object* v_state_567_; lean_object* v_knownSize_568_; lean_object* v_messageHead_569_; uint8_t v_sentMessage_570_; uint8_t v_userClosedBody_571_; uint8_t v_omitBody_572_; lean_object* v_userDataBytes_573_; lean_object* v_fst_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___y_593_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_userData_565_ = lean_ctor_get(v_writer_528_, 0);
v_outputData_566_ = lean_ctor_get(v_writer_528_, 1);
v_state_567_ = lean_ctor_get(v_writer_528_, 2);
v_knownSize_568_ = lean_ctor_get(v_writer_528_, 3);
v_messageHead_569_ = lean_ctor_get(v_writer_528_, 4);
v_sentMessage_570_ = lean_ctor_get_uint8(v_writer_528_, sizeof(void*)*6);
v_userClosedBody_571_ = lean_ctor_get_uint8(v_writer_528_, sizeof(void*)*6 + 1);
v_omitBody_572_ = lean_ctor_get_uint8(v_writer_528_, sizeof(void*)*6 + 2);
v_userDataBytes_573_ = lean_ctor_get(v_writer_528_, 5);
v___x_598_ = lean_array_get_size(v_userData_565_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_nat_dec_eq(v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
lean_inc(v_userDataBytes_573_);
lean_inc(v_messageHead_569_);
lean_inc(v_knownSize_568_);
lean_inc(v_state_567_);
lean_inc_ref(v_outputData_566_);
lean_inc_ref(v_userData_565_);
lean_dec_ref(v_writer_528_);
v___x_601_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__0));
v___x_602_ = lean_nat_dec_lt(v___x_599_, v___x_598_);
if (v___x_602_ == 0)
{
lean_dec_ref(v_userData_565_);
v_fst_575_ = v___x_601_;
v_fst_576_ = v___x_601_;
v_snd_577_ = v___x_599_;
goto v___jp_574_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg___closed__2));
v___x_604_ = lean_nat_dec_le(v___x_598_, v___x_598_);
if (v___x_604_ == 0)
{
if (v___x_602_ == 0)
{
lean_dec_ref(v_userData_565_);
v_fst_575_ = v___x_601_;
v_fst_576_ = v___x_601_;
v_snd_577_ = v___x_599_;
goto v___jp_574_;
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((size_t)0ULL);
v___x_606_ = lean_usize_of_nat(v___x_598_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_529_, v_userData_565_, v___x_605_, v___x_606_, v___x_603_);
lean_dec_ref(v_userData_565_);
v___y_593_ = v___x_607_;
goto v___jp_592_;
}
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_598_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__1(v_limitSize_529_, v_userData_565_, v___x_608_, v___x_609_, v___x_603_);
lean_dec_ref(v_userData_565_);
v___y_593_ = v___x_610_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v_writer_528_);
lean_ctor_set(v___x_611_, 1, v_limitSize_529_);
return v___x_611_;
}
v___jp_530_:
{
lean_object* v_data_542_; lean_object* v_size_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_564_; 
v_data_542_ = lean_ctor_get(v___y_540_, 0);
v_size_543_ = lean_ctor_get(v___y_540_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v___y_540_);
if (v_isSharedCheck_564_ == 0)
{
v___x_545_ = v___y_540_;
v_isShared_546_ = v_isSharedCheck_564_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_size_543_);
lean_inc(v_data_542_);
lean_dec(v___y_540_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_564_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_data_547_; lean_object* v_size_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_563_; 
v_data_547_ = lean_ctor_get(v___y_541_, 0);
v_size_548_ = lean_ctor_get(v___y_541_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v___y_541_);
if (v_isSharedCheck_563_ == 0)
{
v___x_550_ = v___y_541_;
v_isShared_551_ = v_isSharedCheck_563_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_size_548_);
lean_inc(v_data_547_);
lean_dec(v___y_541_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_563_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_outputData_555_; 
v___x_552_ = l_Array_append___redArg(v_data_542_, v_data_547_);
lean_dec_ref(v_data_547_);
v___x_553_ = lean_nat_add(v_size_543_, v_size_548_);
lean_dec(v_size_548_);
lean_dec(v_size_543_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_553_);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v_outputData_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_553_);
v_outputData_555_ = v_reuseFailAlloc_562_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v_remaining_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v_remaining_556_ = lean_nat_sub(v_limitSize_529_, v___y_534_);
lean_dec(v_limitSize_529_);
v___x_557_ = lean_nat_sub(v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec(v___y_533_);
v___x_558_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_558_, 0, v___y_537_);
lean_ctor_set(v___x_558_, 1, v_outputData_555_);
lean_ctor_set(v___x_558_, 2, v___y_532_);
lean_ctor_set(v___x_558_, 3, v___y_538_);
lean_ctor_set(v___x_558_, 4, v___y_536_);
lean_ctor_set(v___x_558_, 5, v___x_557_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*6, v___y_535_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*6 + 1, v___y_539_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*6 + 2, v___y_531_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v_remaining_556_);
lean_ctor_set(v___x_545_, 0, v___x_558_);
v___x_560_ = v___x_545_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_remaining_556_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
v___jp_574_:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_array_get_size(v_fst_575_);
v___x_580_ = lean_nat_dec_lt(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_fst_575_);
lean_ctor_set(v___x_581_, 1, v___x_578_);
v___y_531_ = v_omitBody_572_;
v___y_532_ = v_state_567_;
v___y_533_ = v_userDataBytes_573_;
v___y_534_ = v_snd_577_;
v___y_535_ = v_sentMessage_570_;
v___y_536_ = v_messageHead_569_;
v___y_537_ = v_fst_576_;
v___y_538_ = v_knownSize_568_;
v___y_539_ = v_userClosedBody_571_;
v___y_540_ = v_outputData_566_;
v___y_541_ = v___x_581_;
goto v___jp_530_;
}
else
{
uint8_t v___x_582_; 
v___x_582_ = lean_nat_dec_le(v___x_579_, v___x_579_);
if (v___x_582_ == 0)
{
if (v___x_580_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_fst_575_);
lean_ctor_set(v___x_583_, 1, v___x_578_);
v___y_531_ = v_omitBody_572_;
v___y_532_ = v_state_567_;
v___y_533_ = v_userDataBytes_573_;
v___y_534_ = v_snd_577_;
v___y_535_ = v_sentMessage_570_;
v___y_536_ = v_messageHead_569_;
v___y_537_ = v_fst_576_;
v___y_538_ = v_knownSize_568_;
v___y_539_ = v_userClosedBody_571_;
v___y_540_ = v_outputData_566_;
v___y_541_ = v___x_583_;
goto v___jp_530_;
}
else
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_579_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_575_, v___x_584_, v___x_585_, v___x_578_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_fst_575_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___y_531_ = v_omitBody_572_;
v___y_532_ = v_state_567_;
v___y_533_ = v_userDataBytes_573_;
v___y_534_ = v_snd_577_;
v___y_535_ = v_sentMessage_570_;
v___y_536_ = v_messageHead_569_;
v___y_537_ = v_fst_576_;
v___y_538_ = v_knownSize_568_;
v___y_539_ = v_userClosedBody_571_;
v___y_540_ = v_outputData_566_;
v___y_541_ = v___x_587_;
goto v___jp_530_;
}
}
else
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = ((size_t)0ULL);
v___x_589_ = lean_usize_of_nat(v___x_579_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v_fst_575_, v___x_588_, v___x_589_, v___x_578_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_fst_575_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___y_531_ = v_omitBody_572_;
v___y_532_ = v_state_567_;
v___y_533_ = v_userDataBytes_573_;
v___y_534_ = v_snd_577_;
v___y_535_ = v_sentMessage_570_;
v___y_536_ = v_messageHead_569_;
v___y_537_ = v_fst_576_;
v___y_538_ = v_knownSize_568_;
v___y_539_ = v_userClosedBody_571_;
v___y_540_ = v_outputData_566_;
v___y_541_ = v___x_591_;
goto v___jp_530_;
}
}
}
v___jp_592_:
{
lean_object* v_snd_594_; lean_object* v_fst_595_; lean_object* v_fst_596_; lean_object* v_snd_597_; 
v_snd_594_ = lean_ctor_get(v___y_593_, 1);
lean_inc(v_snd_594_);
v_fst_595_ = lean_ctor_get(v___y_593_, 0);
lean_inc(v_fst_595_);
lean_dec_ref(v___y_593_);
v_fst_596_ = lean_ctor_get(v_snd_594_, 0);
lean_inc(v_fst_596_);
v_snd_597_ = lean_ctor_get(v_snd_594_, 1);
lean_inc(v_snd_597_);
lean_dec(v_snd_594_);
v_fst_575_ = v_fst_595_;
v_fst_576_ = v_fst_596_;
v_snd_577_ = v_snd_597_;
goto v___jp_574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody(uint8_t v_dir_612_, lean_object* v_writer_613_, lean_object* v_limitSize_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody___redArg(v_writer_613_, v_limitSize_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFixedBody___boxed(lean_object* v_dir_616_, lean_object* v_writer_617_, lean_object* v_limitSize_618_){
_start:
{
uint8_t v_dir_boxed_619_; lean_object* v_res_620_; 
v_dir_boxed_619_ = lean_unbox(v_dir_616_);
v_res_620_ = l_Std_Http_Protocol_H1_Writer_writeFixedBody(v_dir_boxed_619_, v_writer_617_, v_limitSize_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(size_t v_sz_621_, size_t v_i_622_, lean_object* v_bs_623_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_lt(v_i_622_, v_sz_621_);
if (v___x_624_ == 0)
{
return v_bs_623_;
}
else
{
lean_object* v_v_625_; lean_object* v___x_626_; lean_object* v_bs_x27_627_; uint32_t v___x_628_; uint8_t v___x_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_v_625_ = lean_array_uget(v_bs_623_, v_i_622_);
v___x_626_ = lean_unsigned_to_nat(0u);
v_bs_x27_627_ = lean_array_uset(v_bs_623_, v_i_622_, v___x_626_);
v___x_628_ = lean_unbox_uint32(v_v_625_);
lean_dec(v_v_625_);
v___x_629_ = lean_uint32_to_uint8(v___x_628_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_622_, v___x_630_);
v___x_632_ = lean_box(v___x_629_);
v___x_633_ = lean_array_uset(v_bs_x27_627_, v_i_622_, v___x_632_);
v_i_622_ = v___x_631_;
v_bs_623_ = v___x_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0___boxed(lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_bs_637_){
_start:
{
size_t v_sz_boxed_638_; size_t v_i_boxed_639_; lean_object* v_res_640_; 
v_sz_boxed_638_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_639_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_boxed_638_, v_i_boxed_639_, v_bs_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(lean_object* v_as_643_, size_t v_i_644_, size_t v_stop_645_, lean_object* v_b_646_){
_start:
{
lean_object* v___y_648_; uint8_t v___x_652_; 
v___x_652_ = lean_usize_dec_eq(v_i_644_, v_stop_645_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = lean_array_uget_borrowed(v_as_643_, v_i_644_);
v_fst_654_ = lean_ctor_get(v___x_653_, 0);
v_snd_655_ = lean_ctor_get(v___x_653_, 1);
v___x_656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__0));
v___x_657_ = lean_string_append(v_b_646_, v___x_656_);
v___x_658_ = lean_string_append(v___x_657_, v_fst_654_);
if (lean_obj_tag(v_snd_655_) == 0)
{
v___y_648_ = v___x_658_;
goto v___jp_647_;
}
else
{
lean_object* v_val_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_val_659_ = lean_ctor_get(v_snd_655_, 0);
v___x_660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___closed__1));
lean_inc(v_val_659_);
v___x_661_ = l_Std_Http_Chunk_ExtensionValue_quote(v_val_659_);
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
lean_dec_ref(v___x_661_);
v___x_663_ = lean_string_append(v___x_658_, v___x_662_);
lean_dec_ref(v___x_662_);
v___y_648_ = v___x_663_;
goto v___jp_647_;
}
}
else
{
return v_b_646_;
}
v___jp_647_:
{
size_t v___x_649_; size_t v___x_650_; 
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_644_, v___x_649_);
v_i_644_ = v___x_650_;
v_b_646_ = v___y_648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1___boxed(lean_object* v_as_664_, lean_object* v_i_665_, lean_object* v_stop_666_, lean_object* v_b_667_){
_start:
{
size_t v_i_boxed_668_; size_t v_stop_boxed_669_; lean_object* v_res_670_; 
v_i_boxed_668_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_stop_boxed_669_ = lean_unbox_usize(v_stop_666_);
lean_dec(v_stop_666_);
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_as_664_, v_i_boxed_668_, v_stop_boxed_669_, v_b_667_);
lean_dec_ref(v_as_664_);
return v_res_670_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__0));
v___x_673_ = lean_string_to_utf8(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(lean_object* v_as_675_, size_t v_i_676_, size_t v_stop_677_, lean_object* v_b_678_){
_start:
{
lean_object* v___y_680_; uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_eq(v_i_676_, v_stop_677_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v_data_699_; lean_object* v_extensions_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_754_; 
v___x_698_ = lean_array_uget(v_as_675_, v_i_676_);
v_data_699_ = lean_ctor_get(v___x_698_, 0);
v_extensions_700_ = lean_ctor_get(v___x_698_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_754_ == 0)
{
v___x_702_ = v___x_698_;
v_isShared_703_ = v_isSharedCheck_754_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_extensions_700_);
lean_inc(v_data_699_);
lean_dec(v___x_698_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_754_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_chunkLen_704_; lean_object* v___y_706_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_chunkLen_704_ = lean_byte_array_size(v_data_699_);
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__2));
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_get_size(v_extensions_700_);
v___x_746_ = lean_nat_dec_lt(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec_ref(v_extensions_700_);
v___y_706_ = v___x_743_;
goto v___jp_705_;
}
else
{
uint8_t v___x_747_; 
v___x_747_ = lean_nat_dec_le(v___x_745_, v___x_745_);
if (v___x_747_ == 0)
{
if (v___x_746_ == 0)
{
lean_dec_ref(v_extensions_700_);
v___y_706_ = v___x_743_;
goto v___jp_705_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_745_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_700_, v___x_748_, v___x_749_, v___x_743_);
lean_dec_ref(v_extensions_700_);
v___y_706_ = v___x_750_;
goto v___jp_705_;
}
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_745_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__1(v_extensions_700_, v___x_751_, v___x_752_, v___x_743_);
lean_dec_ref(v_extensions_700_);
v___y_706_ = v___x_753_;
goto v___jp_705_;
}
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; size_t v_sz_710_; size_t v___x_711_; lean_object* v___x_712_; lean_object* v_size_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_707_ = lean_unsigned_to_nat(16u);
v___x_708_ = l_Nat_toDigits(v___x_707_, v_chunkLen_704_);
v___x_709_ = lean_array_mk(v___x_708_);
v_sz_710_ = lean_array_size(v___x_709_);
v___x_711_ = ((size_t)0ULL);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__0(v_sz_710_, v___x_711_, v___x_709_);
v_size_713_ = lean_byte_array_mk(v___x_712_);
v___x_714_ = lean_string_to_utf8(v___y_706_);
lean_dec_ref(v___y_706_);
v___x_715_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___closed__1);
v___x_716_ = lean_unsigned_to_nat(5u);
v___x_717_ = lean_mk_empty_array_with_capacity(v___x_716_);
v___x_718_ = lean_array_push(v___x_717_, v_size_713_);
v___x_719_ = lean_array_push(v___x_718_, v___x_714_);
v___x_720_ = lean_array_push(v___x_719_, v___x_715_);
v___x_721_ = lean_array_push(v___x_720_, v_data_699_);
v___x_722_ = lean_array_push(v___x_721_, v___x_715_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_array_get_size(v___x_722_);
v___x_725_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_723_);
lean_ctor_set(v___x_702_, 0, v___x_722_);
v___x_727_ = v___x_702_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_723_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v___y_680_ = v___x_727_;
goto v___jp_679_;
}
}
else
{
uint8_t v___x_729_; 
v___x_729_ = lean_nat_dec_le(v___x_724_, v___x_724_);
if (v___x_729_ == 0)
{
if (v___x_725_ == 0)
{
lean_object* v___x_731_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_723_);
lean_ctor_set(v___x_702_, 0, v___x_722_);
v___x_731_ = v___x_702_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_723_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v___y_680_ = v___x_731_;
goto v___jp_679_;
}
}
else
{
size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_733_ = lean_usize_of_nat(v___x_724_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_722_, v___x_711_, v___x_733_, v___x_723_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_734_);
lean_ctor_set(v___x_702_, 0, v___x_722_);
v___x_736_ = v___x_702_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
v___y_680_ = v___x_736_;
goto v___jp_679_;
}
}
}
else
{
size_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_738_ = lean_usize_of_nat(v___x_724_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeFixedBody_spec__0(v___x_722_, v___x_711_, v___x_738_, v___x_723_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_739_);
lean_ctor_set(v___x_702_, 0, v___x_722_);
v___x_741_ = v___x_702_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v___y_680_ = v___x_741_;
goto v___jp_679_;
}
}
}
}
}
}
else
{
return v_b_678_;
}
v___jp_679_:
{
lean_object* v_data_681_; lean_object* v_size_682_; lean_object* v_data_683_; lean_object* v_size_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_data_681_ = lean_ctor_get(v_b_678_, 0);
lean_inc_ref(v_data_681_);
v_size_682_ = lean_ctor_get(v_b_678_, 1);
lean_inc(v_size_682_);
lean_dec_ref(v_b_678_);
v_data_683_ = lean_ctor_get(v___y_680_, 0);
v_size_684_ = lean_ctor_get(v___y_680_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___y_680_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v___y_680_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_size_684_);
lean_inc(v_data_683_);
lean_dec(v___y_680_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = l_Array_append___redArg(v_data_681_, v_data_683_);
lean_dec_ref(v_data_683_);
v___x_689_ = lean_nat_add(v_size_682_, v_size_684_);
lean_dec(v_size_684_);
lean_dec(v_size_682_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_689_);
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_676_, v___x_692_);
v_i_676_ = v___x_693_;
v_b_678_ = v___x_691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2___boxed(lean_object* v_as_755_, lean_object* v_i_756_, lean_object* v_stop_757_, lean_object* v_b_758_){
_start:
{
size_t v_i_boxed_759_; size_t v_stop_boxed_760_; lean_object* v_res_761_; 
v_i_boxed_759_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_stop_boxed_760_ = lean_unbox_usize(v_stop_757_);
lean_dec(v_stop_757_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_as_755_, v_i_boxed_759_, v_stop_boxed_760_, v_b_758_);
lean_dec_ref(v_as_755_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(lean_object* v_writer_764_){
_start:
{
lean_object* v_userData_765_; lean_object* v_outputData_766_; lean_object* v_state_767_; lean_object* v_knownSize_768_; lean_object* v_messageHead_769_; uint8_t v_sentMessage_770_; uint8_t v_userClosedBody_771_; uint8_t v_omitBody_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_userData_765_ = lean_ctor_get(v_writer_764_, 0);
v_outputData_766_ = lean_ctor_get(v_writer_764_, 1);
v_state_767_ = lean_ctor_get(v_writer_764_, 2);
v_knownSize_768_ = lean_ctor_get(v_writer_764_, 3);
v_messageHead_769_ = lean_ctor_get(v_writer_764_, 4);
v_sentMessage_770_ = lean_ctor_get_uint8(v_writer_764_, sizeof(void*)*6);
v_userClosedBody_771_ = lean_ctor_get_uint8(v_writer_764_, sizeof(void*)*6 + 1);
v_omitBody_772_ = lean_ctor_get_uint8(v_writer_764_, sizeof(void*)*6 + 2);
v___x_773_ = lean_array_get_size(v_userData_765_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_nat_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_800_; 
lean_inc(v_messageHead_769_);
lean_inc(v_knownSize_768_);
lean_inc(v_state_767_);
lean_inc_ref(v_outputData_766_);
lean_inc_ref(v_userData_765_);
v_isSharedCheck_800_ = !lean_is_exclusive(v_writer_764_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; 
v_unused_801_ = lean_ctor_get(v_writer_764_, 5);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_writer_764_, 4);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_writer_764_, 3);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_writer_764_, 2);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_writer_764_, 1);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_writer_764_, 0);
lean_dec(v_unused_806_);
v___x_777_ = v_writer_764_;
v_isShared_778_ = v_isSharedCheck_800_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_writer_764_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_800_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg___closed__0));
v___x_780_ = lean_nat_dec_lt(v___x_774_, v___x_773_);
if (v___x_780_ == 0)
{
lean_object* v___x_782_; 
lean_dec_ref(v_userData_765_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 5, v___x_774_);
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_outputData_766_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_state_767_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_knownSize_768_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_messageHead_769_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v___x_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*6, v_sentMessage_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*6 + 1, v_userClosedBody_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*6 + 2, v_omitBody_772_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_773_, v___x_773_);
if (v___x_784_ == 0)
{
if (v___x_780_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v_userData_765_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 5, v___x_774_);
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_outputData_766_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_state_767_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_knownSize_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_messageHead_769_);
lean_ctor_set(v_reuseFailAlloc_787_, 5, v___x_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_787_, sizeof(void*)*6, v_sentMessage_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_787_, sizeof(void*)*6 + 1, v_userClosedBody_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_787_, sizeof(void*)*6 + 2, v_omitBody_772_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_773_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_userData_765_, v___x_788_, v___x_789_, v_outputData_766_);
lean_dec_ref(v_userData_765_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 5, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_790_);
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_792_ = v___x_777_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_state_767_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_knownSize_768_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_messageHead_769_);
lean_ctor_set(v_reuseFailAlloc_793_, 5, v___x_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_793_, sizeof(void*)*6, v_sentMessage_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_793_, sizeof(void*)*6 + 1, v_userClosedBody_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_793_, sizeof(void*)*6 + 2, v_omitBody_772_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_794_ = ((size_t)0ULL);
v___x_795_ = lean_usize_of_nat(v___x_773_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Writer_writeChunkedBody_spec__2(v_userData_765_, v___x_794_, v___x_795_, v_outputData_766_);
lean_dec_ref(v_userData_765_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 5, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_796_);
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_798_ = v___x_777_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_state_767_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_knownSize_768_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_messageHead_769_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v___x_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*6, v_sentMessage_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*6 + 1, v_userClosedBody_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*6 + 2, v_omitBody_772_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
else
{
return v_writer_764_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody(uint8_t v_dir_807_, lean_object* v_writer_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeChunkedBody___boxed(lean_object* v_dir_810_, lean_object* v_writer_811_){
_start:
{
uint8_t v_dir_boxed_812_; lean_object* v_res_813_; 
v_dir_boxed_812_ = lean_unbox(v_dir_810_);
v_res_813_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody(v_dir_boxed_812_, v_writer_811_);
return v_res_813_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__0));
v___x_816_ = lean_string_to_utf8(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_818_ = lean_byte_array_size(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(lean_object* v_writer_819_){
_start:
{
lean_object* v_writer_820_; lean_object* v_outputData_821_; lean_object* v_userData_822_; lean_object* v_knownSize_823_; lean_object* v_messageHead_824_; uint8_t v_sentMessage_825_; uint8_t v_userClosedBody_826_; uint8_t v_omitBody_827_; lean_object* v_userDataBytes_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_849_; 
v_writer_820_ = l_Std_Http_Protocol_H1_Writer_writeChunkedBody___redArg(v_writer_819_);
v_outputData_821_ = lean_ctor_get(v_writer_820_, 1);
v_userData_822_ = lean_ctor_get(v_writer_820_, 0);
v_knownSize_823_ = lean_ctor_get(v_writer_820_, 3);
v_messageHead_824_ = lean_ctor_get(v_writer_820_, 4);
v_sentMessage_825_ = lean_ctor_get_uint8(v_writer_820_, sizeof(void*)*6);
v_userClosedBody_826_ = lean_ctor_get_uint8(v_writer_820_, sizeof(void*)*6 + 1);
v_omitBody_827_ = lean_ctor_get_uint8(v_writer_820_, sizeof(void*)*6 + 2);
v_userDataBytes_828_ = lean_ctor_get(v_writer_820_, 5);
v_isSharedCheck_849_ = !lean_is_exclusive(v_writer_820_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_writer_820_, 2);
lean_dec(v_unused_850_);
v___x_830_ = v_writer_820_;
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_userDataBytes_828_);
lean_inc(v_messageHead_824_);
lean_inc(v_knownSize_823_);
lean_inc(v_outputData_821_);
lean_inc(v_userData_822_);
lean_dec(v_writer_820_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_data_832_; lean_object* v_size_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_848_; 
v_data_832_ = lean_ctor_get(v_outputData_821_, 0);
v_size_833_ = lean_ctor_get(v_outputData_821_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_outputData_821_);
if (v_isSharedCheck_848_ == 0)
{
v___x_835_ = v_outputData_821_;
v_isShared_836_ = v_isSharedCheck_848_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_size_833_);
lean_inc(v_data_832_);
lean_dec(v_outputData_821_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_848_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_837_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__1);
v___x_838_ = lean_array_push(v_data_832_, v___x_837_);
v___x_839_ = lean_obj_once(&l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2, &l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2_once, _init_l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg___closed__2);
v___x_840_ = lean_nat_add(v_size_833_, v___x_839_);
lean_dec(v_size_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_840_);
lean_ctor_set(v___x_835_, 0, v___x_838_);
v___x_842_ = v___x_835_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_847_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(4);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 2, v___x_843_);
lean_ctor_set(v___x_830_, 1, v___x_842_);
v___x_845_ = v___x_830_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_userData_822_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_knownSize_823_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_messageHead_824_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v_userDataBytes_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_846_, sizeof(void*)*6, v_sentMessage_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_846_, sizeof(void*)*6 + 1, v_userClosedBody_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_846_, sizeof(void*)*6 + 2, v_omitBody_827_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk(uint8_t v_dir_851_, lean_object* v_writer_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk___redArg(v_writer_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_writeFinalChunk___boxed(lean_object* v_dir_854_, lean_object* v_writer_855_){
_start:
{
uint8_t v_dir_boxed_856_; lean_object* v_res_857_; 
v_dir_boxed_856_ = lean_unbox(v_dir_854_);
v_res_857_ = l_Std_Http_Protocol_H1_Writer_writeFinalChunk(v_dir_boxed_856_, v_writer_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(uint8_t v___x_858_, lean_object* v_x1_859_, lean_object* v_x2_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_byte_array_size(v_x1_859_);
v___x_863_ = lean_byte_array_size(v_x2_860_);
v___x_864_ = lean_byte_array_copy_slice(v_x2_860_, v___x_861_, v_x1_859_, v___x_862_, v___x_863_, v___x_858_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed(lean_object* v___x_865_, lean_object* v_x1_866_, lean_object* v_x2_867_){
_start:
{
uint8_t v___x_120__boxed_868_; lean_object* v_res_869_; 
v___x_120__boxed_868_ = lean_unbox(v___x_865_);
v_res_869_ = l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0(v___x_120__boxed_868_, v_x1_866_, v_x2_867_);
lean_dec_ref(v_x2_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___redArg(lean_object* v_writer_873_){
_start:
{
lean_object* v_userData_874_; lean_object* v_outputData_875_; lean_object* v_state_876_; lean_object* v_knownSize_877_; lean_object* v_messageHead_878_; uint8_t v_sentMessage_879_; uint8_t v_userClosedBody_880_; uint8_t v_omitBody_881_; lean_object* v_userDataBytes_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_914_; 
v_userData_874_ = lean_ctor_get(v_writer_873_, 0);
v_outputData_875_ = lean_ctor_get(v_writer_873_, 1);
v_state_876_ = lean_ctor_get(v_writer_873_, 2);
v_knownSize_877_ = lean_ctor_get(v_writer_873_, 3);
v_messageHead_878_ = lean_ctor_get(v_writer_873_, 4);
v_sentMessage_879_ = lean_ctor_get_uint8(v_writer_873_, sizeof(void*)*6);
v_userClosedBody_880_ = lean_ctor_get_uint8(v_writer_873_, sizeof(void*)*6 + 1);
v_omitBody_881_ = lean_ctor_get_uint8(v_writer_873_, sizeof(void*)*6 + 2);
v_userDataBytes_882_ = lean_ctor_get(v_writer_873_, 5);
v_isSharedCheck_914_ = !lean_is_exclusive(v_writer_873_);
if (v_isSharedCheck_914_ == 0)
{
v___x_884_ = v_writer_873_;
v_isShared_885_ = v_isSharedCheck_914_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_userDataBytes_882_);
lean_inc(v_messageHead_878_);
lean_inc(v_knownSize_877_);
lean_inc(v_state_876_);
lean_inc(v_outputData_875_);
lean_inc(v_userData_874_);
lean_dec(v_writer_873_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_914_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___y_887_; lean_object* v_data_894_; lean_object* v_size_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_data_894_ = lean_ctor_get(v_outputData_875_, 0);
lean_inc_ref(v_data_894_);
v_size_895_ = lean_ctor_get(v_outputData_875_, 1);
lean_inc(v_size_895_);
lean_dec_ref(v_outputData_875_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_array_get_size(v_data_894_);
v___x_898_ = lean_nat_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_899_ = lean_mk_empty_byte_array(v_size_895_);
lean_dec(v_size_895_);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_897_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_data_894_);
v___y_887_ = v___x_899_;
goto v___jp_886_;
}
else
{
lean_object* v___x_903_; lean_object* v___f_904_; uint8_t v___x_905_; 
v___x_903_ = lean_box(v___x_898_);
v___f_904_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_904_, 0, v___x_903_);
v___x_905_ = lean_nat_dec_le(v___x_897_, v___x_897_);
if (v___x_905_ == 0)
{
if (v___x_902_ == 0)
{
lean_dec_ref(v___f_904_);
lean_dec_ref(v_data_894_);
v___y_887_ = v___x_899_;
goto v___jp_886_;
}
else
{
size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((size_t)0ULL);
v___x_907_ = lean_usize_of_nat(v___x_897_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_901_, v___f_904_, v_data_894_, v___x_906_, v___x_907_, v___x_899_);
v___y_887_ = v___x_908_;
goto v___jp_886_;
}
}
else
{
size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((size_t)0ULL);
v___x_910_ = lean_usize_of_nat(v___x_897_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_901_, v___f_904_, v_data_894_, v___x_909_, v___x_910_, v___x_899_);
v___y_887_ = v___x_911_;
goto v___jp_886_;
}
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_size_895_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_fget(v_data_894_, v___x_912_);
lean_dec_ref(v_data_894_);
v___y_887_ = v___x_913_;
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_888_);
v___x_890_ = v___x_884_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_userData_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_state_876_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_knownSize_877_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_messageHead_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 5, v_userDataBytes_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*6, v_sentMessage_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*6 + 1, v_userClosedBody_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*6 + 2, v_omitBody_881_);
v___x_890_ = v_reuseFailAlloc_893_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___y_887_);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput(uint8_t v_dir_915_, lean_object* v_writer_916_){
_start:
{
lean_object* v_userData_917_; lean_object* v_outputData_918_; lean_object* v_state_919_; lean_object* v_knownSize_920_; lean_object* v_messageHead_921_; uint8_t v_sentMessage_922_; uint8_t v_userClosedBody_923_; uint8_t v_omitBody_924_; lean_object* v_userDataBytes_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_957_; 
v_userData_917_ = lean_ctor_get(v_writer_916_, 0);
v_outputData_918_ = lean_ctor_get(v_writer_916_, 1);
v_state_919_ = lean_ctor_get(v_writer_916_, 2);
v_knownSize_920_ = lean_ctor_get(v_writer_916_, 3);
v_messageHead_921_ = lean_ctor_get(v_writer_916_, 4);
v_sentMessage_922_ = lean_ctor_get_uint8(v_writer_916_, sizeof(void*)*6);
v_userClosedBody_923_ = lean_ctor_get_uint8(v_writer_916_, sizeof(void*)*6 + 1);
v_omitBody_924_ = lean_ctor_get_uint8(v_writer_916_, sizeof(void*)*6 + 2);
v_userDataBytes_925_ = lean_ctor_get(v_writer_916_, 5);
v_isSharedCheck_957_ = !lean_is_exclusive(v_writer_916_);
if (v_isSharedCheck_957_ == 0)
{
v___x_927_ = v_writer_916_;
v_isShared_928_ = v_isSharedCheck_957_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_userDataBytes_925_);
lean_inc(v_messageHead_921_);
lean_inc(v_knownSize_920_);
lean_inc(v_state_919_);
lean_inc(v_outputData_918_);
lean_inc(v_userData_917_);
lean_dec(v_writer_916_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_957_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___y_930_; lean_object* v_data_937_; lean_object* v_size_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_data_937_ = lean_ctor_get(v_outputData_918_, 0);
lean_inc_ref(v_data_937_);
v_size_938_ = lean_ctor_get(v_outputData_918_, 1);
lean_inc(v_size_938_);
lean_dec_ref(v_outputData_918_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_array_get_size(v_data_937_);
v___x_941_ = lean_nat_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_942_ = lean_mk_empty_byte_array(v_size_938_);
lean_dec(v_size_938_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_addUserData___redArg___closed__10));
v___x_945_ = lean_nat_dec_lt(v___x_943_, v___x_940_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_data_937_);
v___y_930_ = v___x_942_;
goto v___jp_929_;
}
else
{
lean_object* v___x_946_; lean_object* v___f_947_; uint8_t v___x_948_; 
v___x_946_ = lean_box(v___x_941_);
v___f_947_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_947_, 0, v___x_946_);
v___x_948_ = lean_nat_dec_le(v___x_940_, v___x_940_);
if (v___x_948_ == 0)
{
if (v___x_945_ == 0)
{
lean_dec_ref(v___f_947_);
lean_dec_ref(v_data_937_);
v___y_930_ = v___x_942_;
goto v___jp_929_;
}
else
{
size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; 
v___x_949_ = ((size_t)0ULL);
v___x_950_ = lean_usize_of_nat(v___x_940_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_944_, v___f_947_, v_data_937_, v___x_949_, v___x_950_, v___x_942_);
v___y_930_ = v___x_951_;
goto v___jp_929_;
}
}
else
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_952_ = ((size_t)0ULL);
v___x_953_ = lean_usize_of_nat(v___x_940_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_944_, v___f_947_, v_data_937_, v___x_952_, v___x_953_, v___x_942_);
v___y_930_ = v___x_954_;
goto v___jp_929_;
}
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_size_938_);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_fget(v_data_937_, v___x_955_);
lean_dec_ref(v_data_937_);
v___y_930_ = v___x_956_;
goto v___jp_929_;
}
v___jp_929_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_takeOutput___redArg___closed__0));
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_931_);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_userData_917_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_state_919_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_knownSize_920_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_messageHead_921_);
lean_ctor_set(v_reuseFailAlloc_936_, 5, v_userDataBytes_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*6, v_sentMessage_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*6 + 1, v_userClosedBody_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*6 + 2, v_omitBody_924_);
v___x_933_ = v_reuseFailAlloc_936_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___y_930_);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_takeOutput___boxed(lean_object* v_dir_958_, lean_object* v_writer_959_){
_start:
{
uint8_t v_dir_boxed_960_; lean_object* v_res_961_; 
v_dir_boxed_960_ = lean_unbox(v_dir_958_);
v_res_961_ = l_Std_Http_Protocol_H1_Writer_takeOutput(v_dir_boxed_960_, v_writer_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___redArg(lean_object* v_state_962_, lean_object* v_writer_963_){
_start:
{
lean_object* v_userData_964_; lean_object* v_outputData_965_; lean_object* v_knownSize_966_; lean_object* v_messageHead_967_; uint8_t v_sentMessage_968_; uint8_t v_userClosedBody_969_; uint8_t v_omitBody_970_; lean_object* v_userDataBytes_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_userData_964_ = lean_ctor_get(v_writer_963_, 0);
v_outputData_965_ = lean_ctor_get(v_writer_963_, 1);
v_knownSize_966_ = lean_ctor_get(v_writer_963_, 3);
v_messageHead_967_ = lean_ctor_get(v_writer_963_, 4);
v_sentMessage_968_ = lean_ctor_get_uint8(v_writer_963_, sizeof(void*)*6);
v_userClosedBody_969_ = lean_ctor_get_uint8(v_writer_963_, sizeof(void*)*6 + 1);
v_omitBody_970_ = lean_ctor_get_uint8(v_writer_963_, sizeof(void*)*6 + 2);
v_userDataBytes_971_ = lean_ctor_get(v_writer_963_, 5);
v_isSharedCheck_978_ = !lean_is_exclusive(v_writer_963_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_writer_963_, 2);
lean_dec(v_unused_979_);
v___x_973_ = v_writer_963_;
v_isShared_974_ = v_isSharedCheck_978_;
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
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v_state_962_);
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_userData_964_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_outputData_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_state_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_knownSize_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_messageHead_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 5, v_userDataBytes_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*6, v_sentMessage_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*6 + 1, v_userClosedBody_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*6 + 2, v_omitBody_970_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState(uint8_t v_dir_980_, lean_object* v_state_981_, lean_object* v_writer_982_){
_start:
{
lean_object* v_userData_983_; lean_object* v_outputData_984_; lean_object* v_knownSize_985_; lean_object* v_messageHead_986_; uint8_t v_sentMessage_987_; uint8_t v_userClosedBody_988_; uint8_t v_omitBody_989_; lean_object* v_userDataBytes_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v_userData_983_ = lean_ctor_get(v_writer_982_, 0);
v_outputData_984_ = lean_ctor_get(v_writer_982_, 1);
v_knownSize_985_ = lean_ctor_get(v_writer_982_, 3);
v_messageHead_986_ = lean_ctor_get(v_writer_982_, 4);
v_sentMessage_987_ = lean_ctor_get_uint8(v_writer_982_, sizeof(void*)*6);
v_userClosedBody_988_ = lean_ctor_get_uint8(v_writer_982_, sizeof(void*)*6 + 1);
v_omitBody_989_ = lean_ctor_get_uint8(v_writer_982_, sizeof(void*)*6 + 2);
v_userDataBytes_990_ = lean_ctor_get(v_writer_982_, 5);
v_isSharedCheck_997_ = !lean_is_exclusive(v_writer_982_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_writer_982_, 2);
lean_dec(v_unused_998_);
v___x_992_ = v_writer_982_;
v_isShared_993_ = v_isSharedCheck_997_;
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
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v_state_981_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_userData_983_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_outputData_984_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_state_981_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_knownSize_985_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_messageHead_986_);
lean_ctor_set(v_reuseFailAlloc_996_, 5, v_userDataBytes_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6, v_sentMessage_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6 + 1, v_userClosedBody_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6 + 2, v_omitBody_989_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_setState___boxed(lean_object* v_dir_999_, lean_object* v_state_1000_, lean_object* v_writer_1001_){
_start:
{
uint8_t v_dir_boxed_1002_; lean_object* v_res_1003_; 
v_dir_boxed_1002_ = lean_unbox(v_dir_999_);
v_res_1003_ = l_Std_Http_Protocol_H1_Writer_setState(v_dir_boxed_1002_, v_state_1000_, v_writer_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(uint8_t v_dir_1004_, lean_object* v_messageHead_1005_, lean_object* v_writer_1006_){
_start:
{
lean_object* v_userData_1007_; lean_object* v_outputData_1008_; lean_object* v_state_1009_; lean_object* v_knownSize_1010_; lean_object* v_messageHead_1011_; uint8_t v_sentMessage_1012_; uint8_t v_userClosedBody_1013_; uint8_t v_omitBody_1014_; lean_object* v_userDataBytes_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1028_; 
v_userData_1007_ = lean_ctor_get(v_writer_1006_, 0);
v_outputData_1008_ = lean_ctor_get(v_writer_1006_, 1);
v_state_1009_ = lean_ctor_get(v_writer_1006_, 2);
v_knownSize_1010_ = lean_ctor_get(v_writer_1006_, 3);
v_messageHead_1011_ = lean_ctor_get(v_writer_1006_, 4);
v_sentMessage_1012_ = lean_ctor_get_uint8(v_writer_1006_, sizeof(void*)*6);
v_userClosedBody_1013_ = lean_ctor_get_uint8(v_writer_1006_, sizeof(void*)*6 + 1);
v_omitBody_1014_ = lean_ctor_get_uint8(v_writer_1006_, sizeof(void*)*6 + 2);
v_userDataBytes_1015_ = lean_ctor_get(v_writer_1006_, 5);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_writer_1006_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1017_ = v_writer_1006_;
v_isShared_1018_ = v_isSharedCheck_1028_;
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
v_isShared_1018_ = v_isSharedCheck_1028_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
uint8_t v___y_1020_; 
if (v_dir_1004_ == 0)
{
uint8_t v___x_1026_; 
v___x_1026_ = 1;
v___y_1020_ = v___x_1026_;
goto v___jp_1019_;
}
else
{
uint8_t v___x_1027_; 
v___x_1027_ = 0;
v___y_1020_ = v___x_1027_;
goto v___jp_1019_;
}
v___jp_1019_:
{
lean_object* v___x_6__overap_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_6__overap_1021_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1020_);
v___x_1022_ = lean_apply_2(v___x_6__overap_1021_, v_outputData_1008_, v_messageHead_1005_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v___x_1022_);
v___x_1024_ = v___x_1017_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_userData_1007_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_state_1009_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_knownSize_1010_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_messageHead_1011_);
lean_ctor_set(v_reuseFailAlloc_1025_, 5, v_userDataBytes_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*6, v_sentMessage_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*6 + 1, v_userClosedBody_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*6 + 2, v_omitBody_1014_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders___boxed(lean_object* v_dir_1029_, lean_object* v_messageHead_1030_, lean_object* v_writer_1031_){
_start:
{
uint8_t v_dir_boxed_1032_; lean_object* v_res_1033_; 
v_dir_boxed_1032_ = lean_unbox(v_dir_1029_);
v_res_1033_ = l___private_Std_Internal_Http_Protocol_H1_Writer_0__Std_Http_Protocol_H1_Writer_writeHeaders(v_dir_boxed_1032_, v_messageHead_1030_, v_writer_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(lean_object* v_a_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_key_1036_; lean_object* v_value_1037_; lean_object* v_tail_1038_; uint8_t v___x_1039_; 
v_key_1036_ = lean_ctor_get(v_x_1035_, 0);
v_value_1037_ = lean_ctor_get(v_x_1035_, 1);
v_tail_1038_ = lean_ctor_get(v_x_1035_, 2);
v___x_1039_ = lean_string_dec_eq(v_key_1036_, v_a_1034_);
if (v___x_1039_ == 0)
{
v_x_1035_ = v_tail_1038_;
goto _start;
}
else
{
lean_inc(v_value_1037_);
return v_value_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg___boxed(lean_object* v_a_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1041_, v_x_1042_);
lean_dec(v_x_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(lean_object* v_m_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_buckets_1046_; lean_object* v___x_1047_; uint64_t v___x_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v_fold_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_buckets_1046_ = lean_ctor_get(v_m_1044_, 1);
v___x_1047_ = lean_array_get_size(v_buckets_1046_);
v___x_1048_ = lean_string_hash(v_a_1045_);
v___x_1049_ = 32ULL;
v___x_1050_ = lean_uint64_shift_right(v___x_1048_, v___x_1049_);
v_fold_1051_ = lean_uint64_xor(v___x_1048_, v___x_1050_);
v___x_1052_ = 16ULL;
v___x_1053_ = lean_uint64_shift_right(v_fold_1051_, v___x_1052_);
v___x_1054_ = lean_uint64_xor(v_fold_1051_, v___x_1053_);
v___x_1055_ = lean_uint64_to_usize(v___x_1054_);
v___x_1056_ = lean_usize_of_nat(v___x_1047_);
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_sub(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_usize_land(v___x_1055_, v___x_1058_);
v___x_1060_ = lean_array_uget_borrowed(v_buckets_1046_, v___x_1059_);
v___x_1061_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1045_, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg___boxed(lean_object* v_m_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1062_, v_a_1063_);
lean_dec_ref(v_a_1063_);
lean_dec_ref(v_m_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(lean_object* v_s_1065_, lean_object* v_p_1066_){
_start:
{
uint32_t v___y_1068_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_string_utf8_byte_size(v_s_1065_);
v___x_1074_ = lean_nat_dec_eq(v_p_1066_, v___x_1073_);
if (v___x_1074_ == 0)
{
uint32_t v___x_1075_; uint32_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_string_utf8_get_fast(v_s_1065_, v_p_1066_);
v___x_1076_ = 65;
v___x_1077_ = lean_uint32_dec_le(v___x_1076_, v___x_1075_);
if (v___x_1077_ == 0)
{
v___y_1068_ = v___x_1075_;
goto v___jp_1067_;
}
else
{
uint32_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = 90;
v___x_1079_ = lean_uint32_dec_le(v___x_1075_, v___x_1078_);
if (v___x_1079_ == 0)
{
v___y_1068_ = v___x_1075_;
goto v___jp_1067_;
}
else
{
uint32_t v___x_1080_; uint32_t v___x_1081_; 
v___x_1080_ = 32;
v___x_1081_ = lean_uint32_add(v___x_1075_, v___x_1080_);
v___y_1068_ = v___x_1081_;
goto v___jp_1067_;
}
}
}
else
{
lean_dec(v_p_1066_);
return v_s_1065_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_inc(v_p_1066_);
v___x_1069_ = lean_string_utf8_set(v_s_1065_, v_p_1066_, v___y_1068_);
v___x_1070_ = l_Char_utf8Size(v___y_1068_);
v___x_1071_ = lean_nat_add(v_p_1066_, v___x_1070_);
lean_dec(v___x_1070_);
lean_dec(v_p_1066_);
v_s_1065_ = v___x_1069_;
v_p_1066_ = v___x_1071_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(uint8_t v_dir_1085_, lean_object* v_writer_1086_){
_start:
{
uint8_t v___y_1088_; 
if (v_dir_1085_ == 0)
{
uint8_t v___x_1107_; 
v___x_1107_ = 1;
v___y_1088_ = v___x_1107_;
goto v___jp_1087_;
}
else
{
uint8_t v___x_1108_; 
v___x_1108_ = 0;
v___y_1088_ = v___x_1108_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v_messageHead_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___f_1093_; uint8_t v___x_1094_; 
v_messageHead_1089_ = lean_ctor_get(v_writer_1086_, 4);
v___x_1090_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___y_1088_, v_messageHead_1089_);
v___x_1091_ = l_Std_Http_Header_Name_connection;
v___f_1092_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__0));
v___f_1093_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__1));
v___x_1094_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1092_, v___f_1093_, v___x_1091_, v___x_1090_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; 
lean_dec_ref(v___x_1090_);
v___x_1095_ = 1;
return v___x_1095_;
}
else
{
lean_object* v_entries_1096_; lean_object* v_indexes_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_entry_1100_; lean_object* v___x_1101_; lean_object* v_snd_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_entries_1096_ = lean_ctor_get(v___x_1090_, 0);
lean_inc_ref(v_entries_1096_);
v_indexes_1097_ = lean_ctor_get(v___x_1090_, 1);
lean_inc_ref(v_indexes_1097_);
lean_dec_ref(v___x_1090_);
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_indexes_1097_, v___x_1091_);
lean_dec_ref(v_indexes_1097_);
v___x_1099_ = lean_unsigned_to_nat(0u);
v_entry_1100_ = lean_array_fget(v___x_1098_, v___x_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_array_fget(v_entries_1096_, v_entry_1100_);
lean_dec(v_entry_1100_);
lean_dec_ref(v_entries_1096_);
v_snd_1102_ = lean_ctor_get(v___x_1101_, 1);
lean_inc(v_snd_1102_);
lean_dec(v___x_1101_);
v___x_1103_ = l_String_mapAux___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__1(v_snd_1102_, v___x_1099_);
v___x_1104_ = ((lean_object*)(l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___closed__2));
v___x_1105_ = lean_string_dec_eq(v___x_1103_, v___x_1104_);
lean_dec_ref(v___x_1103_);
if (v___x_1105_ == 0)
{
return v___x_1094_;
}
else
{
uint8_t v___x_1106_; 
v___x_1106_ = 0;
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_shouldKeepAlive___boxed(lean_object* v_dir_1109_, lean_object* v_writer_1110_){
_start:
{
uint8_t v_dir_boxed_1111_; uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_dir_boxed_1111_ = lean_unbox(v_dir_1109_);
v_res_1112_ = l_Std_Http_Protocol_H1_Writer_shouldKeepAlive(v_dir_boxed_1111_, v_writer_1110_);
lean_dec_ref(v_writer_1110_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(lean_object* v_00_u03b2_1114_, lean_object* v_m_1115_, lean_object* v_a_1116_, lean_object* v_hma_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___redArg(v_m_1115_, v_a_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_m_1120_, lean_object* v_a_1121_, lean_object* v_hma_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0(v_00_u03b2_1119_, v_m_1120_, v_a_1121_, v_hma_1122_);
lean_dec_ref(v_a_1121_);
lean_dec_ref(v_m_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(lean_object* v_00_u03b2_1124_, lean_object* v_a_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___redArg(v_a_1125_, v_x_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1129_, lean_object* v_a_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Writer_shouldKeepAlive_spec__0_spec__0(v_00_u03b2_1129_, v_a_1130_, v_x_1131_, v_x_1132_);
lean_dec(v_x_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___redArg(lean_object* v_writer_1134_){
_start:
{
lean_object* v_userData_1135_; lean_object* v_outputData_1136_; lean_object* v_knownSize_1137_; lean_object* v_messageHead_1138_; uint8_t v_sentMessage_1139_; uint8_t v_userClosedBody_1140_; uint8_t v_omitBody_1141_; lean_object* v_userDataBytes_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_userData_1135_ = lean_ctor_get(v_writer_1134_, 0);
v_outputData_1136_ = lean_ctor_get(v_writer_1134_, 1);
v_knownSize_1137_ = lean_ctor_get(v_writer_1134_, 3);
v_messageHead_1138_ = lean_ctor_get(v_writer_1134_, 4);
v_sentMessage_1139_ = lean_ctor_get_uint8(v_writer_1134_, sizeof(void*)*6);
v_userClosedBody_1140_ = lean_ctor_get_uint8(v_writer_1134_, sizeof(void*)*6 + 1);
v_omitBody_1141_ = lean_ctor_get_uint8(v_writer_1134_, sizeof(void*)*6 + 2);
v_userDataBytes_1142_ = lean_ctor_get(v_writer_1134_, 5);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_writer_1134_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_writer_1134_, 2);
lean_dec(v_unused_1151_);
v___x_1144_ = v_writer_1134_;
v_isShared_1145_ = v_isSharedCheck_1150_;
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
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_box(5);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 2, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_userData_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_outputData_1136_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_knownSize_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_messageHead_1138_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_userDataBytes_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*6, v_sentMessage_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*6 + 1, v_userClosedBody_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*6 + 2, v_omitBody_1141_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close(uint8_t v_dir_1152_, lean_object* v_writer_1153_){
_start:
{
lean_object* v_userData_1154_; lean_object* v_outputData_1155_; lean_object* v_knownSize_1156_; lean_object* v_messageHead_1157_; uint8_t v_sentMessage_1158_; uint8_t v_userClosedBody_1159_; uint8_t v_omitBody_1160_; lean_object* v_userDataBytes_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1169_; 
v_userData_1154_ = lean_ctor_get(v_writer_1153_, 0);
v_outputData_1155_ = lean_ctor_get(v_writer_1153_, 1);
v_knownSize_1156_ = lean_ctor_get(v_writer_1153_, 3);
v_messageHead_1157_ = lean_ctor_get(v_writer_1153_, 4);
v_sentMessage_1158_ = lean_ctor_get_uint8(v_writer_1153_, sizeof(void*)*6);
v_userClosedBody_1159_ = lean_ctor_get_uint8(v_writer_1153_, sizeof(void*)*6 + 1);
v_omitBody_1160_ = lean_ctor_get_uint8(v_writer_1153_, sizeof(void*)*6 + 2);
v_userDataBytes_1161_ = lean_ctor_get(v_writer_1153_, 5);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_writer_1153_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_writer_1153_, 2);
lean_dec(v_unused_1170_);
v___x_1163_ = v_writer_1153_;
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_userDataBytes_1161_);
lean_inc(v_messageHead_1157_);
lean_inc(v_knownSize_1156_);
lean_inc(v_outputData_1155_);
lean_inc(v_userData_1154_);
lean_dec(v_writer_1153_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(5);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 2, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_userData_1154_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_outputData_1155_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_knownSize_1156_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_messageHead_1157_);
lean_ctor_set(v_reuseFailAlloc_1168_, 5, v_userDataBytes_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*6, v_sentMessage_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*6 + 1, v_userClosedBody_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*6 + 2, v_omitBody_1160_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Writer_close___boxed(lean_object* v_dir_1171_, lean_object* v_writer_1172_){
_start:
{
uint8_t v_dir_boxed_1173_; lean_object* v_res_1174_; 
v_dir_boxed_1173_ = lean_unbox(v_dir_1171_);
v_res_1174_ = l_Std_Http_Protocol_H1_Writer_close(v_dir_boxed_1173_, v_writer_1172_);
return v_res_1174_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_Writer_instInhabitedState_default = _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState_default();
lean_mark_persistent(l_Std_Http_Protocol_H1_Writer_instInhabitedState_default);
l_Std_Http_Protocol_H1_Writer_instInhabitedState = _init_l_Std_Http_Protocol_H1_Writer_instInhabitedState();
lean_mark_persistent(l_Std_Http_Protocol_H1_Writer_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Protocol_H1_Writer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1_Writer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Protocol_H1_Writer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Protocol_H1_Writer(builtin);
}
#ifdef __cplusplus
}
#endif
